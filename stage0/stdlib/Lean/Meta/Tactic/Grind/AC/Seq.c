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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instInhabitedStartsWithResult_default;
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instInhabitedStartsWithResult_default(void){
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
lean_dec_ref(v_a_315_);
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
lean_inc(v_quotContext_322_);
v_currMacroScope_323_ = lean_ctor_get(v_a_315_, 2);
lean_inc(v_currMacroScope_323_);
v_ref_324_ = lean_ctor_get(v_a_315_, 5);
lean_inc(v_ref_324_);
lean_dec_ref(v_a_315_);
v___x_325_ = l_Lean_Syntax_getArg(v_x_314_, v___x_317_);
v___x_326_ = lean_unsigned_to_nat(2u);
v___x_327_ = l_Lean_Syntax_getArg(v_x_314_, v___x_326_);
lean_dec(v_x_314_);
v___x_328_ = 0;
v___x_329_ = l_Lean_SourceInfo_fromRef(v_ref_324_, v___x_328_);
lean_dec(v_ref_324_);
v___x_330_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__3));
v___x_331_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__5, &l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__5);
v___x_332_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__7));
v___x_333_ = l_Lean_addMacroScope(v_quotContext_322_, v___x_332_, v_currMacroScope_323_);
v___x_334_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__12));
lean_inc(v___x_329_);
v___x_335_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_335_, 0, v___x_329_);
lean_ctor_set(v___x_335_, 1, v___x_331_);
lean_ctor_set(v___x_335_, 2, v___x_333_);
lean_ctor_set(v___x_335_, 3, v___x_334_);
v___x_336_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__14));
lean_inc(v___x_329_);
v___x_337_ = l_Lean_Syntax_node2(v___x_329_, v___x_336_, v___x_325_, v___x_327_);
v___x_338_ = l_Lean_Syntax_node2(v___x_329_, v___x_330_, v___x_335_, v___x_337_);
v___x_339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
lean_ctor_set(v___x_339_, 1, v_a_316_);
return v___x_339_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______unexpand__Lean__Grind__AC__Seq__cons__1(lean_object* v_x_343_, lean_object* v_a_344_, lean_object* v_a_345_){
_start:
{
lean_object* v___x_346_; uint8_t v___x_347_; 
v___x_346_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__3));
lean_inc(v_x_343_);
v___x_347_ = l_Lean_Syntax_isOfKind(v_x_343_, v___x_346_);
if (v___x_347_ == 0)
{
lean_object* v___x_348_; lean_object* v___x_349_; 
lean_dec(v_x_343_);
v___x_348_ = lean_box(0);
v___x_349_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_349_, 0, v___x_348_);
lean_ctor_set(v___x_349_, 1, v_a_345_);
return v___x_349_;
}
else
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; uint8_t v___x_353_; 
v___x_350_ = lean_unsigned_to_nat(0u);
v___x_351_ = l_Lean_Syntax_getArg(v_x_343_, v___x_350_);
v___x_352_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______unexpand__Lean__Grind__AC__Seq__cons__1___closed__1));
lean_inc(v___x_351_);
v___x_353_ = l_Lean_Syntax_isOfKind(v___x_351_, v___x_352_);
if (v___x_353_ == 0)
{
lean_object* v___x_354_; lean_object* v___x_355_; 
lean_dec(v___x_351_);
lean_dec(v_x_343_);
v___x_354_ = lean_box(0);
v___x_355_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_355_, 0, v___x_354_);
lean_ctor_set(v___x_355_, 1, v_a_345_);
return v___x_355_;
}
else
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; uint8_t v___x_359_; 
v___x_356_ = lean_unsigned_to_nat(1u);
v___x_357_ = l_Lean_Syntax_getArg(v_x_343_, v___x_356_);
lean_dec(v_x_343_);
v___x_358_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_357_);
v___x_359_ = l_Lean_Syntax_matchesNull(v___x_357_, v___x_358_);
if (v___x_359_ == 0)
{
lean_object* v___x_360_; lean_object* v___x_361_; 
lean_dec(v___x_357_);
lean_dec(v___x_351_);
v___x_360_ = lean_box(0);
v___x_361_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_361_, 0, v___x_360_);
lean_ctor_set(v___x_361_, 1, v_a_345_);
return v___x_361_;
}
else
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v_ref_364_; uint8_t v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_362_ = l_Lean_Syntax_getArg(v___x_357_, v___x_350_);
v___x_363_ = l_Lean_Syntax_getArg(v___x_357_, v___x_356_);
lean_dec(v___x_357_);
v_ref_364_ = l_Lean_replaceRef(v___x_351_, v_a_344_);
lean_dec(v___x_351_);
v___x_365_ = 0;
v___x_366_ = l_Lean_SourceInfo_fromRef(v_ref_364_, v___x_365_);
lean_dec(v_ref_364_);
v___x_367_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__19));
v___x_368_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__22));
lean_inc(v___x_366_);
v___x_369_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_369_, 0, v___x_366_);
lean_ctor_set(v___x_369_, 1, v___x_368_);
v___x_370_ = l_Lean_Syntax_node3(v___x_366_, v___x_367_, v___x_362_, v___x_369_, v___x_363_);
v___x_371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_371_, 0, v___x_370_);
lean_ctor_set(v___x_371_, 1, v_a_345_);
return v___x_371_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______unexpand__Lean__Grind__AC__Seq__cons__1___boxed(lean_object* v_x_372_, lean_object* v_a_373_, lean_object* v_a_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______unexpand__Lean__Grind__AC__Seq__cons__1(v_x_372_, v_a_373_, v_a_374_);
lean_dec(v_a_373_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_instOfNatSeq__lean(lean_object* v_n_376_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_377_, 0, v_n_376_);
return v___x_377_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_a(void){
_start:
{
lean_object* v___x_378_; 
v___x_378_ = lean_unsigned_to_nat(1u);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_ctorIdx(lean_object* v_x_379_){
_start:
{
switch(lean_obj_tag(v_x_379_))
{
case 0:
{
lean_object* v___x_380_; 
v___x_380_ = lean_unsigned_to_nat(0u);
return v___x_380_;
}
case 1:
{
lean_object* v___x_381_; 
v___x_381_ = lean_unsigned_to_nat(1u);
return v___x_381_;
}
case 2:
{
lean_object* v___x_382_; 
v___x_382_ = lean_unsigned_to_nat(2u);
return v___x_382_;
}
case 3:
{
lean_object* v___x_383_; 
v___x_383_ = lean_unsigned_to_nat(3u);
return v___x_383_;
}
default: 
{
lean_object* v___x_384_; 
v___x_384_ = lean_unsigned_to_nat(4u);
return v___x_384_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_ctorIdx___boxed(lean_object* v_x_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_Lean_Grind_AC_SubseqResult_ctorIdx(v_x_385_);
lean_dec(v_x_385_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_ctorElim___redArg(lean_object* v_t_387_, lean_object* v_k_388_){
_start:
{
switch(lean_obj_tag(v_t_387_))
{
case 2:
{
lean_object* v_s_389_; lean_object* v___x_390_; 
v_s_389_ = lean_ctor_get(v_t_387_, 0);
lean_inc_ref(v_s_389_);
lean_dec_ref(v_t_387_);
v___x_390_ = lean_apply_1(v_k_388_, v_s_389_);
return v___x_390_;
}
case 3:
{
lean_object* v_s_391_; lean_object* v___x_392_; 
v_s_391_ = lean_ctor_get(v_t_387_, 0);
lean_inc_ref(v_s_391_);
lean_dec_ref(v_t_387_);
v___x_392_ = lean_apply_1(v_k_388_, v_s_391_);
return v___x_392_;
}
case 4:
{
lean_object* v_p_393_; lean_object* v_s_394_; lean_object* v___x_395_; 
v_p_393_ = lean_ctor_get(v_t_387_, 0);
lean_inc_ref(v_p_393_);
v_s_394_ = lean_ctor_get(v_t_387_, 1);
lean_inc_ref(v_s_394_);
lean_dec_ref(v_t_387_);
v___x_395_ = lean_apply_2(v_k_388_, v_p_393_, v_s_394_);
return v___x_395_;
}
default: 
{
lean_dec(v_t_387_);
return v_k_388_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_ctorElim(lean_object* v_motive_396_, lean_object* v_ctorIdx_397_, lean_object* v_t_398_, lean_object* v_h_399_, lean_object* v_k_400_){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = l_Lean_Grind_AC_SubseqResult_ctorElim___redArg(v_t_398_, v_k_400_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_ctorElim___boxed(lean_object* v_motive_402_, lean_object* v_ctorIdx_403_, lean_object* v_t_404_, lean_object* v_h_405_, lean_object* v_k_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_Lean_Grind_AC_SubseqResult_ctorElim(v_motive_402_, v_ctorIdx_403_, v_t_404_, v_h_405_, v_k_406_);
lean_dec(v_ctorIdx_403_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_false_elim___redArg(lean_object* v_t_408_, lean_object* v_false_409_){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = l_Lean_Grind_AC_SubseqResult_ctorElim___redArg(v_t_408_, v_false_409_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_false_elim(lean_object* v_motive_411_, lean_object* v_t_412_, lean_object* v_h_413_, lean_object* v_false_414_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = l_Lean_Grind_AC_SubseqResult_ctorElim___redArg(v_t_412_, v_false_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_exact_elim___redArg(lean_object* v_t_416_, lean_object* v_exact_417_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l_Lean_Grind_AC_SubseqResult_ctorElim___redArg(v_t_416_, v_exact_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_exact_elim(lean_object* v_motive_419_, lean_object* v_t_420_, lean_object* v_h_421_, lean_object* v_exact_422_){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = l_Lean_Grind_AC_SubseqResult_ctorElim___redArg(v_t_420_, v_exact_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_prefix_elim___redArg(lean_object* v_t_424_, lean_object* v_prefix_425_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = l_Lean_Grind_AC_SubseqResult_ctorElim___redArg(v_t_424_, v_prefix_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_prefix_elim(lean_object* v_motive_427_, lean_object* v_t_428_, lean_object* v_h_429_, lean_object* v_prefix_430_){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = l_Lean_Grind_AC_SubseqResult_ctorElim___redArg(v_t_428_, v_prefix_430_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_suffix_elim___redArg(lean_object* v_t_432_, lean_object* v_suffix_433_){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = l_Lean_Grind_AC_SubseqResult_ctorElim___redArg(v_t_432_, v_suffix_433_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_suffix_elim(lean_object* v_motive_435_, lean_object* v_t_436_, lean_object* v_h_437_, lean_object* v_suffix_438_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = l_Lean_Grind_AC_SubseqResult_ctorElim___redArg(v_t_436_, v_suffix_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_middle_elim___redArg(lean_object* v_t_440_, lean_object* v_middle_441_){
_start:
{
lean_object* v___x_442_; 
v___x_442_ = l_Lean_Grind_AC_SubseqResult_ctorElim___redArg(v_t_440_, v_middle_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_middle_elim(lean_object* v_motive_443_, lean_object* v_t_444_, lean_object* v_h_445_, lean_object* v_middle_446_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l_Lean_Grind_AC_SubseqResult_ctorElim___redArg(v_t_444_, v_middle_446_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_subseq_go(lean_object* v_s_u2081_448_, lean_object* v_s_u2082_449_, lean_object* v_acc_450_){
_start:
{
if (lean_obj_tag(v_s_u2082_449_) == 0)
{
uint8_t v___x_451_; 
v___x_451_ = l_Lean_Grind_AC_instBEqSeq_beq(v_s_u2081_448_, v_s_u2082_449_);
lean_dec_ref(v_s_u2082_449_);
lean_dec_ref(v_s_u2081_448_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; 
lean_dec_ref(v_acc_450_);
v___x_452_ = lean_box(0);
return v___x_452_;
}
else
{
lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_453_ = l_Lean_Grind_AC_Seq_reverse(v_acc_450_);
v___x_454_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_454_, 0, v___x_453_);
return v___x_454_;
}
}
else
{
lean_object* v_x_455_; lean_object* v_s_456_; lean_object* v___x_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_470_; 
v_x_455_ = lean_ctor_get(v_s_u2082_449_, 0);
lean_inc(v_x_455_);
v_s_456_ = lean_ctor_get(v_s_u2082_449_, 1);
lean_inc_ref(v_s_456_);
lean_inc_ref(v_s_u2081_448_);
v___x_457_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_startsWith(v_s_u2082_449_, v_s_u2081_448_);
v_isSharedCheck_470_ = !lean_is_exclusive(v_s_u2082_449_);
if (v_isSharedCheck_470_ == 0)
{
lean_object* v_unused_471_; lean_object* v_unused_472_; 
v_unused_471_ = lean_ctor_get(v_s_u2082_449_, 1);
lean_dec(v_unused_471_);
v_unused_472_ = lean_ctor_get(v_s_u2082_449_, 0);
lean_dec(v_unused_472_);
v___x_459_ = v_s_u2082_449_;
v_isShared_460_ = v_isSharedCheck_470_;
goto v_resetjp_458_;
}
else
{
lean_dec(v_s_u2082_449_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_470_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
switch(lean_obj_tag(v___x_457_))
{
case 0:
{
lean_object* v___x_462_; 
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 1, v_acc_450_);
v___x_462_ = v___x_459_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_x_455_);
lean_ctor_set(v_reuseFailAlloc_464_, 1, v_acc_450_);
v___x_462_ = v_reuseFailAlloc_464_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
v_s_u2082_449_ = v_s_456_;
v_acc_450_ = v___x_462_;
goto _start;
}
}
case 1:
{
lean_object* v___x_465_; lean_object* v___x_466_; 
lean_del_object(v___x_459_);
lean_dec_ref(v_s_456_);
lean_dec(v_x_455_);
lean_dec_ref(v_s_u2081_448_);
v___x_465_ = l_Lean_Grind_AC_Seq_reverse(v_acc_450_);
v___x_466_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_466_, 0, v___x_465_);
return v___x_466_;
}
default: 
{
lean_object* v_s_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
lean_del_object(v___x_459_);
lean_dec_ref(v_s_456_);
lean_dec(v_x_455_);
lean_dec_ref(v_s_u2081_448_);
v_s_467_ = lean_ctor_get(v___x_457_, 0);
lean_inc_ref(v_s_467_);
lean_dec_ref(v___x_457_);
v___x_468_ = l_Lean_Grind_AC_Seq_reverse(v_acc_450_);
v___x_469_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_469_, 0, v___x_468_);
lean_ctor_set(v___x_469_, 1, v_s_467_);
return v___x_469_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_subseq(lean_object* v_s_u2081_473_, lean_object* v_s_u2082_474_){
_start:
{
if (lean_obj_tag(v_s_u2082_474_) == 0)
{
uint8_t v___x_475_; 
v___x_475_ = l_Lean_Grind_AC_instBEqSeq_beq(v_s_u2081_473_, v_s_u2082_474_);
lean_dec_ref(v_s_u2082_474_);
lean_dec_ref(v_s_u2081_473_);
if (v___x_475_ == 0)
{
lean_object* v___x_476_; 
v___x_476_ = lean_box(0);
return v___x_476_;
}
else
{
lean_object* v___x_477_; 
v___x_477_ = lean_box(1);
return v___x_477_;
}
}
else
{
lean_object* v_x_478_; lean_object* v_s_479_; lean_object* v___x_480_; 
v_x_478_ = lean_ctor_get(v_s_u2082_474_, 0);
lean_inc(v_x_478_);
v_s_479_ = lean_ctor_get(v_s_u2082_474_, 1);
lean_inc_ref(v_s_479_);
lean_inc_ref(v_s_u2081_473_);
v___x_480_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_startsWith(v_s_u2082_474_, v_s_u2081_473_);
lean_dec_ref(v_s_u2082_474_);
switch(lean_obj_tag(v___x_480_))
{
case 0:
{
lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_481_, 0, v_x_478_);
v___x_482_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_subseq_go(v_s_u2081_473_, v_s_479_, v___x_481_);
return v___x_482_;
}
case 1:
{
lean_object* v___x_483_; 
lean_dec_ref(v_s_479_);
lean_dec(v_x_478_);
lean_dec_ref(v_s_u2081_473_);
v___x_483_ = lean_box(1);
return v___x_483_;
}
default: 
{
lean_object* v_s_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_491_; 
lean_dec_ref(v_s_479_);
lean_dec(v_x_478_);
lean_dec_ref(v_s_u2081_473_);
v_s_484_ = lean_ctor_get(v___x_480_, 0);
v_isSharedCheck_491_ = !lean_is_exclusive(v___x_480_);
if (v_isSharedCheck_491_ == 0)
{
v___x_486_ = v___x_480_;
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_s_484_);
lean_dec(v___x_480_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_489_; 
if (v_isShared_487_ == 0)
{
v___x_489_ = v___x_486_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v_s_484_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
return v___x_489_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubsetResult_ctorIdx(lean_object* v_x_492_){
_start:
{
switch(lean_obj_tag(v_x_492_))
{
case 0:
{
lean_object* v___x_493_; 
v___x_493_ = lean_unsigned_to_nat(0u);
return v___x_493_;
}
case 1:
{
lean_object* v___x_494_; 
v___x_494_ = lean_unsigned_to_nat(1u);
return v___x_494_;
}
default: 
{
lean_object* v___x_495_; 
v___x_495_ = lean_unsigned_to_nat(2u);
return v___x_495_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubsetResult_ctorIdx___boxed(lean_object* v_x_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l_Lean_Grind_AC_SubsetResult_ctorIdx(v_x_496_);
lean_dec(v_x_496_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubsetResult_ctorElim___redArg(lean_object* v_t_498_, lean_object* v_k_499_){
_start:
{
if (lean_obj_tag(v_t_498_) == 2)
{
lean_object* v_s_500_; lean_object* v___x_501_; 
v_s_500_ = lean_ctor_get(v_t_498_, 0);
lean_inc_ref(v_s_500_);
lean_dec_ref(v_t_498_);
v___x_501_ = lean_apply_1(v_k_499_, v_s_500_);
return v___x_501_;
}
else
{
lean_dec(v_t_498_);
return v_k_499_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubsetResult_ctorElim(lean_object* v_motive_502_, lean_object* v_ctorIdx_503_, lean_object* v_t_504_, lean_object* v_h_505_, lean_object* v_k_506_){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = l_Lean_Grind_AC_SubsetResult_ctorElim___redArg(v_t_504_, v_k_506_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubsetResult_ctorElim___boxed(lean_object* v_motive_508_, lean_object* v_ctorIdx_509_, lean_object* v_t_510_, lean_object* v_h_511_, lean_object* v_k_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_Lean_Grind_AC_SubsetResult_ctorElim(v_motive_508_, v_ctorIdx_509_, v_t_510_, v_h_511_, v_k_512_);
lean_dec(v_ctorIdx_509_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubsetResult_false_elim___redArg(lean_object* v_t_514_, lean_object* v_false_515_){
_start:
{
lean_object* v___x_516_; 
v___x_516_ = l_Lean_Grind_AC_SubsetResult_ctorElim___redArg(v_t_514_, v_false_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubsetResult_false_elim(lean_object* v_motive_517_, lean_object* v_t_518_, lean_object* v_h_519_, lean_object* v_false_520_){
_start:
{
lean_object* v___x_521_; 
v___x_521_ = l_Lean_Grind_AC_SubsetResult_ctorElim___redArg(v_t_518_, v_false_520_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubsetResult_exact_elim___redArg(lean_object* v_t_522_, lean_object* v_exact_523_){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = l_Lean_Grind_AC_SubsetResult_ctorElim___redArg(v_t_522_, v_exact_523_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubsetResult_exact_elim(lean_object* v_motive_525_, lean_object* v_t_526_, lean_object* v_h_527_, lean_object* v_exact_528_){
_start:
{
lean_object* v___x_529_; 
v___x_529_ = l_Lean_Grind_AC_SubsetResult_ctorElim___redArg(v_t_526_, v_exact_528_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubsetResult_strict_elim___redArg(lean_object* v_t_530_, lean_object* v_strict_531_){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = l_Lean_Grind_AC_SubsetResult_ctorElim___redArg(v_t_530_, v_strict_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubsetResult_strict_elim(lean_object* v_motive_533_, lean_object* v_t_534_, lean_object* v_h_535_, lean_object* v_strict_536_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l_Lean_Grind_AC_SubsetResult_ctorElim___redArg(v_t_534_, v_strict_536_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_subset_go(lean_object* v_s_u2081_538_, lean_object* v_s_u2082_539_, lean_object* v_acc_540_){
_start:
{
if (lean_obj_tag(v_s_u2081_538_) == 0)
{
if (lean_obj_tag(v_s_u2082_539_) == 0)
{
lean_object* v_x_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_552_; 
v_x_541_ = lean_ctor_get(v_s_u2081_538_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v_s_u2081_538_);
if (v_isSharedCheck_552_ == 0)
{
v___x_543_ = v_s_u2081_538_;
v_isShared_544_ = v_isSharedCheck_552_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_x_541_);
lean_dec(v_s_u2081_538_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_552_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v_x_545_; uint8_t v___x_546_; 
v_x_545_ = lean_ctor_get(v_s_u2082_539_, 0);
lean_inc(v_x_545_);
lean_dec_ref(v_s_u2082_539_);
v___x_546_ = lean_nat_dec_eq(v_x_541_, v_x_545_);
lean_dec(v_x_545_);
lean_dec(v_x_541_);
if (v___x_546_ == 0)
{
lean_object* v___x_547_; 
lean_del_object(v___x_543_);
lean_dec_ref(v_acc_540_);
v___x_547_ = lean_box(0);
return v___x_547_;
}
else
{
lean_object* v___x_548_; lean_object* v___x_550_; 
v___x_548_ = l_Lean_Grind_AC_Seq_reverse(v_acc_540_);
if (v_isShared_544_ == 0)
{
lean_ctor_set_tag(v___x_543_, 2);
lean_ctor_set(v___x_543_, 0, v___x_548_);
v___x_550_ = v___x_543_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v___x_548_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
}
else
{
lean_object* v_x_553_; lean_object* v_x_554_; lean_object* v_s_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_576_; 
v_x_553_ = lean_ctor_get(v_s_u2081_538_, 0);
v_x_554_ = lean_ctor_get(v_s_u2082_539_, 0);
v_s_555_ = lean_ctor_get(v_s_u2082_539_, 1);
v_isSharedCheck_576_ = !lean_is_exclusive(v_s_u2082_539_);
if (v_isSharedCheck_576_ == 0)
{
v___x_557_ = v_s_u2082_539_;
v_isShared_558_ = v_isSharedCheck_576_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_s_555_);
lean_inc(v_x_554_);
lean_dec(v_s_u2082_539_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_576_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
uint8_t v___x_559_; 
v___x_559_ = lean_nat_dec_eq(v_x_553_, v_x_554_);
if (v___x_559_ == 0)
{
uint8_t v___x_560_; 
v___x_560_ = lean_nat_dec_lt(v_x_553_, v_x_554_);
if (v___x_560_ == 0)
{
lean_object* v___x_562_; 
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 1, v_acc_540_);
v___x_562_ = v___x_557_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v_x_554_);
lean_ctor_set(v_reuseFailAlloc_564_, 1, v_acc_540_);
v___x_562_ = v_reuseFailAlloc_564_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
v_s_u2082_539_ = v_s_555_;
v_acc_540_ = v___x_562_;
goto _start;
}
}
else
{
lean_object* v___x_565_; 
lean_del_object(v___x_557_);
lean_dec_ref(v_s_555_);
lean_dec(v_x_554_);
lean_dec_ref(v_s_u2081_538_);
lean_dec_ref(v_acc_540_);
v___x_565_ = lean_box(0);
return v___x_565_;
}
}
else
{
lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_574_; 
lean_del_object(v___x_557_);
lean_dec(v_x_554_);
v_isSharedCheck_574_ = !lean_is_exclusive(v_s_u2081_538_);
if (v_isSharedCheck_574_ == 0)
{
lean_object* v_unused_575_; 
v_unused_575_ = lean_ctor_get(v_s_u2081_538_, 0);
lean_dec(v_unused_575_);
v___x_567_ = v_s_u2081_538_;
v_isShared_568_ = v_isSharedCheck_574_;
goto v_resetjp_566_;
}
else
{
lean_dec(v_s_u2081_538_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_574_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_572_; 
v___x_569_ = l_Lean_Grind_AC_Seq_reverse(v_acc_540_);
v___x_570_ = l_Lean_Grind_AC_Seq_concat(v___x_569_, v_s_555_);
if (v_isShared_568_ == 0)
{
lean_ctor_set_tag(v___x_567_, 2);
lean_ctor_set(v___x_567_, 0, v___x_570_);
v___x_572_ = v___x_567_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v___x_570_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_s_u2082_539_) == 0)
{
lean_object* v___x_577_; 
lean_dec_ref(v_s_u2082_539_);
lean_dec_ref(v_s_u2081_538_);
lean_dec_ref(v_acc_540_);
v___x_577_ = lean_box(0);
return v___x_577_;
}
else
{
lean_object* v_x_578_; lean_object* v_s_579_; lean_object* v_x_580_; lean_object* v_s_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_593_; 
v_x_578_ = lean_ctor_get(v_s_u2081_538_, 0);
v_s_579_ = lean_ctor_get(v_s_u2081_538_, 1);
v_x_580_ = lean_ctor_get(v_s_u2082_539_, 0);
v_s_581_ = lean_ctor_get(v_s_u2082_539_, 1);
v_isSharedCheck_593_ = !lean_is_exclusive(v_s_u2082_539_);
if (v_isSharedCheck_593_ == 0)
{
v___x_583_ = v_s_u2082_539_;
v_isShared_584_ = v_isSharedCheck_593_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_s_581_);
lean_inc(v_x_580_);
lean_dec(v_s_u2082_539_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_593_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
uint8_t v___x_585_; 
v___x_585_ = lean_nat_dec_eq(v_x_578_, v_x_580_);
if (v___x_585_ == 0)
{
uint8_t v___x_586_; 
v___x_586_ = lean_nat_dec_lt(v_x_578_, v_x_580_);
if (v___x_586_ == 0)
{
lean_object* v___x_588_; 
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 1, v_acc_540_);
v___x_588_ = v___x_583_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_x_580_);
lean_ctor_set(v_reuseFailAlloc_590_, 1, v_acc_540_);
v___x_588_ = v_reuseFailAlloc_590_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
v_s_u2082_539_ = v_s_581_;
v_acc_540_ = v___x_588_;
goto _start;
}
}
else
{
lean_object* v___x_591_; 
lean_del_object(v___x_583_);
lean_dec_ref(v_s_581_);
lean_dec(v_x_580_);
lean_dec_ref(v_s_u2081_538_);
lean_dec_ref(v_acc_540_);
v___x_591_ = lean_box(0);
return v___x_591_;
}
}
else
{
lean_inc_ref(v_s_579_);
lean_del_object(v___x_583_);
lean_dec(v_x_580_);
lean_dec_ref(v_s_u2081_538_);
v_s_u2081_538_ = v_s_579_;
v_s_u2082_539_ = v_s_581_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_subset(lean_object* v_s_u2081_594_, lean_object* v_s_u2082_595_){
_start:
{
if (lean_obj_tag(v_s_u2081_594_) == 0)
{
if (lean_obj_tag(v_s_u2082_595_) == 0)
{
lean_object* v_x_596_; lean_object* v_x_597_; uint8_t v___x_598_; 
v_x_596_ = lean_ctor_get(v_s_u2081_594_, 0);
lean_inc(v_x_596_);
lean_dec_ref(v_s_u2081_594_);
v_x_597_ = lean_ctor_get(v_s_u2082_595_, 0);
lean_inc(v_x_597_);
lean_dec_ref(v_s_u2082_595_);
v___x_598_ = lean_nat_dec_eq(v_x_596_, v_x_597_);
lean_dec(v_x_597_);
lean_dec(v_x_596_);
if (v___x_598_ == 0)
{
lean_object* v___x_599_; 
v___x_599_ = lean_box(0);
return v___x_599_;
}
else
{
lean_object* v___x_600_; 
v___x_600_ = lean_box(1);
return v___x_600_;
}
}
else
{
lean_object* v_x_601_; lean_object* v_x_602_; lean_object* v_s_603_; uint8_t v___x_604_; 
v_x_601_ = lean_ctor_get(v_s_u2081_594_, 0);
v_x_602_ = lean_ctor_get(v_s_u2082_595_, 0);
lean_inc(v_x_602_);
v_s_603_ = lean_ctor_get(v_s_u2082_595_, 1);
lean_inc_ref(v_s_603_);
lean_dec_ref(v_s_u2082_595_);
v___x_604_ = lean_nat_dec_eq(v_x_601_, v_x_602_);
if (v___x_604_ == 0)
{
uint8_t v___x_605_; 
v___x_605_ = lean_nat_dec_lt(v_x_601_, v_x_602_);
if (v___x_605_ == 0)
{
lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_606_, 0, v_x_602_);
v___x_607_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_subset_go(v_s_u2081_594_, v_s_603_, v___x_606_);
return v___x_607_;
}
else
{
lean_object* v___x_608_; 
lean_dec_ref(v_s_603_);
lean_dec(v_x_602_);
lean_dec_ref(v_s_u2081_594_);
v___x_608_ = lean_box(0);
return v___x_608_;
}
}
else
{
lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_615_; 
lean_dec(v_x_602_);
v_isSharedCheck_615_ = !lean_is_exclusive(v_s_u2081_594_);
if (v_isSharedCheck_615_ == 0)
{
lean_object* v_unused_616_; 
v_unused_616_ = lean_ctor_get(v_s_u2081_594_, 0);
lean_dec(v_unused_616_);
v___x_610_ = v_s_u2081_594_;
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
else
{
lean_dec(v_s_u2081_594_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_613_; 
if (v_isShared_611_ == 0)
{
lean_ctor_set_tag(v___x_610_, 2);
lean_ctor_set(v___x_610_, 0, v_s_603_);
v___x_613_ = v___x_610_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_s_603_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_s_u2082_595_) == 0)
{
lean_object* v___x_617_; 
lean_dec_ref(v_s_u2082_595_);
lean_dec_ref(v_s_u2081_594_);
v___x_617_ = lean_box(0);
return v___x_617_;
}
else
{
lean_object* v_x_618_; lean_object* v_s_619_; lean_object* v_x_620_; lean_object* v_s_621_; uint8_t v___x_622_; 
v_x_618_ = lean_ctor_get(v_s_u2081_594_, 0);
v_s_619_ = lean_ctor_get(v_s_u2081_594_, 1);
v_x_620_ = lean_ctor_get(v_s_u2082_595_, 0);
lean_inc(v_x_620_);
v_s_621_ = lean_ctor_get(v_s_u2082_595_, 1);
lean_inc_ref(v_s_621_);
lean_dec_ref(v_s_u2082_595_);
v___x_622_ = lean_nat_dec_eq(v_x_618_, v_x_620_);
if (v___x_622_ == 0)
{
uint8_t v___x_623_; 
v___x_623_ = lean_nat_dec_lt(v_x_618_, v_x_620_);
if (v___x_623_ == 0)
{
lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_624_, 0, v_x_620_);
v___x_625_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_subset_go(v_s_u2081_594_, v_s_621_, v___x_624_);
return v___x_625_;
}
else
{
lean_object* v___x_626_; 
lean_dec_ref(v_s_621_);
lean_dec(v_x_620_);
lean_dec_ref(v_s_u2081_594_);
v___x_626_ = lean_box(0);
return v___x_626_;
}
}
else
{
lean_inc_ref(v_s_619_);
lean_dec(v_x_620_);
lean_dec_ref(v_s_u2081_594_);
v_s_u2081_594_ = v_s_619_;
v_s_u2082_595_ = v_s_621_;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_isSorted_go(lean_object* v_x_628_, lean_object* v_s_629_){
_start:
{
if (lean_obj_tag(v_s_629_) == 0)
{
lean_object* v_x_630_; uint8_t v___x_631_; 
v_x_630_ = lean_ctor_get(v_s_629_, 0);
v___x_631_ = lean_nat_dec_le(v_x_628_, v_x_630_);
return v___x_631_;
}
else
{
lean_object* v_x_632_; lean_object* v_s_633_; uint8_t v___x_634_; 
v_x_632_ = lean_ctor_get(v_s_629_, 0);
v_s_633_ = lean_ctor_get(v_s_629_, 1);
v___x_634_ = lean_nat_dec_le(v_x_628_, v_x_632_);
if (v___x_634_ == 0)
{
return v___x_634_;
}
else
{
v_x_628_ = v_x_632_;
v_s_629_ = v_s_633_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_isSorted_go___boxed(lean_object* v_x_636_, lean_object* v_s_637_){
_start:
{
uint8_t v_res_638_; lean_object* v_r_639_; 
v_res_638_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_isSorted_go(v_x_636_, v_s_637_);
lean_dec_ref(v_s_637_);
lean_dec(v_x_636_);
v_r_639_ = lean_box(v_res_638_);
return v_r_639_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_AC_Seq_isSorted(lean_object* v_s_640_){
_start:
{
if (lean_obj_tag(v_s_640_) == 0)
{
uint8_t v___x_641_; 
v___x_641_ = 1;
return v___x_641_;
}
else
{
lean_object* v_x_642_; lean_object* v_s_643_; uint8_t v___x_644_; 
v_x_642_ = lean_ctor_get(v_s_640_, 0);
v_s_643_ = lean_ctor_get(v_s_640_, 1);
v___x_644_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_isSorted_go(v_x_642_, v_s_643_);
return v___x_644_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_isSorted___boxed(lean_object* v_s_645_){
_start:
{
uint8_t v_res_646_; lean_object* v_r_647_; 
v_res_646_ = l_Lean_Grind_AC_Seq_isSorted(v_s_645_);
lean_dec_ref(v_s_645_);
v_r_647_ = lean_box(v_res_646_);
return v_r_647_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_AC_Seq_contains(lean_object* v_s_648_, lean_object* v_x_649_){
_start:
{
if (lean_obj_tag(v_s_648_) == 0)
{
lean_object* v_x_650_; uint8_t v___x_651_; 
v_x_650_ = lean_ctor_get(v_s_648_, 0);
v___x_651_ = lean_nat_dec_eq(v_x_649_, v_x_650_);
return v___x_651_;
}
else
{
lean_object* v_x_652_; lean_object* v_s_653_; uint8_t v___x_654_; 
v_x_652_ = lean_ctor_get(v_s_648_, 0);
v_s_653_ = lean_ctor_get(v_s_648_, 1);
v___x_654_ = lean_nat_dec_eq(v_x_649_, v_x_652_);
if (v___x_654_ == 0)
{
v_s_648_ = v_s_653_;
goto _start;
}
else
{
return v___x_654_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_contains___boxed(lean_object* v_s_656_, lean_object* v_x_657_){
_start:
{
uint8_t v_res_658_; lean_object* v_r_659_; 
v_res_658_ = l_Lean_Grind_AC_Seq_contains(v_s_656_, v_x_657_);
lean_dec(v_x_657_);
lean_dec_ref(v_s_656_);
v_r_659_ = lean_box(v_res_658_);
return v_r_659_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_noAdjacentDuplicates_go(lean_object* v_x_660_, lean_object* v_s_661_){
_start:
{
if (lean_obj_tag(v_s_661_) == 0)
{
lean_object* v_x_662_; uint8_t v___x_663_; 
v_x_662_ = lean_ctor_get(v_s_661_, 0);
v___x_663_ = lean_nat_dec_eq(v_x_660_, v_x_662_);
if (v___x_663_ == 0)
{
uint8_t v___x_664_; 
v___x_664_ = 1;
return v___x_664_;
}
else
{
uint8_t v___x_665_; 
v___x_665_ = 0;
return v___x_665_;
}
}
else
{
lean_object* v_x_666_; lean_object* v_s_667_; uint8_t v___x_668_; 
v_x_666_ = lean_ctor_get(v_s_661_, 0);
v_s_667_ = lean_ctor_get(v_s_661_, 1);
v___x_668_ = lean_nat_dec_eq(v_x_660_, v_x_666_);
if (v___x_668_ == 0)
{
v_x_660_ = v_x_666_;
v_s_661_ = v_s_667_;
goto _start;
}
else
{
uint8_t v___x_670_; 
v___x_670_ = 0;
return v___x_670_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_noAdjacentDuplicates_go___boxed(lean_object* v_x_671_, lean_object* v_s_672_){
_start:
{
uint8_t v_res_673_; lean_object* v_r_674_; 
v_res_673_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_noAdjacentDuplicates_go(v_x_671_, v_s_672_);
lean_dec_ref(v_s_672_);
lean_dec(v_x_671_);
v_r_674_ = lean_box(v_res_673_);
return v_r_674_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_AC_Seq_noAdjacentDuplicates(lean_object* v_s_675_){
_start:
{
if (lean_obj_tag(v_s_675_) == 0)
{
uint8_t v___x_676_; 
v___x_676_ = 1;
return v___x_676_;
}
else
{
lean_object* v_x_677_; lean_object* v_s_678_; uint8_t v___x_679_; 
v_x_677_ = lean_ctor_get(v_s_675_, 0);
v_s_678_ = lean_ctor_get(v_s_675_, 1);
v___x_679_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_noAdjacentDuplicates_go(v_x_677_, v_s_678_);
return v___x_679_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_noAdjacentDuplicates___boxed(lean_object* v_s_680_){
_start:
{
uint8_t v_res_681_; lean_object* v_r_682_; 
v_res_681_ = l_Lean_Grind_AC_Seq_noAdjacentDuplicates(v_s_680_);
lean_dec_ref(v_s_680_);
v_r_682_ = lean_box(v_res_681_);
return v_r_682_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_AC_Seq_sharesVar(lean_object* v_s_u2081_683_, lean_object* v_s_u2082_684_){
_start:
{
if (lean_obj_tag(v_s_u2081_683_) == 0)
{
if (lean_obj_tag(v_s_u2082_684_) == 0)
{
lean_object* v_x_685_; lean_object* v_x_686_; uint8_t v___x_687_; 
v_x_685_ = lean_ctor_get(v_s_u2081_683_, 0);
v_x_686_ = lean_ctor_get(v_s_u2082_684_, 0);
v___x_687_ = lean_nat_dec_eq(v_x_685_, v_x_686_);
return v___x_687_;
}
else
{
lean_object* v_x_688_; lean_object* v_x_689_; lean_object* v_s_690_; uint8_t v___x_691_; 
v_x_688_ = lean_ctor_get(v_s_u2081_683_, 0);
v_x_689_ = lean_ctor_get(v_s_u2082_684_, 0);
v_s_690_ = lean_ctor_get(v_s_u2082_684_, 1);
v___x_691_ = lean_nat_dec_eq(v_x_688_, v_x_689_);
if (v___x_691_ == 0)
{
v_s_u2082_684_ = v_s_690_;
goto _start;
}
else
{
return v___x_691_;
}
}
}
else
{
if (lean_obj_tag(v_s_u2082_684_) == 0)
{
lean_object* v_x_693_; lean_object* v_s_694_; lean_object* v_x_695_; uint8_t v___x_696_; 
v_x_693_ = lean_ctor_get(v_s_u2081_683_, 0);
v_s_694_ = lean_ctor_get(v_s_u2081_683_, 1);
v_x_695_ = lean_ctor_get(v_s_u2082_684_, 0);
v___x_696_ = lean_nat_dec_eq(v_x_693_, v_x_695_);
if (v___x_696_ == 0)
{
v_s_u2081_683_ = v_s_694_;
goto _start;
}
else
{
return v___x_696_;
}
}
else
{
lean_object* v_x_698_; lean_object* v_s_699_; lean_object* v_x_700_; lean_object* v_s_701_; uint8_t v___x_702_; 
v_x_698_ = lean_ctor_get(v_s_u2081_683_, 0);
v_s_699_ = lean_ctor_get(v_s_u2081_683_, 1);
v_x_700_ = lean_ctor_get(v_s_u2082_684_, 0);
v_s_701_ = lean_ctor_get(v_s_u2082_684_, 1);
v___x_702_ = lean_nat_dec_eq(v_x_698_, v_x_700_);
if (v___x_702_ == 0)
{
uint8_t v___x_703_; 
v___x_703_ = lean_nat_dec_lt(v_x_698_, v_x_700_);
if (v___x_703_ == 0)
{
v_s_u2082_684_ = v_s_701_;
goto _start;
}
else
{
v_s_u2081_683_ = v_s_699_;
goto _start;
}
}
else
{
return v___x_702_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_sharesVar___boxed(lean_object* v_s_u2081_706_, lean_object* v_s_u2082_707_){
_start:
{
uint8_t v_res_708_; lean_object* v_r_709_; 
v_res_708_ = l_Lean_Grind_AC_Seq_sharesVar(v_s_u2081_706_, v_s_u2082_707_);
lean_dec_ref(v_s_u2082_707_);
lean_dec_ref(v_s_u2081_706_);
v_r_709_ = lean_box(v_res_708_);
return v_r_709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_startsWith_match__1_splitter___redArg(lean_object* v_s_u2082_710_, lean_object* v_s_u2081_711_, lean_object* v_h__1_712_, lean_object* v_h__2_713_, lean_object* v_h__3_714_, lean_object* v_h__4_715_){
_start:
{
if (lean_obj_tag(v_s_u2082_710_) == 0)
{
lean_dec(v_h__4_715_);
lean_dec(v_h__3_714_);
if (lean_obj_tag(v_s_u2081_711_) == 0)
{
lean_object* v_x_716_; lean_object* v_x_717_; lean_object* v___x_718_; 
lean_dec(v_h__2_713_);
v_x_716_ = lean_ctor_get(v_s_u2082_710_, 0);
lean_inc(v_x_716_);
lean_dec_ref(v_s_u2082_710_);
v_x_717_ = lean_ctor_get(v_s_u2081_711_, 0);
lean_inc(v_x_717_);
lean_dec_ref(v_s_u2081_711_);
v___x_718_ = lean_apply_2(v_h__1_712_, v_x_716_, v_x_717_);
return v___x_718_;
}
else
{
lean_object* v_x_719_; lean_object* v_x_720_; lean_object* v_s_721_; lean_object* v___x_722_; 
lean_dec(v_h__1_712_);
v_x_719_ = lean_ctor_get(v_s_u2082_710_, 0);
lean_inc(v_x_719_);
lean_dec_ref(v_s_u2082_710_);
v_x_720_ = lean_ctor_get(v_s_u2081_711_, 0);
lean_inc(v_x_720_);
v_s_721_ = lean_ctor_get(v_s_u2081_711_, 1);
lean_inc_ref(v_s_721_);
lean_dec_ref(v_s_u2081_711_);
v___x_722_ = lean_apply_3(v_h__2_713_, v_x_719_, v_x_720_, v_s_721_);
return v___x_722_;
}
}
else
{
lean_dec(v_h__2_713_);
lean_dec(v_h__1_712_);
if (lean_obj_tag(v_s_u2081_711_) == 0)
{
lean_object* v_x_723_; lean_object* v_s_724_; lean_object* v_x_725_; lean_object* v___x_726_; 
lean_dec(v_h__4_715_);
v_x_723_ = lean_ctor_get(v_s_u2082_710_, 0);
lean_inc(v_x_723_);
v_s_724_ = lean_ctor_get(v_s_u2082_710_, 1);
lean_inc_ref(v_s_724_);
lean_dec_ref(v_s_u2082_710_);
v_x_725_ = lean_ctor_get(v_s_u2081_711_, 0);
lean_inc(v_x_725_);
lean_dec_ref(v_s_u2081_711_);
v___x_726_ = lean_apply_3(v_h__3_714_, v_x_723_, v_s_724_, v_x_725_);
return v___x_726_;
}
else
{
lean_object* v_x_727_; lean_object* v_s_728_; lean_object* v_x_729_; lean_object* v_s_730_; lean_object* v___x_731_; 
lean_dec(v_h__3_714_);
v_x_727_ = lean_ctor_get(v_s_u2082_710_, 0);
lean_inc(v_x_727_);
v_s_728_ = lean_ctor_get(v_s_u2082_710_, 1);
lean_inc_ref(v_s_728_);
lean_dec_ref(v_s_u2082_710_);
v_x_729_ = lean_ctor_get(v_s_u2081_711_, 0);
lean_inc(v_x_729_);
v_s_730_ = lean_ctor_get(v_s_u2081_711_, 1);
lean_inc_ref(v_s_730_);
lean_dec_ref(v_s_u2081_711_);
v___x_731_ = lean_apply_4(v_h__4_715_, v_x_727_, v_s_728_, v_x_729_, v_s_730_);
return v___x_731_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_startsWith_match__1_splitter(lean_object* v_motive_732_, lean_object* v_s_u2082_733_, lean_object* v_s_u2081_734_, lean_object* v_h__1_735_, lean_object* v_h__2_736_, lean_object* v_h__3_737_, lean_object* v_h__4_738_){
_start:
{
if (lean_obj_tag(v_s_u2082_733_) == 0)
{
lean_dec(v_h__4_738_);
lean_dec(v_h__3_737_);
if (lean_obj_tag(v_s_u2081_734_) == 0)
{
lean_object* v_x_739_; lean_object* v_x_740_; lean_object* v___x_741_; 
lean_dec(v_h__2_736_);
v_x_739_ = lean_ctor_get(v_s_u2082_733_, 0);
lean_inc(v_x_739_);
lean_dec_ref(v_s_u2082_733_);
v_x_740_ = lean_ctor_get(v_s_u2081_734_, 0);
lean_inc(v_x_740_);
lean_dec_ref(v_s_u2081_734_);
v___x_741_ = lean_apply_2(v_h__1_735_, v_x_739_, v_x_740_);
return v___x_741_;
}
else
{
lean_object* v_x_742_; lean_object* v_x_743_; lean_object* v_s_744_; lean_object* v___x_745_; 
lean_dec(v_h__1_735_);
v_x_742_ = lean_ctor_get(v_s_u2082_733_, 0);
lean_inc(v_x_742_);
lean_dec_ref(v_s_u2082_733_);
v_x_743_ = lean_ctor_get(v_s_u2081_734_, 0);
lean_inc(v_x_743_);
v_s_744_ = lean_ctor_get(v_s_u2081_734_, 1);
lean_inc_ref(v_s_744_);
lean_dec_ref(v_s_u2081_734_);
v___x_745_ = lean_apply_3(v_h__2_736_, v_x_742_, v_x_743_, v_s_744_);
return v___x_745_;
}
}
else
{
lean_dec(v_h__2_736_);
lean_dec(v_h__1_735_);
if (lean_obj_tag(v_s_u2081_734_) == 0)
{
lean_object* v_x_746_; lean_object* v_s_747_; lean_object* v_x_748_; lean_object* v___x_749_; 
lean_dec(v_h__4_738_);
v_x_746_ = lean_ctor_get(v_s_u2082_733_, 0);
lean_inc(v_x_746_);
v_s_747_ = lean_ctor_get(v_s_u2082_733_, 1);
lean_inc_ref(v_s_747_);
lean_dec_ref(v_s_u2082_733_);
v_x_748_ = lean_ctor_get(v_s_u2081_734_, 0);
lean_inc(v_x_748_);
lean_dec_ref(v_s_u2081_734_);
v___x_749_ = lean_apply_3(v_h__3_737_, v_x_746_, v_s_747_, v_x_748_);
return v___x_749_;
}
else
{
lean_object* v_x_750_; lean_object* v_s_751_; lean_object* v_x_752_; lean_object* v_s_753_; lean_object* v___x_754_; 
lean_dec(v_h__3_737_);
v_x_750_ = lean_ctor_get(v_s_u2082_733_, 0);
lean_inc(v_x_750_);
v_s_751_ = lean_ctor_get(v_s_u2082_733_, 1);
lean_inc_ref(v_s_751_);
lean_dec_ref(v_s_u2082_733_);
v_x_752_ = lean_ctor_get(v_s_u2081_734_, 0);
lean_inc(v_x_752_);
v_s_753_ = lean_ctor_get(v_s_u2081_734_, 1);
lean_inc_ref(v_s_753_);
lean_dec_ref(v_s_u2081_734_);
v___x_754_ = lean_apply_4(v_h__4_738_, v_x_750_, v_s_751_, v_x_752_, v_s_753_);
return v___x_754_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_toSeq_x3f_go(lean_object* v_xs_755_, lean_object* v_acc_756_){
_start:
{
if (lean_obj_tag(v_xs_755_) == 0)
{
lean_object* v___x_757_; 
v___x_757_ = l_Lean_Grind_AC_Seq_reverse(v_acc_756_);
return v___x_757_;
}
else
{
lean_object* v_head_758_; lean_object* v_tail_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_767_; 
v_head_758_ = lean_ctor_get(v_xs_755_, 0);
v_tail_759_ = lean_ctor_get(v_xs_755_, 1);
v_isSharedCheck_767_ = !lean_is_exclusive(v_xs_755_);
if (v_isSharedCheck_767_ == 0)
{
v___x_761_ = v_xs_755_;
v_isShared_762_ = v_isSharedCheck_767_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_tail_759_);
lean_inc(v_head_758_);
lean_dec(v_xs_755_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_767_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_764_; 
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 1, v_acc_756_);
v___x_764_ = v___x_761_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_head_758_);
lean_ctor_set(v_reuseFailAlloc_766_, 1, v_acc_756_);
v___x_764_ = v_reuseFailAlloc_766_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
v_xs_755_ = v_tail_759_;
v_acc_756_ = v___x_764_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_toSeq_x3f(lean_object* v_xs_768_){
_start:
{
if (lean_obj_tag(v_xs_768_) == 0)
{
lean_object* v___x_769_; 
v___x_769_ = lean_box(0);
return v___x_769_;
}
else
{
lean_object* v_head_770_; lean_object* v_tail_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v_head_770_ = lean_ctor_get(v_xs_768_, 0);
lean_inc(v_head_770_);
v_tail_771_ = lean_ctor_get(v_xs_768_, 1);
lean_inc(v_tail_771_);
lean_dec_ref(v_xs_768_);
v___x_772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_772_, 0, v_head_770_);
v___x_773_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_toSeq_x3f_go(v_tail_771_, v___x_772_);
v___x_774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_774_, 0, v___x_773_);
return v___x_774_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(lean_object* v_s_x3f_775_, lean_object* v_x_776_){
_start:
{
if (lean_obj_tag(v_s_x3f_775_) == 0)
{
lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_777_, 0, v_x_776_);
v___x_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_778_, 0, v___x_777_);
return v___x_778_;
}
else
{
lean_object* v_val_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_787_; 
v_val_779_ = lean_ctor_get(v_s_x3f_775_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v_s_x3f_775_);
if (v_isSharedCheck_787_ == 0)
{
v___x_781_ = v_s_x3f_775_;
v_isShared_782_ = v_isSharedCheck_787_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_val_779_);
lean_dec(v_s_x3f_775_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_787_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_783_; lean_object* v___x_785_; 
v___x_783_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_783_, 0, v_x_776_);
lean_ctor_set(v___x_783_, 1, v_val_779_);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 0, v___x_783_);
v___x_785_ = v___x_781_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v___x_783_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(lean_object* v_s_x3f_788_){
_start:
{
if (lean_obj_tag(v_s_x3f_788_) == 0)
{
return v_s_x3f_788_;
}
else
{
lean_object* v_val_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_797_; 
v_val_789_ = lean_ctor_get(v_s_x3f_788_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v_s_x3f_788_);
if (v_isSharedCheck_797_ == 0)
{
v___x_791_ = v_s_x3f_788_;
v_isShared_792_ = v_isSharedCheck_797_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_val_789_);
lean_dec(v_s_x3f_788_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_797_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_793_; lean_object* v___x_795_; 
v___x_793_ = l_Lean_Grind_AC_Seq_reverse(v_val_789_);
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 0, v___x_793_);
v___x_795_ = v___x_791_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v___x_793_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_app(lean_object* v_s_x3f_798_, lean_object* v_s_x27_799_){
_start:
{
if (lean_obj_tag(v_s_x3f_798_) == 0)
{
lean_object* v___x_800_; 
v___x_800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_800_, 0, v_s_x27_799_);
return v___x_800_;
}
else
{
lean_object* v_val_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_809_; 
v_val_801_ = lean_ctor_get(v_s_x3f_798_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v_s_x3f_798_);
if (v_isSharedCheck_809_ == 0)
{
v___x_803_ = v_s_x3f_798_;
v_isShared_804_ = v_isSharedCheck_809_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_val_801_);
lean_dec(v_s_x3f_798_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_809_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___x_805_; lean_object* v___x_807_; 
v___x_805_ = l_Lean_Grind_AC_Seq_concat(v_val_801_, v_s_x27_799_);
if (v_isShared_804_ == 0)
{
lean_ctor_set(v___x_803_, 0, v___x_805_);
v___x_807_ = v___x_803_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v___x_805_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superposeAC_x3f_mkResult(lean_object* v_r_u2081_810_, lean_object* v_c_811_, lean_object* v_r_u2082_812_){
_start:
{
if (lean_obj_tag(v_r_u2081_810_) == 1)
{
if (lean_obj_tag(v_c_811_) == 1)
{
if (lean_obj_tag(v_r_u2082_812_) == 1)
{
lean_object* v_val_813_; lean_object* v_val_814_; lean_object* v_val_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_824_; 
v_val_813_ = lean_ctor_get(v_r_u2081_810_, 0);
v_val_814_ = lean_ctor_get(v_c_811_, 0);
v_val_815_ = lean_ctor_get(v_r_u2082_812_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v_r_u2082_812_);
if (v_isSharedCheck_824_ == 0)
{
v___x_817_ = v_r_u2082_812_;
v_isShared_818_ = v_isSharedCheck_824_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_val_815_);
lean_dec(v_r_u2082_812_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_824_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_822_; 
lean_inc(v_val_814_);
v___x_819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_819_, 0, v_val_814_);
lean_ctor_set(v___x_819_, 1, v_val_815_);
lean_inc(v_val_813_);
v___x_820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_820_, 0, v_val_813_);
lean_ctor_set(v___x_820_, 1, v___x_819_);
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 0, v___x_820_);
v___x_822_ = v___x_817_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v___x_820_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
}
else
{
lean_object* v___x_825_; 
lean_dec(v_r_u2082_812_);
v___x_825_ = lean_box(0);
return v___x_825_;
}
}
else
{
lean_object* v___x_826_; 
lean_dec(v_r_u2082_812_);
v___x_826_ = lean_box(0);
return v___x_826_;
}
}
else
{
lean_object* v___x_827_; 
lean_dec(v_r_u2082_812_);
v___x_827_ = lean_box(0);
return v___x_827_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superposeAC_x3f_mkResult___boxed(lean_object* v_r_u2081_828_, lean_object* v_c_829_, lean_object* v_r_u2082_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superposeAC_x3f_mkResult(v_r_u2081_828_, v_c_829_, v_r_u2082_830_);
lean_dec(v_c_829_);
lean_dec(v_r_u2081_828_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superposeAC_x3f_go(lean_object* v_s_u2081_832_, lean_object* v_s_u2082_833_, lean_object* v_r_u2081_834_, lean_object* v_c_835_, lean_object* v_r_u2082_836_){
_start:
{
if (lean_obj_tag(v_s_u2081_832_) == 0)
{
if (lean_obj_tag(v_s_u2082_833_) == 0)
{
lean_object* v_x_837_; lean_object* v_x_838_; uint8_t v___x_839_; 
v_x_837_ = lean_ctor_get(v_s_u2081_832_, 0);
lean_inc(v_x_837_);
lean_dec_ref(v_s_u2081_832_);
v_x_838_ = lean_ctor_get(v_s_u2082_833_, 0);
lean_inc(v_x_838_);
lean_dec_ref(v_s_u2082_833_);
v___x_839_ = lean_nat_dec_eq(v_x_837_, v_x_838_);
if (v___x_839_ == 0)
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_840_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(v_r_u2081_834_, v_x_837_);
v___x_841_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v___x_840_);
v___x_842_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v_c_835_);
v___x_843_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(v_r_u2082_836_, v_x_838_);
v___x_844_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v___x_843_);
v___x_845_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superposeAC_x3f_mkResult(v___x_841_, v___x_842_, v___x_844_);
lean_dec(v___x_842_);
lean_dec(v___x_841_);
return v___x_845_;
}
else
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
lean_dec(v_x_838_);
v___x_846_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v_r_u2081_834_);
v___x_847_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(v_c_835_, v_x_837_);
v___x_848_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v___x_847_);
v___x_849_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v_r_u2082_836_);
v___x_850_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superposeAC_x3f_mkResult(v___x_846_, v___x_848_, v___x_849_);
lean_dec(v___x_848_);
lean_dec(v___x_846_);
return v___x_850_;
}
}
else
{
lean_object* v_x_851_; lean_object* v_x_852_; lean_object* v_s_853_; uint8_t v___x_854_; 
v_x_851_ = lean_ctor_get(v_s_u2081_832_, 0);
v_x_852_ = lean_ctor_get(v_s_u2082_833_, 0);
v_s_853_ = lean_ctor_get(v_s_u2082_833_, 1);
v___x_854_ = lean_nat_dec_eq(v_x_851_, v_x_852_);
if (v___x_854_ == 0)
{
uint8_t v___x_855_; 
v___x_855_ = lean_nat_dec_lt(v_x_851_, v_x_852_);
if (v___x_855_ == 0)
{
lean_object* v___x_856_; 
lean_inc_ref(v_s_853_);
lean_inc(v_x_852_);
lean_dec_ref(v_s_u2082_833_);
v___x_856_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(v_r_u2082_836_, v_x_852_);
v_s_u2082_833_ = v_s_853_;
v_r_u2082_836_ = v___x_856_;
goto _start;
}
else
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
lean_inc(v_x_851_);
lean_dec_ref(v_s_u2081_832_);
v___x_858_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(v_r_u2081_834_, v_x_851_);
v___x_859_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v___x_858_);
v___x_860_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v_c_835_);
v___x_861_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v_r_u2082_836_);
v___x_862_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_app(v___x_861_, v_s_u2082_833_);
v___x_863_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superposeAC_x3f_mkResult(v___x_859_, v___x_860_, v___x_862_);
lean_dec(v___x_860_);
lean_dec(v___x_859_);
return v___x_863_;
}
}
else
{
lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
lean_inc_ref(v_s_853_);
lean_inc(v_x_851_);
lean_dec_ref(v_s_u2082_833_);
lean_dec_ref(v_s_u2081_832_);
v___x_864_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v_r_u2081_834_);
v___x_865_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(v_c_835_, v_x_851_);
v___x_866_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v___x_865_);
v___x_867_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v_r_u2082_836_);
v___x_868_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_app(v___x_867_, v_s_853_);
v___x_869_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superposeAC_x3f_mkResult(v___x_864_, v___x_866_, v___x_868_);
lean_dec(v___x_866_);
lean_dec(v___x_864_);
return v___x_869_;
}
}
}
else
{
if (lean_obj_tag(v_s_u2082_833_) == 0)
{
lean_object* v_x_870_; lean_object* v_s_871_; lean_object* v_x_872_; uint8_t v___x_873_; 
v_x_870_ = lean_ctor_get(v_s_u2081_832_, 0);
v_s_871_ = lean_ctor_get(v_s_u2081_832_, 1);
v_x_872_ = lean_ctor_get(v_s_u2082_833_, 0);
v___x_873_ = lean_nat_dec_eq(v_x_870_, v_x_872_);
if (v___x_873_ == 0)
{
uint8_t v___x_874_; 
v___x_874_ = lean_nat_dec_lt(v_x_870_, v_x_872_);
if (v___x_874_ == 0)
{
lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
lean_inc(v_x_872_);
lean_dec_ref(v_s_u2082_833_);
v___x_875_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v_r_u2081_834_);
v___x_876_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_app(v___x_875_, v_s_u2081_832_);
v___x_877_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v_c_835_);
v___x_878_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(v_r_u2082_836_, v_x_872_);
v___x_879_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v___x_878_);
v___x_880_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superposeAC_x3f_mkResult(v___x_876_, v___x_877_, v___x_879_);
lean_dec(v___x_877_);
lean_dec(v___x_876_);
return v___x_880_;
}
else
{
lean_object* v___x_881_; 
lean_inc_ref(v_s_871_);
lean_inc(v_x_870_);
lean_dec_ref(v_s_u2081_832_);
v___x_881_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(v_r_u2081_834_, v_x_870_);
v_s_u2081_832_ = v_s_871_;
v_r_u2081_834_ = v___x_881_;
goto _start;
}
}
else
{
lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
lean_inc_ref(v_s_871_);
lean_inc(v_x_870_);
lean_dec_ref(v_s_u2082_833_);
lean_dec_ref(v_s_u2081_832_);
v___x_883_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v_r_u2081_834_);
v___x_884_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_app(v___x_883_, v_s_871_);
v___x_885_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(v_c_835_, v_x_870_);
v___x_886_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v___x_885_);
v___x_887_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v_r_u2082_836_);
v___x_888_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superposeAC_x3f_mkResult(v___x_884_, v___x_886_, v___x_887_);
lean_dec(v___x_886_);
lean_dec(v___x_884_);
return v___x_888_;
}
}
else
{
lean_object* v_x_889_; lean_object* v_s_890_; lean_object* v_x_891_; lean_object* v_s_892_; uint8_t v___x_893_; 
v_x_889_ = lean_ctor_get(v_s_u2081_832_, 0);
v_s_890_ = lean_ctor_get(v_s_u2081_832_, 1);
v_x_891_ = lean_ctor_get(v_s_u2082_833_, 0);
v_s_892_ = lean_ctor_get(v_s_u2082_833_, 1);
v___x_893_ = lean_nat_dec_eq(v_x_889_, v_x_891_);
if (v___x_893_ == 0)
{
uint8_t v___x_894_; 
v___x_894_ = lean_nat_dec_lt(v_x_889_, v_x_891_);
if (v___x_894_ == 0)
{
lean_object* v___x_895_; 
lean_inc_ref(v_s_892_);
lean_inc(v_x_891_);
lean_dec_ref(v_s_u2082_833_);
v___x_895_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(v_r_u2082_836_, v_x_891_);
v_s_u2082_833_ = v_s_892_;
v_r_u2082_836_ = v___x_895_;
goto _start;
}
else
{
lean_object* v___x_897_; 
lean_inc_ref(v_s_890_);
lean_inc(v_x_889_);
lean_dec_ref(v_s_u2081_832_);
v___x_897_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(v_r_u2081_834_, v_x_889_);
v_s_u2081_832_ = v_s_890_;
v_r_u2081_834_ = v___x_897_;
goto _start;
}
}
else
{
lean_object* v___x_899_; 
lean_inc_ref(v_s_892_);
lean_inc_ref(v_s_890_);
lean_inc(v_x_889_);
lean_dec_ref(v_s_u2082_833_);
lean_dec_ref(v_s_u2081_832_);
v___x_899_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(v_c_835_, v_x_889_);
v_s_u2081_832_ = v_s_890_;
v_s_u2082_833_ = v_s_892_;
v_c_835_ = v___x_899_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_superposeAC_x3f(lean_object* v_s_u2081_901_, lean_object* v_s_u2082_902_){
_start:
{
lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_903_ = lean_box(0);
v___x_904_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superposeAC_x3f_go(v_s_u2081_901_, v_s_u2082_902_, v___x_903_, v___x_903_, v___x_903_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superpose_x3f_go(lean_object* v_s_u2081_905_, lean_object* v_s_u2082_906_, lean_object* v_p_907_){
_start:
{
lean_object* v___x_908_; 
lean_inc_ref(v_s_u2081_905_);
v___x_908_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_startsWith(v_s_u2082_906_, v_s_u2081_905_);
switch(lean_obj_tag(v___x_908_))
{
case 0:
{
if (lean_obj_tag(v_s_u2081_905_) == 0)
{
lean_object* v___x_909_; 
lean_dec_ref(v_s_u2081_905_);
lean_dec_ref(v_p_907_);
v___x_909_ = lean_box(0);
return v___x_909_;
}
else
{
lean_object* v_x_910_; lean_object* v_s_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_919_; 
v_x_910_ = lean_ctor_get(v_s_u2081_905_, 0);
v_s_911_ = lean_ctor_get(v_s_u2081_905_, 1);
v_isSharedCheck_919_ = !lean_is_exclusive(v_s_u2081_905_);
if (v_isSharedCheck_919_ == 0)
{
v___x_913_ = v_s_u2081_905_;
v_isShared_914_ = v_isSharedCheck_919_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_s_911_);
lean_inc(v_x_910_);
lean_dec(v_s_u2081_905_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_919_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_916_; 
if (v_isShared_914_ == 0)
{
lean_ctor_set(v___x_913_, 1, v_p_907_);
v___x_916_ = v___x_913_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_x_910_);
lean_ctor_set(v_reuseFailAlloc_918_, 1, v_p_907_);
v___x_916_ = v_reuseFailAlloc_918_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
v_s_u2081_905_ = v_s_911_;
v_p_907_ = v___x_916_;
goto _start;
}
}
}
}
case 1:
{
lean_object* v___x_920_; 
lean_dec_ref(v_p_907_);
lean_dec_ref(v_s_u2081_905_);
v___x_920_ = lean_box(0);
return v___x_920_;
}
default: 
{
lean_object* v_s_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_931_; 
v_s_921_ = lean_ctor_get(v___x_908_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_931_ == 0)
{
v___x_923_ = v___x_908_;
v_isShared_924_ = v_isSharedCheck_931_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_s_921_);
lean_dec(v___x_908_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_931_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_929_; 
v___x_925_ = l_Lean_Grind_AC_Seq_reverse(v_p_907_);
v___x_926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_926_, 0, v_s_u2081_905_);
lean_ctor_set(v___x_926_, 1, v_s_921_);
v___x_927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_927_, 0, v___x_925_);
lean_ctor_set(v___x_927_, 1, v___x_926_);
if (v_isShared_924_ == 0)
{
lean_ctor_set_tag(v___x_923_, 1);
lean_ctor_set(v___x_923_, 0, v___x_927_);
v___x_929_ = v___x_923_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v___x_927_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superpose_x3f_go___boxed(lean_object* v_s_u2081_932_, lean_object* v_s_u2082_933_, lean_object* v_p_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superpose_x3f_go(v_s_u2081_932_, v_s_u2082_933_, v_p_934_);
lean_dec_ref(v_s_u2082_933_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_superpose_x3f(lean_object* v_s_u2081_936_, lean_object* v_s_u2082_937_){
_start:
{
if (lean_obj_tag(v_s_u2081_936_) == 0)
{
lean_object* v___x_938_; 
lean_dec_ref(v_s_u2081_936_);
v___x_938_ = lean_box(0);
return v___x_938_;
}
else
{
lean_object* v_x_939_; lean_object* v_s_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
v_x_939_ = lean_ctor_get(v_s_u2081_936_, 0);
lean_inc(v_x_939_);
v_s_940_ = lean_ctor_get(v_s_u2081_936_, 1);
lean_inc_ref(v_s_940_);
lean_dec_ref(v_s_u2081_936_);
v___x_941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_941_, 0, v_x_939_);
v___x_942_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superpose_x3f_go(v_s_940_, v_s_u2082_937_, v___x_941_);
return v___x_942_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_superpose_x3f___boxed(lean_object* v_s_u2081_943_, lean_object* v_s_u2082_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_Lean_Grind_AC_Seq_superpose_x3f(v_s_u2081_943_, v_s_u2082_944_);
lean_dec_ref(v_s_u2082_944_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_firstVar(lean_object* v_s_946_){
_start:
{
lean_object* v_x_947_; 
v_x_947_ = lean_ctor_get(v_s_946_, 0);
lean_inc(v_x_947_);
return v_x_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_firstVar___boxed(lean_object* v_s_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_Lean_Grind_AC_Seq_firstVar(v_s_948_);
lean_dec_ref(v_s_948_);
return v_res_949_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_AC_Seq_startsWithVar(lean_object* v_s_950_, lean_object* v_x_951_){
_start:
{
lean_object* v_x_952_; uint8_t v___x_953_; 
v_x_952_ = lean_ctor_get(v_s_950_, 0);
v___x_953_ = lean_nat_dec_eq(v_x_951_, v_x_952_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_startsWithVar___boxed(lean_object* v_s_954_, lean_object* v_x_955_){
_start:
{
uint8_t v_res_956_; lean_object* v_r_957_; 
v_res_956_ = l_Lean_Grind_AC_Seq_startsWithVar(v_s_954_, v_x_955_);
lean_dec(v_x_955_);
lean_dec_ref(v_s_954_);
v_r_957_ = lean_box(v_res_956_);
return v_r_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_lastVar(lean_object* v_s_958_){
_start:
{
if (lean_obj_tag(v_s_958_) == 0)
{
lean_object* v_x_959_; 
v_x_959_ = lean_ctor_get(v_s_958_, 0);
lean_inc(v_x_959_);
return v_x_959_;
}
else
{
lean_object* v_s_960_; 
v_s_960_ = lean_ctor_get(v_s_958_, 1);
v_s_958_ = v_s_960_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_lastVar___boxed(lean_object* v_s_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Lean_Grind_AC_Seq_lastVar(v_s_962_);
lean_dec_ref(v_s_962_);
return v_res_963_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_AC_Seq_endsWithVar(lean_object* v_s_964_, lean_object* v_x_965_){
_start:
{
if (lean_obj_tag(v_s_964_) == 0)
{
lean_object* v_x_966_; uint8_t v___x_967_; 
v_x_966_ = lean_ctor_get(v_s_964_, 0);
v___x_967_ = lean_nat_dec_eq(v_x_965_, v_x_966_);
return v___x_967_;
}
else
{
lean_object* v_s_968_; 
v_s_968_ = lean_ctor_get(v_s_964_, 1);
v_s_964_ = v_s_968_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_endsWithVar___boxed(lean_object* v_s_970_, lean_object* v_x_971_){
_start:
{
uint8_t v_res_972_; lean_object* v_r_973_; 
v_res_972_ = l_Lean_Grind_AC_Seq_endsWithVar(v_s_970_, v_x_971_);
lean_dec(v_x_971_);
lean_dec_ref(v_s_970_);
v_r_973_ = lean_box(v_res_972_);
return v_r_973_;
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
l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instInhabitedStartsWithResult_default = _init_l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instInhabitedStartsWithResult_default();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instInhabitedStartsWithResult_default);
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
