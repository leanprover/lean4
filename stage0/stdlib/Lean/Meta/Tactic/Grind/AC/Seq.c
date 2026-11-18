// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.AC.Seq
// Imports: public import Init.Grind.AC public import Init.Data.Ord import Init.Data.Nat.Internal.Linear
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
lean_object* lean_obj_tag_nat(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubsetResult_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubsetResult_ctorIdx___impl___boxed(lean_object*);
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
lean_dec_ref_known(v_a_15_, 1);
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
lean_dec_ref_known(v_s_29_, 2);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_ctorIdx___impl(lean_object* v_x_75_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = lean_obj_tag_nat(v_x_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_ctorIdx___impl___boxed(lean_object* v_x_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_ctorIdx___impl(v_x_77_);
lean_dec(v_x_77_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_ctorElim___redArg(lean_object* v_t_79_, lean_object* v_k_80_){
_start:
{
if (lean_obj_tag(v_t_79_) == 2)
{
lean_object* v_s_81_; lean_object* v___x_82_; 
v_s_81_ = lean_ctor_get(v_t_79_, 0);
lean_inc_ref(v_s_81_);
lean_dec_ref_known(v_t_79_, 1);
v___x_82_ = lean_apply_1(v_k_80_, v_s_81_);
return v___x_82_;
}
else
{
lean_dec(v_t_79_);
return v_k_80_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_ctorElim(lean_object* v_motive_83_, lean_object* v_ctorIdx_84_, lean_object* v_t_85_, lean_object* v_h_86_, lean_object* v_k_87_){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_ctorElim___redArg(v_t_85_, v_k_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_ctorElim___boxed(lean_object* v_motive_89_, lean_object* v_ctorIdx_90_, lean_object* v_t_91_, lean_object* v_h_92_, lean_object* v_k_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_ctorElim(v_motive_89_, v_ctorIdx_90_, v_t_91_, v_h_92_, v_k_93_);
lean_dec(v_ctorIdx_90_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_false_elim___redArg(lean_object* v_t_95_, lean_object* v_false_96_){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_ctorElim___redArg(v_t_95_, v_false_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_false_elim(lean_object* v_motive_98_, lean_object* v_t_99_, lean_object* v_h_100_, lean_object* v_false_101_){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_ctorElim___redArg(v_t_99_, v_false_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_exact_elim___redArg(lean_object* v_t_103_, lean_object* v_exact_104_){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_ctorElim___redArg(v_t_103_, v_exact_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_exact_elim(lean_object* v_motive_106_, lean_object* v_t_107_, lean_object* v_h_108_, lean_object* v_exact_109_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_ctorElim___redArg(v_t_107_, v_exact_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_prefix_elim___redArg(lean_object* v_t_111_, lean_object* v_prefix_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_ctorElim___redArg(v_t_111_, v_prefix_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_prefix_elim(lean_object* v_motive_114_, lean_object* v_t_115_, lean_object* v_h_116_, lean_object* v_prefix_117_){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_ctorElim___redArg(v_t_115_, v_prefix_117_);
return v___x_118_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__4(void){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_125_ = lean_unsigned_to_nat(2u);
v___x_126_ = lean_nat_to_int(v___x_125_);
return v___x_126_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__5(void){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_127_ = lean_unsigned_to_nat(1u);
v___x_128_ = lean_nat_to_int(v___x_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr(lean_object* v_x_135_, lean_object* v_prec_136_){
_start:
{
lean_object* v___y_138_; lean_object* v___y_145_; 
switch(lean_obj_tag(v_x_135_))
{
case 0:
{
lean_object* v___x_151_; uint8_t v___x_152_; 
v___x_151_ = lean_unsigned_to_nat(1024u);
v___x_152_ = lean_nat_dec_le(v___x_151_, v_prec_136_);
if (v___x_152_ == 0)
{
lean_object* v___x_153_; 
v___x_153_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__4, &l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__4);
v___y_145_ = v___x_153_;
goto v___jp_144_;
}
else
{
lean_object* v___x_154_; 
v___x_154_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__5, &l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__5);
v___y_145_ = v___x_154_;
goto v___jp_144_;
}
}
case 1:
{
lean_object* v___x_155_; uint8_t v___x_156_; 
v___x_155_ = lean_unsigned_to_nat(1024u);
v___x_156_ = lean_nat_dec_le(v___x_155_, v_prec_136_);
if (v___x_156_ == 0)
{
lean_object* v___x_157_; 
v___x_157_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__4, &l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__4);
v___y_138_ = v___x_157_;
goto v___jp_137_;
}
else
{
lean_object* v___x_158_; 
v___x_158_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__5, &l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__5);
v___y_138_ = v___x_158_;
goto v___jp_137_;
}
}
default: 
{
lean_object* v_s_159_; lean_object* v___y_161_; lean_object* v___x_170_; uint8_t v___x_171_; 
v_s_159_ = lean_ctor_get(v_x_135_, 0);
lean_inc_ref(v_s_159_);
lean_dec_ref_known(v_x_135_, 1);
v___x_170_ = lean_unsigned_to_nat(1024u);
v___x_171_ = lean_nat_dec_le(v___x_170_, v_prec_136_);
if (v___x_171_ == 0)
{
lean_object* v___x_172_; 
v___x_172_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__4, &l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__4);
v___y_161_ = v___x_172_;
goto v___jp_160_;
}
else
{
lean_object* v___x_173_; 
v___x_173_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__5, &l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__5);
v___y_161_ = v___x_173_;
goto v___jp_160_;
}
v___jp_160_:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; uint8_t v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_162_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__8));
v___x_163_ = lean_unsigned_to_nat(1024u);
v___x_164_ = l_Lean_Grind_AC_instReprSeq_repr(v_s_159_, v___x_163_);
v___x_165_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_165_, 0, v___x_162_);
lean_ctor_set(v___x_165_, 1, v___x_164_);
lean_inc(v___y_161_);
v___x_166_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_166_, 0, v___y_161_);
lean_ctor_set(v___x_166_, 1, v___x_165_);
v___x_167_ = 0;
v___x_168_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_168_, 0, v___x_166_);
lean_ctor_set_uint8(v___x_168_, sizeof(void*)*1, v___x_167_);
v___x_169_ = l_Repr_addAppParen(v___x_168_, v_prec_136_);
return v___x_169_;
}
}
}
v___jp_137_:
{
lean_object* v___x_139_; lean_object* v___x_140_; uint8_t v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_139_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__1));
lean_inc(v___y_138_);
v___x_140_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_140_, 0, v___y_138_);
lean_ctor_set(v___x_140_, 1, v___x_139_);
v___x_141_ = 0;
v___x_142_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_142_, 0, v___x_140_);
lean_ctor_set_uint8(v___x_142_, sizeof(void*)*1, v___x_141_);
v___x_143_ = l_Repr_addAppParen(v___x_142_, v_prec_136_);
return v___x_143_;
}
v___jp_144_:
{
lean_object* v___x_146_; lean_object* v___x_147_; uint8_t v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_146_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__3));
lean_inc(v___y_145_);
v___x_147_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_147_, 0, v___y_145_);
lean_ctor_set(v___x_147_, 1, v___x_146_);
v___x_148_ = 0;
v___x_149_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_149_, 0, v___x_147_);
lean_ctor_set_uint8(v___x_149_, sizeof(void*)*1, v___x_148_);
v___x_150_ = l_Repr_addAppParen(v___x_149_, v_prec_136_);
return v___x_150_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___boxed(lean_object* v_x_174_, lean_object* v_prec_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr(v_x_174_, v_prec_175_);
lean_dec(v_prec_175_);
return v_res_176_;
}
}
static lean_object* _init_l_Lean_Grind_AC_instInhabitedStartsWithResult_default(void){
_start:
{
lean_object* v___x_179_; 
v___x_179_ = lean_box(0);
return v___x_179_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instInhabitedStartsWithResult(void){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = lean_box(0);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_startsWith(lean_object* v_s_u2081_181_, lean_object* v_s_u2082_182_){
_start:
{
if (lean_obj_tag(v_s_u2082_182_) == 0)
{
if (lean_obj_tag(v_s_u2081_181_) == 0)
{
lean_object* v_x_183_; lean_object* v_x_184_; uint8_t v___x_185_; 
v_x_183_ = lean_ctor_get(v_s_u2082_182_, 0);
lean_inc(v_x_183_);
lean_dec_ref_known(v_s_u2082_182_, 1);
v_x_184_ = lean_ctor_get(v_s_u2081_181_, 0);
v___x_185_ = lean_nat_dec_eq(v_x_183_, v_x_184_);
lean_dec(v_x_183_);
if (v___x_185_ == 0)
{
lean_object* v___x_186_; 
v___x_186_ = lean_box(0);
return v___x_186_;
}
else
{
lean_object* v___x_187_; 
v___x_187_ = lean_box(1);
return v___x_187_;
}
}
else
{
lean_object* v_x_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_199_; 
v_x_188_ = lean_ctor_get(v_s_u2082_182_, 0);
v_isSharedCheck_199_ = !lean_is_exclusive(v_s_u2082_182_);
if (v_isSharedCheck_199_ == 0)
{
v___x_190_ = v_s_u2082_182_;
v_isShared_191_ = v_isSharedCheck_199_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_x_188_);
lean_dec(v_s_u2082_182_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_199_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v_x_192_; lean_object* v_s_193_; uint8_t v___x_194_; 
v_x_192_ = lean_ctor_get(v_s_u2081_181_, 0);
v_s_193_ = lean_ctor_get(v_s_u2081_181_, 1);
v___x_194_ = lean_nat_dec_eq(v_x_188_, v_x_192_);
lean_dec(v_x_188_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; 
lean_del_object(v___x_190_);
v___x_195_ = lean_box(0);
return v___x_195_;
}
else
{
lean_object* v___x_197_; 
lean_inc_ref(v_s_193_);
if (v_isShared_191_ == 0)
{
lean_ctor_set_tag(v___x_190_, 2);
lean_ctor_set(v___x_190_, 0, v_s_193_);
v___x_197_ = v___x_190_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v_s_193_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_s_u2081_181_) == 0)
{
lean_object* v___x_200_; 
lean_dec_ref_known(v_s_u2082_182_, 2);
v___x_200_ = lean_box(0);
return v___x_200_;
}
else
{
lean_object* v_x_201_; lean_object* v_s_202_; lean_object* v_x_203_; lean_object* v_s_204_; uint8_t v___x_205_; 
v_x_201_ = lean_ctor_get(v_s_u2082_182_, 0);
lean_inc(v_x_201_);
v_s_202_ = lean_ctor_get(v_s_u2082_182_, 1);
lean_inc_ref(v_s_202_);
lean_dec_ref_known(v_s_u2082_182_, 2);
v_x_203_ = lean_ctor_get(v_s_u2081_181_, 0);
v_s_204_ = lean_ctor_get(v_s_u2081_181_, 1);
v___x_205_ = lean_nat_dec_eq(v_x_201_, v_x_203_);
lean_dec(v_x_201_);
if (v___x_205_ == 0)
{
lean_object* v___x_206_; 
lean_dec_ref(v_s_202_);
v___x_206_ = lean_box(0);
return v___x_206_;
}
else
{
v_s_u2081_181_ = v_s_204_;
v_s_u2082_182_ = v_s_202_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_startsWith___boxed(lean_object* v_s_u2081_208_, lean_object* v_s_u2082_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_startsWith(v_s_u2081_208_, v_s_u2082_209_);
lean_dec_ref(v_s_u2081_208_);
return v_res_210_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__5(void){
_start:
{
lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_286_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__4));
v___x_287_ = l_String_toRawSubstring_x27(v___x_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1(lean_object* v_x_312_, lean_object* v_a_313_, lean_object* v_a_314_){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; uint8_t v___x_317_; 
v___x_315_ = lean_unsigned_to_nat(0u);
v___x_316_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__19));
lean_inc(v_x_312_);
v___x_317_ = l_Lean_Syntax_isOfKind(v_x_312_, v___x_316_);
if (v___x_317_ == 0)
{
lean_object* v___x_318_; lean_object* v___x_319_; 
lean_dec(v_x_312_);
v___x_318_ = lean_box(1);
v___x_319_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_318_);
lean_ctor_set(v___x_319_, 1, v_a_314_);
return v___x_319_;
}
else
{
lean_object* v_quotContext_320_; lean_object* v_currMacroScope_321_; lean_object* v_ref_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; uint8_t v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v_quotContext_320_ = lean_ctor_get(v_a_313_, 1);
v_currMacroScope_321_ = lean_ctor_get(v_a_313_, 2);
v_ref_322_ = lean_ctor_get(v_a_313_, 5);
v___x_323_ = l_Lean_Syntax_getArg(v_x_312_, v___x_315_);
v___x_324_ = lean_unsigned_to_nat(2u);
v___x_325_ = l_Lean_Syntax_getArg(v_x_312_, v___x_324_);
lean_dec(v_x_312_);
v___x_326_ = 0;
v___x_327_ = l_Lean_SourceInfo_fromRef(v_ref_322_, v___x_326_);
v___x_328_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__3));
v___x_329_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__5, &l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__5);
v___x_330_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__7));
lean_inc(v_currMacroScope_321_);
lean_inc(v_quotContext_320_);
v___x_331_ = l_Lean_addMacroScope(v_quotContext_320_, v___x_330_, v_currMacroScope_321_);
v___x_332_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__12));
lean_inc_n(v___x_327_, 2);
v___x_333_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_333_, 0, v___x_327_);
lean_ctor_set(v___x_333_, 1, v___x_329_);
lean_ctor_set(v___x_333_, 2, v___x_331_);
lean_ctor_set(v___x_333_, 3, v___x_332_);
v___x_334_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__14));
v___x_335_ = l_Lean_Syntax_node2(v___x_327_, v___x_334_, v___x_323_, v___x_325_);
v___x_336_ = l_Lean_Syntax_node2(v___x_327_, v___x_328_, v___x_333_, v___x_335_);
v___x_337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
lean_ctor_set(v___x_337_, 1, v_a_314_);
return v___x_337_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___boxed(lean_object* v_x_338_, lean_object* v_a_339_, lean_object* v_a_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1(v_x_338_, v_a_339_, v_a_340_);
lean_dec_ref(v_a_339_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______unexpand__Lean__Grind__AC__Seq__cons__1(lean_object* v_x_345_, lean_object* v_a_346_, lean_object* v_a_347_){
_start:
{
lean_object* v___x_348_; uint8_t v___x_349_; 
v___x_348_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__3));
lean_inc(v_x_345_);
v___x_349_ = l_Lean_Syntax_isOfKind(v_x_345_, v___x_348_);
if (v___x_349_ == 0)
{
lean_object* v___x_350_; lean_object* v___x_351_; 
lean_dec(v_x_345_);
v___x_350_ = lean_box(0);
v___x_351_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_351_, 0, v___x_350_);
lean_ctor_set(v___x_351_, 1, v_a_347_);
return v___x_351_;
}
else
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; uint8_t v___x_355_; 
v___x_352_ = lean_unsigned_to_nat(0u);
v___x_353_ = l_Lean_Syntax_getArg(v_x_345_, v___x_352_);
v___x_354_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______unexpand__Lean__Grind__AC__Seq__cons__1___closed__1));
lean_inc(v___x_353_);
v___x_355_ = l_Lean_Syntax_isOfKind(v___x_353_, v___x_354_);
if (v___x_355_ == 0)
{
lean_object* v___x_356_; lean_object* v___x_357_; 
lean_dec(v___x_353_);
lean_dec(v_x_345_);
v___x_356_ = lean_box(0);
v___x_357_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_357_, 0, v___x_356_);
lean_ctor_set(v___x_357_, 1, v_a_347_);
return v___x_357_;
}
else
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; uint8_t v___x_361_; 
v___x_358_ = lean_unsigned_to_nat(1u);
v___x_359_ = l_Lean_Syntax_getArg(v_x_345_, v___x_358_);
lean_dec(v_x_345_);
v___x_360_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_359_);
v___x_361_ = l_Lean_Syntax_matchesNull(v___x_359_, v___x_360_);
if (v___x_361_ == 0)
{
lean_object* v___x_362_; lean_object* v___x_363_; 
lean_dec(v___x_359_);
lean_dec(v___x_353_);
v___x_362_ = lean_box(0);
v___x_363_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_363_, 0, v___x_362_);
lean_ctor_set(v___x_363_, 1, v_a_347_);
return v___x_363_;
}
else
{
lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v_ref_366_; uint8_t v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_364_ = l_Lean_Syntax_getArg(v___x_359_, v___x_352_);
v___x_365_ = l_Lean_Syntax_getArg(v___x_359_, v___x_358_);
lean_dec(v___x_359_);
v_ref_366_ = l_Lean_replaceRef(v___x_353_, v_a_346_);
lean_dec(v___x_353_);
v___x_367_ = 0;
v___x_368_ = l_Lean_SourceInfo_fromRef(v_ref_366_, v___x_367_);
lean_dec(v_ref_366_);
v___x_369_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__19));
v___x_370_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__22));
lean_inc(v___x_368_);
v___x_371_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_371_, 0, v___x_368_);
lean_ctor_set(v___x_371_, 1, v___x_370_);
v___x_372_ = l_Lean_Syntax_node3(v___x_368_, v___x_369_, v___x_364_, v___x_371_, v___x_365_);
v___x_373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_373_, 0, v___x_372_);
lean_ctor_set(v___x_373_, 1, v_a_347_);
return v___x_373_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______unexpand__Lean__Grind__AC__Seq__cons__1___boxed(lean_object* v_x_374_, lean_object* v_a_375_, lean_object* v_a_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______unexpand__Lean__Grind__AC__Seq__cons__1(v_x_374_, v_a_375_, v_a_376_);
lean_dec(v_a_375_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_instOfNatSeq__lean(lean_object* v_n_378_){
_start:
{
lean_object* v___x_379_; 
v___x_379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_379_, 0, v_n_378_);
return v___x_379_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_a(void){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = lean_unsigned_to_nat(1u);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_ctorIdx___impl(lean_object* v_x_381_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = lean_obj_tag_nat(v_x_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_ctorIdx___impl___boxed(lean_object* v_x_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Lean_Grind_AC_SubseqResult_ctorIdx___impl(v_x_383_);
lean_dec(v_x_383_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_ctorElim___redArg(lean_object* v_t_385_, lean_object* v_k_386_){
_start:
{
switch(lean_obj_tag(v_t_385_))
{
case 2:
{
lean_object* v_s_387_; lean_object* v___x_388_; 
v_s_387_ = lean_ctor_get(v_t_385_, 0);
lean_inc_ref(v_s_387_);
lean_dec_ref_known(v_t_385_, 1);
v___x_388_ = lean_apply_1(v_k_386_, v_s_387_);
return v___x_388_;
}
case 3:
{
lean_object* v_s_389_; lean_object* v___x_390_; 
v_s_389_ = lean_ctor_get(v_t_385_, 0);
lean_inc_ref(v_s_389_);
lean_dec_ref_known(v_t_385_, 1);
v___x_390_ = lean_apply_1(v_k_386_, v_s_389_);
return v___x_390_;
}
case 4:
{
lean_object* v_p_391_; lean_object* v_s_392_; lean_object* v___x_393_; 
v_p_391_ = lean_ctor_get(v_t_385_, 0);
lean_inc_ref(v_p_391_);
v_s_392_ = lean_ctor_get(v_t_385_, 1);
lean_inc_ref(v_s_392_);
lean_dec_ref_known(v_t_385_, 2);
v___x_393_ = lean_apply_2(v_k_386_, v_p_391_, v_s_392_);
return v___x_393_;
}
default: 
{
lean_dec(v_t_385_);
return v_k_386_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_ctorElim(lean_object* v_motive_394_, lean_object* v_ctorIdx_395_, lean_object* v_t_396_, lean_object* v_h_397_, lean_object* v_k_398_){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = l_Lean_Grind_AC_SubseqResult_ctorElim___redArg(v_t_396_, v_k_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_ctorElim___boxed(lean_object* v_motive_400_, lean_object* v_ctorIdx_401_, lean_object* v_t_402_, lean_object* v_h_403_, lean_object* v_k_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Lean_Grind_AC_SubseqResult_ctorElim(v_motive_400_, v_ctorIdx_401_, v_t_402_, v_h_403_, v_k_404_);
lean_dec(v_ctorIdx_401_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_false_elim___redArg(lean_object* v_t_406_, lean_object* v_false_407_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = l_Lean_Grind_AC_SubseqResult_ctorElim___redArg(v_t_406_, v_false_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_false_elim(lean_object* v_motive_409_, lean_object* v_t_410_, lean_object* v_h_411_, lean_object* v_false_412_){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = l_Lean_Grind_AC_SubseqResult_ctorElim___redArg(v_t_410_, v_false_412_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_exact_elim___redArg(lean_object* v_t_414_, lean_object* v_exact_415_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = l_Lean_Grind_AC_SubseqResult_ctorElim___redArg(v_t_414_, v_exact_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_exact_elim(lean_object* v_motive_417_, lean_object* v_t_418_, lean_object* v_h_419_, lean_object* v_exact_420_){
_start:
{
lean_object* v___x_421_; 
v___x_421_ = l_Lean_Grind_AC_SubseqResult_ctorElim___redArg(v_t_418_, v_exact_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_prefix_elim___redArg(lean_object* v_t_422_, lean_object* v_prefix_423_){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = l_Lean_Grind_AC_SubseqResult_ctorElim___redArg(v_t_422_, v_prefix_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_prefix_elim(lean_object* v_motive_425_, lean_object* v_t_426_, lean_object* v_h_427_, lean_object* v_prefix_428_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = l_Lean_Grind_AC_SubseqResult_ctorElim___redArg(v_t_426_, v_prefix_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_suffix_elim___redArg(lean_object* v_t_430_, lean_object* v_suffix_431_){
_start:
{
lean_object* v___x_432_; 
v___x_432_ = l_Lean_Grind_AC_SubseqResult_ctorElim___redArg(v_t_430_, v_suffix_431_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_suffix_elim(lean_object* v_motive_433_, lean_object* v_t_434_, lean_object* v_h_435_, lean_object* v_suffix_436_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = l_Lean_Grind_AC_SubseqResult_ctorElim___redArg(v_t_434_, v_suffix_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_middle_elim___redArg(lean_object* v_t_438_, lean_object* v_middle_439_){
_start:
{
lean_object* v___x_440_; 
v___x_440_ = l_Lean_Grind_AC_SubseqResult_ctorElim___redArg(v_t_438_, v_middle_439_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_middle_elim(lean_object* v_motive_441_, lean_object* v_t_442_, lean_object* v_h_443_, lean_object* v_middle_444_){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = l_Lean_Grind_AC_SubseqResult_ctorElim___redArg(v_t_442_, v_middle_444_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_subseq_go(lean_object* v_s_u2081_446_, lean_object* v_s_u2082_447_, lean_object* v_acc_448_){
_start:
{
if (lean_obj_tag(v_s_u2082_447_) == 0)
{
uint8_t v___x_449_; 
v___x_449_ = l_Lean_Grind_AC_instBEqSeq_beq(v_s_u2081_446_, v_s_u2082_447_);
lean_dec_ref_known(v_s_u2082_447_, 1);
lean_dec_ref(v_s_u2081_446_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; 
lean_dec_ref(v_acc_448_);
v___x_450_ = lean_box(0);
return v___x_450_;
}
else
{
lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_451_ = l_Lean_Grind_AC_Seq_reverse(v_acc_448_);
v___x_452_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_452_, 0, v___x_451_);
return v___x_452_;
}
}
else
{
lean_object* v_x_453_; lean_object* v_s_454_; lean_object* v___x_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_468_; 
v_x_453_ = lean_ctor_get(v_s_u2082_447_, 0);
lean_inc(v_x_453_);
v_s_454_ = lean_ctor_get(v_s_u2082_447_, 1);
lean_inc_ref(v_s_454_);
lean_inc_ref(v_s_u2081_446_);
v___x_455_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_startsWith(v_s_u2082_447_, v_s_u2081_446_);
v_isSharedCheck_468_ = !lean_is_exclusive(v_s_u2082_447_);
if (v_isSharedCheck_468_ == 0)
{
lean_object* v_unused_469_; lean_object* v_unused_470_; 
v_unused_469_ = lean_ctor_get(v_s_u2082_447_, 1);
lean_dec(v_unused_469_);
v_unused_470_ = lean_ctor_get(v_s_u2082_447_, 0);
lean_dec(v_unused_470_);
v___x_457_ = v_s_u2082_447_;
v_isShared_458_ = v_isSharedCheck_468_;
goto v_resetjp_456_;
}
else
{
lean_dec(v_s_u2082_447_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_468_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
switch(lean_obj_tag(v___x_455_))
{
case 0:
{
lean_object* v___x_460_; 
if (v_isShared_458_ == 0)
{
lean_ctor_set(v___x_457_, 1, v_acc_448_);
v___x_460_ = v___x_457_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v_x_453_);
lean_ctor_set(v_reuseFailAlloc_462_, 1, v_acc_448_);
v___x_460_ = v_reuseFailAlloc_462_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
v_s_u2082_447_ = v_s_454_;
v_acc_448_ = v___x_460_;
goto _start;
}
}
case 1:
{
lean_object* v___x_463_; lean_object* v___x_464_; 
lean_del_object(v___x_457_);
lean_dec_ref(v_s_454_);
lean_dec(v_x_453_);
lean_dec_ref(v_s_u2081_446_);
v___x_463_ = l_Lean_Grind_AC_Seq_reverse(v_acc_448_);
v___x_464_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_464_, 0, v___x_463_);
return v___x_464_;
}
default: 
{
lean_object* v_s_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
lean_del_object(v___x_457_);
lean_dec_ref(v_s_454_);
lean_dec(v_x_453_);
lean_dec_ref(v_s_u2081_446_);
v_s_465_ = lean_ctor_get(v___x_455_, 0);
lean_inc_ref(v_s_465_);
lean_dec_ref_known(v___x_455_, 1);
v___x_466_ = l_Lean_Grind_AC_Seq_reverse(v_acc_448_);
v___x_467_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_467_, 0, v___x_466_);
lean_ctor_set(v___x_467_, 1, v_s_465_);
return v___x_467_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_subseq(lean_object* v_s_u2081_471_, lean_object* v_s_u2082_472_){
_start:
{
if (lean_obj_tag(v_s_u2082_472_) == 0)
{
uint8_t v___x_473_; 
v___x_473_ = l_Lean_Grind_AC_instBEqSeq_beq(v_s_u2081_471_, v_s_u2082_472_);
lean_dec_ref_known(v_s_u2082_472_, 1);
lean_dec_ref(v_s_u2081_471_);
if (v___x_473_ == 0)
{
lean_object* v___x_474_; 
v___x_474_ = lean_box(0);
return v___x_474_;
}
else
{
lean_object* v___x_475_; 
v___x_475_ = lean_box(1);
return v___x_475_;
}
}
else
{
lean_object* v_x_476_; lean_object* v_s_477_; lean_object* v___x_478_; 
v_x_476_ = lean_ctor_get(v_s_u2082_472_, 0);
lean_inc(v_x_476_);
v_s_477_ = lean_ctor_get(v_s_u2082_472_, 1);
lean_inc_ref(v_s_477_);
lean_inc_ref(v_s_u2081_471_);
v___x_478_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_startsWith(v_s_u2082_472_, v_s_u2081_471_);
lean_dec_ref_known(v_s_u2082_472_, 2);
switch(lean_obj_tag(v___x_478_))
{
case 0:
{
lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_479_, 0, v_x_476_);
v___x_480_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_subseq_go(v_s_u2081_471_, v_s_477_, v___x_479_);
return v___x_480_;
}
case 1:
{
lean_object* v___x_481_; 
lean_dec_ref(v_s_477_);
lean_dec(v_x_476_);
lean_dec_ref(v_s_u2081_471_);
v___x_481_ = lean_box(1);
return v___x_481_;
}
default: 
{
lean_object* v_s_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_489_; 
lean_dec_ref(v_s_477_);
lean_dec(v_x_476_);
lean_dec_ref(v_s_u2081_471_);
v_s_482_ = lean_ctor_get(v___x_478_, 0);
v_isSharedCheck_489_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_489_ == 0)
{
v___x_484_ = v___x_478_;
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_s_482_);
lean_dec(v___x_478_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_487_; 
if (v_isShared_485_ == 0)
{
v___x_487_ = v___x_484_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_s_482_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubsetResult_ctorIdx___impl(lean_object* v_x_490_){
_start:
{
lean_object* v___x_491_; 
v___x_491_ = lean_obj_tag_nat(v_x_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubsetResult_ctorIdx___impl___boxed(lean_object* v_x_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_Lean_Grind_AC_SubsetResult_ctorIdx___impl(v_x_492_);
lean_dec(v_x_492_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubsetResult_ctorElim___redArg(lean_object* v_t_494_, lean_object* v_k_495_){
_start:
{
if (lean_obj_tag(v_t_494_) == 2)
{
lean_object* v_s_496_; lean_object* v___x_497_; 
v_s_496_ = lean_ctor_get(v_t_494_, 0);
lean_inc_ref(v_s_496_);
lean_dec_ref_known(v_t_494_, 1);
v___x_497_ = lean_apply_1(v_k_495_, v_s_496_);
return v___x_497_;
}
else
{
lean_dec(v_t_494_);
return v_k_495_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubsetResult_ctorElim(lean_object* v_motive_498_, lean_object* v_ctorIdx_499_, lean_object* v_t_500_, lean_object* v_h_501_, lean_object* v_k_502_){
_start:
{
lean_object* v___x_503_; 
v___x_503_ = l_Lean_Grind_AC_SubsetResult_ctorElim___redArg(v_t_500_, v_k_502_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubsetResult_ctorElim___boxed(lean_object* v_motive_504_, lean_object* v_ctorIdx_505_, lean_object* v_t_506_, lean_object* v_h_507_, lean_object* v_k_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Lean_Grind_AC_SubsetResult_ctorElim(v_motive_504_, v_ctorIdx_505_, v_t_506_, v_h_507_, v_k_508_);
lean_dec(v_ctorIdx_505_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubsetResult_false_elim___redArg(lean_object* v_t_510_, lean_object* v_false_511_){
_start:
{
lean_object* v___x_512_; 
v___x_512_ = l_Lean_Grind_AC_SubsetResult_ctorElim___redArg(v_t_510_, v_false_511_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubsetResult_false_elim(lean_object* v_motive_513_, lean_object* v_t_514_, lean_object* v_h_515_, lean_object* v_false_516_){
_start:
{
lean_object* v___x_517_; 
v___x_517_ = l_Lean_Grind_AC_SubsetResult_ctorElim___redArg(v_t_514_, v_false_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubsetResult_exact_elim___redArg(lean_object* v_t_518_, lean_object* v_exact_519_){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = l_Lean_Grind_AC_SubsetResult_ctorElim___redArg(v_t_518_, v_exact_519_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubsetResult_exact_elim(lean_object* v_motive_521_, lean_object* v_t_522_, lean_object* v_h_523_, lean_object* v_exact_524_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = l_Lean_Grind_AC_SubsetResult_ctorElim___redArg(v_t_522_, v_exact_524_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubsetResult_strict_elim___redArg(lean_object* v_t_526_, lean_object* v_strict_527_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = l_Lean_Grind_AC_SubsetResult_ctorElim___redArg(v_t_526_, v_strict_527_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubsetResult_strict_elim(lean_object* v_motive_529_, lean_object* v_t_530_, lean_object* v_h_531_, lean_object* v_strict_532_){
_start:
{
lean_object* v___x_533_; 
v___x_533_ = l_Lean_Grind_AC_SubsetResult_ctorElim___redArg(v_t_530_, v_strict_532_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_subset_go(lean_object* v_s_u2081_534_, lean_object* v_s_u2082_535_, lean_object* v_acc_536_){
_start:
{
if (lean_obj_tag(v_s_u2081_534_) == 0)
{
if (lean_obj_tag(v_s_u2082_535_) == 0)
{
lean_object* v_x_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_548_; 
v_x_537_ = lean_ctor_get(v_s_u2081_534_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v_s_u2081_534_);
if (v_isSharedCheck_548_ == 0)
{
v___x_539_ = v_s_u2081_534_;
v_isShared_540_ = v_isSharedCheck_548_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_x_537_);
lean_dec(v_s_u2081_534_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_548_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v_x_541_; uint8_t v___x_542_; 
v_x_541_ = lean_ctor_get(v_s_u2082_535_, 0);
lean_inc(v_x_541_);
lean_dec_ref_known(v_s_u2082_535_, 1);
v___x_542_ = lean_nat_dec_eq(v_x_537_, v_x_541_);
lean_dec(v_x_541_);
lean_dec(v_x_537_);
if (v___x_542_ == 0)
{
lean_object* v___x_543_; 
lean_del_object(v___x_539_);
lean_dec_ref(v_acc_536_);
v___x_543_ = lean_box(0);
return v___x_543_;
}
else
{
lean_object* v___x_544_; lean_object* v___x_546_; 
v___x_544_ = l_Lean_Grind_AC_Seq_reverse(v_acc_536_);
if (v_isShared_540_ == 0)
{
lean_ctor_set_tag(v___x_539_, 2);
lean_ctor_set(v___x_539_, 0, v___x_544_);
v___x_546_ = v___x_539_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v___x_544_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
}
else
{
lean_object* v_x_549_; lean_object* v_x_550_; lean_object* v_s_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_572_; 
v_x_549_ = lean_ctor_get(v_s_u2081_534_, 0);
v_x_550_ = lean_ctor_get(v_s_u2082_535_, 0);
v_s_551_ = lean_ctor_get(v_s_u2082_535_, 1);
v_isSharedCheck_572_ = !lean_is_exclusive(v_s_u2082_535_);
if (v_isSharedCheck_572_ == 0)
{
v___x_553_ = v_s_u2082_535_;
v_isShared_554_ = v_isSharedCheck_572_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_s_551_);
lean_inc(v_x_550_);
lean_dec(v_s_u2082_535_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_572_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
uint8_t v___x_555_; 
v___x_555_ = lean_nat_dec_eq(v_x_549_, v_x_550_);
if (v___x_555_ == 0)
{
uint8_t v___x_556_; 
v___x_556_ = lean_nat_dec_lt(v_x_549_, v_x_550_);
if (v___x_556_ == 0)
{
lean_object* v___x_558_; 
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 1, v_acc_536_);
v___x_558_ = v___x_553_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_x_550_);
lean_ctor_set(v_reuseFailAlloc_560_, 1, v_acc_536_);
v___x_558_ = v_reuseFailAlloc_560_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
v_s_u2082_535_ = v_s_551_;
v_acc_536_ = v___x_558_;
goto _start;
}
}
else
{
lean_object* v___x_561_; 
lean_del_object(v___x_553_);
lean_dec_ref(v_s_551_);
lean_dec(v_x_550_);
lean_dec_ref_known(v_s_u2081_534_, 1);
lean_dec_ref(v_acc_536_);
v___x_561_ = lean_box(0);
return v___x_561_;
}
}
else
{
lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_570_; 
lean_del_object(v___x_553_);
lean_dec(v_x_550_);
v_isSharedCheck_570_ = !lean_is_exclusive(v_s_u2081_534_);
if (v_isSharedCheck_570_ == 0)
{
lean_object* v_unused_571_; 
v_unused_571_ = lean_ctor_get(v_s_u2081_534_, 0);
lean_dec(v_unused_571_);
v___x_563_ = v_s_u2081_534_;
v_isShared_564_ = v_isSharedCheck_570_;
goto v_resetjp_562_;
}
else
{
lean_dec(v_s_u2081_534_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_570_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_568_; 
v___x_565_ = l_Lean_Grind_AC_Seq_reverse(v_acc_536_);
v___x_566_ = l_Lean_Grind_AC_Seq_concat(v___x_565_, v_s_551_);
if (v_isShared_564_ == 0)
{
lean_ctor_set_tag(v___x_563_, 2);
lean_ctor_set(v___x_563_, 0, v___x_566_);
v___x_568_ = v___x_563_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v___x_566_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_s_u2082_535_) == 0)
{
lean_object* v___x_573_; 
lean_dec_ref_known(v_s_u2082_535_, 1);
lean_dec_ref_known(v_s_u2081_534_, 2);
lean_dec_ref(v_acc_536_);
v___x_573_ = lean_box(0);
return v___x_573_;
}
else
{
lean_object* v_x_574_; lean_object* v_s_575_; lean_object* v_x_576_; lean_object* v_s_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_589_; 
v_x_574_ = lean_ctor_get(v_s_u2081_534_, 0);
v_s_575_ = lean_ctor_get(v_s_u2081_534_, 1);
v_x_576_ = lean_ctor_get(v_s_u2082_535_, 0);
v_s_577_ = lean_ctor_get(v_s_u2082_535_, 1);
v_isSharedCheck_589_ = !lean_is_exclusive(v_s_u2082_535_);
if (v_isSharedCheck_589_ == 0)
{
v___x_579_ = v_s_u2082_535_;
v_isShared_580_ = v_isSharedCheck_589_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_s_577_);
lean_inc(v_x_576_);
lean_dec(v_s_u2082_535_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_589_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
uint8_t v___x_581_; 
v___x_581_ = lean_nat_dec_eq(v_x_574_, v_x_576_);
if (v___x_581_ == 0)
{
uint8_t v___x_582_; 
v___x_582_ = lean_nat_dec_lt(v_x_574_, v_x_576_);
if (v___x_582_ == 0)
{
lean_object* v___x_584_; 
if (v_isShared_580_ == 0)
{
lean_ctor_set(v___x_579_, 1, v_acc_536_);
v___x_584_ = v___x_579_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_x_576_);
lean_ctor_set(v_reuseFailAlloc_586_, 1, v_acc_536_);
v___x_584_ = v_reuseFailAlloc_586_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
v_s_u2082_535_ = v_s_577_;
v_acc_536_ = v___x_584_;
goto _start;
}
}
else
{
lean_object* v___x_587_; 
lean_del_object(v___x_579_);
lean_dec_ref(v_s_577_);
lean_dec(v_x_576_);
lean_dec_ref_known(v_s_u2081_534_, 2);
lean_dec_ref(v_acc_536_);
v___x_587_ = lean_box(0);
return v___x_587_;
}
}
else
{
lean_inc_ref(v_s_575_);
lean_del_object(v___x_579_);
lean_dec(v_x_576_);
lean_dec_ref_known(v_s_u2081_534_, 2);
v_s_u2081_534_ = v_s_575_;
v_s_u2082_535_ = v_s_577_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_subset(lean_object* v_s_u2081_590_, lean_object* v_s_u2082_591_){
_start:
{
if (lean_obj_tag(v_s_u2081_590_) == 0)
{
if (lean_obj_tag(v_s_u2082_591_) == 0)
{
lean_object* v_x_592_; lean_object* v_x_593_; uint8_t v___x_594_; 
v_x_592_ = lean_ctor_get(v_s_u2081_590_, 0);
lean_inc(v_x_592_);
lean_dec_ref_known(v_s_u2081_590_, 1);
v_x_593_ = lean_ctor_get(v_s_u2082_591_, 0);
lean_inc(v_x_593_);
lean_dec_ref_known(v_s_u2082_591_, 1);
v___x_594_ = lean_nat_dec_eq(v_x_592_, v_x_593_);
lean_dec(v_x_593_);
lean_dec(v_x_592_);
if (v___x_594_ == 0)
{
lean_object* v___x_595_; 
v___x_595_ = lean_box(0);
return v___x_595_;
}
else
{
lean_object* v___x_596_; 
v___x_596_ = lean_box(1);
return v___x_596_;
}
}
else
{
lean_object* v_x_597_; lean_object* v_x_598_; lean_object* v_s_599_; uint8_t v___x_600_; 
v_x_597_ = lean_ctor_get(v_s_u2081_590_, 0);
v_x_598_ = lean_ctor_get(v_s_u2082_591_, 0);
lean_inc(v_x_598_);
v_s_599_ = lean_ctor_get(v_s_u2082_591_, 1);
lean_inc_ref(v_s_599_);
lean_dec_ref_known(v_s_u2082_591_, 2);
v___x_600_ = lean_nat_dec_eq(v_x_597_, v_x_598_);
if (v___x_600_ == 0)
{
uint8_t v___x_601_; 
v___x_601_ = lean_nat_dec_lt(v_x_597_, v_x_598_);
if (v___x_601_ == 0)
{
lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_602_, 0, v_x_598_);
v___x_603_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_subset_go(v_s_u2081_590_, v_s_599_, v___x_602_);
return v___x_603_;
}
else
{
lean_object* v___x_604_; 
lean_dec_ref(v_s_599_);
lean_dec(v_x_598_);
lean_dec_ref_known(v_s_u2081_590_, 1);
v___x_604_ = lean_box(0);
return v___x_604_;
}
}
else
{
lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_611_; 
lean_dec(v_x_598_);
v_isSharedCheck_611_ = !lean_is_exclusive(v_s_u2081_590_);
if (v_isSharedCheck_611_ == 0)
{
lean_object* v_unused_612_; 
v_unused_612_ = lean_ctor_get(v_s_u2081_590_, 0);
lean_dec(v_unused_612_);
v___x_606_ = v_s_u2081_590_;
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
else
{
lean_dec(v_s_u2081_590_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_609_; 
if (v_isShared_607_ == 0)
{
lean_ctor_set_tag(v___x_606_, 2);
lean_ctor_set(v___x_606_, 0, v_s_599_);
v___x_609_ = v___x_606_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_s_599_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_s_u2082_591_) == 0)
{
lean_object* v___x_613_; 
lean_dec_ref_known(v_s_u2082_591_, 1);
lean_dec_ref_known(v_s_u2081_590_, 2);
v___x_613_ = lean_box(0);
return v___x_613_;
}
else
{
lean_object* v_x_614_; lean_object* v_s_615_; lean_object* v_x_616_; lean_object* v_s_617_; uint8_t v___x_618_; 
v_x_614_ = lean_ctor_get(v_s_u2081_590_, 0);
v_s_615_ = lean_ctor_get(v_s_u2081_590_, 1);
v_x_616_ = lean_ctor_get(v_s_u2082_591_, 0);
lean_inc(v_x_616_);
v_s_617_ = lean_ctor_get(v_s_u2082_591_, 1);
lean_inc_ref(v_s_617_);
lean_dec_ref_known(v_s_u2082_591_, 2);
v___x_618_ = lean_nat_dec_eq(v_x_614_, v_x_616_);
if (v___x_618_ == 0)
{
uint8_t v___x_619_; 
v___x_619_ = lean_nat_dec_lt(v_x_614_, v_x_616_);
if (v___x_619_ == 0)
{
lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_620_, 0, v_x_616_);
v___x_621_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_subset_go(v_s_u2081_590_, v_s_617_, v___x_620_);
return v___x_621_;
}
else
{
lean_object* v___x_622_; 
lean_dec_ref(v_s_617_);
lean_dec(v_x_616_);
lean_dec_ref_known(v_s_u2081_590_, 2);
v___x_622_ = lean_box(0);
return v___x_622_;
}
}
else
{
lean_inc_ref(v_s_615_);
lean_dec(v_x_616_);
lean_dec_ref_known(v_s_u2081_590_, 2);
v_s_u2081_590_ = v_s_615_;
v_s_u2082_591_ = v_s_617_;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_isSorted_go(lean_object* v_x_624_, lean_object* v_s_625_){
_start:
{
if (lean_obj_tag(v_s_625_) == 0)
{
lean_object* v_x_626_; uint8_t v___x_627_; 
v_x_626_ = lean_ctor_get(v_s_625_, 0);
v___x_627_ = lean_nat_dec_le(v_x_624_, v_x_626_);
return v___x_627_;
}
else
{
lean_object* v_x_628_; lean_object* v_s_629_; uint8_t v___x_630_; 
v_x_628_ = lean_ctor_get(v_s_625_, 0);
v_s_629_ = lean_ctor_get(v_s_625_, 1);
v___x_630_ = lean_nat_dec_le(v_x_624_, v_x_628_);
if (v___x_630_ == 0)
{
return v___x_630_;
}
else
{
v_x_624_ = v_x_628_;
v_s_625_ = v_s_629_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_isSorted_go___boxed(lean_object* v_x_632_, lean_object* v_s_633_){
_start:
{
uint8_t v_res_634_; lean_object* v_r_635_; 
v_res_634_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_isSorted_go(v_x_632_, v_s_633_);
lean_dec_ref(v_s_633_);
lean_dec(v_x_632_);
v_r_635_ = lean_box(v_res_634_);
return v_r_635_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_AC_Seq_isSorted(lean_object* v_s_636_){
_start:
{
if (lean_obj_tag(v_s_636_) == 0)
{
uint8_t v___x_637_; 
v___x_637_ = 1;
return v___x_637_;
}
else
{
lean_object* v_x_638_; lean_object* v_s_639_; uint8_t v___x_640_; 
v_x_638_ = lean_ctor_get(v_s_636_, 0);
v_s_639_ = lean_ctor_get(v_s_636_, 1);
v___x_640_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_isSorted_go(v_x_638_, v_s_639_);
return v___x_640_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_isSorted___boxed(lean_object* v_s_641_){
_start:
{
uint8_t v_res_642_; lean_object* v_r_643_; 
v_res_642_ = l_Lean_Grind_AC_Seq_isSorted(v_s_641_);
lean_dec_ref(v_s_641_);
v_r_643_ = lean_box(v_res_642_);
return v_r_643_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_AC_Seq_contains(lean_object* v_s_644_, lean_object* v_x_645_){
_start:
{
if (lean_obj_tag(v_s_644_) == 0)
{
lean_object* v_x_646_; uint8_t v___x_647_; 
v_x_646_ = lean_ctor_get(v_s_644_, 0);
v___x_647_ = lean_nat_dec_eq(v_x_645_, v_x_646_);
return v___x_647_;
}
else
{
lean_object* v_x_648_; lean_object* v_s_649_; uint8_t v___x_650_; 
v_x_648_ = lean_ctor_get(v_s_644_, 0);
v_s_649_ = lean_ctor_get(v_s_644_, 1);
v___x_650_ = lean_nat_dec_eq(v_x_645_, v_x_648_);
if (v___x_650_ == 0)
{
v_s_644_ = v_s_649_;
goto _start;
}
else
{
return v___x_650_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_contains___boxed(lean_object* v_s_652_, lean_object* v_x_653_){
_start:
{
uint8_t v_res_654_; lean_object* v_r_655_; 
v_res_654_ = l_Lean_Grind_AC_Seq_contains(v_s_652_, v_x_653_);
lean_dec(v_x_653_);
lean_dec_ref(v_s_652_);
v_r_655_ = lean_box(v_res_654_);
return v_r_655_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_noAdjacentDuplicates_go(lean_object* v_x_656_, lean_object* v_s_657_){
_start:
{
if (lean_obj_tag(v_s_657_) == 0)
{
lean_object* v_x_658_; uint8_t v___x_659_; 
v_x_658_ = lean_ctor_get(v_s_657_, 0);
v___x_659_ = lean_nat_dec_eq(v_x_656_, v_x_658_);
if (v___x_659_ == 0)
{
uint8_t v___x_660_; 
v___x_660_ = 1;
return v___x_660_;
}
else
{
uint8_t v___x_661_; 
v___x_661_ = 0;
return v___x_661_;
}
}
else
{
lean_object* v_x_662_; lean_object* v_s_663_; uint8_t v___x_664_; 
v_x_662_ = lean_ctor_get(v_s_657_, 0);
v_s_663_ = lean_ctor_get(v_s_657_, 1);
v___x_664_ = lean_nat_dec_eq(v_x_656_, v_x_662_);
if (v___x_664_ == 0)
{
v_x_656_ = v_x_662_;
v_s_657_ = v_s_663_;
goto _start;
}
else
{
uint8_t v___x_666_; 
v___x_666_ = 0;
return v___x_666_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_noAdjacentDuplicates_go___boxed(lean_object* v_x_667_, lean_object* v_s_668_){
_start:
{
uint8_t v_res_669_; lean_object* v_r_670_; 
v_res_669_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_noAdjacentDuplicates_go(v_x_667_, v_s_668_);
lean_dec_ref(v_s_668_);
lean_dec(v_x_667_);
v_r_670_ = lean_box(v_res_669_);
return v_r_670_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_AC_Seq_noAdjacentDuplicates(lean_object* v_s_671_){
_start:
{
if (lean_obj_tag(v_s_671_) == 0)
{
uint8_t v___x_672_; 
v___x_672_ = 1;
return v___x_672_;
}
else
{
lean_object* v_x_673_; lean_object* v_s_674_; uint8_t v___x_675_; 
v_x_673_ = lean_ctor_get(v_s_671_, 0);
v_s_674_ = lean_ctor_get(v_s_671_, 1);
v___x_675_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_noAdjacentDuplicates_go(v_x_673_, v_s_674_);
return v___x_675_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_noAdjacentDuplicates___boxed(lean_object* v_s_676_){
_start:
{
uint8_t v_res_677_; lean_object* v_r_678_; 
v_res_677_ = l_Lean_Grind_AC_Seq_noAdjacentDuplicates(v_s_676_);
lean_dec_ref(v_s_676_);
v_r_678_ = lean_box(v_res_677_);
return v_r_678_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_AC_Seq_sharesVar(lean_object* v_s_u2081_679_, lean_object* v_s_u2082_680_){
_start:
{
if (lean_obj_tag(v_s_u2081_679_) == 0)
{
if (lean_obj_tag(v_s_u2082_680_) == 0)
{
lean_object* v_x_681_; lean_object* v_x_682_; uint8_t v___x_683_; 
v_x_681_ = lean_ctor_get(v_s_u2081_679_, 0);
v_x_682_ = lean_ctor_get(v_s_u2082_680_, 0);
v___x_683_ = lean_nat_dec_eq(v_x_681_, v_x_682_);
return v___x_683_;
}
else
{
lean_object* v_x_684_; lean_object* v_x_685_; lean_object* v_s_686_; uint8_t v___x_687_; 
v_x_684_ = lean_ctor_get(v_s_u2081_679_, 0);
v_x_685_ = lean_ctor_get(v_s_u2082_680_, 0);
v_s_686_ = lean_ctor_get(v_s_u2082_680_, 1);
v___x_687_ = lean_nat_dec_eq(v_x_684_, v_x_685_);
if (v___x_687_ == 0)
{
v_s_u2082_680_ = v_s_686_;
goto _start;
}
else
{
return v___x_687_;
}
}
}
else
{
if (lean_obj_tag(v_s_u2082_680_) == 0)
{
lean_object* v_x_689_; lean_object* v_s_690_; lean_object* v_x_691_; uint8_t v___x_692_; 
v_x_689_ = lean_ctor_get(v_s_u2081_679_, 0);
v_s_690_ = lean_ctor_get(v_s_u2081_679_, 1);
v_x_691_ = lean_ctor_get(v_s_u2082_680_, 0);
v___x_692_ = lean_nat_dec_eq(v_x_689_, v_x_691_);
if (v___x_692_ == 0)
{
v_s_u2081_679_ = v_s_690_;
goto _start;
}
else
{
return v___x_692_;
}
}
else
{
lean_object* v_x_694_; lean_object* v_s_695_; lean_object* v_x_696_; lean_object* v_s_697_; uint8_t v___x_698_; 
v_x_694_ = lean_ctor_get(v_s_u2081_679_, 0);
v_s_695_ = lean_ctor_get(v_s_u2081_679_, 1);
v_x_696_ = lean_ctor_get(v_s_u2082_680_, 0);
v_s_697_ = lean_ctor_get(v_s_u2082_680_, 1);
v___x_698_ = lean_nat_dec_eq(v_x_694_, v_x_696_);
if (v___x_698_ == 0)
{
uint8_t v___x_699_; 
v___x_699_ = lean_nat_dec_lt(v_x_694_, v_x_696_);
if (v___x_699_ == 0)
{
v_s_u2082_680_ = v_s_697_;
goto _start;
}
else
{
v_s_u2081_679_ = v_s_695_;
goto _start;
}
}
else
{
return v___x_698_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_sharesVar___boxed(lean_object* v_s_u2081_702_, lean_object* v_s_u2082_703_){
_start:
{
uint8_t v_res_704_; lean_object* v_r_705_; 
v_res_704_ = l_Lean_Grind_AC_Seq_sharesVar(v_s_u2081_702_, v_s_u2082_703_);
lean_dec_ref(v_s_u2082_703_);
lean_dec_ref(v_s_u2081_702_);
v_r_705_ = lean_box(v_res_704_);
return v_r_705_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_startsWith_match__1_splitter___redArg(lean_object* v_s_u2082_706_, lean_object* v_s_u2081_707_, lean_object* v_h__1_708_, lean_object* v_h__2_709_, lean_object* v_h__3_710_, lean_object* v_h__4_711_){
_start:
{
if (lean_obj_tag(v_s_u2082_706_) == 0)
{
lean_dec(v_h__4_711_);
lean_dec(v_h__3_710_);
if (lean_obj_tag(v_s_u2081_707_) == 0)
{
lean_object* v_x_712_; lean_object* v_x_713_; lean_object* v___x_714_; 
lean_dec(v_h__2_709_);
v_x_712_ = lean_ctor_get(v_s_u2082_706_, 0);
lean_inc(v_x_712_);
lean_dec_ref_known(v_s_u2082_706_, 1);
v_x_713_ = lean_ctor_get(v_s_u2081_707_, 0);
lean_inc(v_x_713_);
lean_dec_ref_known(v_s_u2081_707_, 1);
v___x_714_ = lean_apply_2(v_h__1_708_, v_x_712_, v_x_713_);
return v___x_714_;
}
else
{
lean_object* v_x_715_; lean_object* v_x_716_; lean_object* v_s_717_; lean_object* v___x_718_; 
lean_dec(v_h__1_708_);
v_x_715_ = lean_ctor_get(v_s_u2082_706_, 0);
lean_inc(v_x_715_);
lean_dec_ref_known(v_s_u2082_706_, 1);
v_x_716_ = lean_ctor_get(v_s_u2081_707_, 0);
lean_inc(v_x_716_);
v_s_717_ = lean_ctor_get(v_s_u2081_707_, 1);
lean_inc_ref(v_s_717_);
lean_dec_ref_known(v_s_u2081_707_, 2);
v___x_718_ = lean_apply_3(v_h__2_709_, v_x_715_, v_x_716_, v_s_717_);
return v___x_718_;
}
}
else
{
lean_dec(v_h__2_709_);
lean_dec(v_h__1_708_);
if (lean_obj_tag(v_s_u2081_707_) == 0)
{
lean_object* v_x_719_; lean_object* v_s_720_; lean_object* v_x_721_; lean_object* v___x_722_; 
lean_dec(v_h__4_711_);
v_x_719_ = lean_ctor_get(v_s_u2082_706_, 0);
lean_inc(v_x_719_);
v_s_720_ = lean_ctor_get(v_s_u2082_706_, 1);
lean_inc_ref(v_s_720_);
lean_dec_ref_known(v_s_u2082_706_, 2);
v_x_721_ = lean_ctor_get(v_s_u2081_707_, 0);
lean_inc(v_x_721_);
lean_dec_ref_known(v_s_u2081_707_, 1);
v___x_722_ = lean_apply_3(v_h__3_710_, v_x_719_, v_s_720_, v_x_721_);
return v___x_722_;
}
else
{
lean_object* v_x_723_; lean_object* v_s_724_; lean_object* v_x_725_; lean_object* v_s_726_; lean_object* v___x_727_; 
lean_dec(v_h__3_710_);
v_x_723_ = lean_ctor_get(v_s_u2082_706_, 0);
lean_inc(v_x_723_);
v_s_724_ = lean_ctor_get(v_s_u2082_706_, 1);
lean_inc_ref(v_s_724_);
lean_dec_ref_known(v_s_u2082_706_, 2);
v_x_725_ = lean_ctor_get(v_s_u2081_707_, 0);
lean_inc(v_x_725_);
v_s_726_ = lean_ctor_get(v_s_u2081_707_, 1);
lean_inc_ref(v_s_726_);
lean_dec_ref_known(v_s_u2081_707_, 2);
v___x_727_ = lean_apply_4(v_h__4_711_, v_x_723_, v_s_724_, v_x_725_, v_s_726_);
return v___x_727_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_startsWith_match__1_splitter(lean_object* v_motive_728_, lean_object* v_s_u2082_729_, lean_object* v_s_u2081_730_, lean_object* v_h__1_731_, lean_object* v_h__2_732_, lean_object* v_h__3_733_, lean_object* v_h__4_734_){
_start:
{
if (lean_obj_tag(v_s_u2082_729_) == 0)
{
lean_dec(v_h__4_734_);
lean_dec(v_h__3_733_);
if (lean_obj_tag(v_s_u2081_730_) == 0)
{
lean_object* v_x_735_; lean_object* v_x_736_; lean_object* v___x_737_; 
lean_dec(v_h__2_732_);
v_x_735_ = lean_ctor_get(v_s_u2082_729_, 0);
lean_inc(v_x_735_);
lean_dec_ref_known(v_s_u2082_729_, 1);
v_x_736_ = lean_ctor_get(v_s_u2081_730_, 0);
lean_inc(v_x_736_);
lean_dec_ref_known(v_s_u2081_730_, 1);
v___x_737_ = lean_apply_2(v_h__1_731_, v_x_735_, v_x_736_);
return v___x_737_;
}
else
{
lean_object* v_x_738_; lean_object* v_x_739_; lean_object* v_s_740_; lean_object* v___x_741_; 
lean_dec(v_h__1_731_);
v_x_738_ = lean_ctor_get(v_s_u2082_729_, 0);
lean_inc(v_x_738_);
lean_dec_ref_known(v_s_u2082_729_, 1);
v_x_739_ = lean_ctor_get(v_s_u2081_730_, 0);
lean_inc(v_x_739_);
v_s_740_ = lean_ctor_get(v_s_u2081_730_, 1);
lean_inc_ref(v_s_740_);
lean_dec_ref_known(v_s_u2081_730_, 2);
v___x_741_ = lean_apply_3(v_h__2_732_, v_x_738_, v_x_739_, v_s_740_);
return v___x_741_;
}
}
else
{
lean_dec(v_h__2_732_);
lean_dec(v_h__1_731_);
if (lean_obj_tag(v_s_u2081_730_) == 0)
{
lean_object* v_x_742_; lean_object* v_s_743_; lean_object* v_x_744_; lean_object* v___x_745_; 
lean_dec(v_h__4_734_);
v_x_742_ = lean_ctor_get(v_s_u2082_729_, 0);
lean_inc(v_x_742_);
v_s_743_ = lean_ctor_get(v_s_u2082_729_, 1);
lean_inc_ref(v_s_743_);
lean_dec_ref_known(v_s_u2082_729_, 2);
v_x_744_ = lean_ctor_get(v_s_u2081_730_, 0);
lean_inc(v_x_744_);
lean_dec_ref_known(v_s_u2081_730_, 1);
v___x_745_ = lean_apply_3(v_h__3_733_, v_x_742_, v_s_743_, v_x_744_);
return v___x_745_;
}
else
{
lean_object* v_x_746_; lean_object* v_s_747_; lean_object* v_x_748_; lean_object* v_s_749_; lean_object* v___x_750_; 
lean_dec(v_h__3_733_);
v_x_746_ = lean_ctor_get(v_s_u2082_729_, 0);
lean_inc(v_x_746_);
v_s_747_ = lean_ctor_get(v_s_u2082_729_, 1);
lean_inc_ref(v_s_747_);
lean_dec_ref_known(v_s_u2082_729_, 2);
v_x_748_ = lean_ctor_get(v_s_u2081_730_, 0);
lean_inc(v_x_748_);
v_s_749_ = lean_ctor_get(v_s_u2081_730_, 1);
lean_inc_ref(v_s_749_);
lean_dec_ref_known(v_s_u2081_730_, 2);
v___x_750_ = lean_apply_4(v_h__4_734_, v_x_746_, v_s_747_, v_x_748_, v_s_749_);
return v___x_750_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_toSeq_x3f_go(lean_object* v_xs_751_, lean_object* v_acc_752_){
_start:
{
if (lean_obj_tag(v_xs_751_) == 0)
{
lean_object* v___x_753_; 
v___x_753_ = l_Lean_Grind_AC_Seq_reverse(v_acc_752_);
return v___x_753_;
}
else
{
lean_object* v_head_754_; lean_object* v_tail_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_763_; 
v_head_754_ = lean_ctor_get(v_xs_751_, 0);
v_tail_755_ = lean_ctor_get(v_xs_751_, 1);
v_isSharedCheck_763_ = !lean_is_exclusive(v_xs_751_);
if (v_isSharedCheck_763_ == 0)
{
v___x_757_ = v_xs_751_;
v_isShared_758_ = v_isSharedCheck_763_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_tail_755_);
lean_inc(v_head_754_);
lean_dec(v_xs_751_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_763_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_760_; 
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 1, v_acc_752_);
v___x_760_ = v___x_757_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_head_754_);
lean_ctor_set(v_reuseFailAlloc_762_, 1, v_acc_752_);
v___x_760_ = v_reuseFailAlloc_762_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
v_xs_751_ = v_tail_755_;
v_acc_752_ = v___x_760_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_toSeq_x3f(lean_object* v_xs_764_){
_start:
{
if (lean_obj_tag(v_xs_764_) == 0)
{
lean_object* v___x_765_; 
v___x_765_ = lean_box(0);
return v___x_765_;
}
else
{
lean_object* v_head_766_; lean_object* v_tail_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v_head_766_ = lean_ctor_get(v_xs_764_, 0);
lean_inc(v_head_766_);
v_tail_767_ = lean_ctor_get(v_xs_764_, 1);
lean_inc(v_tail_767_);
lean_dec_ref_known(v_xs_764_, 2);
v___x_768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_768_, 0, v_head_766_);
v___x_769_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_toSeq_x3f_go(v_tail_767_, v___x_768_);
v___x_770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_770_, 0, v___x_769_);
return v___x_770_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(lean_object* v_s_x3f_771_, lean_object* v_x_772_){
_start:
{
if (lean_obj_tag(v_s_x3f_771_) == 0)
{
lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_773_, 0, v_x_772_);
v___x_774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_774_, 0, v___x_773_);
return v___x_774_;
}
else
{
lean_object* v_val_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_783_; 
v_val_775_ = lean_ctor_get(v_s_x3f_771_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v_s_x3f_771_);
if (v_isSharedCheck_783_ == 0)
{
v___x_777_ = v_s_x3f_771_;
v_isShared_778_ = v_isSharedCheck_783_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_val_775_);
lean_dec(v_s_x3f_771_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_783_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_779_; lean_object* v___x_781_; 
v___x_779_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_779_, 0, v_x_772_);
lean_ctor_set(v___x_779_, 1, v_val_775_);
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 0, v___x_779_);
v___x_781_ = v___x_777_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v___x_779_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(lean_object* v_s_x3f_784_){
_start:
{
if (lean_obj_tag(v_s_x3f_784_) == 0)
{
return v_s_x3f_784_;
}
else
{
lean_object* v_val_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_793_; 
v_val_785_ = lean_ctor_get(v_s_x3f_784_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v_s_x3f_784_);
if (v_isSharedCheck_793_ == 0)
{
v___x_787_ = v_s_x3f_784_;
v_isShared_788_ = v_isSharedCheck_793_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_val_785_);
lean_dec(v_s_x3f_784_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_793_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_789_; lean_object* v___x_791_; 
v___x_789_ = l_Lean_Grind_AC_Seq_reverse(v_val_785_);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 0, v___x_789_);
v___x_791_ = v___x_787_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v___x_789_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_app(lean_object* v_s_x3f_794_, lean_object* v_s_x27_795_){
_start:
{
if (lean_obj_tag(v_s_x3f_794_) == 0)
{
lean_object* v___x_796_; 
v___x_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_796_, 0, v_s_x27_795_);
return v___x_796_;
}
else
{
lean_object* v_val_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_805_; 
v_val_797_ = lean_ctor_get(v_s_x3f_794_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v_s_x3f_794_);
if (v_isSharedCheck_805_ == 0)
{
v___x_799_ = v_s_x3f_794_;
v_isShared_800_ = v_isSharedCheck_805_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_val_797_);
lean_dec(v_s_x3f_794_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_805_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_801_; lean_object* v___x_803_; 
v___x_801_ = l_Lean_Grind_AC_Seq_concat(v_val_797_, v_s_x27_795_);
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 0, v___x_801_);
v___x_803_ = v___x_799_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v___x_801_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superposeAC_x3f_mkResult(lean_object* v_r_u2081_806_, lean_object* v_c_807_, lean_object* v_r_u2082_808_){
_start:
{
if (lean_obj_tag(v_r_u2081_806_) == 1)
{
if (lean_obj_tag(v_c_807_) == 1)
{
if (lean_obj_tag(v_r_u2082_808_) == 1)
{
lean_object* v_val_809_; lean_object* v_val_810_; lean_object* v_val_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_820_; 
v_val_809_ = lean_ctor_get(v_r_u2081_806_, 0);
v_val_810_ = lean_ctor_get(v_c_807_, 0);
v_val_811_ = lean_ctor_get(v_r_u2082_808_, 0);
v_isSharedCheck_820_ = !lean_is_exclusive(v_r_u2082_808_);
if (v_isSharedCheck_820_ == 0)
{
v___x_813_ = v_r_u2082_808_;
v_isShared_814_ = v_isSharedCheck_820_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_val_811_);
lean_dec(v_r_u2082_808_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_820_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_818_; 
lean_inc(v_val_810_);
v___x_815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_815_, 0, v_val_810_);
lean_ctor_set(v___x_815_, 1, v_val_811_);
lean_inc(v_val_809_);
v___x_816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_816_, 0, v_val_809_);
lean_ctor_set(v___x_816_, 1, v___x_815_);
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 0, v___x_816_);
v___x_818_ = v___x_813_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v___x_816_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
}
else
{
lean_object* v___x_821_; 
lean_dec(v_r_u2082_808_);
v___x_821_ = lean_box(0);
return v___x_821_;
}
}
else
{
lean_object* v___x_822_; 
lean_dec(v_r_u2082_808_);
v___x_822_ = lean_box(0);
return v___x_822_;
}
}
else
{
lean_object* v___x_823_; 
lean_dec(v_r_u2082_808_);
v___x_823_ = lean_box(0);
return v___x_823_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superposeAC_x3f_mkResult___boxed(lean_object* v_r_u2081_824_, lean_object* v_c_825_, lean_object* v_r_u2082_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superposeAC_x3f_mkResult(v_r_u2081_824_, v_c_825_, v_r_u2082_826_);
lean_dec(v_c_825_);
lean_dec(v_r_u2081_824_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superposeAC_x3f_go(lean_object* v_s_u2081_828_, lean_object* v_s_u2082_829_, lean_object* v_r_u2081_830_, lean_object* v_c_831_, lean_object* v_r_u2082_832_){
_start:
{
if (lean_obj_tag(v_s_u2081_828_) == 0)
{
if (lean_obj_tag(v_s_u2082_829_) == 0)
{
lean_object* v_x_833_; lean_object* v_x_834_; uint8_t v___x_835_; 
v_x_833_ = lean_ctor_get(v_s_u2081_828_, 0);
lean_inc(v_x_833_);
lean_dec_ref_known(v_s_u2081_828_, 1);
v_x_834_ = lean_ctor_get(v_s_u2082_829_, 0);
lean_inc(v_x_834_);
lean_dec_ref_known(v_s_u2082_829_, 1);
v___x_835_ = lean_nat_dec_eq(v_x_833_, v_x_834_);
if (v___x_835_ == 0)
{
lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_836_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(v_r_u2081_830_, v_x_833_);
v___x_837_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v___x_836_);
v___x_838_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v_c_831_);
v___x_839_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(v_r_u2082_832_, v_x_834_);
v___x_840_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v___x_839_);
v___x_841_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superposeAC_x3f_mkResult(v___x_837_, v___x_838_, v___x_840_);
lean_dec(v___x_838_);
lean_dec(v___x_837_);
return v___x_841_;
}
else
{
lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
lean_dec(v_x_834_);
v___x_842_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v_r_u2081_830_);
v___x_843_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(v_c_831_, v_x_833_);
v___x_844_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v___x_843_);
v___x_845_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v_r_u2082_832_);
v___x_846_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superposeAC_x3f_mkResult(v___x_842_, v___x_844_, v___x_845_);
lean_dec(v___x_844_);
lean_dec(v___x_842_);
return v___x_846_;
}
}
else
{
lean_object* v_x_847_; lean_object* v_x_848_; lean_object* v_s_849_; uint8_t v___x_850_; 
v_x_847_ = lean_ctor_get(v_s_u2081_828_, 0);
v_x_848_ = lean_ctor_get(v_s_u2082_829_, 0);
v_s_849_ = lean_ctor_get(v_s_u2082_829_, 1);
v___x_850_ = lean_nat_dec_eq(v_x_847_, v_x_848_);
if (v___x_850_ == 0)
{
uint8_t v___x_851_; 
v___x_851_ = lean_nat_dec_lt(v_x_847_, v_x_848_);
if (v___x_851_ == 0)
{
lean_object* v___x_852_; 
lean_inc_ref(v_s_849_);
lean_inc(v_x_848_);
lean_dec_ref_known(v_s_u2082_829_, 2);
v___x_852_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(v_r_u2082_832_, v_x_848_);
v_s_u2082_829_ = v_s_849_;
v_r_u2082_832_ = v___x_852_;
goto _start;
}
else
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
lean_inc(v_x_847_);
lean_dec_ref_known(v_s_u2081_828_, 1);
v___x_854_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(v_r_u2081_830_, v_x_847_);
v___x_855_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v___x_854_);
v___x_856_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v_c_831_);
v___x_857_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v_r_u2082_832_);
v___x_858_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_app(v___x_857_, v_s_u2082_829_);
v___x_859_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superposeAC_x3f_mkResult(v___x_855_, v___x_856_, v___x_858_);
lean_dec(v___x_856_);
lean_dec(v___x_855_);
return v___x_859_;
}
}
else
{
lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
lean_inc_ref(v_s_849_);
lean_inc(v_x_847_);
lean_dec_ref_known(v_s_u2082_829_, 2);
lean_dec_ref_known(v_s_u2081_828_, 1);
v___x_860_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v_r_u2081_830_);
v___x_861_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(v_c_831_, v_x_847_);
v___x_862_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v___x_861_);
v___x_863_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v_r_u2082_832_);
v___x_864_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_app(v___x_863_, v_s_849_);
v___x_865_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superposeAC_x3f_mkResult(v___x_860_, v___x_862_, v___x_864_);
lean_dec(v___x_862_);
lean_dec(v___x_860_);
return v___x_865_;
}
}
}
else
{
if (lean_obj_tag(v_s_u2082_829_) == 0)
{
lean_object* v_x_866_; lean_object* v_s_867_; lean_object* v_x_868_; uint8_t v___x_869_; 
v_x_866_ = lean_ctor_get(v_s_u2081_828_, 0);
v_s_867_ = lean_ctor_get(v_s_u2081_828_, 1);
v_x_868_ = lean_ctor_get(v_s_u2082_829_, 0);
v___x_869_ = lean_nat_dec_eq(v_x_866_, v_x_868_);
if (v___x_869_ == 0)
{
uint8_t v___x_870_; 
v___x_870_ = lean_nat_dec_lt(v_x_866_, v_x_868_);
if (v___x_870_ == 0)
{
lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; 
lean_inc(v_x_868_);
lean_dec_ref_known(v_s_u2082_829_, 1);
v___x_871_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v_r_u2081_830_);
v___x_872_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_app(v___x_871_, v_s_u2081_828_);
v___x_873_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v_c_831_);
v___x_874_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(v_r_u2082_832_, v_x_868_);
v___x_875_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v___x_874_);
v___x_876_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superposeAC_x3f_mkResult(v___x_872_, v___x_873_, v___x_875_);
lean_dec(v___x_873_);
lean_dec(v___x_872_);
return v___x_876_;
}
else
{
lean_object* v___x_877_; 
lean_inc_ref(v_s_867_);
lean_inc(v_x_866_);
lean_dec_ref_known(v_s_u2081_828_, 2);
v___x_877_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(v_r_u2081_830_, v_x_866_);
v_s_u2081_828_ = v_s_867_;
v_r_u2081_830_ = v___x_877_;
goto _start;
}
}
else
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
lean_inc_ref(v_s_867_);
lean_inc(v_x_866_);
lean_dec_ref_known(v_s_u2082_829_, 1);
lean_dec_ref_known(v_s_u2081_828_, 2);
v___x_879_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v_r_u2081_830_);
v___x_880_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_app(v___x_879_, v_s_867_);
v___x_881_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(v_c_831_, v_x_866_);
v___x_882_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v___x_881_);
v___x_883_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v_r_u2082_832_);
v___x_884_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superposeAC_x3f_mkResult(v___x_880_, v___x_882_, v___x_883_);
lean_dec(v___x_882_);
lean_dec(v___x_880_);
return v___x_884_;
}
}
else
{
lean_object* v_x_885_; lean_object* v_s_886_; lean_object* v_x_887_; lean_object* v_s_888_; uint8_t v___x_889_; 
v_x_885_ = lean_ctor_get(v_s_u2081_828_, 0);
v_s_886_ = lean_ctor_get(v_s_u2081_828_, 1);
v_x_887_ = lean_ctor_get(v_s_u2082_829_, 0);
v_s_888_ = lean_ctor_get(v_s_u2082_829_, 1);
v___x_889_ = lean_nat_dec_eq(v_x_885_, v_x_887_);
if (v___x_889_ == 0)
{
uint8_t v___x_890_; 
v___x_890_ = lean_nat_dec_lt(v_x_885_, v_x_887_);
if (v___x_890_ == 0)
{
lean_object* v___x_891_; 
lean_inc_ref(v_s_888_);
lean_inc(v_x_887_);
lean_dec_ref_known(v_s_u2082_829_, 2);
v___x_891_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(v_r_u2082_832_, v_x_887_);
v_s_u2082_829_ = v_s_888_;
v_r_u2082_832_ = v___x_891_;
goto _start;
}
else
{
lean_object* v___x_893_; 
lean_inc_ref(v_s_886_);
lean_inc(v_x_885_);
lean_dec_ref_known(v_s_u2081_828_, 2);
v___x_893_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(v_r_u2081_830_, v_x_885_);
v_s_u2081_828_ = v_s_886_;
v_r_u2081_830_ = v___x_893_;
goto _start;
}
}
else
{
lean_object* v___x_895_; 
lean_inc_ref(v_s_888_);
lean_inc_ref(v_s_886_);
lean_inc(v_x_885_);
lean_dec_ref_known(v_s_u2082_829_, 2);
lean_dec_ref_known(v_s_u2081_828_, 2);
v___x_895_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(v_c_831_, v_x_885_);
v_s_u2081_828_ = v_s_886_;
v_s_u2082_829_ = v_s_888_;
v_c_831_ = v___x_895_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_superposeAC_x3f(lean_object* v_s_u2081_897_, lean_object* v_s_u2082_898_){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_899_ = lean_box(0);
v___x_900_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superposeAC_x3f_go(v_s_u2081_897_, v_s_u2082_898_, v___x_899_, v___x_899_, v___x_899_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superpose_x3f_go(lean_object* v_s_u2081_901_, lean_object* v_s_u2082_902_, lean_object* v_p_903_){
_start:
{
lean_object* v___x_904_; 
lean_inc_ref(v_s_u2081_901_);
v___x_904_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_startsWith(v_s_u2082_902_, v_s_u2081_901_);
switch(lean_obj_tag(v___x_904_))
{
case 0:
{
if (lean_obj_tag(v_s_u2081_901_) == 0)
{
lean_object* v___x_905_; 
lean_dec_ref_known(v_s_u2081_901_, 1);
lean_dec_ref(v_p_903_);
v___x_905_ = lean_box(0);
return v___x_905_;
}
else
{
lean_object* v_x_906_; lean_object* v_s_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_915_; 
v_x_906_ = lean_ctor_get(v_s_u2081_901_, 0);
v_s_907_ = lean_ctor_get(v_s_u2081_901_, 1);
v_isSharedCheck_915_ = !lean_is_exclusive(v_s_u2081_901_);
if (v_isSharedCheck_915_ == 0)
{
v___x_909_ = v_s_u2081_901_;
v_isShared_910_ = v_isSharedCheck_915_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_s_907_);
lean_inc(v_x_906_);
lean_dec(v_s_u2081_901_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_915_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_912_; 
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 1, v_p_903_);
v___x_912_ = v___x_909_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_x_906_);
lean_ctor_set(v_reuseFailAlloc_914_, 1, v_p_903_);
v___x_912_ = v_reuseFailAlloc_914_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
v_s_u2081_901_ = v_s_907_;
v_p_903_ = v___x_912_;
goto _start;
}
}
}
}
case 1:
{
lean_object* v___x_916_; 
lean_dec_ref(v_p_903_);
lean_dec_ref(v_s_u2081_901_);
v___x_916_ = lean_box(0);
return v___x_916_;
}
default: 
{
lean_object* v_s_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_927_; 
v_s_917_ = lean_ctor_get(v___x_904_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_904_);
if (v_isSharedCheck_927_ == 0)
{
v___x_919_ = v___x_904_;
v_isShared_920_ = v_isSharedCheck_927_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_s_917_);
lean_dec(v___x_904_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_927_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_925_; 
v___x_921_ = l_Lean_Grind_AC_Seq_reverse(v_p_903_);
v___x_922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_922_, 0, v_s_u2081_901_);
lean_ctor_set(v___x_922_, 1, v_s_917_);
v___x_923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_923_, 0, v___x_921_);
lean_ctor_set(v___x_923_, 1, v___x_922_);
if (v_isShared_920_ == 0)
{
lean_ctor_set_tag(v___x_919_, 1);
lean_ctor_set(v___x_919_, 0, v___x_923_);
v___x_925_ = v___x_919_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v___x_923_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superpose_x3f_go___boxed(lean_object* v_s_u2081_928_, lean_object* v_s_u2082_929_, lean_object* v_p_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superpose_x3f_go(v_s_u2081_928_, v_s_u2082_929_, v_p_930_);
lean_dec_ref(v_s_u2082_929_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_superpose_x3f(lean_object* v_s_u2081_932_, lean_object* v_s_u2082_933_){
_start:
{
if (lean_obj_tag(v_s_u2081_932_) == 0)
{
lean_object* v___x_934_; 
lean_dec_ref_known(v_s_u2081_932_, 1);
v___x_934_ = lean_box(0);
return v___x_934_;
}
else
{
lean_object* v_x_935_; lean_object* v_s_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v_x_935_ = lean_ctor_get(v_s_u2081_932_, 0);
lean_inc(v_x_935_);
v_s_936_ = lean_ctor_get(v_s_u2081_932_, 1);
lean_inc_ref(v_s_936_);
lean_dec_ref_known(v_s_u2081_932_, 2);
v___x_937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_937_, 0, v_x_935_);
v___x_938_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superpose_x3f_go(v_s_936_, v_s_u2082_933_, v___x_937_);
return v___x_938_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_superpose_x3f___boxed(lean_object* v_s_u2081_939_, lean_object* v_s_u2082_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l_Lean_Grind_AC_Seq_superpose_x3f(v_s_u2081_939_, v_s_u2082_940_);
lean_dec_ref(v_s_u2082_940_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_firstVar(lean_object* v_s_942_){
_start:
{
lean_object* v_x_943_; 
v_x_943_ = lean_ctor_get(v_s_942_, 0);
lean_inc(v_x_943_);
return v_x_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_firstVar___boxed(lean_object* v_s_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_Lean_Grind_AC_Seq_firstVar(v_s_944_);
lean_dec_ref(v_s_944_);
return v_res_945_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_AC_Seq_startsWithVar(lean_object* v_s_946_, lean_object* v_x_947_){
_start:
{
lean_object* v_x_948_; uint8_t v___x_949_; 
v_x_948_ = lean_ctor_get(v_s_946_, 0);
v___x_949_ = lean_nat_dec_eq(v_x_947_, v_x_948_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_startsWithVar___boxed(lean_object* v_s_950_, lean_object* v_x_951_){
_start:
{
uint8_t v_res_952_; lean_object* v_r_953_; 
v_res_952_ = l_Lean_Grind_AC_Seq_startsWithVar(v_s_950_, v_x_951_);
lean_dec(v_x_951_);
lean_dec_ref(v_s_950_);
v_r_953_ = lean_box(v_res_952_);
return v_r_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_lastVar(lean_object* v_s_954_){
_start:
{
if (lean_obj_tag(v_s_954_) == 0)
{
lean_object* v_x_955_; 
v_x_955_ = lean_ctor_get(v_s_954_, 0);
lean_inc(v_x_955_);
return v_x_955_;
}
else
{
lean_object* v_s_956_; 
v_s_956_ = lean_ctor_get(v_s_954_, 1);
v_s_954_ = v_s_956_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_lastVar___boxed(lean_object* v_s_958_){
_start:
{
lean_object* v_res_959_; 
v_res_959_ = l_Lean_Grind_AC_Seq_lastVar(v_s_958_);
lean_dec_ref(v_s_958_);
return v_res_959_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_AC_Seq_endsWithVar(lean_object* v_s_960_, lean_object* v_x_961_){
_start:
{
if (lean_obj_tag(v_s_960_) == 0)
{
lean_object* v_x_962_; uint8_t v___x_963_; 
v_x_962_ = lean_ctor_get(v_s_960_, 0);
v___x_963_ = lean_nat_dec_eq(v_x_961_, v_x_962_);
return v___x_963_;
}
else
{
lean_object* v_s_964_; 
v_s_964_ = lean_ctor_get(v_s_960_, 1);
v_s_960_ = v_s_964_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_endsWithVar___boxed(lean_object* v_s_966_, lean_object* v_x_967_){
_start:
{
uint8_t v_res_968_; lean_object* v_r_969_; 
v_res_968_ = l_Lean_Grind_AC_Seq_endsWithVar(v_s_966_, v_x_967_);
lean_dec(v_x_967_);
lean_dec_ref(v_s_966_);
v_r_969_ = lean_box(v_res_968_);
return v_r_969_;
}
}
lean_object* runtime_initialize_Init_Grind_AC(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Ord(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_AC_Seq(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Grind_AC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Ord(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Internal_Linear(builtin);
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
lean_object* initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin);
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
res = initialize_Init_Data_Nat_Internal_Linear(builtin);
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
