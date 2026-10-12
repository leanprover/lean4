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
uint8_t l_Lean_Grind_AC_Seq_isVar(lean_object* v_x_9_){
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
LEAN_EXPORT void l_Lean_Grind_AC_Seq_isVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_9_ = stack[0].m_obj;
uint8_t v_res_12_;
v_res_12_ = l_Lean_Grind_AC_Seq_isVar(v_x_9_);
stack->m_num = v_res_12_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_isVar___boxed(lean_object* v_x_13_){
_start:
{
uint8_t v_res_14_; lean_object* v_r_15_; 
v_res_14_ = l_Lean_Grind_AC_Seq_isVar(v_x_13_);
lean_dec_ref(v_x_13_);
v_r_15_ = lean_box(v_res_14_);
return v_r_15_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_reverse_go(lean_object* v_a_16_, lean_object* v_a_17_){
_start:
{
if (lean_obj_tag(v_a_16_) == 0)
{
lean_object* v_x_18_; lean_object* v___x_19_; 
v_x_18_ = lean_ctor_get(v_a_16_, 0);
lean_inc(v_x_18_);
lean_dec_ref_known(v_a_16_, 1);
v___x_19_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_19_, 0, v_x_18_);
lean_ctor_set(v___x_19_, 1, v_a_17_);
return v___x_19_;
}
else
{
lean_object* v_x_20_; lean_object* v_s_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_29_; 
v_x_20_ = lean_ctor_get(v_a_16_, 0);
v_s_21_ = lean_ctor_get(v_a_16_, 1);
v_isSharedCheck_29_ = !lean_is_exclusive(v_a_16_);
if (v_isSharedCheck_29_ == 0)
{
v___x_23_ = v_a_16_;
v_isShared_24_ = v_isSharedCheck_29_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_s_21_);
lean_inc(v_x_20_);
lean_dec(v_a_16_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_29_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v___x_26_; 
if (v_isShared_24_ == 0)
{
lean_ctor_set(v___x_23_, 1, v_a_17_);
v___x_26_ = v___x_23_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_28_; 
v_reuseFailAlloc_28_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_28_, 0, v_x_20_);
lean_ctor_set(v_reuseFailAlloc_28_, 1, v_a_17_);
v___x_26_ = v_reuseFailAlloc_28_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
v_a_16_ = v_s_21_;
v_a_17_ = v___x_26_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_reverse(lean_object* v_s_30_){
_start:
{
if (lean_obj_tag(v_s_30_) == 0)
{
return v_s_30_;
}
else
{
lean_object* v_x_31_; lean_object* v_s_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v_x_31_ = lean_ctor_get(v_s_30_, 0);
lean_inc(v_x_31_);
v_s_32_ = lean_ctor_get(v_s_30_, 1);
lean_inc_ref(v_s_32_);
lean_dec_ref_known(v_s_30_, 2);
v___x_33_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_33_, 0, v_x_31_);
v___x_34_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_reverse_go(v_s_32_, v___x_33_);
return v___x_34_;
}
}
}
uint8_t l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_compare_lex(lean_object* v_s_u2081_35_, lean_object* v_s_u2082_36_){
_start:
{
if (lean_obj_tag(v_s_u2081_35_) == 0)
{
if (lean_obj_tag(v_s_u2082_36_) == 0)
{
lean_object* v_x_37_; lean_object* v_x_38_; uint8_t v___x_39_; 
v_x_37_ = lean_ctor_get(v_s_u2081_35_, 0);
v_x_38_ = lean_ctor_get(v_s_u2082_36_, 0);
v___x_39_ = lean_nat_dec_lt(v_x_37_, v_x_38_);
if (v___x_39_ == 0)
{
uint8_t v___x_40_; 
v___x_40_ = lean_nat_dec_eq(v_x_37_, v_x_38_);
if (v___x_40_ == 0)
{
uint8_t v___x_41_; 
v___x_41_ = 2;
return v___x_41_;
}
else
{
uint8_t v___x_42_; 
v___x_42_ = 1;
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
uint8_t v___x_44_; 
v___x_44_ = 0;
return v___x_44_;
}
}
else
{
if (lean_obj_tag(v_s_u2082_36_) == 0)
{
uint8_t v___x_45_; 
v___x_45_ = 2;
return v___x_45_;
}
else
{
lean_object* v_x_46_; lean_object* v_s_47_; lean_object* v_x_48_; lean_object* v_s_49_; uint8_t v___x_50_; 
v_x_46_ = lean_ctor_get(v_s_u2081_35_, 0);
v_s_47_ = lean_ctor_get(v_s_u2081_35_, 1);
v_x_48_ = lean_ctor_get(v_s_u2082_36_, 0);
v_s_49_ = lean_ctor_get(v_s_u2082_36_, 1);
v___x_50_ = lean_nat_dec_lt(v_x_46_, v_x_48_);
if (v___x_50_ == 0)
{
uint8_t v___x_51_; 
v___x_51_ = lean_nat_dec_eq(v_x_46_, v_x_48_);
if (v___x_51_ == 0)
{
uint8_t v___x_52_; 
v___x_52_ = 2;
return v___x_52_;
}
else
{
v_s_u2081_35_ = v_s_47_;
v_s_u2082_36_ = v_s_49_;
goto _start;
}
}
else
{
uint8_t v___x_54_; 
v___x_54_ = 0;
return v___x_54_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_compare_lex_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_u2081_35_ = stack[0].m_obj;
lean_object* v_s_u2082_36_ = stack[1].m_obj;
uint8_t v_res_55_;
v_res_55_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_compare_lex(v_s_u2081_35_, v_s_u2082_36_);
stack->m_num = v_res_55_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_compare_lex___boxed(lean_object* v_s_u2081_56_, lean_object* v_s_u2082_57_){
_start:
{
uint8_t v_res_58_; lean_object* v_r_59_; 
v_res_58_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_compare_lex(v_s_u2081_56_, v_s_u2082_57_);
lean_dec_ref(v_s_u2082_57_);
lean_dec_ref(v_s_u2081_56_);
v_r_59_ = lean_box(v_res_58_);
return v_r_59_;
}
}
uint8_t l_Lean_Grind_AC_Seq_compare(lean_object* v_s_u2081_60_, lean_object* v_s_u2082_61_){
_start:
{
lean_object* v_len_u2081_62_; lean_object* v_len_u2082_63_; uint8_t v___x_64_; 
v_len_u2081_62_ = l_Lean_Grind_AC_Seq_length(v_s_u2081_60_);
v_len_u2082_63_ = l_Lean_Grind_AC_Seq_length(v_s_u2082_61_);
v___x_64_ = lean_nat_dec_lt(v_len_u2081_62_, v_len_u2082_63_);
if (v___x_64_ == 0)
{
uint8_t v___x_65_; 
v___x_65_ = lean_nat_dec_lt(v_len_u2082_63_, v_len_u2081_62_);
lean_dec(v_len_u2081_62_);
lean_dec(v_len_u2082_63_);
if (v___x_65_ == 0)
{
uint8_t v___x_66_; 
v___x_66_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_compare_lex(v_s_u2081_60_, v_s_u2082_61_);
return v___x_66_;
}
else
{
uint8_t v___x_67_; 
v___x_67_ = 2;
return v___x_67_;
}
}
else
{
uint8_t v___x_68_; 
lean_dec(v_len_u2082_63_);
lean_dec(v_len_u2081_62_);
v___x_68_ = 0;
return v___x_68_;
}
}
}
LEAN_EXPORT void l_Lean_Grind_AC_Seq_compare_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_u2081_60_ = stack[0].m_obj;
lean_object* v_s_u2082_61_ = stack[1].m_obj;
uint8_t v_res_69_;
v_res_69_ = l_Lean_Grind_AC_Seq_compare(v_s_u2081_60_, v_s_u2082_61_);
stack->m_num = v_res_69_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_compare___boxed(lean_object* v_s_u2081_70_, lean_object* v_s_u2082_71_){
_start:
{
uint8_t v_res_72_; lean_object* v_r_73_; 
v_res_72_ = l_Lean_Grind_AC_Seq_compare(v_s_u2081_70_, v_s_u2082_71_);
lean_dec_ref(v_s_u2082_71_);
lean_dec_ref(v_s_u2081_70_);
v_r_73_ = lean_box(v_res_72_);
return v_r_73_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_ctorIdx___impl(lean_object* v_x_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = lean_obj_tag_nat(v_x_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_ctorIdx___impl___boxed(lean_object* v_x_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_ctorIdx___impl(v_x_80_);
lean_dec(v_x_80_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_ctorElim___redArg(lean_object* v_t_82_, lean_object* v_k_83_){
_start:
{
if (lean_obj_tag(v_t_82_) == 2)
{
lean_object* v_s_84_; lean_object* v___x_85_; 
v_s_84_ = lean_ctor_get(v_t_82_, 0);
lean_inc_ref(v_s_84_);
lean_dec_ref_known(v_t_82_, 1);
v___x_85_ = lean_apply_1(v_k_83_, v_s_84_);
return v___x_85_;
}
else
{
lean_dec(v_t_82_);
return v_k_83_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_ctorElim(lean_object* v_motive_86_, lean_object* v_ctorIdx_87_, lean_object* v_t_88_, lean_object* v_h_89_, lean_object* v_k_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_ctorElim___redArg(v_t_88_, v_k_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_ctorElim___boxed(lean_object* v_motive_92_, lean_object* v_ctorIdx_93_, lean_object* v_t_94_, lean_object* v_h_95_, lean_object* v_k_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_ctorElim(v_motive_92_, v_ctorIdx_93_, v_t_94_, v_h_95_, v_k_96_);
lean_dec(v_ctorIdx_93_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_false_elim___redArg(lean_object* v_t_98_, lean_object* v_false_99_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_ctorElim___redArg(v_t_98_, v_false_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_false_elim(lean_object* v_motive_101_, lean_object* v_t_102_, lean_object* v_h_103_, lean_object* v_false_104_){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_ctorElim___redArg(v_t_102_, v_false_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_exact_elim___redArg(lean_object* v_t_106_, lean_object* v_exact_107_){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_ctorElim___redArg(v_t_106_, v_exact_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_exact_elim(lean_object* v_motive_109_, lean_object* v_t_110_, lean_object* v_h_111_, lean_object* v_exact_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_ctorElim___redArg(v_t_110_, v_exact_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_prefix_elim___redArg(lean_object* v_t_114_, lean_object* v_prefix_115_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_ctorElim___redArg(v_t_114_, v_prefix_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_prefix_elim(lean_object* v_motive_117_, lean_object* v_t_118_, lean_object* v_h_119_, lean_object* v_prefix_120_){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_StartsWithResult_ctorElim___redArg(v_t_118_, v_prefix_120_);
return v___x_121_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__4(void){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_128_ = lean_unsigned_to_nat(2u);
v___x_129_ = lean_nat_to_int(v___x_128_);
return v___x_129_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__5(void){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = lean_unsigned_to_nat(1u);
v___x_131_ = lean_nat_to_int(v___x_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr(lean_object* v_x_138_, lean_object* v_prec_139_){
_start:
{
lean_object* v___y_141_; lean_object* v___y_148_; 
switch(lean_obj_tag(v_x_138_))
{
case 0:
{
lean_object* v___x_154_; uint8_t v___x_155_; 
v___x_154_ = lean_unsigned_to_nat(1024u);
v___x_155_ = lean_nat_dec_le(v___x_154_, v_prec_139_);
if (v___x_155_ == 0)
{
lean_object* v___x_156_; 
v___x_156_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__4, &l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__4);
v___y_148_ = v___x_156_;
goto v___jp_147_;
}
else
{
lean_object* v___x_157_; 
v___x_157_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__5, &l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__5);
v___y_148_ = v___x_157_;
goto v___jp_147_;
}
}
case 1:
{
lean_object* v___x_158_; uint8_t v___x_159_; 
v___x_158_ = lean_unsigned_to_nat(1024u);
v___x_159_ = lean_nat_dec_le(v___x_158_, v_prec_139_);
if (v___x_159_ == 0)
{
lean_object* v___x_160_; 
v___x_160_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__4, &l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__4);
v___y_141_ = v___x_160_;
goto v___jp_140_;
}
else
{
lean_object* v___x_161_; 
v___x_161_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__5, &l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__5);
v___y_141_ = v___x_161_;
goto v___jp_140_;
}
}
default: 
{
lean_object* v_s_162_; lean_object* v___y_164_; lean_object* v___x_173_; uint8_t v___x_174_; 
v_s_162_ = lean_ctor_get(v_x_138_, 0);
lean_inc_ref(v_s_162_);
lean_dec_ref_known(v_x_138_, 1);
v___x_173_ = lean_unsigned_to_nat(1024u);
v___x_174_ = lean_nat_dec_le(v___x_173_, v_prec_139_);
if (v___x_174_ == 0)
{
lean_object* v___x_175_; 
v___x_175_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__4, &l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__4);
v___y_164_ = v___x_175_;
goto v___jp_163_;
}
else
{
lean_object* v___x_176_; 
v___x_176_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__5, &l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__5);
v___y_164_ = v___x_176_;
goto v___jp_163_;
}
v___jp_163_:
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; uint8_t v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_165_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__8));
v___x_166_ = lean_unsigned_to_nat(1024u);
v___x_167_ = l_Lean_Grind_AC_instReprSeq_repr(v_s_162_, v___x_166_);
v___x_168_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_168_, 0, v___x_165_);
lean_ctor_set(v___x_168_, 1, v___x_167_);
lean_inc(v___y_164_);
v___x_169_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_169_, 0, v___y_164_);
lean_ctor_set(v___x_169_, 1, v___x_168_);
v___x_170_ = 0;
v___x_171_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_171_, 0, v___x_169_);
lean_ctor_set_uint8(v___x_171_, sizeof(void*)*1, v___x_170_);
v___x_172_ = l_Repr_addAppParen(v___x_171_, v_prec_139_);
return v___x_172_;
}
}
}
v___jp_140_:
{
lean_object* v___x_142_; lean_object* v___x_143_; uint8_t v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_142_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__1));
lean_inc(v___y_141_);
v___x_143_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_143_, 0, v___y_141_);
lean_ctor_set(v___x_143_, 1, v___x_142_);
v___x_144_ = 0;
v___x_145_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_145_, 0, v___x_143_);
lean_ctor_set_uint8(v___x_145_, sizeof(void*)*1, v___x_144_);
v___x_146_ = l_Repr_addAppParen(v___x_145_, v_prec_139_);
return v___x_146_;
}
v___jp_147_:
{
lean_object* v___x_149_; lean_object* v___x_150_; uint8_t v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_149_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___closed__3));
lean_inc(v___y_148_);
v___x_150_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_150_, 0, v___y_148_);
lean_ctor_set(v___x_150_, 1, v___x_149_);
v___x_151_ = 0;
v___x_152_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_152_, 0, v___x_150_);
lean_ctor_set_uint8(v___x_152_, sizeof(void*)*1, v___x_151_);
v___x_153_ = l_Repr_addAppParen(v___x_152_, v_prec_139_);
return v___x_153_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr___boxed(lean_object* v_x_177_, lean_object* v_prec_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instReprStartsWithResult_repr(v_x_177_, v_prec_178_);
lean_dec(v_prec_178_);
return v_res_179_;
}
}
static lean_object* _init_l_Lean_Grind_AC_instInhabitedStartsWithResult_default(void){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = lean_box(0);
return v___x_182_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_instInhabitedStartsWithResult(void){
_start:
{
lean_object* v___x_183_; 
v___x_183_ = lean_box(0);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_startsWith(lean_object* v_s_u2081_184_, lean_object* v_s_u2082_185_){
_start:
{
if (lean_obj_tag(v_s_u2082_185_) == 0)
{
if (lean_obj_tag(v_s_u2081_184_) == 0)
{
lean_object* v_x_186_; lean_object* v_x_187_; uint8_t v___x_188_; 
v_x_186_ = lean_ctor_get(v_s_u2082_185_, 0);
lean_inc(v_x_186_);
lean_dec_ref_known(v_s_u2082_185_, 1);
v_x_187_ = lean_ctor_get(v_s_u2081_184_, 0);
v___x_188_ = lean_nat_dec_eq(v_x_186_, v_x_187_);
lean_dec(v_x_186_);
if (v___x_188_ == 0)
{
lean_object* v___x_189_; 
v___x_189_ = lean_box(0);
return v___x_189_;
}
else
{
lean_object* v___x_190_; 
v___x_190_ = lean_box(1);
return v___x_190_;
}
}
else
{
lean_object* v_x_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_202_; 
v_x_191_ = lean_ctor_get(v_s_u2082_185_, 0);
v_isSharedCheck_202_ = !lean_is_exclusive(v_s_u2082_185_);
if (v_isSharedCheck_202_ == 0)
{
v___x_193_ = v_s_u2082_185_;
v_isShared_194_ = v_isSharedCheck_202_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_x_191_);
lean_dec(v_s_u2082_185_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_202_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
lean_object* v_x_195_; lean_object* v_s_196_; uint8_t v___x_197_; 
v_x_195_ = lean_ctor_get(v_s_u2081_184_, 0);
v_s_196_ = lean_ctor_get(v_s_u2081_184_, 1);
v___x_197_ = lean_nat_dec_eq(v_x_191_, v_x_195_);
lean_dec(v_x_191_);
if (v___x_197_ == 0)
{
lean_object* v___x_198_; 
lean_del_object(v___x_193_);
v___x_198_ = lean_box(0);
return v___x_198_;
}
else
{
lean_object* v___x_200_; 
lean_inc_ref(v_s_196_);
if (v_isShared_194_ == 0)
{
lean_ctor_set_tag(v___x_193_, 2);
lean_ctor_set(v___x_193_, 0, v_s_196_);
v___x_200_ = v___x_193_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v_s_196_);
v___x_200_ = v_reuseFailAlloc_201_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
return v___x_200_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_s_u2081_184_) == 0)
{
lean_object* v___x_203_; 
lean_dec_ref_known(v_s_u2082_185_, 2);
v___x_203_ = lean_box(0);
return v___x_203_;
}
else
{
lean_object* v_x_204_; lean_object* v_s_205_; lean_object* v_x_206_; lean_object* v_s_207_; uint8_t v___x_208_; 
v_x_204_ = lean_ctor_get(v_s_u2082_185_, 0);
lean_inc(v_x_204_);
v_s_205_ = lean_ctor_get(v_s_u2082_185_, 1);
lean_inc_ref(v_s_205_);
lean_dec_ref_known(v_s_u2082_185_, 2);
v_x_206_ = lean_ctor_get(v_s_u2081_184_, 0);
v_s_207_ = lean_ctor_get(v_s_u2081_184_, 1);
v___x_208_ = lean_nat_dec_eq(v_x_204_, v_x_206_);
lean_dec(v_x_204_);
if (v___x_208_ == 0)
{
lean_object* v___x_209_; 
lean_dec_ref(v_s_205_);
v___x_209_ = lean_box(0);
return v___x_209_;
}
else
{
v_s_u2081_184_ = v_s_207_;
v_s_u2082_185_ = v_s_205_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_startsWith___boxed(lean_object* v_s_u2081_211_, lean_object* v_s_u2082_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_startsWith(v_s_u2081_211_, v_s_u2082_212_);
lean_dec_ref(v_s_u2081_211_);
return v_res_213_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__5(void){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_289_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__4));
v___x_290_ = l_String_toRawSubstring_x27(v___x_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1(lean_object* v_x_315_, lean_object* v_a_316_, lean_object* v_a_317_){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; uint8_t v___x_320_; 
v___x_318_ = lean_unsigned_to_nat(0u);
v___x_319_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__19));
lean_inc(v_x_315_);
v___x_320_ = l_Lean_Syntax_isOfKind(v_x_315_, v___x_319_);
if (v___x_320_ == 0)
{
lean_object* v___x_321_; lean_object* v___x_322_; 
lean_dec(v_x_315_);
v___x_321_ = lean_box(1);
v___x_322_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
lean_ctor_set(v___x_322_, 1, v_a_317_);
return v___x_322_;
}
else
{
lean_object* v_quotContext_323_; lean_object* v_currMacroScope_324_; lean_object* v_ref_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; uint8_t v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v_quotContext_323_ = lean_ctor_get(v_a_316_, 1);
v_currMacroScope_324_ = lean_ctor_get(v_a_316_, 2);
v_ref_325_ = lean_ctor_get(v_a_316_, 5);
v___x_326_ = l_Lean_Syntax_getArg(v_x_315_, v___x_318_);
v___x_327_ = lean_unsigned_to_nat(2u);
v___x_328_ = l_Lean_Syntax_getArg(v_x_315_, v___x_327_);
lean_dec(v_x_315_);
v___x_329_ = 0;
v___x_330_ = l_Lean_SourceInfo_fromRef(v_ref_325_, v___x_329_);
v___x_331_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__3));
v___x_332_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__5, &l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__5);
v___x_333_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__7));
lean_inc(v_currMacroScope_324_);
lean_inc(v_quotContext_323_);
v___x_334_ = l_Lean_addMacroScope(v_quotContext_323_, v___x_333_, v_currMacroScope_324_);
v___x_335_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__12));
lean_inc_n(v___x_330_, 2);
v___x_336_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_336_, 0, v___x_330_);
lean_ctor_set(v___x_336_, 1, v___x_332_);
lean_ctor_set(v___x_336_, 2, v___x_334_);
lean_ctor_set(v___x_336_, 3, v___x_335_);
v___x_337_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__14));
v___x_338_ = l_Lean_Syntax_node2(v___x_330_, v___x_337_, v___x_326_, v___x_328_);
v___x_339_ = l_Lean_Syntax_node2(v___x_330_, v___x_331_, v___x_336_, v___x_338_);
v___x_340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
lean_ctor_set(v___x_340_, 1, v_a_317_);
return v___x_340_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___boxed(lean_object* v_x_341_, lean_object* v_a_342_, lean_object* v_a_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1(v_x_341_, v_a_342_, v_a_343_);
lean_dec_ref(v_a_342_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______unexpand__Lean__Grind__AC__Seq__cons__1(lean_object* v_x_348_, lean_object* v_a_349_, lean_object* v_a_350_){
_start:
{
lean_object* v___x_351_; uint8_t v___x_352_; 
v___x_351_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______macroRules____private__Lean__Meta__Tactic__Grind__AC__Seq__0__Lean__Grind__AC__term___x3a_x3a____1___closed__3));
lean_inc(v_x_348_);
v___x_352_ = l_Lean_Syntax_isOfKind(v_x_348_, v___x_351_);
if (v___x_352_ == 0)
{
lean_object* v___x_353_; lean_object* v___x_354_; 
lean_dec(v_x_348_);
v___x_353_ = lean_box(0);
v___x_354_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_354_, 0, v___x_353_);
lean_ctor_set(v___x_354_, 1, v_a_350_);
return v___x_354_;
}
else
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; uint8_t v___x_358_; 
v___x_355_ = lean_unsigned_to_nat(0u);
v___x_356_ = l_Lean_Syntax_getArg(v_x_348_, v___x_355_);
v___x_357_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______unexpand__Lean__Grind__AC__Seq__cons__1___closed__1));
lean_inc(v___x_356_);
v___x_358_ = l_Lean_Syntax_isOfKind(v___x_356_, v___x_357_);
if (v___x_358_ == 0)
{
lean_object* v___x_359_; lean_object* v___x_360_; 
lean_dec(v___x_356_);
lean_dec(v_x_348_);
v___x_359_ = lean_box(0);
v___x_360_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_360_, 0, v___x_359_);
lean_ctor_set(v___x_360_, 1, v_a_350_);
return v___x_360_;
}
else
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; uint8_t v___x_364_; 
v___x_361_ = lean_unsigned_to_nat(1u);
v___x_362_ = l_Lean_Syntax_getArg(v_x_348_, v___x_361_);
lean_dec(v_x_348_);
v___x_363_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_362_);
v___x_364_ = l_Lean_Syntax_matchesNull(v___x_362_, v___x_363_);
if (v___x_364_ == 0)
{
lean_object* v___x_365_; lean_object* v___x_366_; 
lean_dec(v___x_362_);
lean_dec(v___x_356_);
v___x_365_ = lean_box(0);
v___x_366_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_366_, 0, v___x_365_);
lean_ctor_set(v___x_366_, 1, v_a_350_);
return v___x_366_;
}
else
{
lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v_ref_369_; uint8_t v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_367_ = l_Lean_Syntax_getArg(v___x_362_, v___x_355_);
v___x_368_ = l_Lean_Syntax_getArg(v___x_362_, v___x_361_);
lean_dec(v___x_362_);
v_ref_369_ = l_Lean_replaceRef(v___x_356_, v_a_349_);
lean_dec(v___x_356_);
v___x_370_ = 0;
v___x_371_ = l_Lean_SourceInfo_fromRef(v_ref_369_, v___x_370_);
lean_dec(v_ref_369_);
v___x_372_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__19));
v___x_373_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_term___x3a_x3a___00__closed__22));
lean_inc(v___x_371_);
v___x_374_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_374_, 0, v___x_371_);
lean_ctor_set(v___x_374_, 1, v___x_373_);
v___x_375_ = l_Lean_Syntax_node3(v___x_371_, v___x_372_, v___x_367_, v___x_374_, v___x_368_);
v___x_376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_376_, 0, v___x_375_);
lean_ctor_set(v___x_376_, 1, v_a_350_);
return v___x_376_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______unexpand__Lean__Grind__AC__Seq__cons__1___boxed(lean_object* v_x_377_, lean_object* v_a_378_, lean_object* v_a_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC___aux__Lean__Meta__Tactic__Grind__AC__Seq______unexpand__Lean__Grind__AC__Seq__cons__1(v_x_377_, v_a_378_, v_a_379_);
lean_dec(v_a_378_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_instOfNatSeq__lean(lean_object* v_n_381_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_382_, 0, v_n_381_);
return v___x_382_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_a(void){
_start:
{
lean_object* v___x_383_; 
v___x_383_ = lean_unsigned_to_nat(1u);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_ctorIdx___impl(lean_object* v_x_384_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = lean_obj_tag_nat(v_x_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_ctorIdx___impl___boxed(lean_object* v_x_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Lean_Grind_AC_SubseqResult_ctorIdx___impl(v_x_386_);
lean_dec(v_x_386_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_ctorElim___redArg(lean_object* v_t_388_, lean_object* v_k_389_){
_start:
{
switch(lean_obj_tag(v_t_388_))
{
case 2:
{
lean_object* v_s_390_; lean_object* v___x_391_; 
v_s_390_ = lean_ctor_get(v_t_388_, 0);
lean_inc_ref(v_s_390_);
lean_dec_ref_known(v_t_388_, 1);
v___x_391_ = lean_apply_1(v_k_389_, v_s_390_);
return v___x_391_;
}
case 3:
{
lean_object* v_s_392_; lean_object* v___x_393_; 
v_s_392_ = lean_ctor_get(v_t_388_, 0);
lean_inc_ref(v_s_392_);
lean_dec_ref_known(v_t_388_, 1);
v___x_393_ = lean_apply_1(v_k_389_, v_s_392_);
return v___x_393_;
}
case 4:
{
lean_object* v_p_394_; lean_object* v_s_395_; lean_object* v___x_396_; 
v_p_394_ = lean_ctor_get(v_t_388_, 0);
lean_inc_ref(v_p_394_);
v_s_395_ = lean_ctor_get(v_t_388_, 1);
lean_inc_ref(v_s_395_);
lean_dec_ref_known(v_t_388_, 2);
v___x_396_ = lean_apply_2(v_k_389_, v_p_394_, v_s_395_);
return v___x_396_;
}
default: 
{
lean_dec(v_t_388_);
return v_k_389_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_ctorElim(lean_object* v_motive_397_, lean_object* v_ctorIdx_398_, lean_object* v_t_399_, lean_object* v_h_400_, lean_object* v_k_401_){
_start:
{
lean_object* v___x_402_; 
v___x_402_ = l_Lean_Grind_AC_SubseqResult_ctorElim___redArg(v_t_399_, v_k_401_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_ctorElim___boxed(lean_object* v_motive_403_, lean_object* v_ctorIdx_404_, lean_object* v_t_405_, lean_object* v_h_406_, lean_object* v_k_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Lean_Grind_AC_SubseqResult_ctorElim(v_motive_403_, v_ctorIdx_404_, v_t_405_, v_h_406_, v_k_407_);
lean_dec(v_ctorIdx_404_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_false_elim___redArg(lean_object* v_t_409_, lean_object* v_false_410_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = l_Lean_Grind_AC_SubseqResult_ctorElim___redArg(v_t_409_, v_false_410_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_false_elim(lean_object* v_motive_412_, lean_object* v_t_413_, lean_object* v_h_414_, lean_object* v_false_415_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = l_Lean_Grind_AC_SubseqResult_ctorElim___redArg(v_t_413_, v_false_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_exact_elim___redArg(lean_object* v_t_417_, lean_object* v_exact_418_){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = l_Lean_Grind_AC_SubseqResult_ctorElim___redArg(v_t_417_, v_exact_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_exact_elim(lean_object* v_motive_420_, lean_object* v_t_421_, lean_object* v_h_422_, lean_object* v_exact_423_){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = l_Lean_Grind_AC_SubseqResult_ctorElim___redArg(v_t_421_, v_exact_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_prefix_elim___redArg(lean_object* v_t_425_, lean_object* v_prefix_426_){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = l_Lean_Grind_AC_SubseqResult_ctorElim___redArg(v_t_425_, v_prefix_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_prefix_elim(lean_object* v_motive_428_, lean_object* v_t_429_, lean_object* v_h_430_, lean_object* v_prefix_431_){
_start:
{
lean_object* v___x_432_; 
v___x_432_ = l_Lean_Grind_AC_SubseqResult_ctorElim___redArg(v_t_429_, v_prefix_431_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_suffix_elim___redArg(lean_object* v_t_433_, lean_object* v_suffix_434_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = l_Lean_Grind_AC_SubseqResult_ctorElim___redArg(v_t_433_, v_suffix_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_suffix_elim(lean_object* v_motive_436_, lean_object* v_t_437_, lean_object* v_h_438_, lean_object* v_suffix_439_){
_start:
{
lean_object* v___x_440_; 
v___x_440_ = l_Lean_Grind_AC_SubseqResult_ctorElim___redArg(v_t_437_, v_suffix_439_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_middle_elim___redArg(lean_object* v_t_441_, lean_object* v_middle_442_){
_start:
{
lean_object* v___x_443_; 
v___x_443_ = l_Lean_Grind_AC_SubseqResult_ctorElim___redArg(v_t_441_, v_middle_442_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubseqResult_middle_elim(lean_object* v_motive_444_, lean_object* v_t_445_, lean_object* v_h_446_, lean_object* v_middle_447_){
_start:
{
lean_object* v___x_448_; 
v___x_448_ = l_Lean_Grind_AC_SubseqResult_ctorElim___redArg(v_t_445_, v_middle_447_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_subseq_go(lean_object* v_s_u2081_449_, lean_object* v_s_u2082_450_, lean_object* v_acc_451_){
_start:
{
if (lean_obj_tag(v_s_u2082_450_) == 0)
{
uint8_t v___x_452_; 
v___x_452_ = l_Lean_Grind_AC_instBEqSeq_beq(v_s_u2081_449_, v_s_u2082_450_);
lean_dec_ref_known(v_s_u2082_450_, 1);
lean_dec_ref(v_s_u2081_449_);
if (v___x_452_ == 0)
{
lean_object* v___x_453_; 
lean_dec_ref(v_acc_451_);
v___x_453_ = lean_box(0);
return v___x_453_;
}
else
{
lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_454_ = l_Lean_Grind_AC_Seq_reverse(v_acc_451_);
v___x_455_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_455_, 0, v___x_454_);
return v___x_455_;
}
}
else
{
lean_object* v_x_456_; lean_object* v_s_457_; lean_object* v___x_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_471_; 
v_x_456_ = lean_ctor_get(v_s_u2082_450_, 0);
lean_inc(v_x_456_);
v_s_457_ = lean_ctor_get(v_s_u2082_450_, 1);
lean_inc_ref(v_s_457_);
lean_inc_ref(v_s_u2081_449_);
v___x_458_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_startsWith(v_s_u2082_450_, v_s_u2081_449_);
v_isSharedCheck_471_ = !lean_is_exclusive(v_s_u2082_450_);
if (v_isSharedCheck_471_ == 0)
{
lean_object* v_unused_472_; lean_object* v_unused_473_; 
v_unused_472_ = lean_ctor_get(v_s_u2082_450_, 1);
lean_dec(v_unused_472_);
v_unused_473_ = lean_ctor_get(v_s_u2082_450_, 0);
lean_dec(v_unused_473_);
v___x_460_ = v_s_u2082_450_;
v_isShared_461_ = v_isSharedCheck_471_;
goto v_resetjp_459_;
}
else
{
lean_dec(v_s_u2082_450_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_471_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
switch(lean_obj_tag(v___x_458_))
{
case 0:
{
lean_object* v___x_463_; 
if (v_isShared_461_ == 0)
{
lean_ctor_set(v___x_460_, 1, v_acc_451_);
v___x_463_ = v___x_460_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_x_456_);
lean_ctor_set(v_reuseFailAlloc_465_, 1, v_acc_451_);
v___x_463_ = v_reuseFailAlloc_465_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
v_s_u2082_450_ = v_s_457_;
v_acc_451_ = v___x_463_;
goto _start;
}
}
case 1:
{
lean_object* v___x_466_; lean_object* v___x_467_; 
lean_del_object(v___x_460_);
lean_dec_ref(v_s_457_);
lean_dec(v_x_456_);
lean_dec_ref(v_s_u2081_449_);
v___x_466_ = l_Lean_Grind_AC_Seq_reverse(v_acc_451_);
v___x_467_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_467_, 0, v___x_466_);
return v___x_467_;
}
default: 
{
lean_object* v_s_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
lean_del_object(v___x_460_);
lean_dec_ref(v_s_457_);
lean_dec(v_x_456_);
lean_dec_ref(v_s_u2081_449_);
v_s_468_ = lean_ctor_get(v___x_458_, 0);
lean_inc_ref(v_s_468_);
lean_dec_ref_known(v___x_458_, 1);
v___x_469_ = l_Lean_Grind_AC_Seq_reverse(v_acc_451_);
v___x_470_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_470_, 0, v___x_469_);
lean_ctor_set(v___x_470_, 1, v_s_468_);
return v___x_470_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_subseq(lean_object* v_s_u2081_474_, lean_object* v_s_u2082_475_){
_start:
{
if (lean_obj_tag(v_s_u2082_475_) == 0)
{
uint8_t v___x_476_; 
v___x_476_ = l_Lean_Grind_AC_instBEqSeq_beq(v_s_u2081_474_, v_s_u2082_475_);
lean_dec_ref_known(v_s_u2082_475_, 1);
lean_dec_ref(v_s_u2081_474_);
if (v___x_476_ == 0)
{
lean_object* v___x_477_; 
v___x_477_ = lean_box(0);
return v___x_477_;
}
else
{
lean_object* v___x_478_; 
v___x_478_ = lean_box(1);
return v___x_478_;
}
}
else
{
lean_object* v_x_479_; lean_object* v_s_480_; lean_object* v___x_481_; 
v_x_479_ = lean_ctor_get(v_s_u2082_475_, 0);
lean_inc(v_x_479_);
v_s_480_ = lean_ctor_get(v_s_u2082_475_, 1);
lean_inc_ref(v_s_480_);
lean_inc_ref(v_s_u2081_474_);
v___x_481_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_startsWith(v_s_u2082_475_, v_s_u2081_474_);
lean_dec_ref_known(v_s_u2082_475_, 2);
switch(lean_obj_tag(v___x_481_))
{
case 0:
{
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_482_, 0, v_x_479_);
v___x_483_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_subseq_go(v_s_u2081_474_, v_s_480_, v___x_482_);
return v___x_483_;
}
case 1:
{
lean_object* v___x_484_; 
lean_dec_ref(v_s_480_);
lean_dec(v_x_479_);
lean_dec_ref(v_s_u2081_474_);
v___x_484_ = lean_box(1);
return v___x_484_;
}
default: 
{
lean_object* v_s_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_492_; 
lean_dec_ref(v_s_480_);
lean_dec(v_x_479_);
lean_dec_ref(v_s_u2081_474_);
v_s_485_ = lean_ctor_get(v___x_481_, 0);
v_isSharedCheck_492_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_492_ == 0)
{
v___x_487_ = v___x_481_;
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_s_485_);
lean_dec(v___x_481_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_490_; 
if (v_isShared_488_ == 0)
{
v___x_490_ = v___x_487_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_s_485_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubsetResult_ctorIdx___impl(lean_object* v_x_493_){
_start:
{
lean_object* v___x_494_; 
v___x_494_ = lean_obj_tag_nat(v_x_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubsetResult_ctorIdx___impl___boxed(lean_object* v_x_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_Lean_Grind_AC_SubsetResult_ctorIdx___impl(v_x_495_);
lean_dec(v_x_495_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubsetResult_ctorElim___redArg(lean_object* v_t_497_, lean_object* v_k_498_){
_start:
{
if (lean_obj_tag(v_t_497_) == 2)
{
lean_object* v_s_499_; lean_object* v___x_500_; 
v_s_499_ = lean_ctor_get(v_t_497_, 0);
lean_inc_ref(v_s_499_);
lean_dec_ref_known(v_t_497_, 1);
v___x_500_ = lean_apply_1(v_k_498_, v_s_499_);
return v___x_500_;
}
else
{
lean_dec(v_t_497_);
return v_k_498_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubsetResult_ctorElim(lean_object* v_motive_501_, lean_object* v_ctorIdx_502_, lean_object* v_t_503_, lean_object* v_h_504_, lean_object* v_k_505_){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = l_Lean_Grind_AC_SubsetResult_ctorElim___redArg(v_t_503_, v_k_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubsetResult_ctorElim___boxed(lean_object* v_motive_507_, lean_object* v_ctorIdx_508_, lean_object* v_t_509_, lean_object* v_h_510_, lean_object* v_k_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l_Lean_Grind_AC_SubsetResult_ctorElim(v_motive_507_, v_ctorIdx_508_, v_t_509_, v_h_510_, v_k_511_);
lean_dec(v_ctorIdx_508_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubsetResult_false_elim___redArg(lean_object* v_t_513_, lean_object* v_false_514_){
_start:
{
lean_object* v___x_515_; 
v___x_515_ = l_Lean_Grind_AC_SubsetResult_ctorElim___redArg(v_t_513_, v_false_514_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubsetResult_false_elim(lean_object* v_motive_516_, lean_object* v_t_517_, lean_object* v_h_518_, lean_object* v_false_519_){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = l_Lean_Grind_AC_SubsetResult_ctorElim___redArg(v_t_517_, v_false_519_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubsetResult_exact_elim___redArg(lean_object* v_t_521_, lean_object* v_exact_522_){
_start:
{
lean_object* v___x_523_; 
v___x_523_ = l_Lean_Grind_AC_SubsetResult_ctorElim___redArg(v_t_521_, v_exact_522_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubsetResult_exact_elim(lean_object* v_motive_524_, lean_object* v_t_525_, lean_object* v_h_526_, lean_object* v_exact_527_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = l_Lean_Grind_AC_SubsetResult_ctorElim___redArg(v_t_525_, v_exact_527_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubsetResult_strict_elim___redArg(lean_object* v_t_529_, lean_object* v_strict_530_){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = l_Lean_Grind_AC_SubsetResult_ctorElim___redArg(v_t_529_, v_strict_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_SubsetResult_strict_elim(lean_object* v_motive_532_, lean_object* v_t_533_, lean_object* v_h_534_, lean_object* v_strict_535_){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = l_Lean_Grind_AC_SubsetResult_ctorElim___redArg(v_t_533_, v_strict_535_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_subset_go(lean_object* v_s_u2081_537_, lean_object* v_s_u2082_538_, lean_object* v_acc_539_){
_start:
{
if (lean_obj_tag(v_s_u2081_537_) == 0)
{
if (lean_obj_tag(v_s_u2082_538_) == 0)
{
lean_object* v_x_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_551_; 
v_x_540_ = lean_ctor_get(v_s_u2081_537_, 0);
v_isSharedCheck_551_ = !lean_is_exclusive(v_s_u2081_537_);
if (v_isSharedCheck_551_ == 0)
{
v___x_542_ = v_s_u2081_537_;
v_isShared_543_ = v_isSharedCheck_551_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_x_540_);
lean_dec(v_s_u2081_537_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_551_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v_x_544_; uint8_t v___x_545_; 
v_x_544_ = lean_ctor_get(v_s_u2082_538_, 0);
lean_inc(v_x_544_);
lean_dec_ref_known(v_s_u2082_538_, 1);
v___x_545_ = lean_nat_dec_eq(v_x_540_, v_x_544_);
lean_dec(v_x_544_);
lean_dec(v_x_540_);
if (v___x_545_ == 0)
{
lean_object* v___x_546_; 
lean_del_object(v___x_542_);
lean_dec_ref(v_acc_539_);
v___x_546_ = lean_box(0);
return v___x_546_;
}
else
{
lean_object* v___x_547_; lean_object* v___x_549_; 
v___x_547_ = l_Lean_Grind_AC_Seq_reverse(v_acc_539_);
if (v_isShared_543_ == 0)
{
lean_ctor_set_tag(v___x_542_, 2);
lean_ctor_set(v___x_542_, 0, v___x_547_);
v___x_549_ = v___x_542_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v___x_547_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
}
else
{
lean_object* v_x_552_; lean_object* v_x_553_; lean_object* v_s_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_575_; 
v_x_552_ = lean_ctor_get(v_s_u2081_537_, 0);
v_x_553_ = lean_ctor_get(v_s_u2082_538_, 0);
v_s_554_ = lean_ctor_get(v_s_u2082_538_, 1);
v_isSharedCheck_575_ = !lean_is_exclusive(v_s_u2082_538_);
if (v_isSharedCheck_575_ == 0)
{
v___x_556_ = v_s_u2082_538_;
v_isShared_557_ = v_isSharedCheck_575_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_s_554_);
lean_inc(v_x_553_);
lean_dec(v_s_u2082_538_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_575_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
uint8_t v___x_558_; 
v___x_558_ = lean_nat_dec_eq(v_x_552_, v_x_553_);
if (v___x_558_ == 0)
{
uint8_t v___x_559_; 
v___x_559_ = lean_nat_dec_lt(v_x_552_, v_x_553_);
if (v___x_559_ == 0)
{
lean_object* v___x_561_; 
if (v_isShared_557_ == 0)
{
lean_ctor_set(v___x_556_, 1, v_acc_539_);
v___x_561_ = v___x_556_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_x_553_);
lean_ctor_set(v_reuseFailAlloc_563_, 1, v_acc_539_);
v___x_561_ = v_reuseFailAlloc_563_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
v_s_u2082_538_ = v_s_554_;
v_acc_539_ = v___x_561_;
goto _start;
}
}
else
{
lean_object* v___x_564_; 
lean_del_object(v___x_556_);
lean_dec_ref(v_s_554_);
lean_dec(v_x_553_);
lean_dec_ref_known(v_s_u2081_537_, 1);
lean_dec_ref(v_acc_539_);
v___x_564_ = lean_box(0);
return v___x_564_;
}
}
else
{
lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_573_; 
lean_del_object(v___x_556_);
lean_dec(v_x_553_);
v_isSharedCheck_573_ = !lean_is_exclusive(v_s_u2081_537_);
if (v_isSharedCheck_573_ == 0)
{
lean_object* v_unused_574_; 
v_unused_574_ = lean_ctor_get(v_s_u2081_537_, 0);
lean_dec(v_unused_574_);
v___x_566_ = v_s_u2081_537_;
v_isShared_567_ = v_isSharedCheck_573_;
goto v_resetjp_565_;
}
else
{
lean_dec(v_s_u2081_537_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_573_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_571_; 
v___x_568_ = l_Lean_Grind_AC_Seq_reverse(v_acc_539_);
v___x_569_ = l_Lean_Grind_AC_Seq_concat(v___x_568_, v_s_554_);
if (v_isShared_567_ == 0)
{
lean_ctor_set_tag(v___x_566_, 2);
lean_ctor_set(v___x_566_, 0, v___x_569_);
v___x_571_ = v___x_566_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v___x_569_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_s_u2082_538_) == 0)
{
lean_object* v___x_576_; 
lean_dec_ref_known(v_s_u2082_538_, 1);
lean_dec_ref_known(v_s_u2081_537_, 2);
lean_dec_ref(v_acc_539_);
v___x_576_ = lean_box(0);
return v___x_576_;
}
else
{
lean_object* v_x_577_; lean_object* v_s_578_; lean_object* v_x_579_; lean_object* v_s_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_592_; 
v_x_577_ = lean_ctor_get(v_s_u2081_537_, 0);
v_s_578_ = lean_ctor_get(v_s_u2081_537_, 1);
v_x_579_ = lean_ctor_get(v_s_u2082_538_, 0);
v_s_580_ = lean_ctor_get(v_s_u2082_538_, 1);
v_isSharedCheck_592_ = !lean_is_exclusive(v_s_u2082_538_);
if (v_isSharedCheck_592_ == 0)
{
v___x_582_ = v_s_u2082_538_;
v_isShared_583_ = v_isSharedCheck_592_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_s_580_);
lean_inc(v_x_579_);
lean_dec(v_s_u2082_538_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_592_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
uint8_t v___x_584_; 
v___x_584_ = lean_nat_dec_eq(v_x_577_, v_x_579_);
if (v___x_584_ == 0)
{
uint8_t v___x_585_; 
v___x_585_ = lean_nat_dec_lt(v_x_577_, v_x_579_);
if (v___x_585_ == 0)
{
lean_object* v___x_587_; 
if (v_isShared_583_ == 0)
{
lean_ctor_set(v___x_582_, 1, v_acc_539_);
v___x_587_ = v___x_582_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_x_579_);
lean_ctor_set(v_reuseFailAlloc_589_, 1, v_acc_539_);
v___x_587_ = v_reuseFailAlloc_589_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
v_s_u2082_538_ = v_s_580_;
v_acc_539_ = v___x_587_;
goto _start;
}
}
else
{
lean_object* v___x_590_; 
lean_del_object(v___x_582_);
lean_dec_ref(v_s_580_);
lean_dec(v_x_579_);
lean_dec_ref_known(v_s_u2081_537_, 2);
lean_dec_ref(v_acc_539_);
v___x_590_ = lean_box(0);
return v___x_590_;
}
}
else
{
lean_inc_ref(v_s_578_);
lean_del_object(v___x_582_);
lean_dec(v_x_579_);
lean_dec_ref_known(v_s_u2081_537_, 2);
v_s_u2081_537_ = v_s_578_;
v_s_u2082_538_ = v_s_580_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_subset(lean_object* v_s_u2081_593_, lean_object* v_s_u2082_594_){
_start:
{
if (lean_obj_tag(v_s_u2081_593_) == 0)
{
if (lean_obj_tag(v_s_u2082_594_) == 0)
{
lean_object* v_x_595_; lean_object* v_x_596_; uint8_t v___x_597_; 
v_x_595_ = lean_ctor_get(v_s_u2081_593_, 0);
lean_inc(v_x_595_);
lean_dec_ref_known(v_s_u2081_593_, 1);
v_x_596_ = lean_ctor_get(v_s_u2082_594_, 0);
lean_inc(v_x_596_);
lean_dec_ref_known(v_s_u2082_594_, 1);
v___x_597_ = lean_nat_dec_eq(v_x_595_, v_x_596_);
lean_dec(v_x_596_);
lean_dec(v_x_595_);
if (v___x_597_ == 0)
{
lean_object* v___x_598_; 
v___x_598_ = lean_box(0);
return v___x_598_;
}
else
{
lean_object* v___x_599_; 
v___x_599_ = lean_box(1);
return v___x_599_;
}
}
else
{
lean_object* v_x_600_; lean_object* v_x_601_; lean_object* v_s_602_; uint8_t v___x_603_; 
v_x_600_ = lean_ctor_get(v_s_u2081_593_, 0);
v_x_601_ = lean_ctor_get(v_s_u2082_594_, 0);
lean_inc(v_x_601_);
v_s_602_ = lean_ctor_get(v_s_u2082_594_, 1);
lean_inc_ref(v_s_602_);
lean_dec_ref_known(v_s_u2082_594_, 2);
v___x_603_ = lean_nat_dec_eq(v_x_600_, v_x_601_);
if (v___x_603_ == 0)
{
uint8_t v___x_604_; 
v___x_604_ = lean_nat_dec_lt(v_x_600_, v_x_601_);
if (v___x_604_ == 0)
{
lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_605_, 0, v_x_601_);
v___x_606_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_subset_go(v_s_u2081_593_, v_s_602_, v___x_605_);
return v___x_606_;
}
else
{
lean_object* v___x_607_; 
lean_dec_ref(v_s_602_);
lean_dec(v_x_601_);
lean_dec_ref_known(v_s_u2081_593_, 1);
v___x_607_ = lean_box(0);
return v___x_607_;
}
}
else
{
lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_614_; 
lean_dec(v_x_601_);
v_isSharedCheck_614_ = !lean_is_exclusive(v_s_u2081_593_);
if (v_isSharedCheck_614_ == 0)
{
lean_object* v_unused_615_; 
v_unused_615_ = lean_ctor_get(v_s_u2081_593_, 0);
lean_dec(v_unused_615_);
v___x_609_ = v_s_u2081_593_;
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
else
{
lean_dec(v_s_u2081_593_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_612_; 
if (v_isShared_610_ == 0)
{
lean_ctor_set_tag(v___x_609_, 2);
lean_ctor_set(v___x_609_, 0, v_s_602_);
v___x_612_ = v___x_609_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_s_602_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_s_u2082_594_) == 0)
{
lean_object* v___x_616_; 
lean_dec_ref_known(v_s_u2082_594_, 1);
lean_dec_ref_known(v_s_u2081_593_, 2);
v___x_616_ = lean_box(0);
return v___x_616_;
}
else
{
lean_object* v_x_617_; lean_object* v_s_618_; lean_object* v_x_619_; lean_object* v_s_620_; uint8_t v___x_621_; 
v_x_617_ = lean_ctor_get(v_s_u2081_593_, 0);
v_s_618_ = lean_ctor_get(v_s_u2081_593_, 1);
v_x_619_ = lean_ctor_get(v_s_u2082_594_, 0);
lean_inc(v_x_619_);
v_s_620_ = lean_ctor_get(v_s_u2082_594_, 1);
lean_inc_ref(v_s_620_);
lean_dec_ref_known(v_s_u2082_594_, 2);
v___x_621_ = lean_nat_dec_eq(v_x_617_, v_x_619_);
if (v___x_621_ == 0)
{
uint8_t v___x_622_; 
v___x_622_ = lean_nat_dec_lt(v_x_617_, v_x_619_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_623_, 0, v_x_619_);
v___x_624_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_subset_go(v_s_u2081_593_, v_s_620_, v___x_623_);
return v___x_624_;
}
else
{
lean_object* v___x_625_; 
lean_dec_ref(v_s_620_);
lean_dec(v_x_619_);
lean_dec_ref_known(v_s_u2081_593_, 2);
v___x_625_ = lean_box(0);
return v___x_625_;
}
}
else
{
lean_inc_ref(v_s_618_);
lean_dec(v_x_619_);
lean_dec_ref_known(v_s_u2081_593_, 2);
v_s_u2081_593_ = v_s_618_;
v_s_u2082_594_ = v_s_620_;
goto _start;
}
}
}
}
}
uint8_t l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_isSorted_go(lean_object* v_x_627_, lean_object* v_s_628_){
_start:
{
if (lean_obj_tag(v_s_628_) == 0)
{
lean_object* v_x_629_; uint8_t v___x_630_; 
v_x_629_ = lean_ctor_get(v_s_628_, 0);
v___x_630_ = lean_nat_dec_le(v_x_627_, v_x_629_);
return v___x_630_;
}
else
{
lean_object* v_x_631_; lean_object* v_s_632_; uint8_t v___x_633_; 
v_x_631_ = lean_ctor_get(v_s_628_, 0);
v_s_632_ = lean_ctor_get(v_s_628_, 1);
v___x_633_ = lean_nat_dec_le(v_x_627_, v_x_631_);
if (v___x_633_ == 0)
{
return v___x_633_;
}
else
{
v_x_627_ = v_x_631_;
v_s_628_ = v_s_632_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_isSorted_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_627_ = stack[0].m_obj;
lean_object* v_s_628_ = stack[1].m_obj;
uint8_t v_res_635_;
v_res_635_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_isSorted_go(v_x_627_, v_s_628_);
stack->m_num = v_res_635_;
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
uint8_t l_Lean_Grind_AC_Seq_isSorted(lean_object* v_s_640_){
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
LEAN_EXPORT void l_Lean_Grind_AC_Seq_isSorted_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_640_ = stack[0].m_obj;
uint8_t v_res_645_;
v_res_645_ = l_Lean_Grind_AC_Seq_isSorted(v_s_640_);
stack->m_num = v_res_645_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_isSorted___boxed(lean_object* v_s_646_){
_start:
{
uint8_t v_res_647_; lean_object* v_r_648_; 
v_res_647_ = l_Lean_Grind_AC_Seq_isSorted(v_s_646_);
lean_dec_ref(v_s_646_);
v_r_648_ = lean_box(v_res_647_);
return v_r_648_;
}
}
uint8_t l_Lean_Grind_AC_Seq_contains(lean_object* v_s_649_, lean_object* v_x_650_){
_start:
{
if (lean_obj_tag(v_s_649_) == 0)
{
lean_object* v_x_651_; uint8_t v___x_652_; 
v_x_651_ = lean_ctor_get(v_s_649_, 0);
v___x_652_ = lean_nat_dec_eq(v_x_650_, v_x_651_);
return v___x_652_;
}
else
{
lean_object* v_x_653_; lean_object* v_s_654_; uint8_t v___x_655_; 
v_x_653_ = lean_ctor_get(v_s_649_, 0);
v_s_654_ = lean_ctor_get(v_s_649_, 1);
v___x_655_ = lean_nat_dec_eq(v_x_650_, v_x_653_);
if (v___x_655_ == 0)
{
v_s_649_ = v_s_654_;
goto _start;
}
else
{
return v___x_655_;
}
}
}
}
LEAN_EXPORT void l_Lean_Grind_AC_Seq_contains_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_649_ = stack[0].m_obj;
lean_object* v_x_650_ = stack[1].m_obj;
uint8_t v_res_657_;
v_res_657_ = l_Lean_Grind_AC_Seq_contains(v_s_649_, v_x_650_);
stack->m_num = v_res_657_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_contains___boxed(lean_object* v_s_658_, lean_object* v_x_659_){
_start:
{
uint8_t v_res_660_; lean_object* v_r_661_; 
v_res_660_ = l_Lean_Grind_AC_Seq_contains(v_s_658_, v_x_659_);
lean_dec(v_x_659_);
lean_dec_ref(v_s_658_);
v_r_661_ = lean_box(v_res_660_);
return v_r_661_;
}
}
uint8_t l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_noAdjacentDuplicates_go(lean_object* v_x_662_, lean_object* v_s_663_){
_start:
{
if (lean_obj_tag(v_s_663_) == 0)
{
lean_object* v_x_664_; uint8_t v___x_665_; 
v_x_664_ = lean_ctor_get(v_s_663_, 0);
v___x_665_ = lean_nat_dec_eq(v_x_662_, v_x_664_);
if (v___x_665_ == 0)
{
uint8_t v___x_666_; 
v___x_666_ = 1;
return v___x_666_;
}
else
{
uint8_t v___x_667_; 
v___x_667_ = 0;
return v___x_667_;
}
}
else
{
lean_object* v_x_668_; lean_object* v_s_669_; uint8_t v___x_670_; 
v_x_668_ = lean_ctor_get(v_s_663_, 0);
v_s_669_ = lean_ctor_get(v_s_663_, 1);
v___x_670_ = lean_nat_dec_eq(v_x_662_, v_x_668_);
if (v___x_670_ == 0)
{
v_x_662_ = v_x_668_;
v_s_663_ = v_s_669_;
goto _start;
}
else
{
uint8_t v___x_672_; 
v___x_672_ = 0;
return v___x_672_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_noAdjacentDuplicates_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_662_ = stack[0].m_obj;
lean_object* v_s_663_ = stack[1].m_obj;
uint8_t v_res_673_;
v_res_673_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_noAdjacentDuplicates_go(v_x_662_, v_s_663_);
stack->m_num = v_res_673_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_noAdjacentDuplicates_go___boxed(lean_object* v_x_674_, lean_object* v_s_675_){
_start:
{
uint8_t v_res_676_; lean_object* v_r_677_; 
v_res_676_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_noAdjacentDuplicates_go(v_x_674_, v_s_675_);
lean_dec_ref(v_s_675_);
lean_dec(v_x_674_);
v_r_677_ = lean_box(v_res_676_);
return v_r_677_;
}
}
uint8_t l_Lean_Grind_AC_Seq_noAdjacentDuplicates(lean_object* v_s_678_){
_start:
{
if (lean_obj_tag(v_s_678_) == 0)
{
uint8_t v___x_679_; 
v___x_679_ = 1;
return v___x_679_;
}
else
{
lean_object* v_x_680_; lean_object* v_s_681_; uint8_t v___x_682_; 
v_x_680_ = lean_ctor_get(v_s_678_, 0);
v_s_681_ = lean_ctor_get(v_s_678_, 1);
v___x_682_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_noAdjacentDuplicates_go(v_x_680_, v_s_681_);
return v___x_682_;
}
}
}
LEAN_EXPORT void l_Lean_Grind_AC_Seq_noAdjacentDuplicates_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_678_ = stack[0].m_obj;
uint8_t v_res_683_;
v_res_683_ = l_Lean_Grind_AC_Seq_noAdjacentDuplicates(v_s_678_);
stack->m_num = v_res_683_;
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
uint8_t l_Lean_Grind_AC_Seq_sharesVar(lean_object* v_s_u2081_687_, lean_object* v_s_u2082_688_){
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
LEAN_EXPORT void l_Lean_Grind_AC_Seq_sharesVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_u2081_687_ = stack[0].m_obj;
lean_object* v_s_u2082_688_ = stack[1].m_obj;
uint8_t v_res_710_;
v_res_710_ = l_Lean_Grind_AC_Seq_sharesVar(v_s_u2081_687_, v_s_u2082_688_);
stack->m_num = v_res_710_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_sharesVar___boxed(lean_object* v_s_u2081_711_, lean_object* v_s_u2082_712_){
_start:
{
uint8_t v_res_713_; lean_object* v_r_714_; 
v_res_713_ = l_Lean_Grind_AC_Seq_sharesVar(v_s_u2081_711_, v_s_u2082_712_);
lean_dec_ref(v_s_u2082_712_);
lean_dec_ref(v_s_u2081_711_);
v_r_714_ = lean_box(v_res_713_);
return v_r_714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_startsWith_match__1_splitter___redArg(lean_object* v_s_u2082_715_, lean_object* v_s_u2081_716_, lean_object* v_h__1_717_, lean_object* v_h__2_718_, lean_object* v_h__3_719_, lean_object* v_h__4_720_){
_start:
{
if (lean_obj_tag(v_s_u2082_715_) == 0)
{
lean_dec(v_h__4_720_);
lean_dec(v_h__3_719_);
if (lean_obj_tag(v_s_u2081_716_) == 0)
{
lean_object* v_x_721_; lean_object* v_x_722_; lean_object* v___x_723_; 
lean_dec(v_h__2_718_);
v_x_721_ = lean_ctor_get(v_s_u2082_715_, 0);
lean_inc(v_x_721_);
lean_dec_ref_known(v_s_u2082_715_, 1);
v_x_722_ = lean_ctor_get(v_s_u2081_716_, 0);
lean_inc(v_x_722_);
lean_dec_ref_known(v_s_u2081_716_, 1);
v___x_723_ = lean_apply_2(v_h__1_717_, v_x_721_, v_x_722_);
return v___x_723_;
}
else
{
lean_object* v_x_724_; lean_object* v_x_725_; lean_object* v_s_726_; lean_object* v___x_727_; 
lean_dec(v_h__1_717_);
v_x_724_ = lean_ctor_get(v_s_u2082_715_, 0);
lean_inc(v_x_724_);
lean_dec_ref_known(v_s_u2082_715_, 1);
v_x_725_ = lean_ctor_get(v_s_u2081_716_, 0);
lean_inc(v_x_725_);
v_s_726_ = lean_ctor_get(v_s_u2081_716_, 1);
lean_inc_ref(v_s_726_);
lean_dec_ref_known(v_s_u2081_716_, 2);
v___x_727_ = lean_apply_3(v_h__2_718_, v_x_724_, v_x_725_, v_s_726_);
return v___x_727_;
}
}
else
{
lean_dec(v_h__2_718_);
lean_dec(v_h__1_717_);
if (lean_obj_tag(v_s_u2081_716_) == 0)
{
lean_object* v_x_728_; lean_object* v_s_729_; lean_object* v_x_730_; lean_object* v___x_731_; 
lean_dec(v_h__4_720_);
v_x_728_ = lean_ctor_get(v_s_u2082_715_, 0);
lean_inc(v_x_728_);
v_s_729_ = lean_ctor_get(v_s_u2082_715_, 1);
lean_inc_ref(v_s_729_);
lean_dec_ref_known(v_s_u2082_715_, 2);
v_x_730_ = lean_ctor_get(v_s_u2081_716_, 0);
lean_inc(v_x_730_);
lean_dec_ref_known(v_s_u2081_716_, 1);
v___x_731_ = lean_apply_3(v_h__3_719_, v_x_728_, v_s_729_, v_x_730_);
return v___x_731_;
}
else
{
lean_object* v_x_732_; lean_object* v_s_733_; lean_object* v_x_734_; lean_object* v_s_735_; lean_object* v___x_736_; 
lean_dec(v_h__3_719_);
v_x_732_ = lean_ctor_get(v_s_u2082_715_, 0);
lean_inc(v_x_732_);
v_s_733_ = lean_ctor_get(v_s_u2082_715_, 1);
lean_inc_ref(v_s_733_);
lean_dec_ref_known(v_s_u2082_715_, 2);
v_x_734_ = lean_ctor_get(v_s_u2081_716_, 0);
lean_inc(v_x_734_);
v_s_735_ = lean_ctor_get(v_s_u2081_716_, 1);
lean_inc_ref(v_s_735_);
lean_dec_ref_known(v_s_u2081_716_, 2);
v___x_736_ = lean_apply_4(v_h__4_720_, v_x_732_, v_s_733_, v_x_734_, v_s_735_);
return v___x_736_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_startsWith_match__1_splitter(lean_object* v_motive_737_, lean_object* v_s_u2082_738_, lean_object* v_s_u2081_739_, lean_object* v_h__1_740_, lean_object* v_h__2_741_, lean_object* v_h__3_742_, lean_object* v_h__4_743_){
_start:
{
if (lean_obj_tag(v_s_u2082_738_) == 0)
{
lean_dec(v_h__4_743_);
lean_dec(v_h__3_742_);
if (lean_obj_tag(v_s_u2081_739_) == 0)
{
lean_object* v_x_744_; lean_object* v_x_745_; lean_object* v___x_746_; 
lean_dec(v_h__2_741_);
v_x_744_ = lean_ctor_get(v_s_u2082_738_, 0);
lean_inc(v_x_744_);
lean_dec_ref_known(v_s_u2082_738_, 1);
v_x_745_ = lean_ctor_get(v_s_u2081_739_, 0);
lean_inc(v_x_745_);
lean_dec_ref_known(v_s_u2081_739_, 1);
v___x_746_ = lean_apply_2(v_h__1_740_, v_x_744_, v_x_745_);
return v___x_746_;
}
else
{
lean_object* v_x_747_; lean_object* v_x_748_; lean_object* v_s_749_; lean_object* v___x_750_; 
lean_dec(v_h__1_740_);
v_x_747_ = lean_ctor_get(v_s_u2082_738_, 0);
lean_inc(v_x_747_);
lean_dec_ref_known(v_s_u2082_738_, 1);
v_x_748_ = lean_ctor_get(v_s_u2081_739_, 0);
lean_inc(v_x_748_);
v_s_749_ = lean_ctor_get(v_s_u2081_739_, 1);
lean_inc_ref(v_s_749_);
lean_dec_ref_known(v_s_u2081_739_, 2);
v___x_750_ = lean_apply_3(v_h__2_741_, v_x_747_, v_x_748_, v_s_749_);
return v___x_750_;
}
}
else
{
lean_dec(v_h__2_741_);
lean_dec(v_h__1_740_);
if (lean_obj_tag(v_s_u2081_739_) == 0)
{
lean_object* v_x_751_; lean_object* v_s_752_; lean_object* v_x_753_; lean_object* v___x_754_; 
lean_dec(v_h__4_743_);
v_x_751_ = lean_ctor_get(v_s_u2082_738_, 0);
lean_inc(v_x_751_);
v_s_752_ = lean_ctor_get(v_s_u2082_738_, 1);
lean_inc_ref(v_s_752_);
lean_dec_ref_known(v_s_u2082_738_, 2);
v_x_753_ = lean_ctor_get(v_s_u2081_739_, 0);
lean_inc(v_x_753_);
lean_dec_ref_known(v_s_u2081_739_, 1);
v___x_754_ = lean_apply_3(v_h__3_742_, v_x_751_, v_s_752_, v_x_753_);
return v___x_754_;
}
else
{
lean_object* v_x_755_; lean_object* v_s_756_; lean_object* v_x_757_; lean_object* v_s_758_; lean_object* v___x_759_; 
lean_dec(v_h__3_742_);
v_x_755_ = lean_ctor_get(v_s_u2082_738_, 0);
lean_inc(v_x_755_);
v_s_756_ = lean_ctor_get(v_s_u2082_738_, 1);
lean_inc_ref(v_s_756_);
lean_dec_ref_known(v_s_u2082_738_, 2);
v_x_757_ = lean_ctor_get(v_s_u2081_739_, 0);
lean_inc(v_x_757_);
v_s_758_ = lean_ctor_get(v_s_u2081_739_, 1);
lean_inc_ref(v_s_758_);
lean_dec_ref_known(v_s_u2081_739_, 2);
v___x_759_ = lean_apply_4(v_h__4_743_, v_x_755_, v_s_756_, v_x_757_, v_s_758_);
return v___x_759_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_toSeq_x3f_go(lean_object* v_xs_760_, lean_object* v_acc_761_){
_start:
{
if (lean_obj_tag(v_xs_760_) == 0)
{
lean_object* v___x_762_; 
v___x_762_ = l_Lean_Grind_AC_Seq_reverse(v_acc_761_);
return v___x_762_;
}
else
{
lean_object* v_head_763_; lean_object* v_tail_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_772_; 
v_head_763_ = lean_ctor_get(v_xs_760_, 0);
v_tail_764_ = lean_ctor_get(v_xs_760_, 1);
v_isSharedCheck_772_ = !lean_is_exclusive(v_xs_760_);
if (v_isSharedCheck_772_ == 0)
{
v___x_766_ = v_xs_760_;
v_isShared_767_ = v_isSharedCheck_772_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_tail_764_);
lean_inc(v_head_763_);
lean_dec(v_xs_760_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_772_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___x_769_; 
if (v_isShared_767_ == 0)
{
lean_ctor_set(v___x_766_, 1, v_acc_761_);
v___x_769_ = v___x_766_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_head_763_);
lean_ctor_set(v_reuseFailAlloc_771_, 1, v_acc_761_);
v___x_769_ = v_reuseFailAlloc_771_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
v_xs_760_ = v_tail_764_;
v_acc_761_ = v___x_769_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_toSeq_x3f(lean_object* v_xs_773_){
_start:
{
if (lean_obj_tag(v_xs_773_) == 0)
{
lean_object* v___x_774_; 
v___x_774_ = lean_box(0);
return v___x_774_;
}
else
{
lean_object* v_head_775_; lean_object* v_tail_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; 
v_head_775_ = lean_ctor_get(v_xs_773_, 0);
lean_inc(v_head_775_);
v_tail_776_ = lean_ctor_get(v_xs_773_, 1);
lean_inc(v_tail_776_);
lean_dec_ref_known(v_xs_773_, 2);
v___x_777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_777_, 0, v_head_775_);
v___x_778_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_toSeq_x3f_go(v_tail_776_, v___x_777_);
v___x_779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_779_, 0, v___x_778_);
return v___x_779_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(lean_object* v_s_x3f_780_, lean_object* v_x_781_){
_start:
{
if (lean_obj_tag(v_s_x3f_780_) == 0)
{
lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_782_, 0, v_x_781_);
v___x_783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_783_, 0, v___x_782_);
return v___x_783_;
}
else
{
lean_object* v_val_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_792_; 
v_val_784_ = lean_ctor_get(v_s_x3f_780_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v_s_x3f_780_);
if (v_isSharedCheck_792_ == 0)
{
v___x_786_ = v_s_x3f_780_;
v_isShared_787_ = v_isSharedCheck_792_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_val_784_);
lean_dec(v_s_x3f_780_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_792_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_788_; lean_object* v___x_790_; 
v___x_788_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_788_, 0, v_x_781_);
lean_ctor_set(v___x_788_, 1, v_val_784_);
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 0, v___x_788_);
v___x_790_ = v___x_786_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v___x_788_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(lean_object* v_s_x3f_793_){
_start:
{
if (lean_obj_tag(v_s_x3f_793_) == 0)
{
return v_s_x3f_793_;
}
else
{
lean_object* v_val_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_802_; 
v_val_794_ = lean_ctor_get(v_s_x3f_793_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v_s_x3f_793_);
if (v_isSharedCheck_802_ == 0)
{
v___x_796_ = v_s_x3f_793_;
v_isShared_797_ = v_isSharedCheck_802_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_val_794_);
lean_dec(v_s_x3f_793_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_802_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_798_; lean_object* v___x_800_; 
v___x_798_ = l_Lean_Grind_AC_Seq_reverse(v_val_794_);
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 0, v___x_798_);
v___x_800_ = v___x_796_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v___x_798_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_app(lean_object* v_s_x3f_803_, lean_object* v_s_x27_804_){
_start:
{
if (lean_obj_tag(v_s_x3f_803_) == 0)
{
lean_object* v___x_805_; 
v___x_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_805_, 0, v_s_x27_804_);
return v___x_805_;
}
else
{
lean_object* v_val_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_814_; 
v_val_806_ = lean_ctor_get(v_s_x3f_803_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v_s_x3f_803_);
if (v_isSharedCheck_814_ == 0)
{
v___x_808_ = v_s_x3f_803_;
v_isShared_809_ = v_isSharedCheck_814_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_val_806_);
lean_dec(v_s_x3f_803_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_814_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_810_; lean_object* v___x_812_; 
v___x_810_ = l_Lean_Grind_AC_Seq_concat(v_val_806_, v_s_x27_804_);
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 0, v___x_810_);
v___x_812_ = v___x_808_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(1, 1, 0);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superposeAC_x3f_mkResult(lean_object* v_r_u2081_815_, lean_object* v_c_816_, lean_object* v_r_u2082_817_){
_start:
{
if (lean_obj_tag(v_r_u2081_815_) == 1)
{
if (lean_obj_tag(v_c_816_) == 1)
{
if (lean_obj_tag(v_r_u2082_817_) == 1)
{
lean_object* v_val_818_; lean_object* v_val_819_; lean_object* v_val_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_829_; 
v_val_818_ = lean_ctor_get(v_r_u2081_815_, 0);
v_val_819_ = lean_ctor_get(v_c_816_, 0);
v_val_820_ = lean_ctor_get(v_r_u2082_817_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v_r_u2082_817_);
if (v_isSharedCheck_829_ == 0)
{
v___x_822_ = v_r_u2082_817_;
v_isShared_823_ = v_isSharedCheck_829_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_val_820_);
lean_dec(v_r_u2082_817_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_829_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_827_; 
lean_inc(v_val_819_);
v___x_824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_824_, 0, v_val_819_);
lean_ctor_set(v___x_824_, 1, v_val_820_);
lean_inc(v_val_818_);
v___x_825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_825_, 0, v_val_818_);
lean_ctor_set(v___x_825_, 1, v___x_824_);
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 0, v___x_825_);
v___x_827_ = v___x_822_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v___x_825_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
}
else
{
lean_object* v___x_830_; 
lean_dec(v_r_u2082_817_);
v___x_830_ = lean_box(0);
return v___x_830_;
}
}
else
{
lean_object* v___x_831_; 
lean_dec(v_r_u2082_817_);
v___x_831_ = lean_box(0);
return v___x_831_;
}
}
else
{
lean_object* v___x_832_; 
lean_dec(v_r_u2082_817_);
v___x_832_ = lean_box(0);
return v___x_832_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superposeAC_x3f_mkResult___boxed(lean_object* v_r_u2081_833_, lean_object* v_c_834_, lean_object* v_r_u2082_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superposeAC_x3f_mkResult(v_r_u2081_833_, v_c_834_, v_r_u2082_835_);
lean_dec(v_c_834_);
lean_dec(v_r_u2081_833_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superposeAC_x3f_go(lean_object* v_s_u2081_837_, lean_object* v_s_u2082_838_, lean_object* v_r_u2081_839_, lean_object* v_c_840_, lean_object* v_r_u2082_841_){
_start:
{
if (lean_obj_tag(v_s_u2081_837_) == 0)
{
if (lean_obj_tag(v_s_u2082_838_) == 0)
{
lean_object* v_x_842_; lean_object* v_x_843_; uint8_t v___x_844_; 
v_x_842_ = lean_ctor_get(v_s_u2081_837_, 0);
lean_inc(v_x_842_);
lean_dec_ref_known(v_s_u2081_837_, 1);
v_x_843_ = lean_ctor_get(v_s_u2082_838_, 0);
lean_inc(v_x_843_);
lean_dec_ref_known(v_s_u2082_838_, 1);
v___x_844_ = lean_nat_dec_eq(v_x_842_, v_x_843_);
if (v___x_844_ == 0)
{
lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_845_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(v_r_u2081_839_, v_x_842_);
v___x_846_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v___x_845_);
v___x_847_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v_c_840_);
v___x_848_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(v_r_u2082_841_, v_x_843_);
v___x_849_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v___x_848_);
v___x_850_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superposeAC_x3f_mkResult(v___x_846_, v___x_847_, v___x_849_);
lean_dec(v___x_847_);
lean_dec(v___x_846_);
return v___x_850_;
}
else
{
lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
lean_dec(v_x_843_);
v___x_851_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v_r_u2081_839_);
v___x_852_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(v_c_840_, v_x_842_);
v___x_853_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v___x_852_);
v___x_854_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v_r_u2082_841_);
v___x_855_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superposeAC_x3f_mkResult(v___x_851_, v___x_853_, v___x_854_);
lean_dec(v___x_853_);
lean_dec(v___x_851_);
return v___x_855_;
}
}
else
{
lean_object* v_x_856_; lean_object* v_x_857_; lean_object* v_s_858_; uint8_t v___x_859_; 
v_x_856_ = lean_ctor_get(v_s_u2081_837_, 0);
v_x_857_ = lean_ctor_get(v_s_u2082_838_, 0);
v_s_858_ = lean_ctor_get(v_s_u2082_838_, 1);
v___x_859_ = lean_nat_dec_eq(v_x_856_, v_x_857_);
if (v___x_859_ == 0)
{
uint8_t v___x_860_; 
v___x_860_ = lean_nat_dec_lt(v_x_856_, v_x_857_);
if (v___x_860_ == 0)
{
lean_object* v___x_861_; 
lean_inc_ref(v_s_858_);
lean_inc(v_x_857_);
lean_dec_ref_known(v_s_u2082_838_, 2);
v___x_861_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(v_r_u2082_841_, v_x_857_);
v_s_u2082_838_ = v_s_858_;
v_r_u2082_841_ = v___x_861_;
goto _start;
}
else
{
lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
lean_inc(v_x_856_);
lean_dec_ref_known(v_s_u2081_837_, 1);
v___x_863_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(v_r_u2081_839_, v_x_856_);
v___x_864_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v___x_863_);
v___x_865_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v_c_840_);
v___x_866_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v_r_u2082_841_);
v___x_867_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_app(v___x_866_, v_s_u2082_838_);
v___x_868_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superposeAC_x3f_mkResult(v___x_864_, v___x_865_, v___x_867_);
lean_dec(v___x_865_);
lean_dec(v___x_864_);
return v___x_868_;
}
}
else
{
lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
lean_inc_ref(v_s_858_);
lean_inc(v_x_856_);
lean_dec_ref_known(v_s_u2082_838_, 2);
lean_dec_ref_known(v_s_u2081_837_, 1);
v___x_869_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v_r_u2081_839_);
v___x_870_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(v_c_840_, v_x_856_);
v___x_871_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v___x_870_);
v___x_872_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v_r_u2082_841_);
v___x_873_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_app(v___x_872_, v_s_858_);
v___x_874_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superposeAC_x3f_mkResult(v___x_869_, v___x_871_, v___x_873_);
lean_dec(v___x_871_);
lean_dec(v___x_869_);
return v___x_874_;
}
}
}
else
{
if (lean_obj_tag(v_s_u2082_838_) == 0)
{
lean_object* v_x_875_; lean_object* v_s_876_; lean_object* v_x_877_; uint8_t v___x_878_; 
v_x_875_ = lean_ctor_get(v_s_u2081_837_, 0);
v_s_876_ = lean_ctor_get(v_s_u2081_837_, 1);
v_x_877_ = lean_ctor_get(v_s_u2082_838_, 0);
v___x_878_ = lean_nat_dec_eq(v_x_875_, v_x_877_);
if (v___x_878_ == 0)
{
uint8_t v___x_879_; 
v___x_879_ = lean_nat_dec_lt(v_x_875_, v_x_877_);
if (v___x_879_ == 0)
{
lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
lean_inc(v_x_877_);
lean_dec_ref_known(v_s_u2082_838_, 1);
v___x_880_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v_r_u2081_839_);
v___x_881_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_app(v___x_880_, v_s_u2081_837_);
v___x_882_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v_c_840_);
v___x_883_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(v_r_u2082_841_, v_x_877_);
v___x_884_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v___x_883_);
v___x_885_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superposeAC_x3f_mkResult(v___x_881_, v___x_882_, v___x_884_);
lean_dec(v___x_882_);
lean_dec(v___x_881_);
return v___x_885_;
}
else
{
lean_object* v___x_886_; 
lean_inc_ref(v_s_876_);
lean_inc(v_x_875_);
lean_dec_ref_known(v_s_u2081_837_, 2);
v___x_886_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(v_r_u2081_839_, v_x_875_);
v_s_u2081_837_ = v_s_876_;
v_r_u2081_839_ = v___x_886_;
goto _start;
}
}
else
{
lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
lean_inc_ref(v_s_876_);
lean_inc(v_x_875_);
lean_dec_ref_known(v_s_u2082_838_, 1);
lean_dec_ref_known(v_s_u2081_837_, 2);
v___x_888_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v_r_u2081_839_);
v___x_889_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_app(v___x_888_, v_s_876_);
v___x_890_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(v_c_840_, v_x_875_);
v___x_891_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v___x_890_);
v___x_892_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_rev(v_r_u2082_841_);
v___x_893_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superposeAC_x3f_mkResult(v___x_889_, v___x_891_, v___x_892_);
lean_dec(v___x_891_);
lean_dec(v___x_889_);
return v___x_893_;
}
}
else
{
lean_object* v_x_894_; lean_object* v_s_895_; lean_object* v_x_896_; lean_object* v_s_897_; uint8_t v___x_898_; 
v_x_894_ = lean_ctor_get(v_s_u2081_837_, 0);
v_s_895_ = lean_ctor_get(v_s_u2081_837_, 1);
v_x_896_ = lean_ctor_get(v_s_u2082_838_, 0);
v_s_897_ = lean_ctor_get(v_s_u2082_838_, 1);
v___x_898_ = lean_nat_dec_eq(v_x_894_, v_x_896_);
if (v___x_898_ == 0)
{
uint8_t v___x_899_; 
v___x_899_ = lean_nat_dec_lt(v_x_894_, v_x_896_);
if (v___x_899_ == 0)
{
lean_object* v___x_900_; 
lean_inc_ref(v_s_897_);
lean_inc(v_x_896_);
lean_dec_ref_known(v_s_u2082_838_, 2);
v___x_900_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(v_r_u2082_841_, v_x_896_);
v_s_u2082_838_ = v_s_897_;
v_r_u2082_841_ = v___x_900_;
goto _start;
}
else
{
lean_object* v___x_902_; 
lean_inc_ref(v_s_895_);
lean_inc(v_x_894_);
lean_dec_ref_known(v_s_u2081_837_, 2);
v___x_902_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(v_r_u2081_839_, v_x_894_);
v_s_u2081_837_ = v_s_895_;
v_r_u2081_839_ = v___x_902_;
goto _start;
}
}
else
{
lean_object* v___x_904_; 
lean_inc_ref(v_s_897_);
lean_inc_ref(v_s_895_);
lean_inc(v_x_894_);
lean_dec_ref_known(v_s_u2082_838_, 2);
lean_dec_ref_known(v_s_u2081_837_, 2);
v___x_904_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_push(v_c_840_, v_x_894_);
v_s_u2081_837_ = v_s_895_;
v_s_u2082_838_ = v_s_897_;
v_c_840_ = v___x_904_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_superposeAC_x3f(lean_object* v_s_u2081_906_, lean_object* v_s_u2082_907_){
_start:
{
lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_908_ = lean_box(0);
v___x_909_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superposeAC_x3f_go(v_s_u2081_906_, v_s_u2082_907_, v___x_908_, v___x_908_, v___x_908_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superpose_x3f_go(lean_object* v_s_u2081_910_, lean_object* v_s_u2082_911_, lean_object* v_p_912_){
_start:
{
lean_object* v___x_913_; 
lean_inc_ref(v_s_u2081_910_);
v___x_913_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_startsWith(v_s_u2082_911_, v_s_u2081_910_);
switch(lean_obj_tag(v___x_913_))
{
case 0:
{
if (lean_obj_tag(v_s_u2081_910_) == 0)
{
lean_object* v___x_914_; 
lean_dec_ref_known(v_s_u2081_910_, 1);
lean_dec_ref(v_p_912_);
v___x_914_ = lean_box(0);
return v___x_914_;
}
else
{
lean_object* v_x_915_; lean_object* v_s_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_924_; 
v_x_915_ = lean_ctor_get(v_s_u2081_910_, 0);
v_s_916_ = lean_ctor_get(v_s_u2081_910_, 1);
v_isSharedCheck_924_ = !lean_is_exclusive(v_s_u2081_910_);
if (v_isSharedCheck_924_ == 0)
{
v___x_918_ = v_s_u2081_910_;
v_isShared_919_ = v_isSharedCheck_924_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_s_916_);
lean_inc(v_x_915_);
lean_dec(v_s_u2081_910_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_924_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_921_; 
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 1, v_p_912_);
v___x_921_ = v___x_918_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_x_915_);
lean_ctor_set(v_reuseFailAlloc_923_, 1, v_p_912_);
v___x_921_ = v_reuseFailAlloc_923_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
v_s_u2081_910_ = v_s_916_;
v_p_912_ = v___x_921_;
goto _start;
}
}
}
}
case 1:
{
lean_object* v___x_925_; 
lean_dec_ref(v_p_912_);
lean_dec_ref(v_s_u2081_910_);
v___x_925_ = lean_box(0);
return v___x_925_;
}
default: 
{
lean_object* v_s_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_936_; 
v_s_926_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_936_ == 0)
{
v___x_928_ = v___x_913_;
v_isShared_929_ = v_isSharedCheck_936_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_s_926_);
lean_dec(v___x_913_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_936_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_934_; 
v___x_930_ = l_Lean_Grind_AC_Seq_reverse(v_p_912_);
v___x_931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_931_, 0, v_s_u2081_910_);
lean_ctor_set(v___x_931_, 1, v_s_926_);
v___x_932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_932_, 0, v___x_930_);
lean_ctor_set(v___x_932_, 1, v___x_931_);
if (v_isShared_929_ == 0)
{
lean_ctor_set_tag(v___x_928_, 1);
lean_ctor_set(v___x_928_, 0, v___x_932_);
v___x_934_ = v___x_928_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v___x_932_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superpose_x3f_go___boxed(lean_object* v_s_u2081_937_, lean_object* v_s_u2082_938_, lean_object* v_p_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superpose_x3f_go(v_s_u2081_937_, v_s_u2082_938_, v_p_939_);
lean_dec_ref(v_s_u2082_938_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_superpose_x3f(lean_object* v_s_u2081_941_, lean_object* v_s_u2082_942_){
_start:
{
if (lean_obj_tag(v_s_u2081_941_) == 0)
{
lean_object* v___x_943_; 
lean_dec_ref_known(v_s_u2081_941_, 1);
v___x_943_ = lean_box(0);
return v___x_943_;
}
else
{
lean_object* v_x_944_; lean_object* v_s_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
v_x_944_ = lean_ctor_get(v_s_u2081_941_, 0);
lean_inc(v_x_944_);
v_s_945_ = lean_ctor_get(v_s_u2081_941_, 1);
lean_inc_ref(v_s_945_);
lean_dec_ref_known(v_s_u2081_941_, 2);
v___x_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_946_, 0, v_x_944_);
v___x_947_ = l___private_Lean_Meta_Tactic_Grind_AC_Seq_0__Lean_Grind_AC_Seq_superpose_x3f_go(v_s_945_, v_s_u2082_942_, v___x_946_);
return v___x_947_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_superpose_x3f___boxed(lean_object* v_s_u2081_948_, lean_object* v_s_u2082_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l_Lean_Grind_AC_Seq_superpose_x3f(v_s_u2081_948_, v_s_u2082_949_);
lean_dec_ref(v_s_u2082_949_);
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_firstVar(lean_object* v_s_951_){
_start:
{
lean_object* v_x_952_; 
v_x_952_ = lean_ctor_get(v_s_951_, 0);
lean_inc(v_x_952_);
return v_x_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_firstVar___boxed(lean_object* v_s_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l_Lean_Grind_AC_Seq_firstVar(v_s_953_);
lean_dec_ref(v_s_953_);
return v_res_954_;
}
}
uint8_t l_Lean_Grind_AC_Seq_startsWithVar(lean_object* v_s_955_, lean_object* v_x_956_){
_start:
{
lean_object* v_x_957_; uint8_t v___x_958_; 
v_x_957_ = lean_ctor_get(v_s_955_, 0);
v___x_958_ = lean_nat_dec_eq(v_x_956_, v_x_957_);
return v___x_958_;
}
}
LEAN_EXPORT void l_Lean_Grind_AC_Seq_startsWithVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_955_ = stack[0].m_obj;
lean_object* v_x_956_ = stack[1].m_obj;
uint8_t v_res_959_;
v_res_959_ = l_Lean_Grind_AC_Seq_startsWithVar(v_s_955_, v_x_956_);
stack->m_num = v_res_959_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_startsWithVar___boxed(lean_object* v_s_960_, lean_object* v_x_961_){
_start:
{
uint8_t v_res_962_; lean_object* v_r_963_; 
v_res_962_ = l_Lean_Grind_AC_Seq_startsWithVar(v_s_960_, v_x_961_);
lean_dec(v_x_961_);
lean_dec_ref(v_s_960_);
v_r_963_ = lean_box(v_res_962_);
return v_r_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_lastVar(lean_object* v_s_964_){
_start:
{
if (lean_obj_tag(v_s_964_) == 0)
{
lean_object* v_x_965_; 
v_x_965_ = lean_ctor_get(v_s_964_, 0);
lean_inc(v_x_965_);
return v_x_965_;
}
else
{
lean_object* v_s_966_; 
v_s_966_ = lean_ctor_get(v_s_964_, 1);
v_s_964_ = v_s_966_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_lastVar___boxed(lean_object* v_s_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l_Lean_Grind_AC_Seq_lastVar(v_s_968_);
lean_dec_ref(v_s_968_);
return v_res_969_;
}
}
uint8_t l_Lean_Grind_AC_Seq_endsWithVar(lean_object* v_s_970_, lean_object* v_x_971_){
_start:
{
if (lean_obj_tag(v_s_970_) == 0)
{
lean_object* v_x_972_; uint8_t v___x_973_; 
v_x_972_ = lean_ctor_get(v_s_970_, 0);
v___x_973_ = lean_nat_dec_eq(v_x_971_, v_x_972_);
return v___x_973_;
}
else
{
lean_object* v_s_974_; 
v_s_974_ = lean_ctor_get(v_s_970_, 1);
v_s_970_ = v_s_974_;
goto _start;
}
}
}
LEAN_EXPORT void l_Lean_Grind_AC_Seq_endsWithVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_970_ = stack[0].m_obj;
lean_object* v_x_971_ = stack[1].m_obj;
uint8_t v_res_976_;
v_res_976_ = l_Lean_Grind_AC_Seq_endsWithVar(v_s_970_, v_x_971_);
stack->m_num = v_res_976_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_endsWithVar___boxed(lean_object* v_s_977_, lean_object* v_x_978_){
_start:
{
uint8_t v_res_979_; lean_object* v_r_980_; 
v_res_979_ = l_Lean_Grind_AC_Seq_endsWithVar(v_s_977_, v_x_978_);
lean_dec(v_x_978_);
lean_dec_ref(v_s_977_);
v_r_980_ = lean_box(v_res_979_);
return v_r_980_;
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
