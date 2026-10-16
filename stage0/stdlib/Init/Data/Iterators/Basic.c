// Lean compiler output
// Module: Init.Data.Iterators.Basic
// Imports: public import Init.NotationExtra public import Init.WFTactics import Init.Ext import Init.PropLemmas
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0___redArg();
lean_object* lean_obj_tag_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Basic_0__Std_Internal_idOpaque___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Basic_0__Std_Internal_idOpaque___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Init_Data_Iterators_Basic_0__Std_Internal_idOpaque___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Iterators_Basic_0__Std_Internal_idOpaque___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Iterators_Basic_0__Std_Internal_idOpaque___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Iterators_Basic_0__Std_Internal_idOpaque___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Basic_0__Std_Internal_idOpaque___redArg();
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Basic_0__Std_Internal_idOpaque___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Basic_0__Std_Internal_idOpaque(lean_object*);
LEAN_EXPORT lean_object* l_Std_Shrink_deflate___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Shrink_deflate___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Shrink_deflate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Shrink_deflate___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Shrink_inflate___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Shrink_inflate___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Shrink_inflate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Shrink_inflate___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toIterM___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toIterM___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toIterM(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toIterM___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toIter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toIter___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toIter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toIter___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterStep_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterStep_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterStep_ctorIdx___impl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterStep_ctorIdx___impl___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterStep_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterStep_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterStep_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterStep_yield_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterStep_yield_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterStep_skip_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterStep_skip_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterStep_done_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterStep_done_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterStep_successor___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterStep_successor(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterStep_mapIterator___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterStep_mapIterator(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PlausibleIterStep_yield___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PlausibleIterStep_yield(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PlausibleIterStep_skip___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_PlausibleIterStep_skip(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PlausibleIterStep_done___redArg();
LEAN_EXPORT lean_object* l_Std_PlausibleIterStep_done___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_PlausibleIterStep_done(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PlausibleIterStep_casesOn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PlausibleIterStep_casesOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_mk_x27___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_mk_x27___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_mk_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_mk_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_toIterM___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_toIterM___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_toIterM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_toIterM___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_step___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_step(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Step_toMonadic___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Step_toMonadic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Step_toMonadic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Step_toPure___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Step_toPure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Step_toPure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_step___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_step(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_TerminationMeasures_instWellFoundedRelationFinite___redArg();
LEAN_EXPORT lean_object* l_Std_IterM_TerminationMeasures_instWellFoundedRelationFinite___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_TerminationMeasures_instWellFoundedRelationFinite(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_TerminationMeasures_instWellFoundedRelationFinite___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySteps___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySteps___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySteps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySteps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySteps_x21___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySteps_x21___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySteps_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySteps_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "tacticDecreasing_trivial"};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__0 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__0_value;
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 43, 154, 34, 2, 43, 185, 79)}};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__1 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__1_value;
static const lean_string_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__2 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__2_value;
static const lean_string_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__3 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__3_value;
static const lean_string_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__4 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__4_value;
static const lean_string_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "first"};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__5 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__5_value;
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__6_value_aux_0),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__6_value_aux_1),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__6_value_aux_2),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(59, 232, 35, 17, 172, 62, 48, 174)}};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__6 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__6_value;
static const lean_string_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__7 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__7_value;
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__8 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__8_value;
static const lean_string_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__9 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__9_value;
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__10 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__10_value;
static const lean_string_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__11 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__11_value;
static const lean_string_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__12 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__12_value;
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__13_value_aux_0),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__13_value_aux_1),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__13_value_aux_2),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__13 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__13_value;
static const lean_string_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__14 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__14_value;
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__15_value_aux_0),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__15_value_aux_1),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__15_value_aux_2),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__15 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__15_value;
static const lean_string_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__16 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__16_value;
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__17_value_aux_0),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__17_value_aux_1),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__17_value_aux_2),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__17 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__17_value;
static const lean_string_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__18 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__18_value;
static const lean_string_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__19 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__19_value;
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__20_value_aux_0),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__20_value_aux_1),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__20_value_aux_2),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__20 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__20_value;
static const lean_string_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "IterM.TerminationMeasures.Finite.rel_of_yield"};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__21 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__21_value;
static lean_once_cell_t l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__22;
static const lean_string_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "IterM"};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__23 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__23_value;
static const lean_string_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "TerminationMeasures"};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__24 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__24_value;
static const lean_string_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Finite"};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__25 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__25_value;
static const lean_string_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "rel_of_yield"};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__26 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__26_value;
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 31, 42, 181, 146, 49, 27)}};
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__27_value_aux_0),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__24_value),LEAN_SCALAR_PTR_LITERAL(169, 212, 213, 21, 142, 220, 208, 72)}};
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__27_value_aux_1),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__25_value),LEAN_SCALAR_PTR_LITERAL(205, 37, 172, 63, 217, 200, 178, 240)}};
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__27_value_aux_2),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__26_value),LEAN_SCALAR_PTR_LITERAL(126, 55, 159, 75, 203, 87, 117, 27)}};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__27 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__27_value;
static const lean_string_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__28 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__28_value;
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__28_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__29_value_aux_0),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(69, 82, 221, 140, 231, 242, 162, 189)}};
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__29_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__29_value_aux_1),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__24_value),LEAN_SCALAR_PTR_LITERAL(170, 200, 225, 233, 145, 226, 104, 82)}};
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__29_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__29_value_aux_2),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__25_value),LEAN_SCALAR_PTR_LITERAL(98, 99, 128, 7, 156, 143, 187, 45)}};
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__29_value_aux_3),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__26_value),LEAN_SCALAR_PTR_LITERAL(93, 51, 4, 58, 111, 99, 16, 1)}};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__29 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__29_value;
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__29_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__30 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__30_value;
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__30_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__31 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__31_value;
static const lean_string_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 7, .m_data = "term‹_›"};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__32 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__32_value;
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__32_value),LEAN_SCALAR_PTR_LITERAL(149, 139, 117, 210, 91, 226, 103, 115)}};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__33 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__33_value;
static const lean_string_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "‹"};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__34 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__34_value;
static const lean_string_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__35 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__35_value;
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__36_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__36_value_aux_0),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__36_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__36_value_aux_1),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__36_value_aux_2),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__35_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__36 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__36_value;
static const lean_string_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__37 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__37_value;
static const lean_string_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "›"};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__38 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__38_value;
static const lean_string_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "IterM.TerminationMeasures.Finite.rel_of_skip"};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__39 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__39_value;
static lean_once_cell_t l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__40;
static const lean_string_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "rel_of_skip"};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__41 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__41_value;
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__42_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 31, 42, 181, 146, 49, 27)}};
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__42_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__42_value_aux_0),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__24_value),LEAN_SCALAR_PTR_LITERAL(169, 212, 213, 21, 142, 220, 208, 72)}};
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__42_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__42_value_aux_1),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__25_value),LEAN_SCALAR_PTR_LITERAL(205, 37, 172, 63, 217, 200, 178, 240)}};
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__42_value_aux_2),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__41_value),LEAN_SCALAR_PTR_LITERAL(108, 19, 226, 143, 248, 98, 32, 233)}};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__42 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__42_value;
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__43_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__28_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__43_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__43_value_aux_0),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(69, 82, 221, 140, 231, 242, 162, 189)}};
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__43_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__43_value_aux_1),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__24_value),LEAN_SCALAR_PTR_LITERAL(170, 200, 225, 233, 145, 226, 104, 82)}};
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__43_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__43_value_aux_2),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__25_value),LEAN_SCALAR_PTR_LITERAL(98, 99, 128, 7, 156, 143, 187, 45)}};
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__43_value_aux_3),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__41_value),LEAN_SCALAR_PTR_LITERAL(15, 202, 24, 228, 40, 65, 103, 247)}};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__43 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__43_value;
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__43_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__44 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__44_value;
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__44_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__45 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__45_value;
static const lean_string_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "fail"};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__46 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__46_value;
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__47_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__47_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__47_value_aux_0),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__47_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__47_value_aux_1),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__47_value_aux_2),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__46_value),LEAN_SCALAR_PTR_LITERAL(251, 214, 242, 89, 226, 36, 213, 0)}};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__47 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__47_value;
static lean_once_cell_t l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48;
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySteps___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySteps___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySteps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySteps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySteps_x21___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySteps_x21___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySteps_x21(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySteps_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "Iter.TerminationMeasures.Finite.rel_of_yield"};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__0 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__0_value;
static lean_once_cell_t l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__1;
static const lean_string_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Iter"};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__2 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__2_value;
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(138, 195, 175, 148, 133, 100, 210, 224)}};
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__3_value_aux_0),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__24_value),LEAN_SCALAR_PTR_LITERAL(209, 7, 69, 112, 75, 84, 239, 144)}};
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__3_value_aux_1),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__25_value),LEAN_SCALAR_PTR_LITERAL(53, 50, 228, 112, 51, 164, 185, 156)}};
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__3_value_aux_2),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__26_value),LEAN_SCALAR_PTR_LITERAL(214, 230, 106, 38, 154, 8, 149, 198)}};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__3 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__3_value;
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__28_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__4_value_aux_0),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(29, 14, 70, 175, 60, 94, 26, 143)}};
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__4_value_aux_1),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__24_value),LEAN_SCALAR_PTR_LITERAL(226, 7, 252, 244, 215, 138, 67, 225)}};
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__4_value_aux_2),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__25_value),LEAN_SCALAR_PTR_LITERAL(122, 130, 58, 69, 124, 110, 42, 29)}};
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__4_value_aux_3),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__26_value),LEAN_SCALAR_PTR_LITERAL(5, 117, 145, 184, 128, 111, 59, 2)}};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__4 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__4_value;
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__5 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__5_value;
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__6 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__6_value;
static const lean_string_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "Iter.TerminationMeasures.Finite.rel_of_skip"};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__7 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__7_value;
static lean_once_cell_t l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__8;
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(138, 195, 175, 148, 133, 100, 210, 224)}};
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__9_value_aux_0),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__24_value),LEAN_SCALAR_PTR_LITERAL(209, 7, 69, 112, 75, 84, 239, 144)}};
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__9_value_aux_1),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__25_value),LEAN_SCALAR_PTR_LITERAL(53, 50, 228, 112, 51, 164, 185, 156)}};
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__9_value_aux_2),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__41_value),LEAN_SCALAR_PTR_LITERAL(148, 164, 186, 206, 160, 29, 175, 51)}};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__9 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__9_value;
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__28_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__10_value_aux_0),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(29, 14, 70, 175, 60, 94, 26, 143)}};
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__10_value_aux_1),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__24_value),LEAN_SCALAR_PTR_LITERAL(226, 7, 252, 244, 215, 138, 67, 225)}};
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__10_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__10_value_aux_2),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__25_value),LEAN_SCALAR_PTR_LITERAL(122, 130, 58, 69, 124, 110, 42, 29)}};
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__10_value_aux_3),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__41_value),LEAN_SCALAR_PTR_LITERAL(103, 50, 45, 116, 59, 32, 142, 2)}};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__10 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__10_value;
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__11 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__11_value;
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__12 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__12_value;
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_TerminationMeasures_instWellFoundedRelationProductive___redArg();
LEAN_EXPORT lean_object* l_Std_IterM_TerminationMeasures_instWellFoundedRelationProductive___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_TerminationMeasures_instWellFoundedRelationProductive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_TerminationMeasures_instWellFoundedRelationProductive___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySkips___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySkips___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySkips(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySkips___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySkips_x21___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySkips_x21___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySkips_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySkips_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "IterM.TerminationMeasures.Productive.rel_of_skip"};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__0 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__0_value;
static lean_once_cell_t l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__1;
static const lean_string_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Productive"};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__2 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__2_value;
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 31, 42, 181, 146, 49, 27)}};
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__3_value_aux_0),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__24_value),LEAN_SCALAR_PTR_LITERAL(169, 212, 213, 21, 142, 220, 208, 72)}};
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__3_value_aux_1),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(114, 129, 8, 70, 246, 73, 95, 178)}};
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__3_value_aux_2),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__41_value),LEAN_SCALAR_PTR_LITERAL(191, 122, 13, 102, 162, 164, 25, 53)}};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__3 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__3_value;
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__28_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__4_value_aux_0),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(69, 82, 221, 140, 231, 242, 162, 189)}};
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__4_value_aux_1),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__24_value),LEAN_SCALAR_PTR_LITERAL(170, 200, 225, 233, 145, 226, 104, 82)}};
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__4_value_aux_2),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(221, 67, 244, 104, 78, 160, 99, 150)}};
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__4_value_aux_3),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__41_value),LEAN_SCALAR_PTR_LITERAL(28, 196, 150, 210, 70, 45, 96, 36)}};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__4 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__4_value;
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__5 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__5_value;
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__6 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__6_value;
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySkips___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySkips___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySkips(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySkips___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySkips_x21___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySkips_x21___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySkips_x21(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySkips_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "Iter.TerminationMeasures.Productive.rel_of_skip"};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__0 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__0_value;
static lean_once_cell_t l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__1;
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(138, 195, 175, 148, 133, 100, 210, 224)}};
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__2_value_aux_0),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__24_value),LEAN_SCALAR_PTR_LITERAL(209, 7, 69, 112, 75, 84, 239, 144)}};
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__2_value_aux_1),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(186, 177, 73, 53, 115, 214, 252, 103)}};
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__2_value_aux_2),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__41_value),LEAN_SCALAR_PTR_LITERAL(39, 231, 130, 158, 254, 127, 122, 104)}};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__2 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__2_value;
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__28_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__3_value_aux_0),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(29, 14, 70, 175, 60, 94, 26, 143)}};
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__3_value_aux_1),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__24_value),LEAN_SCALAR_PTR_LITERAL(226, 7, 252, 244, 215, 138, 67, 225)}};
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__3_value_aux_2),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(117, 97, 217, 86, 100, 8, 28, 170)}};
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__3_value_aux_3),((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__41_value),LEAN_SCALAR_PTR_LITERAL(84, 68, 82, 65, 70, 30, 218, 209)}};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__3 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__3_value;
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__4 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__4_value;
static const lean_ctor_object l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__5 = (const lean_object*)&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__5_value;
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Basic_0__Std_Internal_idOpaque___redArg___lam__0(lean_object* v___y_1_){
_start:
{
lean_inc(v___y_1_);
return v___y_1_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Basic_0__Std_Internal_idOpaque___redArg___lam__0___boxed(lean_object* v___y_2_){
_start:
{
lean_object* v_res_3_; 
v_res_3_ = l___private_Init_Data_Iterators_Basic_0__Std_Internal_idOpaque___redArg___lam__0(v___y_2_);
lean_dec(v___y_2_);
return v_res_3_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Basic_0__Std_Internal_idOpaque___redArg(){
_start:
{
lean_object* v___f_6_; 
v___f_6_ = ((lean_object*)(l___private_Init_Data_Iterators_Basic_0__Std_Internal_idOpaque___redArg___closed__0));
return v___f_6_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Basic_0__Std_Internal_idOpaque___redArg___boxed(lean_object* v___dummy_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l___private_Init_Data_Iterators_Basic_0__Std_Internal_idOpaque___redArg();
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Basic_0__Std_Internal_idOpaque(lean_object* v_00_u03b1_9_){
_start:
{
lean_object* v___f_10_; 
v___f_10_ = ((lean_object*)(l___private_Init_Data_Iterators_Basic_0__Std_Internal_idOpaque___redArg___closed__0));
return v___f_10_;
}
}
LEAN_EXPORT lean_object* l_Std_Shrink_deflate___redArg(lean_object* v_x_11_){
_start:
{
lean_inc(v_x_11_);
return v_x_11_;
}
}
LEAN_EXPORT lean_object* l_Std_Shrink_deflate___redArg___boxed(lean_object* v_x_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l_Std_Shrink_deflate___redArg(v_x_12_);
lean_dec(v_x_12_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l_Std_Shrink_deflate(lean_object* v_00_u03b1_14_, lean_object* v_x_15_){
_start:
{
lean_inc(v_x_15_);
return v_x_15_;
}
}
LEAN_EXPORT lean_object* l_Std_Shrink_deflate___boxed(lean_object* v_00_u03b1_16_, lean_object* v_x_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Std_Shrink_deflate(v_00_u03b1_16_, v_x_17_);
lean_dec(v_x_17_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Std_Shrink_inflate___redArg(lean_object* v_x_19_){
_start:
{
lean_inc(v_x_19_);
return v_x_19_;
}
}
LEAN_EXPORT lean_object* l_Std_Shrink_inflate___redArg___boxed(lean_object* v_x_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l_Std_Shrink_inflate___redArg(v_x_20_);
lean_dec(v_x_20_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Std_Shrink_inflate(lean_object* v_00_u03b1_22_, lean_object* v_x_23_){
_start:
{
lean_inc(v_x_23_);
return v_x_23_;
}
}
LEAN_EXPORT lean_object* l_Std_Shrink_inflate___boxed(lean_object* v_00_u03b1_24_, lean_object* v_x_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Std_Shrink_inflate(v_00_u03b1_24_, v_x_25_);
lean_dec(v_x_25_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toIterM___redArg(lean_object* v_it_27_){
_start:
{
lean_inc(v_it_27_);
return v_it_27_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toIterM___redArg___boxed(lean_object* v_it_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Std_Iter_toIterM___redArg(v_it_28_);
lean_dec(v_it_28_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toIterM(lean_object* v_00_u03b1_30_, lean_object* v_00_u03b2_31_, lean_object* v_it_32_){
_start:
{
lean_inc(v_it_32_);
return v_it_32_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toIterM___boxed(lean_object* v_00_u03b1_33_, lean_object* v_00_u03b2_34_, lean_object* v_it_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_Std_Iter_toIterM(v_00_u03b1_33_, v_00_u03b2_34_, v_it_35_);
lean_dec(v_it_35_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toIter___redArg(lean_object* v_it_37_){
_start:
{
lean_inc(v_it_37_);
return v_it_37_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toIter___redArg___boxed(lean_object* v_it_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_Std_IterM_toIter___redArg(v_it_38_);
lean_dec(v_it_38_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toIter(lean_object* v_00_u03b1_40_, lean_object* v_00_u03b2_41_, lean_object* v_it_42_){
_start:
{
lean_inc(v_it_42_);
return v_it_42_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toIter___boxed(lean_object* v_00_u03b1_43_, lean_object* v_00_u03b2_44_, lean_object* v_it_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Std_IterM_toIter(v_00_u03b1_43_, v_00_u03b2_44_, v_it_45_);
lean_dec(v_it_45_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_ctorIdx___impl___redArg(lean_object* v_x_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = lean_obj_tag_nat(v_x_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_ctorIdx___impl___redArg___boxed(lean_object* v_x_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Std_IterStep_ctorIdx___impl___redArg(v_x_49_);
lean_dec(v_x_49_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_ctorIdx___impl(lean_object* v_00_u03b1_51_, lean_object* v_00_u03b2_52_, lean_object* v_x_53_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = lean_obj_tag_nat(v_x_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_ctorIdx___impl___boxed(lean_object* v_00_u03b1_55_, lean_object* v_00_u03b2_56_, lean_object* v_x_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Std_IterStep_ctorIdx___impl(v_00_u03b1_55_, v_00_u03b2_56_, v_x_57_);
lean_dec(v_x_57_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_ctorElim___redArg(lean_object* v_t_59_, lean_object* v_k_60_){
_start:
{
switch(lean_obj_tag(v_t_59_))
{
case 0:
{
lean_object* v_it_61_; lean_object* v_out_62_; lean_object* v___x_63_; 
v_it_61_ = lean_ctor_get(v_t_59_, 0);
lean_inc(v_it_61_);
v_out_62_ = lean_ctor_get(v_t_59_, 1);
lean_inc(v_out_62_);
lean_dec_ref_known(v_t_59_, 2);
v___x_63_ = lean_apply_2(v_k_60_, v_it_61_, v_out_62_);
return v___x_63_;
}
case 1:
{
lean_object* v_it_64_; lean_object* v___x_65_; 
v_it_64_ = lean_ctor_get(v_t_59_, 0);
lean_inc(v_it_64_);
lean_dec_ref_known(v_t_59_, 1);
v___x_65_ = lean_apply_1(v_k_60_, v_it_64_);
return v___x_65_;
}
default: 
{
return v_k_60_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_ctorElim(lean_object* v_00_u03b1_66_, lean_object* v_00_u03b2_67_, lean_object* v_motive_68_, lean_object* v_ctorIdx_69_, lean_object* v_t_70_, lean_object* v_h_71_, lean_object* v_k_72_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = l_Std_IterStep_ctorElim___redArg(v_t_70_, v_k_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_ctorElim___boxed(lean_object* v_00_u03b1_74_, lean_object* v_00_u03b2_75_, lean_object* v_motive_76_, lean_object* v_ctorIdx_77_, lean_object* v_t_78_, lean_object* v_h_79_, lean_object* v_k_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_Std_IterStep_ctorElim(v_00_u03b1_74_, v_00_u03b2_75_, v_motive_76_, v_ctorIdx_77_, v_t_78_, v_h_79_, v_k_80_);
lean_dec(v_ctorIdx_77_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_yield_elim___redArg(lean_object* v_t_82_, lean_object* v_yield_83_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = l_Std_IterStep_ctorElim___redArg(v_t_82_, v_yield_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_yield_elim(lean_object* v_00_u03b1_85_, lean_object* v_00_u03b2_86_, lean_object* v_motive_87_, lean_object* v_t_88_, lean_object* v_h_89_, lean_object* v_yield_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = l_Std_IterStep_ctorElim___redArg(v_t_88_, v_yield_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_skip_elim___redArg(lean_object* v_t_92_, lean_object* v_skip_93_){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = l_Std_IterStep_ctorElim___redArg(v_t_92_, v_skip_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_skip_elim(lean_object* v_00_u03b1_95_, lean_object* v_00_u03b2_96_, lean_object* v_motive_97_, lean_object* v_t_98_, lean_object* v_h_99_, lean_object* v_skip_100_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = l_Std_IterStep_ctorElim___redArg(v_t_98_, v_skip_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_done_elim___redArg(lean_object* v_t_102_, lean_object* v_done_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = l_Std_IterStep_ctorElim___redArg(v_t_102_, v_done_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_done_elim(lean_object* v_00_u03b1_105_, lean_object* v_00_u03b2_106_, lean_object* v_motive_107_, lean_object* v_t_108_, lean_object* v_h_109_, lean_object* v_done_110_){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = l_Std_IterStep_ctorElim___redArg(v_t_108_, v_done_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_successor___redArg(lean_object* v_x_112_){
_start:
{
switch(lean_obj_tag(v_x_112_))
{
case 0:
{
lean_object* v_it_113_; lean_object* v___x_114_; 
v_it_113_ = lean_ctor_get(v_x_112_, 0);
lean_inc(v_it_113_);
lean_dec_ref_known(v_x_112_, 2);
v___x_114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_114_, 0, v_it_113_);
return v___x_114_;
}
case 1:
{
lean_object* v_it_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_122_; 
v_it_115_ = lean_ctor_get(v_x_112_, 0);
v_isSharedCheck_122_ = !lean_is_exclusive(v_x_112_);
if (v_isSharedCheck_122_ == 0)
{
v___x_117_ = v_x_112_;
v_isShared_118_ = v_isSharedCheck_122_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_it_115_);
lean_dec(v_x_112_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_122_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v___x_120_; 
if (v_isShared_118_ == 0)
{
v___x_120_ = v___x_117_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v_it_115_);
v___x_120_ = v_reuseFailAlloc_121_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
return v___x_120_;
}
}
}
default: 
{
lean_object* v___x_123_; 
v___x_123_ = lean_box(0);
return v___x_123_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_successor(lean_object* v_00_u03b1_124_, lean_object* v_00_u03b2_125_, lean_object* v_x_126_){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = l_Std_IterStep_successor___redArg(v_x_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_mapIterator___redArg(lean_object* v_f_128_, lean_object* v_x_129_){
_start:
{
switch(lean_obj_tag(v_x_129_))
{
case 0:
{
lean_object* v_it_130_; lean_object* v_out_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_139_; 
v_it_130_ = lean_ctor_get(v_x_129_, 0);
v_out_131_ = lean_ctor_get(v_x_129_, 1);
v_isSharedCheck_139_ = !lean_is_exclusive(v_x_129_);
if (v_isSharedCheck_139_ == 0)
{
v___x_133_ = v_x_129_;
v_isShared_134_ = v_isSharedCheck_139_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_out_131_);
lean_inc(v_it_130_);
lean_dec(v_x_129_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_139_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v___x_135_; lean_object* v___x_137_; 
v___x_135_ = lean_apply_1(v_f_128_, v_it_130_);
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 0, v___x_135_);
v___x_137_ = v___x_133_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v___x_135_);
lean_ctor_set(v_reuseFailAlloc_138_, 1, v_out_131_);
v___x_137_ = v_reuseFailAlloc_138_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
return v___x_137_;
}
}
}
case 1:
{
lean_object* v_it_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_148_; 
v_it_140_ = lean_ctor_get(v_x_129_, 0);
v_isSharedCheck_148_ = !lean_is_exclusive(v_x_129_);
if (v_isSharedCheck_148_ == 0)
{
v___x_142_ = v_x_129_;
v_isShared_143_ = v_isSharedCheck_148_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_it_140_);
lean_dec(v_x_129_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_148_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v___x_144_; lean_object* v___x_146_; 
v___x_144_ = lean_apply_1(v_f_128_, v_it_140_);
if (v_isShared_143_ == 0)
{
lean_ctor_set(v___x_142_, 0, v___x_144_);
v___x_146_ = v___x_142_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v___x_144_);
v___x_146_ = v_reuseFailAlloc_147_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
return v___x_146_;
}
}
}
default: 
{
lean_object* v___x_149_; 
lean_dec(v_f_128_);
v___x_149_ = lean_box(2);
return v___x_149_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_mapIterator(lean_object* v_00_u03b1_150_, lean_object* v_00_u03b2_151_, lean_object* v_00_u03b1_x27_152_, lean_object* v_f_153_, lean_object* v_x_154_){
_start:
{
switch(lean_obj_tag(v_x_154_))
{
case 0:
{
lean_object* v_it_155_; lean_object* v_out_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_164_; 
v_it_155_ = lean_ctor_get(v_x_154_, 0);
v_out_156_ = lean_ctor_get(v_x_154_, 1);
v_isSharedCheck_164_ = !lean_is_exclusive(v_x_154_);
if (v_isSharedCheck_164_ == 0)
{
v___x_158_ = v_x_154_;
v_isShared_159_ = v_isSharedCheck_164_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_out_156_);
lean_inc(v_it_155_);
lean_dec(v_x_154_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_164_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v___x_160_; lean_object* v___x_162_; 
v___x_160_ = lean_apply_1(v_f_153_, v_it_155_);
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 0, v___x_160_);
v___x_162_ = v___x_158_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v___x_160_);
lean_ctor_set(v_reuseFailAlloc_163_, 1, v_out_156_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
}
case 1:
{
lean_object* v_it_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_173_; 
v_it_165_ = lean_ctor_get(v_x_154_, 0);
v_isSharedCheck_173_ = !lean_is_exclusive(v_x_154_);
if (v_isSharedCheck_173_ == 0)
{
v___x_167_ = v_x_154_;
v_isShared_168_ = v_isSharedCheck_173_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_it_165_);
lean_dec(v_x_154_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_173_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v___x_169_; lean_object* v___x_171_; 
v___x_169_ = lean_apply_1(v_f_153_, v_it_165_);
if (v_isShared_168_ == 0)
{
lean_ctor_set(v___x_167_, 0, v___x_169_);
v___x_171_ = v___x_167_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v___x_169_);
v___x_171_ = v_reuseFailAlloc_172_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
return v___x_171_;
}
}
}
default: 
{
lean_object* v___x_174_; 
lean_dec(v_f_153_);
v___x_174_ = lean_box(2);
return v___x_174_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PlausibleIterStep_yield___redArg(lean_object* v_it_x27_175_, lean_object* v_out_176_){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_177_, 0, v_it_x27_175_);
lean_ctor_set(v___x_177_, 1, v_out_176_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Std_PlausibleIterStep_yield(lean_object* v_00_u03b1_178_, lean_object* v_00_u03b2_179_, lean_object* v_IsPlausibleStep_180_, lean_object* v_it_x27_181_, lean_object* v_out_182_, lean_object* v_h_183_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_184_, 0, v_it_x27_181_);
lean_ctor_set(v___x_184_, 1, v_out_182_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Std_PlausibleIterStep_skip___redArg(lean_object* v_it_x27_185_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_186_, 0, v_it_x27_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Std_PlausibleIterStep_skip(lean_object* v_00_u03b1_187_, lean_object* v_00_u03b2_188_, lean_object* v_IsPlausibleStep_189_, lean_object* v_it_x27_190_, lean_object* v_h_191_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_192_, 0, v_it_x27_190_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Std_PlausibleIterStep_done___redArg(){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = lean_box(2);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Std_PlausibleIterStep_done___redArg___boxed(lean_object* v___dummy_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l_Std_PlausibleIterStep_done___redArg();
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_Std_PlausibleIterStep_done(lean_object* v_00_u03b1_197_, lean_object* v_00_u03b2_198_, lean_object* v_IsPlausibleStep_199_, lean_object* v_h_200_){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = lean_box(2);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Std_PlausibleIterStep_casesOn___redArg(lean_object* v_s_202_, lean_object* v_yield_203_, lean_object* v_skip_204_, lean_object* v_done_205_){
_start:
{
switch(lean_obj_tag(v_s_202_))
{
case 0:
{
lean_object* v_it_206_; lean_object* v_out_207_; lean_object* v___x_208_; 
lean_dec(v_done_205_);
lean_dec(v_skip_204_);
v_it_206_ = lean_ctor_get(v_s_202_, 0);
lean_inc(v_it_206_);
v_out_207_ = lean_ctor_get(v_s_202_, 1);
lean_inc(v_out_207_);
lean_dec_ref_known(v_s_202_, 2);
v___x_208_ = lean_apply_3(v_yield_203_, v_it_206_, v_out_207_, lean_box(0));
return v___x_208_;
}
case 1:
{
lean_object* v_it_209_; lean_object* v___x_210_; 
lean_dec(v_done_205_);
lean_dec(v_yield_203_);
v_it_209_ = lean_ctor_get(v_s_202_, 0);
lean_inc(v_it_209_);
lean_dec_ref_known(v_s_202_, 1);
v___x_210_ = lean_apply_2(v_skip_204_, v_it_209_, lean_box(0));
return v___x_210_;
}
default: 
{
lean_object* v___x_211_; 
lean_dec(v_skip_204_);
lean_dec(v_yield_203_);
v___x_211_ = lean_apply_1(v_done_205_, lean_box(0));
return v___x_211_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PlausibleIterStep_casesOn(lean_object* v_00_u03b1_212_, lean_object* v_00_u03b2_213_, lean_object* v_IsPlausibleStep_214_, lean_object* v_motive_215_, lean_object* v_s_216_, lean_object* v_yield_217_, lean_object* v_skip_218_, lean_object* v_done_219_){
_start:
{
switch(lean_obj_tag(v_s_216_))
{
case 0:
{
lean_object* v_it_220_; lean_object* v_out_221_; lean_object* v___x_222_; 
lean_dec(v_done_219_);
lean_dec(v_skip_218_);
v_it_220_ = lean_ctor_get(v_s_216_, 0);
lean_inc(v_it_220_);
v_out_221_ = lean_ctor_get(v_s_216_, 1);
lean_inc(v_out_221_);
lean_dec_ref_known(v_s_216_, 2);
v___x_222_ = lean_apply_3(v_yield_217_, v_it_220_, v_out_221_, lean_box(0));
return v___x_222_;
}
case 1:
{
lean_object* v_it_223_; lean_object* v___x_224_; 
lean_dec(v_done_219_);
lean_dec(v_yield_217_);
v_it_223_ = lean_ctor_get(v_s_216_, 0);
lean_inc(v_it_223_);
lean_dec_ref_known(v_s_216_, 1);
v___x_224_ = lean_apply_2(v_skip_218_, v_it_223_, lean_box(0));
return v___x_224_;
}
default: 
{
lean_object* v___x_225_; 
lean_dec(v_skip_218_);
lean_dec(v_yield_217_);
v___x_225_ = lean_apply_1(v_done_219_, lean_box(0));
return v___x_225_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_IterM_mk_x27___redArg(lean_object* v_it_226_){
_start:
{
lean_inc(v_it_226_);
return v_it_226_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_mk_x27___redArg___boxed(lean_object* v_it_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Std_IterM_mk_x27___redArg(v_it_227_);
lean_dec(v_it_227_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_mk_x27(lean_object* v_00_u03b1_229_, lean_object* v_m_230_, lean_object* v_00_u03b2_231_, lean_object* v_it_232_){
_start:
{
lean_inc(v_it_232_);
return v_it_232_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_mk_x27___boxed(lean_object* v_00_u03b1_233_, lean_object* v_m_234_, lean_object* v_00_u03b2_235_, lean_object* v_it_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_Std_IterM_mk_x27(v_00_u03b1_233_, v_m_234_, v_00_u03b2_235_, v_it_236_);
lean_dec(v_it_236_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_toIterM___redArg(lean_object* v_internalState_238_){
_start:
{
lean_inc(v_internalState_238_);
return v_internalState_238_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_toIterM___redArg___boxed(lean_object* v_internalState_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Std_Iterators_toIterM___redArg(v_internalState_239_);
lean_dec(v_internalState_239_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_toIterM(lean_object* v_00_u03b1_241_, lean_object* v_m_242_, lean_object* v_00_u03b2_243_, lean_object* v_internalState_244_){
_start:
{
lean_inc(v_internalState_244_);
return v_internalState_244_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_toIterM___boxed(lean_object* v_00_u03b1_245_, lean_object* v_m_246_, lean_object* v_00_u03b2_247_, lean_object* v_internalState_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l_Std_Iterators_toIterM(v_00_u03b1_245_, v_m_246_, v_00_u03b2_247_, v_internalState_248_);
lean_dec(v_internalState_248_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_step___redArg(lean_object* v_inst_250_, lean_object* v_it_251_){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = lean_apply_1(v_inst_250_, v_it_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_step(lean_object* v_00_u03b1_253_, lean_object* v_m_254_, lean_object* v_00_u03b2_255_, lean_object* v_inst_256_, lean_object* v_it_257_){
_start:
{
lean_object* v___x_258_; 
v___x_258_ = lean_apply_1(v_inst_256_, v_it_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Step_toMonadic___redArg(lean_object* v_step_259_){
_start:
{
switch(lean_obj_tag(v_step_259_))
{
case 0:
{
lean_object* v_it_260_; lean_object* v_out_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_268_; 
v_it_260_ = lean_ctor_get(v_step_259_, 0);
v_out_261_ = lean_ctor_get(v_step_259_, 1);
v_isSharedCheck_268_ = !lean_is_exclusive(v_step_259_);
if (v_isSharedCheck_268_ == 0)
{
v___x_263_ = v_step_259_;
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_out_261_);
lean_inc(v_it_260_);
lean_dec(v_step_259_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_266_; 
if (v_isShared_264_ == 0)
{
v___x_266_ = v___x_263_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v_it_260_);
lean_ctor_set(v_reuseFailAlloc_267_, 1, v_out_261_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
}
case 1:
{
lean_object* v_it_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_276_; 
v_it_269_ = lean_ctor_get(v_step_259_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v_step_259_);
if (v_isSharedCheck_276_ == 0)
{
v___x_271_ = v_step_259_;
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_it_269_);
lean_dec(v_step_259_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_274_; 
if (v_isShared_272_ == 0)
{
v___x_274_ = v___x_271_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_it_269_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
default: 
{
lean_object* v___x_277_; 
v___x_277_ = lean_box(2);
return v___x_277_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Step_toMonadic(lean_object* v_00_u03b1_278_, lean_object* v_00_u03b2_279_, lean_object* v_inst_280_, lean_object* v_it_281_, lean_object* v_step_282_){
_start:
{
switch(lean_obj_tag(v_step_282_))
{
case 0:
{
lean_object* v_it_283_; lean_object* v_out_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_291_; 
v_it_283_ = lean_ctor_get(v_step_282_, 0);
v_out_284_ = lean_ctor_get(v_step_282_, 1);
v_isSharedCheck_291_ = !lean_is_exclusive(v_step_282_);
if (v_isSharedCheck_291_ == 0)
{
v___x_286_ = v_step_282_;
v_isShared_287_ = v_isSharedCheck_291_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_out_284_);
lean_inc(v_it_283_);
lean_dec(v_step_282_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_291_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v___x_289_; 
if (v_isShared_287_ == 0)
{
v___x_289_ = v___x_286_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_it_283_);
lean_ctor_set(v_reuseFailAlloc_290_, 1, v_out_284_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
return v___x_289_;
}
}
}
case 1:
{
lean_object* v_it_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_299_; 
v_it_292_ = lean_ctor_get(v_step_282_, 0);
v_isSharedCheck_299_ = !lean_is_exclusive(v_step_282_);
if (v_isSharedCheck_299_ == 0)
{
v___x_294_ = v_step_282_;
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_it_292_);
lean_dec(v_step_282_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_297_; 
if (v_isShared_295_ == 0)
{
v___x_297_ = v___x_294_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_it_292_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
}
default: 
{
lean_object* v___x_300_; 
v___x_300_ = lean_box(2);
return v___x_300_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Step_toMonadic___boxed(lean_object* v_00_u03b1_301_, lean_object* v_00_u03b2_302_, lean_object* v_inst_303_, lean_object* v_it_304_, lean_object* v_step_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Std_Iter_Step_toMonadic(v_00_u03b1_301_, v_00_u03b2_302_, v_inst_303_, v_it_304_, v_step_305_);
lean_dec(v_it_304_);
lean_dec(v_inst_303_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Step_toPure___redArg(lean_object* v_step_307_){
_start:
{
switch(lean_obj_tag(v_step_307_))
{
case 0:
{
lean_object* v_it_308_; lean_object* v_out_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_316_; 
v_it_308_ = lean_ctor_get(v_step_307_, 0);
v_out_309_ = lean_ctor_get(v_step_307_, 1);
v_isSharedCheck_316_ = !lean_is_exclusive(v_step_307_);
if (v_isSharedCheck_316_ == 0)
{
v___x_311_ = v_step_307_;
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_out_309_);
lean_inc(v_it_308_);
lean_dec(v_step_307_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_314_; 
if (v_isShared_312_ == 0)
{
v___x_314_ = v___x_311_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_it_308_);
lean_ctor_set(v_reuseFailAlloc_315_, 1, v_out_309_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
}
case 1:
{
lean_object* v_it_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_324_; 
v_it_317_ = lean_ctor_get(v_step_307_, 0);
v_isSharedCheck_324_ = !lean_is_exclusive(v_step_307_);
if (v_isSharedCheck_324_ == 0)
{
v___x_319_ = v_step_307_;
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_it_317_);
lean_dec(v_step_307_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_322_; 
if (v_isShared_320_ == 0)
{
v___x_322_ = v___x_319_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_it_317_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
}
default: 
{
lean_object* v___x_325_; 
v___x_325_ = lean_box(2);
return v___x_325_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Step_toPure(lean_object* v_00_u03b1_326_, lean_object* v_00_u03b2_327_, lean_object* v_inst_328_, lean_object* v_it_329_, lean_object* v_step_330_){
_start:
{
switch(lean_obj_tag(v_step_330_))
{
case 0:
{
lean_object* v_it_331_; lean_object* v_out_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_339_; 
v_it_331_ = lean_ctor_get(v_step_330_, 0);
v_out_332_ = lean_ctor_get(v_step_330_, 1);
v_isSharedCheck_339_ = !lean_is_exclusive(v_step_330_);
if (v_isSharedCheck_339_ == 0)
{
v___x_334_ = v_step_330_;
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_out_332_);
lean_inc(v_it_331_);
lean_dec(v_step_330_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_337_; 
if (v_isShared_335_ == 0)
{
v___x_337_ = v___x_334_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_it_331_);
lean_ctor_set(v_reuseFailAlloc_338_, 1, v_out_332_);
v___x_337_ = v_reuseFailAlloc_338_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
return v___x_337_;
}
}
}
case 1:
{
lean_object* v_it_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_347_; 
v_it_340_ = lean_ctor_get(v_step_330_, 0);
v_isSharedCheck_347_ = !lean_is_exclusive(v_step_330_);
if (v_isSharedCheck_347_ == 0)
{
v___x_342_ = v_step_330_;
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_it_340_);
lean_dec(v_step_330_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_345_; 
if (v_isShared_343_ == 0)
{
v___x_345_ = v___x_342_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v_it_340_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
default: 
{
lean_object* v___x_348_; 
v___x_348_ = lean_box(2);
return v___x_348_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Step_toPure___boxed(lean_object* v_00_u03b1_349_, lean_object* v_00_u03b2_350_, lean_object* v_inst_351_, lean_object* v_it_352_, lean_object* v_step_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_Std_IterM_Step_toPure(v_00_u03b1_349_, v_00_u03b2_350_, v_inst_351_, v_it_352_, v_step_353_);
lean_dec(v_it_352_);
lean_dec(v_inst_351_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_step___redArg(lean_object* v_inst_355_, lean_object* v_it_356_){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = lean_apply_1(v_inst_355_, v_it_356_);
switch(lean_obj_tag(v___x_357_))
{
case 0:
{
lean_object* v_it_358_; lean_object* v_out_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_366_; 
v_it_358_ = lean_ctor_get(v___x_357_, 0);
v_out_359_ = lean_ctor_get(v___x_357_, 1);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_366_ == 0)
{
v___x_361_ = v___x_357_;
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_out_359_);
lean_inc(v_it_358_);
lean_dec(v___x_357_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_364_; 
if (v_isShared_362_ == 0)
{
v___x_364_ = v___x_361_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_it_358_);
lean_ctor_set(v_reuseFailAlloc_365_, 1, v_out_359_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
case 1:
{
lean_object* v_it_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_374_; 
v_it_367_ = lean_ctor_get(v___x_357_, 0);
v_isSharedCheck_374_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_374_ == 0)
{
v___x_369_ = v___x_357_;
v_isShared_370_ = v_isSharedCheck_374_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_it_367_);
lean_dec(v___x_357_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_374_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_372_; 
if (v_isShared_370_ == 0)
{
v___x_372_ = v___x_369_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_it_367_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
}
default: 
{
lean_object* v___x_375_; 
v___x_375_ = lean_box(2);
return v___x_375_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iter_step(lean_object* v_00_u03b1_376_, lean_object* v_00_u03b2_377_, lean_object* v_inst_378_, lean_object* v_it_379_){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = lean_apply_1(v_inst_378_, v_it_379_);
switch(lean_obj_tag(v___x_380_))
{
case 0:
{
lean_object* v_it_381_; lean_object* v_out_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_389_; 
v_it_381_ = lean_ctor_get(v___x_380_, 0);
v_out_382_ = lean_ctor_get(v___x_380_, 1);
v_isSharedCheck_389_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_389_ == 0)
{
v___x_384_ = v___x_380_;
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_out_382_);
lean_inc(v_it_381_);
lean_dec(v___x_380_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_387_; 
if (v_isShared_385_ == 0)
{
v___x_387_ = v___x_384_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_it_381_);
lean_ctor_set(v_reuseFailAlloc_388_, 1, v_out_382_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
}
case 1:
{
lean_object* v_it_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_397_; 
v_it_390_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_397_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_397_ == 0)
{
v___x_392_ = v___x_380_;
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_it_390_);
lean_dec(v___x_380_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___x_395_; 
if (v_isShared_393_ == 0)
{
v___x_395_ = v___x_392_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_it_390_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
}
default: 
{
lean_object* v___x_398_; 
v___x_398_ = lean_box(2);
return v___x_398_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_IterM_TerminationMeasures_instWellFoundedRelationFinite___redArg(){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = lean_box(0);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_TerminationMeasures_instWellFoundedRelationFinite___redArg___boxed(lean_object* v___dummy_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l_Std_IterM_TerminationMeasures_instWellFoundedRelationFinite___redArg();
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_TerminationMeasures_instWellFoundedRelationFinite(lean_object* v_00_u03b1_403_, lean_object* v_m_404_, lean_object* v_00_u03b2_405_, lean_object* v_inst_406_, lean_object* v_inst_407_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = lean_box(0);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_TerminationMeasures_instWellFoundedRelationFinite___boxed(lean_object* v_00_u03b1_409_, lean_object* v_m_410_, lean_object* v_00_u03b2_411_, lean_object* v_inst_412_, lean_object* v_inst_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Std_IterM_TerminationMeasures_instWellFoundedRelationFinite(v_00_u03b1_409_, v_m_410_, v_00_u03b2_411_, v_inst_412_, v_inst_413_);
lean_dec(v_inst_412_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySteps___redArg(lean_object* v_it_415_){
_start:
{
lean_inc(v_it_415_);
return v_it_415_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySteps___redArg___boxed(lean_object* v_it_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Std_IterM_finitelyManySteps___redArg(v_it_416_);
lean_dec(v_it_416_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySteps(lean_object* v_00_u03b1_418_, lean_object* v_m_419_, lean_object* v_00_u03b2_420_, lean_object* v_inst_421_, lean_object* v_inst_422_, lean_object* v_it_423_){
_start:
{
lean_inc(v_it_423_);
return v_it_423_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySteps___boxed(lean_object* v_00_u03b1_424_, lean_object* v_m_425_, lean_object* v_00_u03b2_426_, lean_object* v_inst_427_, lean_object* v_inst_428_, lean_object* v_it_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_Std_IterM_finitelyManySteps(v_00_u03b1_424_, v_m_425_, v_00_u03b2_426_, v_inst_427_, v_inst_428_, v_it_429_);
lean_dec(v_it_429_);
lean_dec(v_inst_427_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySteps_x21___redArg(lean_object* v_it_431_){
_start:
{
lean_inc(v_it_431_);
return v_it_431_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySteps_x21___redArg___boxed(lean_object* v_it_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Std_IterM_finitelyManySteps_x21___redArg(v_it_432_);
lean_dec(v_it_432_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySteps_x21(lean_object* v_00_u03b1_434_, lean_object* v_m_435_, lean_object* v_00_u03b2_436_, lean_object* v_inst_437_, lean_object* v_it_438_){
_start:
{
lean_inc(v_it_438_);
return v_it_438_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySteps_x21___boxed(lean_object* v_00_u03b1_439_, lean_object* v_m_440_, lean_object* v_00_u03b2_441_, lean_object* v_inst_442_, lean_object* v_it_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Std_IterM_finitelyManySteps_x21(v_00_u03b1_439_, v_m_440_, v_00_u03b2_441_, v_inst_442_, v_it_443_);
lean_dec(v_it_443_);
lean_dec(v_inst_442_);
return v_res_444_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__22(void){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_490_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__21));
v___x_491_ = l_String_toRawSubstring_x27(v___x_490_);
return v___x_491_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__40(void){
_start:
{
lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_527_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__39));
v___x_528_ = l_String_toRawSubstring_x27(v___x_527_);
return v___x_528_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48(void){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l_Array_mkArray0___redArg();
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1(lean_object* v_x_554_, lean_object* v_a_555_, lean_object* v_a_556_){
_start:
{
lean_object* v___x_557_; uint8_t v___x_558_; 
v___x_557_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__1));
v___x_558_ = l_Lean_Syntax_isOfKind(v_x_554_, v___x_557_);
if (v___x_558_ == 0)
{
lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_559_ = lean_box(1);
v___x_560_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_560_, 0, v___x_559_);
lean_ctor_set(v___x_560_, 1, v_a_556_);
return v___x_560_;
}
else
{
lean_object* v_quotContext_561_; lean_object* v_currMacroScope_562_; lean_object* v_ref_563_; uint8_t v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v_quotContext_561_ = lean_ctor_get(v_a_555_, 1);
v_currMacroScope_562_ = lean_ctor_get(v_a_555_, 2);
v_ref_563_ = lean_ctor_get(v_a_555_, 5);
v___x_564_ = 0;
v___x_565_ = l_Lean_SourceInfo_fromRef(v_ref_563_, v___x_564_);
v___x_566_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__5));
v___x_567_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__6));
lean_inc_n(v___x_565_, 31);
v___x_568_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_568_, 0, v___x_565_);
lean_ctor_set(v___x_568_, 1, v___x_566_);
v___x_569_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__8));
v___x_570_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__10));
v___x_571_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__11));
v___x_572_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_572_, 0, v___x_565_);
lean_ctor_set(v___x_572_, 1, v___x_571_);
v___x_573_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__13));
v___x_574_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__15));
v___x_575_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__16));
v___x_576_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__17));
v___x_577_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_565_);
lean_ctor_set(v___x_577_, 1, v___x_575_);
v___x_578_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__20));
v___x_579_ = lean_obj_once(&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__22, &l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__22_once, _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__22);
v___x_580_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__27));
lean_inc_n(v_currMacroScope_562_, 2);
lean_inc_n(v_quotContext_561_, 2);
v___x_581_ = l_Lean_addMacroScope(v_quotContext_561_, v___x_580_, v_currMacroScope_562_);
v___x_582_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__31));
v___x_583_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_583_, 0, v___x_565_);
lean_ctor_set(v___x_583_, 1, v___x_579_);
lean_ctor_set(v___x_583_, 2, v___x_581_);
lean_ctor_set(v___x_583_, 3, v___x_582_);
v___x_584_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__33));
v___x_585_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__34));
v___x_586_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_586_, 0, v___x_565_);
lean_ctor_set(v___x_586_, 1, v___x_585_);
v___x_587_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__36));
v___x_588_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__37));
v___x_589_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_589_, 0, v___x_565_);
lean_ctor_set(v___x_589_, 1, v___x_588_);
v___x_590_ = l_Lean_Syntax_node1(v___x_565_, v___x_587_, v___x_589_);
v___x_591_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__38));
v___x_592_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_592_, 0, v___x_565_);
lean_ctor_set(v___x_592_, 1, v___x_591_);
v___x_593_ = l_Lean_Syntax_node3(v___x_565_, v___x_584_, v___x_586_, v___x_590_, v___x_592_);
v___x_594_ = l_Lean_Syntax_node1(v___x_565_, v___x_569_, v___x_593_);
lean_inc(v___x_594_);
v___x_595_ = l_Lean_Syntax_node2(v___x_565_, v___x_578_, v___x_583_, v___x_594_);
lean_inc_ref(v___x_577_);
v___x_596_ = l_Lean_Syntax_node2(v___x_565_, v___x_576_, v___x_577_, v___x_595_);
v___x_597_ = l_Lean_Syntax_node1(v___x_565_, v___x_569_, v___x_596_);
v___x_598_ = l_Lean_Syntax_node1(v___x_565_, v___x_574_, v___x_597_);
v___x_599_ = l_Lean_Syntax_node1(v___x_565_, v___x_573_, v___x_598_);
lean_inc_ref_n(v___x_572_, 2);
v___x_600_ = l_Lean_Syntax_node2(v___x_565_, v___x_570_, v___x_572_, v___x_599_);
v___x_601_ = lean_obj_once(&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__40, &l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__40_once, _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__40);
v___x_602_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__42));
v___x_603_ = l_Lean_addMacroScope(v_quotContext_561_, v___x_602_, v_currMacroScope_562_);
v___x_604_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__45));
v___x_605_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_605_, 0, v___x_565_);
lean_ctor_set(v___x_605_, 1, v___x_601_);
lean_ctor_set(v___x_605_, 2, v___x_603_);
lean_ctor_set(v___x_605_, 3, v___x_604_);
v___x_606_ = l_Lean_Syntax_node2(v___x_565_, v___x_578_, v___x_605_, v___x_594_);
v___x_607_ = l_Lean_Syntax_node2(v___x_565_, v___x_576_, v___x_577_, v___x_606_);
v___x_608_ = l_Lean_Syntax_node1(v___x_565_, v___x_569_, v___x_607_);
v___x_609_ = l_Lean_Syntax_node1(v___x_565_, v___x_574_, v___x_608_);
v___x_610_ = l_Lean_Syntax_node1(v___x_565_, v___x_573_, v___x_609_);
v___x_611_ = l_Lean_Syntax_node2(v___x_565_, v___x_570_, v___x_572_, v___x_610_);
v___x_612_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__46));
v___x_613_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__47));
v___x_614_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_614_, 0, v___x_565_);
lean_ctor_set(v___x_614_, 1, v___x_612_);
v___x_615_ = lean_obj_once(&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48, &l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48_once, _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48);
v___x_616_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_616_, 0, v___x_565_);
lean_ctor_set(v___x_616_, 1, v___x_569_);
lean_ctor_set(v___x_616_, 2, v___x_615_);
v___x_617_ = l_Lean_Syntax_node2(v___x_565_, v___x_613_, v___x_614_, v___x_616_);
v___x_618_ = l_Lean_Syntax_node1(v___x_565_, v___x_569_, v___x_617_);
v___x_619_ = l_Lean_Syntax_node1(v___x_565_, v___x_574_, v___x_618_);
v___x_620_ = l_Lean_Syntax_node1(v___x_565_, v___x_573_, v___x_619_);
v___x_621_ = l_Lean_Syntax_node2(v___x_565_, v___x_570_, v___x_572_, v___x_620_);
v___x_622_ = l_Lean_Syntax_node3(v___x_565_, v___x_569_, v___x_600_, v___x_611_, v___x_621_);
v___x_623_ = l_Lean_Syntax_node2(v___x_565_, v___x_567_, v___x_568_, v___x_622_);
v___x_624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_624_, 0, v___x_623_);
lean_ctor_set(v___x_624_, 1, v_a_556_);
return v___x_624_;
}
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___boxed(lean_object* v_x_625_, lean_object* v_a_626_, lean_object* v_a_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1(v_x_625_, v_a_626_, v_a_627_);
lean_dec_ref(v_a_626_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySteps___redArg(lean_object* v_it_629_){
_start:
{
lean_inc(v_it_629_);
return v_it_629_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySteps___redArg___boxed(lean_object* v_it_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l_Std_Iter_finitelyManySteps___redArg(v_it_630_);
lean_dec(v_it_630_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySteps(lean_object* v_00_u03b1_632_, lean_object* v_00_u03b2_633_, lean_object* v_inst_634_, lean_object* v_inst_635_, lean_object* v_it_636_){
_start:
{
lean_inc(v_it_636_);
return v_it_636_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySteps___boxed(lean_object* v_00_u03b1_637_, lean_object* v_00_u03b2_638_, lean_object* v_inst_639_, lean_object* v_inst_640_, lean_object* v_it_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l_Std_Iter_finitelyManySteps(v_00_u03b1_637_, v_00_u03b2_638_, v_inst_639_, v_inst_640_, v_it_641_);
lean_dec(v_it_641_);
lean_dec(v_inst_639_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySteps_x21___redArg(lean_object* v_it_643_){
_start:
{
lean_inc(v_it_643_);
return v_it_643_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySteps_x21___redArg___boxed(lean_object* v_it_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_Std_Iter_finitelyManySteps_x21___redArg(v_it_644_);
lean_dec(v_it_644_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySteps_x21(lean_object* v_00_u03b1_646_, lean_object* v_00_u03b2_647_, lean_object* v_inst_648_, lean_object* v_it_649_){
_start:
{
lean_inc(v_it_649_);
return v_it_649_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySteps_x21___boxed(lean_object* v_00_u03b1_650_, lean_object* v_00_u03b2_651_, lean_object* v_inst_652_, lean_object* v_it_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_Std_Iter_finitelyManySteps_x21(v_00_u03b1_650_, v_00_u03b2_651_, v_inst_652_, v_it_653_);
lean_dec(v_it_653_);
lean_dec(v_inst_652_);
return v_res_654_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__1(void){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_656_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__0));
v___x_657_ = l_String_toRawSubstring_x27(v___x_656_);
return v___x_657_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__8(void){
_start:
{
lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_677_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__7));
v___x_678_ = l_String_toRawSubstring_x27(v___x_677_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2(lean_object* v_x_696_, lean_object* v_a_697_, lean_object* v_a_698_){
_start:
{
lean_object* v___x_699_; uint8_t v___x_700_; 
v___x_699_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__1));
v___x_700_ = l_Lean_Syntax_isOfKind(v_x_696_, v___x_699_);
if (v___x_700_ == 0)
{
lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_701_ = lean_box(1);
v___x_702_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_702_, 0, v___x_701_);
lean_ctor_set(v___x_702_, 1, v_a_698_);
return v___x_702_;
}
else
{
lean_object* v_quotContext_703_; lean_object* v_currMacroScope_704_; lean_object* v_ref_705_; uint8_t v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
v_quotContext_703_ = lean_ctor_get(v_a_697_, 1);
v_currMacroScope_704_ = lean_ctor_get(v_a_697_, 2);
v_ref_705_ = lean_ctor_get(v_a_697_, 5);
v___x_706_ = 0;
v___x_707_ = l_Lean_SourceInfo_fromRef(v_ref_705_, v___x_706_);
v___x_708_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__5));
v___x_709_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__6));
lean_inc_n(v___x_707_, 31);
v___x_710_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_710_, 0, v___x_707_);
lean_ctor_set(v___x_710_, 1, v___x_708_);
v___x_711_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__8));
v___x_712_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__10));
v___x_713_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__11));
v___x_714_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_714_, 0, v___x_707_);
lean_ctor_set(v___x_714_, 1, v___x_713_);
v___x_715_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__13));
v___x_716_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__15));
v___x_717_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__16));
v___x_718_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__17));
v___x_719_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_719_, 0, v___x_707_);
lean_ctor_set(v___x_719_, 1, v___x_717_);
v___x_720_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__20));
v___x_721_ = lean_obj_once(&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__1, &l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__1_once, _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__1);
v___x_722_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__3));
lean_inc_n(v_currMacroScope_704_, 2);
lean_inc_n(v_quotContext_703_, 2);
v___x_723_ = l_Lean_addMacroScope(v_quotContext_703_, v___x_722_, v_currMacroScope_704_);
v___x_724_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__6));
v___x_725_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_725_, 0, v___x_707_);
lean_ctor_set(v___x_725_, 1, v___x_721_);
lean_ctor_set(v___x_725_, 2, v___x_723_);
lean_ctor_set(v___x_725_, 3, v___x_724_);
v___x_726_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__33));
v___x_727_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__34));
v___x_728_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_728_, 0, v___x_707_);
lean_ctor_set(v___x_728_, 1, v___x_727_);
v___x_729_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__36));
v___x_730_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__37));
v___x_731_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_731_, 0, v___x_707_);
lean_ctor_set(v___x_731_, 1, v___x_730_);
v___x_732_ = l_Lean_Syntax_node1(v___x_707_, v___x_729_, v___x_731_);
v___x_733_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__38));
v___x_734_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_734_, 0, v___x_707_);
lean_ctor_set(v___x_734_, 1, v___x_733_);
v___x_735_ = l_Lean_Syntax_node3(v___x_707_, v___x_726_, v___x_728_, v___x_732_, v___x_734_);
v___x_736_ = l_Lean_Syntax_node1(v___x_707_, v___x_711_, v___x_735_);
lean_inc(v___x_736_);
v___x_737_ = l_Lean_Syntax_node2(v___x_707_, v___x_720_, v___x_725_, v___x_736_);
lean_inc_ref(v___x_719_);
v___x_738_ = l_Lean_Syntax_node2(v___x_707_, v___x_718_, v___x_719_, v___x_737_);
v___x_739_ = l_Lean_Syntax_node1(v___x_707_, v___x_711_, v___x_738_);
v___x_740_ = l_Lean_Syntax_node1(v___x_707_, v___x_716_, v___x_739_);
v___x_741_ = l_Lean_Syntax_node1(v___x_707_, v___x_715_, v___x_740_);
lean_inc_ref_n(v___x_714_, 2);
v___x_742_ = l_Lean_Syntax_node2(v___x_707_, v___x_712_, v___x_714_, v___x_741_);
v___x_743_ = lean_obj_once(&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__8, &l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__8_once, _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__8);
v___x_744_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__9));
v___x_745_ = l_Lean_addMacroScope(v_quotContext_703_, v___x_744_, v_currMacroScope_704_);
v___x_746_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__12));
v___x_747_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_747_, 0, v___x_707_);
lean_ctor_set(v___x_747_, 1, v___x_743_);
lean_ctor_set(v___x_747_, 2, v___x_745_);
lean_ctor_set(v___x_747_, 3, v___x_746_);
v___x_748_ = l_Lean_Syntax_node2(v___x_707_, v___x_720_, v___x_747_, v___x_736_);
v___x_749_ = l_Lean_Syntax_node2(v___x_707_, v___x_718_, v___x_719_, v___x_748_);
v___x_750_ = l_Lean_Syntax_node1(v___x_707_, v___x_711_, v___x_749_);
v___x_751_ = l_Lean_Syntax_node1(v___x_707_, v___x_716_, v___x_750_);
v___x_752_ = l_Lean_Syntax_node1(v___x_707_, v___x_715_, v___x_751_);
v___x_753_ = l_Lean_Syntax_node2(v___x_707_, v___x_712_, v___x_714_, v___x_752_);
v___x_754_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__46));
v___x_755_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__47));
v___x_756_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_756_, 0, v___x_707_);
lean_ctor_set(v___x_756_, 1, v___x_754_);
v___x_757_ = lean_obj_once(&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48, &l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48_once, _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48);
v___x_758_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_758_, 0, v___x_707_);
lean_ctor_set(v___x_758_, 1, v___x_711_);
lean_ctor_set(v___x_758_, 2, v___x_757_);
v___x_759_ = l_Lean_Syntax_node2(v___x_707_, v___x_755_, v___x_756_, v___x_758_);
v___x_760_ = l_Lean_Syntax_node1(v___x_707_, v___x_711_, v___x_759_);
v___x_761_ = l_Lean_Syntax_node1(v___x_707_, v___x_716_, v___x_760_);
v___x_762_ = l_Lean_Syntax_node1(v___x_707_, v___x_715_, v___x_761_);
v___x_763_ = l_Lean_Syntax_node2(v___x_707_, v___x_712_, v___x_714_, v___x_762_);
v___x_764_ = l_Lean_Syntax_node3(v___x_707_, v___x_711_, v___x_742_, v___x_753_, v___x_763_);
v___x_765_ = l_Lean_Syntax_node2(v___x_707_, v___x_709_, v___x_710_, v___x_764_);
v___x_766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_766_, 0, v___x_765_);
lean_ctor_set(v___x_766_, 1, v_a_698_);
return v___x_766_;
}
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___boxed(lean_object* v_x_767_, lean_object* v_a_768_, lean_object* v_a_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2(v_x_767_, v_a_768_, v_a_769_);
lean_dec_ref(v_a_768_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_TerminationMeasures_instWellFoundedRelationProductive___redArg(){
_start:
{
lean_object* v___x_772_; 
v___x_772_ = lean_box(0);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_TerminationMeasures_instWellFoundedRelationProductive___redArg___boxed(lean_object* v___dummy_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l_Std_IterM_TerminationMeasures_instWellFoundedRelationProductive___redArg();
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_TerminationMeasures_instWellFoundedRelationProductive(lean_object* v_00_u03b1_775_, lean_object* v_m_776_, lean_object* v_00_u03b2_777_, lean_object* v_inst_778_, lean_object* v_inst_779_){
_start:
{
lean_object* v___x_780_; 
v___x_780_ = lean_box(0);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_TerminationMeasures_instWellFoundedRelationProductive___boxed(lean_object* v_00_u03b1_781_, lean_object* v_m_782_, lean_object* v_00_u03b2_783_, lean_object* v_inst_784_, lean_object* v_inst_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l_Std_IterM_TerminationMeasures_instWellFoundedRelationProductive(v_00_u03b1_781_, v_m_782_, v_00_u03b2_783_, v_inst_784_, v_inst_785_);
lean_dec(v_inst_784_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySkips___redArg(lean_object* v_it_787_){
_start:
{
lean_inc(v_it_787_);
return v_it_787_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySkips___redArg___boxed(lean_object* v_it_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_Std_IterM_finitelyManySkips___redArg(v_it_788_);
lean_dec(v_it_788_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySkips(lean_object* v_00_u03b1_790_, lean_object* v_m_791_, lean_object* v_00_u03b2_792_, lean_object* v_inst_793_, lean_object* v_inst_794_, lean_object* v_it_795_){
_start:
{
lean_inc(v_it_795_);
return v_it_795_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySkips___boxed(lean_object* v_00_u03b1_796_, lean_object* v_m_797_, lean_object* v_00_u03b2_798_, lean_object* v_inst_799_, lean_object* v_inst_800_, lean_object* v_it_801_){
_start:
{
lean_object* v_res_802_; 
v_res_802_ = l_Std_IterM_finitelyManySkips(v_00_u03b1_796_, v_m_797_, v_00_u03b2_798_, v_inst_799_, v_inst_800_, v_it_801_);
lean_dec(v_it_801_);
lean_dec(v_inst_799_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySkips_x21___redArg(lean_object* v_it_803_){
_start:
{
lean_inc(v_it_803_);
return v_it_803_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySkips_x21___redArg___boxed(lean_object* v_it_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_Std_IterM_finitelyManySkips_x21___redArg(v_it_804_);
lean_dec(v_it_804_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySkips_x21(lean_object* v_00_u03b1_806_, lean_object* v_m_807_, lean_object* v_00_u03b2_808_, lean_object* v_inst_809_, lean_object* v_it_810_){
_start:
{
lean_inc(v_it_810_);
return v_it_810_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySkips_x21___boxed(lean_object* v_00_u03b1_811_, lean_object* v_m_812_, lean_object* v_00_u03b2_813_, lean_object* v_inst_814_, lean_object* v_it_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l_Std_IterM_finitelyManySkips_x21(v_00_u03b1_811_, v_m_812_, v_00_u03b2_813_, v_inst_814_, v_it_815_);
lean_dec(v_it_815_);
lean_dec(v_inst_814_);
return v_res_816_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__1(void){
_start:
{
lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_818_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__0));
v___x_819_ = l_String_toRawSubstring_x27(v___x_818_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3(lean_object* v_x_838_, lean_object* v_a_839_, lean_object* v_a_840_){
_start:
{
lean_object* v___x_841_; uint8_t v___x_842_; 
v___x_841_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__1));
v___x_842_ = l_Lean_Syntax_isOfKind(v_x_838_, v___x_841_);
if (v___x_842_ == 0)
{
lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_843_ = lean_box(1);
v___x_844_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_844_, 0, v___x_843_);
lean_ctor_set(v___x_844_, 1, v_a_840_);
return v___x_844_;
}
else
{
lean_object* v_quotContext_845_; lean_object* v_currMacroScope_846_; lean_object* v_ref_847_; uint8_t v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v_quotContext_845_ = lean_ctor_get(v_a_839_, 1);
v_currMacroScope_846_ = lean_ctor_get(v_a_839_, 2);
v_ref_847_ = lean_ctor_get(v_a_839_, 5);
v___x_848_ = 0;
v___x_849_ = l_Lean_SourceInfo_fromRef(v_ref_847_, v___x_848_);
v___x_850_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__5));
v___x_851_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__6));
lean_inc_n(v___x_849_, 24);
v___x_852_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_852_, 0, v___x_849_);
lean_ctor_set(v___x_852_, 1, v___x_850_);
v___x_853_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__8));
v___x_854_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__10));
v___x_855_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__11));
v___x_856_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_856_, 0, v___x_849_);
lean_ctor_set(v___x_856_, 1, v___x_855_);
v___x_857_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__13));
v___x_858_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__15));
v___x_859_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__16));
v___x_860_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__17));
v___x_861_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_861_, 0, v___x_849_);
lean_ctor_set(v___x_861_, 1, v___x_859_);
v___x_862_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__20));
v___x_863_ = lean_obj_once(&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__1, &l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__1_once, _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__1);
v___x_864_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__3));
lean_inc(v_currMacroScope_846_);
lean_inc(v_quotContext_845_);
v___x_865_ = l_Lean_addMacroScope(v_quotContext_845_, v___x_864_, v_currMacroScope_846_);
v___x_866_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__6));
v___x_867_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_867_, 0, v___x_849_);
lean_ctor_set(v___x_867_, 1, v___x_863_);
lean_ctor_set(v___x_867_, 2, v___x_865_);
lean_ctor_set(v___x_867_, 3, v___x_866_);
v___x_868_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__33));
v___x_869_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__34));
v___x_870_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_870_, 0, v___x_849_);
lean_ctor_set(v___x_870_, 1, v___x_869_);
v___x_871_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__36));
v___x_872_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__37));
v___x_873_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_873_, 0, v___x_849_);
lean_ctor_set(v___x_873_, 1, v___x_872_);
v___x_874_ = l_Lean_Syntax_node1(v___x_849_, v___x_871_, v___x_873_);
v___x_875_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__38));
v___x_876_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_876_, 0, v___x_849_);
lean_ctor_set(v___x_876_, 1, v___x_875_);
v___x_877_ = l_Lean_Syntax_node3(v___x_849_, v___x_868_, v___x_870_, v___x_874_, v___x_876_);
v___x_878_ = l_Lean_Syntax_node1(v___x_849_, v___x_853_, v___x_877_);
v___x_879_ = l_Lean_Syntax_node2(v___x_849_, v___x_862_, v___x_867_, v___x_878_);
v___x_880_ = l_Lean_Syntax_node2(v___x_849_, v___x_860_, v___x_861_, v___x_879_);
v___x_881_ = l_Lean_Syntax_node1(v___x_849_, v___x_853_, v___x_880_);
v___x_882_ = l_Lean_Syntax_node1(v___x_849_, v___x_858_, v___x_881_);
v___x_883_ = l_Lean_Syntax_node1(v___x_849_, v___x_857_, v___x_882_);
lean_inc_ref(v___x_856_);
v___x_884_ = l_Lean_Syntax_node2(v___x_849_, v___x_854_, v___x_856_, v___x_883_);
v___x_885_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__46));
v___x_886_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__47));
v___x_887_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_887_, 0, v___x_849_);
lean_ctor_set(v___x_887_, 1, v___x_885_);
v___x_888_ = lean_obj_once(&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48, &l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48_once, _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48);
v___x_889_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_889_, 0, v___x_849_);
lean_ctor_set(v___x_889_, 1, v___x_853_);
lean_ctor_set(v___x_889_, 2, v___x_888_);
v___x_890_ = l_Lean_Syntax_node2(v___x_849_, v___x_886_, v___x_887_, v___x_889_);
v___x_891_ = l_Lean_Syntax_node1(v___x_849_, v___x_853_, v___x_890_);
v___x_892_ = l_Lean_Syntax_node1(v___x_849_, v___x_858_, v___x_891_);
v___x_893_ = l_Lean_Syntax_node1(v___x_849_, v___x_857_, v___x_892_);
v___x_894_ = l_Lean_Syntax_node2(v___x_849_, v___x_854_, v___x_856_, v___x_893_);
v___x_895_ = l_Lean_Syntax_node2(v___x_849_, v___x_853_, v___x_884_, v___x_894_);
v___x_896_ = l_Lean_Syntax_node2(v___x_849_, v___x_851_, v___x_852_, v___x_895_);
v___x_897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_897_, 0, v___x_896_);
lean_ctor_set(v___x_897_, 1, v_a_840_);
return v___x_897_;
}
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___boxed(lean_object* v_x_898_, lean_object* v_a_899_, lean_object* v_a_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3(v_x_898_, v_a_899_, v_a_900_);
lean_dec_ref(v_a_899_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySkips___redArg(lean_object* v_it_902_){
_start:
{
lean_inc(v_it_902_);
return v_it_902_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySkips___redArg___boxed(lean_object* v_it_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l_Std_Iter_finitelyManySkips___redArg(v_it_903_);
lean_dec(v_it_903_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySkips(lean_object* v_00_u03b1_905_, lean_object* v_00_u03b2_906_, lean_object* v_inst_907_, lean_object* v_inst_908_, lean_object* v_it_909_){
_start:
{
lean_inc(v_it_909_);
return v_it_909_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySkips___boxed(lean_object* v_00_u03b1_910_, lean_object* v_00_u03b2_911_, lean_object* v_inst_912_, lean_object* v_inst_913_, lean_object* v_it_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l_Std_Iter_finitelyManySkips(v_00_u03b1_910_, v_00_u03b2_911_, v_inst_912_, v_inst_913_, v_it_914_);
lean_dec(v_it_914_);
lean_dec(v_inst_912_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySkips_x21___redArg(lean_object* v_it_916_){
_start:
{
lean_inc(v_it_916_);
return v_it_916_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySkips_x21___redArg___boxed(lean_object* v_it_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l_Std_Iter_finitelyManySkips_x21___redArg(v_it_917_);
lean_dec(v_it_917_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySkips_x21(lean_object* v_00_u03b1_919_, lean_object* v_00_u03b2_920_, lean_object* v_inst_921_, lean_object* v_it_922_){
_start:
{
lean_inc(v_it_922_);
return v_it_922_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySkips_x21___boxed(lean_object* v_00_u03b1_923_, lean_object* v_00_u03b2_924_, lean_object* v_inst_925_, lean_object* v_it_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_Std_Iter_finitelyManySkips_x21(v_00_u03b1_923_, v_00_u03b2_924_, v_inst_925_, v_it_926_);
lean_dec(v_it_926_);
lean_dec(v_inst_925_);
return v_res_927_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__1(void){
_start:
{
lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_929_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__0));
v___x_930_ = l_String_toRawSubstring_x27(v___x_929_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4(lean_object* v_x_948_, lean_object* v_a_949_, lean_object* v_a_950_){
_start:
{
lean_object* v___x_951_; uint8_t v___x_952_; 
v___x_951_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__1));
v___x_952_ = l_Lean_Syntax_isOfKind(v_x_948_, v___x_951_);
if (v___x_952_ == 0)
{
lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_953_ = lean_box(1);
v___x_954_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_954_, 0, v___x_953_);
lean_ctor_set(v___x_954_, 1, v_a_950_);
return v___x_954_;
}
else
{
lean_object* v_quotContext_955_; lean_object* v_currMacroScope_956_; lean_object* v_ref_957_; uint8_t v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v_quotContext_955_ = lean_ctor_get(v_a_949_, 1);
v_currMacroScope_956_ = lean_ctor_get(v_a_949_, 2);
v_ref_957_ = lean_ctor_get(v_a_949_, 5);
v___x_958_ = 0;
v___x_959_ = l_Lean_SourceInfo_fromRef(v_ref_957_, v___x_958_);
v___x_960_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__5));
v___x_961_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__6));
lean_inc_n(v___x_959_, 24);
v___x_962_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_962_, 0, v___x_959_);
lean_ctor_set(v___x_962_, 1, v___x_960_);
v___x_963_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__8));
v___x_964_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__10));
v___x_965_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__11));
v___x_966_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_959_);
lean_ctor_set(v___x_966_, 1, v___x_965_);
v___x_967_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__13));
v___x_968_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__15));
v___x_969_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__16));
v___x_970_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__17));
v___x_971_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_971_, 0, v___x_959_);
lean_ctor_set(v___x_971_, 1, v___x_969_);
v___x_972_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__20));
v___x_973_ = lean_obj_once(&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__1, &l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__1_once, _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__1);
v___x_974_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__2));
lean_inc(v_currMacroScope_956_);
lean_inc(v_quotContext_955_);
v___x_975_ = l_Lean_addMacroScope(v_quotContext_955_, v___x_974_, v_currMacroScope_956_);
v___x_976_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__5));
v___x_977_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_977_, 0, v___x_959_);
lean_ctor_set(v___x_977_, 1, v___x_973_);
lean_ctor_set(v___x_977_, 2, v___x_975_);
lean_ctor_set(v___x_977_, 3, v___x_976_);
v___x_978_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__33));
v___x_979_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__34));
v___x_980_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_980_, 0, v___x_959_);
lean_ctor_set(v___x_980_, 1, v___x_979_);
v___x_981_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__36));
v___x_982_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__37));
v___x_983_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_983_, 0, v___x_959_);
lean_ctor_set(v___x_983_, 1, v___x_982_);
v___x_984_ = l_Lean_Syntax_node1(v___x_959_, v___x_981_, v___x_983_);
v___x_985_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__38));
v___x_986_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_959_);
lean_ctor_set(v___x_986_, 1, v___x_985_);
v___x_987_ = l_Lean_Syntax_node3(v___x_959_, v___x_978_, v___x_980_, v___x_984_, v___x_986_);
v___x_988_ = l_Lean_Syntax_node1(v___x_959_, v___x_963_, v___x_987_);
v___x_989_ = l_Lean_Syntax_node2(v___x_959_, v___x_972_, v___x_977_, v___x_988_);
v___x_990_ = l_Lean_Syntax_node2(v___x_959_, v___x_970_, v___x_971_, v___x_989_);
v___x_991_ = l_Lean_Syntax_node1(v___x_959_, v___x_963_, v___x_990_);
v___x_992_ = l_Lean_Syntax_node1(v___x_959_, v___x_968_, v___x_991_);
v___x_993_ = l_Lean_Syntax_node1(v___x_959_, v___x_967_, v___x_992_);
lean_inc_ref(v___x_966_);
v___x_994_ = l_Lean_Syntax_node2(v___x_959_, v___x_964_, v___x_966_, v___x_993_);
v___x_995_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__46));
v___x_996_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__47));
v___x_997_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_959_);
lean_ctor_set(v___x_997_, 1, v___x_995_);
v___x_998_ = lean_obj_once(&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48, &l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48_once, _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48);
v___x_999_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_999_, 0, v___x_959_);
lean_ctor_set(v___x_999_, 1, v___x_963_);
lean_ctor_set(v___x_999_, 2, v___x_998_);
v___x_1000_ = l_Lean_Syntax_node2(v___x_959_, v___x_996_, v___x_997_, v___x_999_);
v___x_1001_ = l_Lean_Syntax_node1(v___x_959_, v___x_963_, v___x_1000_);
v___x_1002_ = l_Lean_Syntax_node1(v___x_959_, v___x_968_, v___x_1001_);
v___x_1003_ = l_Lean_Syntax_node1(v___x_959_, v___x_967_, v___x_1002_);
v___x_1004_ = l_Lean_Syntax_node2(v___x_959_, v___x_964_, v___x_966_, v___x_1003_);
v___x_1005_ = l_Lean_Syntax_node2(v___x_959_, v___x_963_, v___x_994_, v___x_1004_);
v___x_1006_ = l_Lean_Syntax_node2(v___x_959_, v___x_961_, v___x_962_, v___x_1005_);
v___x_1007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1006_);
lean_ctor_set(v___x_1007_, 1, v_a_950_);
return v___x_1007_;
}
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___boxed(lean_object* v_x_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4(v_x_1008_, v_a_1009_, v_a_1010_);
lean_dec_ref(v_a_1009_);
return v_res_1011_;
}
}
lean_object* runtime_initialize_Init_NotationExtra(uint8_t builtin);
lean_object* runtime_initialize_Init_WFTactics(uint8_t builtin);
lean_object* runtime_initialize_Init_Ext(uint8_t builtin);
lean_object* runtime_initialize_Init_PropLemmas(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Iterators_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_NotationExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_PropLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Iterators_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_NotationExtra(uint8_t builtin);
lean_object* initialize_Init_WFTactics(uint8_t builtin);
lean_object* initialize_Init_Ext(uint8_t builtin);
lean_object* initialize_Init_PropLemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Iterators_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_NotationExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_PropLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Iterators_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Iterators_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
