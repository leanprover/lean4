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
lean_object* l___private_Init_Data_Iterators_Basic_0__Std_Internal_idOpaque___redArg(){
_start:
{
lean_object* v___f_6_; 
v___f_6_ = ((lean_object*)(l___private_Init_Data_Iterators_Basic_0__Std_Internal_idOpaque___redArg___closed__0));
return v___f_6_;
}
}
LEAN_EXPORT void l___private_Init_Data_Iterators_Basic_0__Std_Internal_idOpaque___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_7_;
v_res_7_ = l___private_Init_Data_Iterators_Basic_0__Std_Internal_idOpaque___redArg();
stack->m_obj
 = v_res_7_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Basic_0__Std_Internal_idOpaque___redArg___boxed(lean_object* v___dummy_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l___private_Init_Data_Iterators_Basic_0__Std_Internal_idOpaque___redArg();
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Basic_0__Std_Internal_idOpaque(lean_object* v_00_u03b1_10_){
_start:
{
lean_object* v___f_11_; 
v___f_11_ = ((lean_object*)(l___private_Init_Data_Iterators_Basic_0__Std_Internal_idOpaque___redArg___closed__0));
return v___f_11_;
}
}
LEAN_EXPORT lean_object* l_Std_Shrink_deflate___redArg(lean_object* v_x_12_){
_start:
{
lean_inc(v_x_12_);
return v_x_12_;
}
}
LEAN_EXPORT lean_object* l_Std_Shrink_deflate___redArg___boxed(lean_object* v_x_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Std_Shrink_deflate___redArg(v_x_13_);
lean_dec(v_x_13_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Std_Shrink_deflate(lean_object* v_00_u03b1_15_, lean_object* v_x_16_){
_start:
{
lean_inc(v_x_16_);
return v_x_16_;
}
}
LEAN_EXPORT lean_object* l_Std_Shrink_deflate___boxed(lean_object* v_00_u03b1_17_, lean_object* v_x_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l_Std_Shrink_deflate(v_00_u03b1_17_, v_x_18_);
lean_dec(v_x_18_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l_Std_Shrink_inflate___redArg(lean_object* v_x_20_){
_start:
{
lean_inc(v_x_20_);
return v_x_20_;
}
}
LEAN_EXPORT lean_object* l_Std_Shrink_inflate___redArg___boxed(lean_object* v_x_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Std_Shrink_inflate___redArg(v_x_21_);
lean_dec(v_x_21_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Std_Shrink_inflate(lean_object* v_00_u03b1_23_, lean_object* v_x_24_){
_start:
{
lean_inc(v_x_24_);
return v_x_24_;
}
}
LEAN_EXPORT lean_object* l_Std_Shrink_inflate___boxed(lean_object* v_00_u03b1_25_, lean_object* v_x_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = l_Std_Shrink_inflate(v_00_u03b1_25_, v_x_26_);
lean_dec(v_x_26_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toIterM___redArg(lean_object* v_it_28_){
_start:
{
lean_inc(v_it_28_);
return v_it_28_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toIterM___redArg___boxed(lean_object* v_it_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Std_Iter_toIterM___redArg(v_it_29_);
lean_dec(v_it_29_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toIterM(lean_object* v_00_u03b1_31_, lean_object* v_00_u03b2_32_, lean_object* v_it_33_){
_start:
{
lean_inc(v_it_33_);
return v_it_33_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toIterM___boxed(lean_object* v_00_u03b1_34_, lean_object* v_00_u03b2_35_, lean_object* v_it_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Std_Iter_toIterM(v_00_u03b1_34_, v_00_u03b2_35_, v_it_36_);
lean_dec(v_it_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toIter___redArg(lean_object* v_it_38_){
_start:
{
lean_inc(v_it_38_);
return v_it_38_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toIter___redArg___boxed(lean_object* v_it_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Std_IterM_toIter___redArg(v_it_39_);
lean_dec(v_it_39_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toIter(lean_object* v_00_u03b1_41_, lean_object* v_00_u03b2_42_, lean_object* v_it_43_){
_start:
{
lean_inc(v_it_43_);
return v_it_43_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toIter___boxed(lean_object* v_00_u03b1_44_, lean_object* v_00_u03b2_45_, lean_object* v_it_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_Std_IterM_toIter(v_00_u03b1_44_, v_00_u03b2_45_, v_it_46_);
lean_dec(v_it_46_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_ctorIdx___impl___redArg(lean_object* v_x_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = lean_obj_tag_nat(v_x_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_ctorIdx___impl___redArg___boxed(lean_object* v_x_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Std_IterStep_ctorIdx___impl___redArg(v_x_50_);
lean_dec(v_x_50_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_ctorIdx___impl(lean_object* v_00_u03b1_52_, lean_object* v_00_u03b2_53_, lean_object* v_x_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = lean_obj_tag_nat(v_x_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_ctorIdx___impl___boxed(lean_object* v_00_u03b1_56_, lean_object* v_00_u03b2_57_, lean_object* v_x_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Std_IterStep_ctorIdx___impl(v_00_u03b1_56_, v_00_u03b2_57_, v_x_58_);
lean_dec(v_x_58_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_ctorElim___redArg(lean_object* v_t_60_, lean_object* v_k_61_){
_start:
{
switch(lean_obj_tag(v_t_60_))
{
case 0:
{
lean_object* v_it_62_; lean_object* v_out_63_; lean_object* v___x_64_; 
v_it_62_ = lean_ctor_get(v_t_60_, 0);
lean_inc(v_it_62_);
v_out_63_ = lean_ctor_get(v_t_60_, 1);
lean_inc(v_out_63_);
lean_dec_ref_known(v_t_60_, 2);
v___x_64_ = lean_apply_2(v_k_61_, v_it_62_, v_out_63_);
return v___x_64_;
}
case 1:
{
lean_object* v_it_65_; lean_object* v___x_66_; 
v_it_65_ = lean_ctor_get(v_t_60_, 0);
lean_inc(v_it_65_);
lean_dec_ref_known(v_t_60_, 1);
v___x_66_ = lean_apply_1(v_k_61_, v_it_65_);
return v___x_66_;
}
default: 
{
return v_k_61_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_ctorElim(lean_object* v_00_u03b1_67_, lean_object* v_00_u03b2_68_, lean_object* v_motive_69_, lean_object* v_ctorIdx_70_, lean_object* v_t_71_, lean_object* v_h_72_, lean_object* v_k_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = l_Std_IterStep_ctorElim___redArg(v_t_71_, v_k_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_ctorElim___boxed(lean_object* v_00_u03b1_75_, lean_object* v_00_u03b2_76_, lean_object* v_motive_77_, lean_object* v_ctorIdx_78_, lean_object* v_t_79_, lean_object* v_h_80_, lean_object* v_k_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_Std_IterStep_ctorElim(v_00_u03b1_75_, v_00_u03b2_76_, v_motive_77_, v_ctorIdx_78_, v_t_79_, v_h_80_, v_k_81_);
lean_dec(v_ctorIdx_78_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_yield_elim___redArg(lean_object* v_t_83_, lean_object* v_yield_84_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = l_Std_IterStep_ctorElim___redArg(v_t_83_, v_yield_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_yield_elim(lean_object* v_00_u03b1_86_, lean_object* v_00_u03b2_87_, lean_object* v_motive_88_, lean_object* v_t_89_, lean_object* v_h_90_, lean_object* v_yield_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l_Std_IterStep_ctorElim___redArg(v_t_89_, v_yield_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_skip_elim___redArg(lean_object* v_t_93_, lean_object* v_skip_94_){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = l_Std_IterStep_ctorElim___redArg(v_t_93_, v_skip_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_skip_elim(lean_object* v_00_u03b1_96_, lean_object* v_00_u03b2_97_, lean_object* v_motive_98_, lean_object* v_t_99_, lean_object* v_h_100_, lean_object* v_skip_101_){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = l_Std_IterStep_ctorElim___redArg(v_t_99_, v_skip_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_done_elim___redArg(lean_object* v_t_103_, lean_object* v_done_104_){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = l_Std_IterStep_ctorElim___redArg(v_t_103_, v_done_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_done_elim(lean_object* v_00_u03b1_106_, lean_object* v_00_u03b2_107_, lean_object* v_motive_108_, lean_object* v_t_109_, lean_object* v_h_110_, lean_object* v_done_111_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = l_Std_IterStep_ctorElim___redArg(v_t_109_, v_done_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_successor___redArg(lean_object* v_x_113_){
_start:
{
switch(lean_obj_tag(v_x_113_))
{
case 0:
{
lean_object* v_it_114_; lean_object* v___x_115_; 
v_it_114_ = lean_ctor_get(v_x_113_, 0);
lean_inc(v_it_114_);
lean_dec_ref_known(v_x_113_, 2);
v___x_115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_115_, 0, v_it_114_);
return v___x_115_;
}
case 1:
{
lean_object* v_it_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_123_; 
v_it_116_ = lean_ctor_get(v_x_113_, 0);
v_isSharedCheck_123_ = !lean_is_exclusive(v_x_113_);
if (v_isSharedCheck_123_ == 0)
{
v___x_118_ = v_x_113_;
v_isShared_119_ = v_isSharedCheck_123_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_it_116_);
lean_dec(v_x_113_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_123_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v___x_121_; 
if (v_isShared_119_ == 0)
{
v___x_121_ = v___x_118_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v_it_116_);
v___x_121_ = v_reuseFailAlloc_122_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
return v___x_121_;
}
}
}
default: 
{
lean_object* v___x_124_; 
v___x_124_ = lean_box(0);
return v___x_124_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_successor(lean_object* v_00_u03b1_125_, lean_object* v_00_u03b2_126_, lean_object* v_x_127_){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = l_Std_IterStep_successor___redArg(v_x_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_mapIterator___redArg(lean_object* v_f_129_, lean_object* v_x_130_){
_start:
{
switch(lean_obj_tag(v_x_130_))
{
case 0:
{
lean_object* v_it_131_; lean_object* v_out_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_140_; 
v_it_131_ = lean_ctor_get(v_x_130_, 0);
v_out_132_ = lean_ctor_get(v_x_130_, 1);
v_isSharedCheck_140_ = !lean_is_exclusive(v_x_130_);
if (v_isSharedCheck_140_ == 0)
{
v___x_134_ = v_x_130_;
v_isShared_135_ = v_isSharedCheck_140_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_out_132_);
lean_inc(v_it_131_);
lean_dec(v_x_130_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_140_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
lean_object* v___x_136_; lean_object* v___x_138_; 
v___x_136_ = lean_apply_1(v_f_129_, v_it_131_);
if (v_isShared_135_ == 0)
{
lean_ctor_set(v___x_134_, 0, v___x_136_);
v___x_138_ = v___x_134_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v___x_136_);
lean_ctor_set(v_reuseFailAlloc_139_, 1, v_out_132_);
v___x_138_ = v_reuseFailAlloc_139_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
return v___x_138_;
}
}
}
case 1:
{
lean_object* v_it_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_149_; 
v_it_141_ = lean_ctor_get(v_x_130_, 0);
v_isSharedCheck_149_ = !lean_is_exclusive(v_x_130_);
if (v_isSharedCheck_149_ == 0)
{
v___x_143_ = v_x_130_;
v_isShared_144_ = v_isSharedCheck_149_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_it_141_);
lean_dec(v_x_130_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_149_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_145_; lean_object* v___x_147_; 
v___x_145_ = lean_apply_1(v_f_129_, v_it_141_);
if (v_isShared_144_ == 0)
{
lean_ctor_set(v___x_143_, 0, v___x_145_);
v___x_147_ = v___x_143_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v___x_145_);
v___x_147_ = v_reuseFailAlloc_148_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
return v___x_147_;
}
}
}
default: 
{
lean_object* v___x_150_; 
lean_dec(v_f_129_);
v___x_150_ = lean_box(2);
return v___x_150_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_mapIterator(lean_object* v_00_u03b1_151_, lean_object* v_00_u03b2_152_, lean_object* v_00_u03b1_x27_153_, lean_object* v_f_154_, lean_object* v_x_155_){
_start:
{
switch(lean_obj_tag(v_x_155_))
{
case 0:
{
lean_object* v_it_156_; lean_object* v_out_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_165_; 
v_it_156_ = lean_ctor_get(v_x_155_, 0);
v_out_157_ = lean_ctor_get(v_x_155_, 1);
v_isSharedCheck_165_ = !lean_is_exclusive(v_x_155_);
if (v_isSharedCheck_165_ == 0)
{
v___x_159_ = v_x_155_;
v_isShared_160_ = v_isSharedCheck_165_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_out_157_);
lean_inc(v_it_156_);
lean_dec(v_x_155_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_165_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
lean_object* v___x_161_; lean_object* v___x_163_; 
v___x_161_ = lean_apply_1(v_f_154_, v_it_156_);
if (v_isShared_160_ == 0)
{
lean_ctor_set(v___x_159_, 0, v___x_161_);
v___x_163_ = v___x_159_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v___x_161_);
lean_ctor_set(v_reuseFailAlloc_164_, 1, v_out_157_);
v___x_163_ = v_reuseFailAlloc_164_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
return v___x_163_;
}
}
}
case 1:
{
lean_object* v_it_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_174_; 
v_it_166_ = lean_ctor_get(v_x_155_, 0);
v_isSharedCheck_174_ = !lean_is_exclusive(v_x_155_);
if (v_isSharedCheck_174_ == 0)
{
v___x_168_ = v_x_155_;
v_isShared_169_ = v_isSharedCheck_174_;
goto v_resetjp_167_;
}
else
{
lean_inc(v_it_166_);
lean_dec(v_x_155_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_174_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
lean_object* v___x_170_; lean_object* v___x_172_; 
v___x_170_ = lean_apply_1(v_f_154_, v_it_166_);
if (v_isShared_169_ == 0)
{
lean_ctor_set(v___x_168_, 0, v___x_170_);
v___x_172_ = v___x_168_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v___x_170_);
v___x_172_ = v_reuseFailAlloc_173_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
return v___x_172_;
}
}
}
default: 
{
lean_object* v___x_175_; 
lean_dec(v_f_154_);
v___x_175_ = lean_box(2);
return v___x_175_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PlausibleIterStep_yield___redArg(lean_object* v_it_x27_176_, lean_object* v_out_177_){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_178_, 0, v_it_x27_176_);
lean_ctor_set(v___x_178_, 1, v_out_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Std_PlausibleIterStep_yield(lean_object* v_00_u03b1_179_, lean_object* v_00_u03b2_180_, lean_object* v_IsPlausibleStep_181_, lean_object* v_it_x27_182_, lean_object* v_out_183_, lean_object* v_h_184_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_185_, 0, v_it_x27_182_);
lean_ctor_set(v___x_185_, 1, v_out_183_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Std_PlausibleIterStep_skip___redArg(lean_object* v_it_x27_186_){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_187_, 0, v_it_x27_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Std_PlausibleIterStep_skip(lean_object* v_00_u03b1_188_, lean_object* v_00_u03b2_189_, lean_object* v_IsPlausibleStep_190_, lean_object* v_it_x27_191_, lean_object* v_h_192_){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_193_, 0, v_it_x27_191_);
return v___x_193_;
}
}
lean_object* l_Std_PlausibleIterStep_done___redArg(){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = lean_box(2);
return v___x_195_;
}
}
LEAN_EXPORT void l_Std_PlausibleIterStep_done___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_196_;
v_res_196_ = l_Std_PlausibleIterStep_done___redArg();
stack->m_obj
 = v_res_196_;
}
LEAN_EXPORT lean_object* l_Std_PlausibleIterStep_done___redArg___boxed(lean_object* v___dummy_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_Std_PlausibleIterStep_done___redArg();
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l_Std_PlausibleIterStep_done(lean_object* v_00_u03b1_199_, lean_object* v_00_u03b2_200_, lean_object* v_IsPlausibleStep_201_, lean_object* v_h_202_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = lean_box(2);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Std_PlausibleIterStep_casesOn___redArg(lean_object* v_s_204_, lean_object* v_yield_205_, lean_object* v_skip_206_, lean_object* v_done_207_){
_start:
{
switch(lean_obj_tag(v_s_204_))
{
case 0:
{
lean_object* v_it_208_; lean_object* v_out_209_; lean_object* v___x_210_; 
lean_dec(v_done_207_);
lean_dec(v_skip_206_);
v_it_208_ = lean_ctor_get(v_s_204_, 0);
lean_inc(v_it_208_);
v_out_209_ = lean_ctor_get(v_s_204_, 1);
lean_inc(v_out_209_);
lean_dec_ref_known(v_s_204_, 2);
v___x_210_ = lean_apply_3(v_yield_205_, v_it_208_, v_out_209_, lean_box(0));
return v___x_210_;
}
case 1:
{
lean_object* v_it_211_; lean_object* v___x_212_; 
lean_dec(v_done_207_);
lean_dec(v_yield_205_);
v_it_211_ = lean_ctor_get(v_s_204_, 0);
lean_inc(v_it_211_);
lean_dec_ref_known(v_s_204_, 1);
v___x_212_ = lean_apply_2(v_skip_206_, v_it_211_, lean_box(0));
return v___x_212_;
}
default: 
{
lean_object* v___x_213_; 
lean_dec(v_skip_206_);
lean_dec(v_yield_205_);
v___x_213_ = lean_apply_1(v_done_207_, lean_box(0));
return v___x_213_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PlausibleIterStep_casesOn(lean_object* v_00_u03b1_214_, lean_object* v_00_u03b2_215_, lean_object* v_IsPlausibleStep_216_, lean_object* v_motive_217_, lean_object* v_s_218_, lean_object* v_yield_219_, lean_object* v_skip_220_, lean_object* v_done_221_){
_start:
{
switch(lean_obj_tag(v_s_218_))
{
case 0:
{
lean_object* v_it_222_; lean_object* v_out_223_; lean_object* v___x_224_; 
lean_dec(v_done_221_);
lean_dec(v_skip_220_);
v_it_222_ = lean_ctor_get(v_s_218_, 0);
lean_inc(v_it_222_);
v_out_223_ = lean_ctor_get(v_s_218_, 1);
lean_inc(v_out_223_);
lean_dec_ref_known(v_s_218_, 2);
v___x_224_ = lean_apply_3(v_yield_219_, v_it_222_, v_out_223_, lean_box(0));
return v___x_224_;
}
case 1:
{
lean_object* v_it_225_; lean_object* v___x_226_; 
lean_dec(v_done_221_);
lean_dec(v_yield_219_);
v_it_225_ = lean_ctor_get(v_s_218_, 0);
lean_inc(v_it_225_);
lean_dec_ref_known(v_s_218_, 1);
v___x_226_ = lean_apply_2(v_skip_220_, v_it_225_, lean_box(0));
return v___x_226_;
}
default: 
{
lean_object* v___x_227_; 
lean_dec(v_skip_220_);
lean_dec(v_yield_219_);
v___x_227_ = lean_apply_1(v_done_221_, lean_box(0));
return v___x_227_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_IterM_mk_x27___redArg(lean_object* v_it_228_){
_start:
{
lean_inc(v_it_228_);
return v_it_228_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_mk_x27___redArg___boxed(lean_object* v_it_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_Std_IterM_mk_x27___redArg(v_it_229_);
lean_dec(v_it_229_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_mk_x27(lean_object* v_00_u03b1_231_, lean_object* v_m_232_, lean_object* v_00_u03b2_233_, lean_object* v_it_234_){
_start:
{
lean_inc(v_it_234_);
return v_it_234_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_mk_x27___boxed(lean_object* v_00_u03b1_235_, lean_object* v_m_236_, lean_object* v_00_u03b2_237_, lean_object* v_it_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Std_IterM_mk_x27(v_00_u03b1_235_, v_m_236_, v_00_u03b2_237_, v_it_238_);
lean_dec(v_it_238_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_toIterM___redArg(lean_object* v_internalState_240_){
_start:
{
lean_inc(v_internalState_240_);
return v_internalState_240_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_toIterM___redArg___boxed(lean_object* v_internalState_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_Std_Iterators_toIterM___redArg(v_internalState_241_);
lean_dec(v_internalState_241_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_toIterM(lean_object* v_00_u03b1_243_, lean_object* v_m_244_, lean_object* v_00_u03b2_245_, lean_object* v_internalState_246_){
_start:
{
lean_inc(v_internalState_246_);
return v_internalState_246_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_toIterM___boxed(lean_object* v_00_u03b1_247_, lean_object* v_m_248_, lean_object* v_00_u03b2_249_, lean_object* v_internalState_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_Std_Iterators_toIterM(v_00_u03b1_247_, v_m_248_, v_00_u03b2_249_, v_internalState_250_);
lean_dec(v_internalState_250_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_step___redArg(lean_object* v_inst_252_, lean_object* v_it_253_){
_start:
{
lean_object* v___x_254_; 
v___x_254_ = lean_apply_1(v_inst_252_, v_it_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_step(lean_object* v_00_u03b1_255_, lean_object* v_m_256_, lean_object* v_00_u03b2_257_, lean_object* v_inst_258_, lean_object* v_it_259_){
_start:
{
lean_object* v___x_260_; 
v___x_260_ = lean_apply_1(v_inst_258_, v_it_259_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Step_toMonadic___redArg(lean_object* v_step_261_){
_start:
{
switch(lean_obj_tag(v_step_261_))
{
case 0:
{
lean_object* v_it_262_; lean_object* v_out_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_270_; 
v_it_262_ = lean_ctor_get(v_step_261_, 0);
v_out_263_ = lean_ctor_get(v_step_261_, 1);
v_isSharedCheck_270_ = !lean_is_exclusive(v_step_261_);
if (v_isSharedCheck_270_ == 0)
{
v___x_265_ = v_step_261_;
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_out_263_);
lean_inc(v_it_262_);
lean_dec(v_step_261_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_268_; 
if (v_isShared_266_ == 0)
{
v___x_268_ = v___x_265_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_it_262_);
lean_ctor_set(v_reuseFailAlloc_269_, 1, v_out_263_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
}
case 1:
{
lean_object* v_it_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_278_; 
v_it_271_ = lean_ctor_get(v_step_261_, 0);
v_isSharedCheck_278_ = !lean_is_exclusive(v_step_261_);
if (v_isSharedCheck_278_ == 0)
{
v___x_273_ = v_step_261_;
v_isShared_274_ = v_isSharedCheck_278_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_it_271_);
lean_dec(v_step_261_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_278_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v___x_276_; 
if (v_isShared_274_ == 0)
{
v___x_276_ = v___x_273_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v_it_271_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
default: 
{
lean_object* v___x_279_; 
v___x_279_ = lean_box(2);
return v___x_279_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Step_toMonadic(lean_object* v_00_u03b1_280_, lean_object* v_00_u03b2_281_, lean_object* v_inst_282_, lean_object* v_it_283_, lean_object* v_step_284_){
_start:
{
switch(lean_obj_tag(v_step_284_))
{
case 0:
{
lean_object* v_it_285_; lean_object* v_out_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_293_; 
v_it_285_ = lean_ctor_get(v_step_284_, 0);
v_out_286_ = lean_ctor_get(v_step_284_, 1);
v_isSharedCheck_293_ = !lean_is_exclusive(v_step_284_);
if (v_isSharedCheck_293_ == 0)
{
v___x_288_ = v_step_284_;
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_out_286_);
lean_inc(v_it_285_);
lean_dec(v_step_284_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_291_; 
if (v_isShared_289_ == 0)
{
v___x_291_ = v___x_288_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_it_285_);
lean_ctor_set(v_reuseFailAlloc_292_, 1, v_out_286_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
case 1:
{
lean_object* v_it_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_301_; 
v_it_294_ = lean_ctor_get(v_step_284_, 0);
v_isSharedCheck_301_ = !lean_is_exclusive(v_step_284_);
if (v_isSharedCheck_301_ == 0)
{
v___x_296_ = v_step_284_;
v_isShared_297_ = v_isSharedCheck_301_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_it_294_);
lean_dec(v_step_284_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_301_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___x_299_; 
if (v_isShared_297_ == 0)
{
v___x_299_ = v___x_296_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v_it_294_);
v___x_299_ = v_reuseFailAlloc_300_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
return v___x_299_;
}
}
}
default: 
{
lean_object* v___x_302_; 
v___x_302_ = lean_box(2);
return v___x_302_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Step_toMonadic___boxed(lean_object* v_00_u03b1_303_, lean_object* v_00_u03b2_304_, lean_object* v_inst_305_, lean_object* v_it_306_, lean_object* v_step_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l_Std_Iter_Step_toMonadic(v_00_u03b1_303_, v_00_u03b2_304_, v_inst_305_, v_it_306_, v_step_307_);
lean_dec(v_it_306_);
lean_dec(v_inst_305_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Step_toPure___redArg(lean_object* v_step_309_){
_start:
{
switch(lean_obj_tag(v_step_309_))
{
case 0:
{
lean_object* v_it_310_; lean_object* v_out_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_318_; 
v_it_310_ = lean_ctor_get(v_step_309_, 0);
v_out_311_ = lean_ctor_get(v_step_309_, 1);
v_isSharedCheck_318_ = !lean_is_exclusive(v_step_309_);
if (v_isSharedCheck_318_ == 0)
{
v___x_313_ = v_step_309_;
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_out_311_);
lean_inc(v_it_310_);
lean_dec(v_step_309_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_316_; 
if (v_isShared_314_ == 0)
{
v___x_316_ = v___x_313_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_it_310_);
lean_ctor_set(v_reuseFailAlloc_317_, 1, v_out_311_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
return v___x_316_;
}
}
}
case 1:
{
lean_object* v_it_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_326_; 
v_it_319_ = lean_ctor_get(v_step_309_, 0);
v_isSharedCheck_326_ = !lean_is_exclusive(v_step_309_);
if (v_isSharedCheck_326_ == 0)
{
v___x_321_ = v_step_309_;
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_it_319_);
lean_dec(v_step_309_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_324_; 
if (v_isShared_322_ == 0)
{
v___x_324_ = v___x_321_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_it_319_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
default: 
{
lean_object* v___x_327_; 
v___x_327_ = lean_box(2);
return v___x_327_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Step_toPure(lean_object* v_00_u03b1_328_, lean_object* v_00_u03b2_329_, lean_object* v_inst_330_, lean_object* v_it_331_, lean_object* v_step_332_){
_start:
{
switch(lean_obj_tag(v_step_332_))
{
case 0:
{
lean_object* v_it_333_; lean_object* v_out_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_341_; 
v_it_333_ = lean_ctor_get(v_step_332_, 0);
v_out_334_ = lean_ctor_get(v_step_332_, 1);
v_isSharedCheck_341_ = !lean_is_exclusive(v_step_332_);
if (v_isSharedCheck_341_ == 0)
{
v___x_336_ = v_step_332_;
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_out_334_);
lean_inc(v_it_333_);
lean_dec(v_step_332_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_339_; 
if (v_isShared_337_ == 0)
{
v___x_339_ = v___x_336_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v_it_333_);
lean_ctor_set(v_reuseFailAlloc_340_, 1, v_out_334_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
}
case 1:
{
lean_object* v_it_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_349_; 
v_it_342_ = lean_ctor_get(v_step_332_, 0);
v_isSharedCheck_349_ = !lean_is_exclusive(v_step_332_);
if (v_isSharedCheck_349_ == 0)
{
v___x_344_ = v_step_332_;
v_isShared_345_ = v_isSharedCheck_349_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_it_342_);
lean_dec(v_step_332_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_349_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v___x_347_; 
if (v_isShared_345_ == 0)
{
v___x_347_ = v___x_344_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_it_342_);
v___x_347_ = v_reuseFailAlloc_348_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
return v___x_347_;
}
}
}
default: 
{
lean_object* v___x_350_; 
v___x_350_ = lean_box(2);
return v___x_350_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Step_toPure___boxed(lean_object* v_00_u03b1_351_, lean_object* v_00_u03b2_352_, lean_object* v_inst_353_, lean_object* v_it_354_, lean_object* v_step_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Std_IterM_Step_toPure(v_00_u03b1_351_, v_00_u03b2_352_, v_inst_353_, v_it_354_, v_step_355_);
lean_dec(v_it_354_);
lean_dec(v_inst_353_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_step___redArg(lean_object* v_inst_357_, lean_object* v_it_358_){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = lean_apply_1(v_inst_357_, v_it_358_);
switch(lean_obj_tag(v___x_359_))
{
case 0:
{
lean_object* v_it_360_; lean_object* v_out_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_368_; 
v_it_360_ = lean_ctor_get(v___x_359_, 0);
v_out_361_ = lean_ctor_get(v___x_359_, 1);
v_isSharedCheck_368_ = !lean_is_exclusive(v___x_359_);
if (v_isSharedCheck_368_ == 0)
{
v___x_363_ = v___x_359_;
v_isShared_364_ = v_isSharedCheck_368_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_out_361_);
lean_inc(v_it_360_);
lean_dec(v___x_359_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_368_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_366_; 
if (v_isShared_364_ == 0)
{
v___x_366_ = v___x_363_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_it_360_);
lean_ctor_set(v_reuseFailAlloc_367_, 1, v_out_361_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
return v___x_366_;
}
}
}
case 1:
{
lean_object* v_it_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_376_; 
v_it_369_ = lean_ctor_get(v___x_359_, 0);
v_isSharedCheck_376_ = !lean_is_exclusive(v___x_359_);
if (v_isSharedCheck_376_ == 0)
{
v___x_371_ = v___x_359_;
v_isShared_372_ = v_isSharedCheck_376_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_it_369_);
lean_dec(v___x_359_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_376_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_374_; 
if (v_isShared_372_ == 0)
{
v___x_374_ = v___x_371_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_it_369_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
}
default: 
{
lean_object* v___x_377_; 
v___x_377_ = lean_box(2);
return v___x_377_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iter_step(lean_object* v_00_u03b1_378_, lean_object* v_00_u03b2_379_, lean_object* v_inst_380_, lean_object* v_it_381_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = lean_apply_1(v_inst_380_, v_it_381_);
switch(lean_obj_tag(v___x_382_))
{
case 0:
{
lean_object* v_it_383_; lean_object* v_out_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_391_; 
v_it_383_ = lean_ctor_get(v___x_382_, 0);
v_out_384_ = lean_ctor_get(v___x_382_, 1);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_382_);
if (v_isSharedCheck_391_ == 0)
{
v___x_386_ = v___x_382_;
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_out_384_);
lean_inc(v_it_383_);
lean_dec(v___x_382_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_389_; 
if (v_isShared_387_ == 0)
{
v___x_389_ = v___x_386_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_it_383_);
lean_ctor_set(v_reuseFailAlloc_390_, 1, v_out_384_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
}
case 1:
{
lean_object* v_it_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_399_; 
v_it_392_ = lean_ctor_get(v___x_382_, 0);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_382_);
if (v_isSharedCheck_399_ == 0)
{
v___x_394_ = v___x_382_;
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_it_392_);
lean_dec(v___x_382_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_397_; 
if (v_isShared_395_ == 0)
{
v___x_397_ = v___x_394_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_it_392_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
}
default: 
{
lean_object* v___x_400_; 
v___x_400_ = lean_box(2);
return v___x_400_;
}
}
}
}
lean_object* l_Std_IterM_TerminationMeasures_instWellFoundedRelationFinite___redArg(){
_start:
{
lean_object* v___x_402_; 
v___x_402_ = lean_box(0);
return v___x_402_;
}
}
LEAN_EXPORT void l_Std_IterM_TerminationMeasures_instWellFoundedRelationFinite___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_403_;
v_res_403_ = l_Std_IterM_TerminationMeasures_instWellFoundedRelationFinite___redArg();
stack->m_obj
 = v_res_403_;
}
LEAN_EXPORT lean_object* l_Std_IterM_TerminationMeasures_instWellFoundedRelationFinite___redArg___boxed(lean_object* v___dummy_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Std_IterM_TerminationMeasures_instWellFoundedRelationFinite___redArg();
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_TerminationMeasures_instWellFoundedRelationFinite(lean_object* v_00_u03b1_406_, lean_object* v_m_407_, lean_object* v_00_u03b2_408_, lean_object* v_inst_409_, lean_object* v_inst_410_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = lean_box(0);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_TerminationMeasures_instWellFoundedRelationFinite___boxed(lean_object* v_00_u03b1_412_, lean_object* v_m_413_, lean_object* v_00_u03b2_414_, lean_object* v_inst_415_, lean_object* v_inst_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Std_IterM_TerminationMeasures_instWellFoundedRelationFinite(v_00_u03b1_412_, v_m_413_, v_00_u03b2_414_, v_inst_415_, v_inst_416_);
lean_dec(v_inst_415_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySteps___redArg(lean_object* v_it_418_){
_start:
{
lean_inc(v_it_418_);
return v_it_418_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySteps___redArg___boxed(lean_object* v_it_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l_Std_IterM_finitelyManySteps___redArg(v_it_419_);
lean_dec(v_it_419_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySteps(lean_object* v_00_u03b1_421_, lean_object* v_m_422_, lean_object* v_00_u03b2_423_, lean_object* v_inst_424_, lean_object* v_inst_425_, lean_object* v_it_426_){
_start:
{
lean_inc(v_it_426_);
return v_it_426_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySteps___boxed(lean_object* v_00_u03b1_427_, lean_object* v_m_428_, lean_object* v_00_u03b2_429_, lean_object* v_inst_430_, lean_object* v_inst_431_, lean_object* v_it_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Std_IterM_finitelyManySteps(v_00_u03b1_427_, v_m_428_, v_00_u03b2_429_, v_inst_430_, v_inst_431_, v_it_432_);
lean_dec(v_it_432_);
lean_dec(v_inst_430_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySteps_x21___redArg(lean_object* v_it_434_){
_start:
{
lean_inc(v_it_434_);
return v_it_434_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySteps_x21___redArg___boxed(lean_object* v_it_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Std_IterM_finitelyManySteps_x21___redArg(v_it_435_);
lean_dec(v_it_435_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySteps_x21(lean_object* v_00_u03b1_437_, lean_object* v_m_438_, lean_object* v_00_u03b2_439_, lean_object* v_inst_440_, lean_object* v_it_441_){
_start:
{
lean_inc(v_it_441_);
return v_it_441_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySteps_x21___boxed(lean_object* v_00_u03b1_442_, lean_object* v_m_443_, lean_object* v_00_u03b2_444_, lean_object* v_inst_445_, lean_object* v_it_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_Std_IterM_finitelyManySteps_x21(v_00_u03b1_442_, v_m_443_, v_00_u03b2_444_, v_inst_445_, v_it_446_);
lean_dec(v_it_446_);
lean_dec(v_inst_445_);
return v_res_447_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__22(void){
_start:
{
lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_493_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__21));
v___x_494_ = l_String_toRawSubstring_x27(v___x_493_);
return v___x_494_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__40(void){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_530_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__39));
v___x_531_ = l_String_toRawSubstring_x27(v___x_530_);
return v___x_531_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48(void){
_start:
{
lean_object* v___x_556_; 
v___x_556_ = l_Array_mkArray0___redArg();
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1(lean_object* v_x_557_, lean_object* v_a_558_, lean_object* v_a_559_){
_start:
{
lean_object* v___x_560_; uint8_t v___x_561_; 
v___x_560_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__1));
v___x_561_ = l_Lean_Syntax_isOfKind(v_x_557_, v___x_560_);
if (v___x_561_ == 0)
{
lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_562_ = lean_box(1);
v___x_563_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_563_, 0, v___x_562_);
lean_ctor_set(v___x_563_, 1, v_a_559_);
return v___x_563_;
}
else
{
lean_object* v_quotContext_564_; lean_object* v_currMacroScope_565_; lean_object* v_ref_566_; uint8_t v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v_quotContext_564_ = lean_ctor_get(v_a_558_, 1);
v_currMacroScope_565_ = lean_ctor_get(v_a_558_, 2);
v_ref_566_ = lean_ctor_get(v_a_558_, 5);
v___x_567_ = 0;
v___x_568_ = l_Lean_SourceInfo_fromRef(v_ref_566_, v___x_567_);
v___x_569_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__5));
v___x_570_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__6));
lean_inc_n(v___x_568_, 31);
v___x_571_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_571_, 0, v___x_568_);
lean_ctor_set(v___x_571_, 1, v___x_569_);
v___x_572_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__8));
v___x_573_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__10));
v___x_574_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__11));
v___x_575_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_575_, 0, v___x_568_);
lean_ctor_set(v___x_575_, 1, v___x_574_);
v___x_576_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__13));
v___x_577_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__15));
v___x_578_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__16));
v___x_579_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__17));
v___x_580_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_580_, 0, v___x_568_);
lean_ctor_set(v___x_580_, 1, v___x_578_);
v___x_581_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__20));
v___x_582_ = lean_obj_once(&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__22, &l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__22_once, _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__22);
v___x_583_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__27));
lean_inc_n(v_currMacroScope_565_, 2);
lean_inc_n(v_quotContext_564_, 2);
v___x_584_ = l_Lean_addMacroScope(v_quotContext_564_, v___x_583_, v_currMacroScope_565_);
v___x_585_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__31));
v___x_586_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_586_, 0, v___x_568_);
lean_ctor_set(v___x_586_, 1, v___x_582_);
lean_ctor_set(v___x_586_, 2, v___x_584_);
lean_ctor_set(v___x_586_, 3, v___x_585_);
v___x_587_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__33));
v___x_588_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__34));
v___x_589_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_589_, 0, v___x_568_);
lean_ctor_set(v___x_589_, 1, v___x_588_);
v___x_590_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__36));
v___x_591_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__37));
v___x_592_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_592_, 0, v___x_568_);
lean_ctor_set(v___x_592_, 1, v___x_591_);
v___x_593_ = l_Lean_Syntax_node1(v___x_568_, v___x_590_, v___x_592_);
v___x_594_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__38));
v___x_595_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_595_, 0, v___x_568_);
lean_ctor_set(v___x_595_, 1, v___x_594_);
v___x_596_ = l_Lean_Syntax_node3(v___x_568_, v___x_587_, v___x_589_, v___x_593_, v___x_595_);
v___x_597_ = l_Lean_Syntax_node1(v___x_568_, v___x_572_, v___x_596_);
lean_inc(v___x_597_);
v___x_598_ = l_Lean_Syntax_node2(v___x_568_, v___x_581_, v___x_586_, v___x_597_);
lean_inc_ref(v___x_580_);
v___x_599_ = l_Lean_Syntax_node2(v___x_568_, v___x_579_, v___x_580_, v___x_598_);
v___x_600_ = l_Lean_Syntax_node1(v___x_568_, v___x_572_, v___x_599_);
v___x_601_ = l_Lean_Syntax_node1(v___x_568_, v___x_577_, v___x_600_);
v___x_602_ = l_Lean_Syntax_node1(v___x_568_, v___x_576_, v___x_601_);
lean_inc_ref_n(v___x_575_, 2);
v___x_603_ = l_Lean_Syntax_node2(v___x_568_, v___x_573_, v___x_575_, v___x_602_);
v___x_604_ = lean_obj_once(&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__40, &l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__40_once, _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__40);
v___x_605_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__42));
v___x_606_ = l_Lean_addMacroScope(v_quotContext_564_, v___x_605_, v_currMacroScope_565_);
v___x_607_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__45));
v___x_608_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_608_, 0, v___x_568_);
lean_ctor_set(v___x_608_, 1, v___x_604_);
lean_ctor_set(v___x_608_, 2, v___x_606_);
lean_ctor_set(v___x_608_, 3, v___x_607_);
v___x_609_ = l_Lean_Syntax_node2(v___x_568_, v___x_581_, v___x_608_, v___x_597_);
v___x_610_ = l_Lean_Syntax_node2(v___x_568_, v___x_579_, v___x_580_, v___x_609_);
v___x_611_ = l_Lean_Syntax_node1(v___x_568_, v___x_572_, v___x_610_);
v___x_612_ = l_Lean_Syntax_node1(v___x_568_, v___x_577_, v___x_611_);
v___x_613_ = l_Lean_Syntax_node1(v___x_568_, v___x_576_, v___x_612_);
v___x_614_ = l_Lean_Syntax_node2(v___x_568_, v___x_573_, v___x_575_, v___x_613_);
v___x_615_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__46));
v___x_616_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__47));
v___x_617_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_617_, 0, v___x_568_);
lean_ctor_set(v___x_617_, 1, v___x_615_);
v___x_618_ = lean_obj_once(&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48, &l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48_once, _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48);
v___x_619_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_619_, 0, v___x_568_);
lean_ctor_set(v___x_619_, 1, v___x_572_);
lean_ctor_set(v___x_619_, 2, v___x_618_);
v___x_620_ = l_Lean_Syntax_node2(v___x_568_, v___x_616_, v___x_617_, v___x_619_);
v___x_621_ = l_Lean_Syntax_node1(v___x_568_, v___x_572_, v___x_620_);
v___x_622_ = l_Lean_Syntax_node1(v___x_568_, v___x_577_, v___x_621_);
v___x_623_ = l_Lean_Syntax_node1(v___x_568_, v___x_576_, v___x_622_);
v___x_624_ = l_Lean_Syntax_node2(v___x_568_, v___x_573_, v___x_575_, v___x_623_);
v___x_625_ = l_Lean_Syntax_node3(v___x_568_, v___x_572_, v___x_603_, v___x_614_, v___x_624_);
v___x_626_ = l_Lean_Syntax_node2(v___x_568_, v___x_570_, v___x_571_, v___x_625_);
v___x_627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
lean_ctor_set(v___x_627_, 1, v_a_559_);
return v___x_627_;
}
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___boxed(lean_object* v_x_628_, lean_object* v_a_629_, lean_object* v_a_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1(v_x_628_, v_a_629_, v_a_630_);
lean_dec_ref(v_a_629_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySteps___redArg(lean_object* v_it_632_){
_start:
{
lean_inc(v_it_632_);
return v_it_632_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySteps___redArg___boxed(lean_object* v_it_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Std_Iter_finitelyManySteps___redArg(v_it_633_);
lean_dec(v_it_633_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySteps(lean_object* v_00_u03b1_635_, lean_object* v_00_u03b2_636_, lean_object* v_inst_637_, lean_object* v_inst_638_, lean_object* v_it_639_){
_start:
{
lean_inc(v_it_639_);
return v_it_639_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySteps___boxed(lean_object* v_00_u03b1_640_, lean_object* v_00_u03b2_641_, lean_object* v_inst_642_, lean_object* v_inst_643_, lean_object* v_it_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_Std_Iter_finitelyManySteps(v_00_u03b1_640_, v_00_u03b2_641_, v_inst_642_, v_inst_643_, v_it_644_);
lean_dec(v_it_644_);
lean_dec(v_inst_642_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySteps_x21___redArg(lean_object* v_it_646_){
_start:
{
lean_inc(v_it_646_);
return v_it_646_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySteps_x21___redArg___boxed(lean_object* v_it_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l_Std_Iter_finitelyManySteps_x21___redArg(v_it_647_);
lean_dec(v_it_647_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySteps_x21(lean_object* v_00_u03b1_649_, lean_object* v_00_u03b2_650_, lean_object* v_inst_651_, lean_object* v_it_652_){
_start:
{
lean_inc(v_it_652_);
return v_it_652_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySteps_x21___boxed(lean_object* v_00_u03b1_653_, lean_object* v_00_u03b2_654_, lean_object* v_inst_655_, lean_object* v_it_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_Std_Iter_finitelyManySteps_x21(v_00_u03b1_653_, v_00_u03b2_654_, v_inst_655_, v_it_656_);
lean_dec(v_it_656_);
lean_dec(v_inst_655_);
return v_res_657_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__1(void){
_start:
{
lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_659_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__0));
v___x_660_ = l_String_toRawSubstring_x27(v___x_659_);
return v___x_660_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__8(void){
_start:
{
lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_680_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__7));
v___x_681_ = l_String_toRawSubstring_x27(v___x_680_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2(lean_object* v_x_699_, lean_object* v_a_700_, lean_object* v_a_701_){
_start:
{
lean_object* v___x_702_; uint8_t v___x_703_; 
v___x_702_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__1));
v___x_703_ = l_Lean_Syntax_isOfKind(v_x_699_, v___x_702_);
if (v___x_703_ == 0)
{
lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_704_ = lean_box(1);
v___x_705_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_705_, 0, v___x_704_);
lean_ctor_set(v___x_705_, 1, v_a_701_);
return v___x_705_;
}
else
{
lean_object* v_quotContext_706_; lean_object* v_currMacroScope_707_; lean_object* v_ref_708_; uint8_t v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v_quotContext_706_ = lean_ctor_get(v_a_700_, 1);
v_currMacroScope_707_ = lean_ctor_get(v_a_700_, 2);
v_ref_708_ = lean_ctor_get(v_a_700_, 5);
v___x_709_ = 0;
v___x_710_ = l_Lean_SourceInfo_fromRef(v_ref_708_, v___x_709_);
v___x_711_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__5));
v___x_712_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__6));
lean_inc_n(v___x_710_, 31);
v___x_713_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_713_, 0, v___x_710_);
lean_ctor_set(v___x_713_, 1, v___x_711_);
v___x_714_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__8));
v___x_715_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__10));
v___x_716_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__11));
v___x_717_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_717_, 0, v___x_710_);
lean_ctor_set(v___x_717_, 1, v___x_716_);
v___x_718_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__13));
v___x_719_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__15));
v___x_720_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__16));
v___x_721_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__17));
v___x_722_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_722_, 0, v___x_710_);
lean_ctor_set(v___x_722_, 1, v___x_720_);
v___x_723_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__20));
v___x_724_ = lean_obj_once(&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__1, &l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__1_once, _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__1);
v___x_725_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__3));
lean_inc_n(v_currMacroScope_707_, 2);
lean_inc_n(v_quotContext_706_, 2);
v___x_726_ = l_Lean_addMacroScope(v_quotContext_706_, v___x_725_, v_currMacroScope_707_);
v___x_727_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__6));
v___x_728_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_728_, 0, v___x_710_);
lean_ctor_set(v___x_728_, 1, v___x_724_);
lean_ctor_set(v___x_728_, 2, v___x_726_);
lean_ctor_set(v___x_728_, 3, v___x_727_);
v___x_729_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__33));
v___x_730_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__34));
v___x_731_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_731_, 0, v___x_710_);
lean_ctor_set(v___x_731_, 1, v___x_730_);
v___x_732_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__36));
v___x_733_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__37));
v___x_734_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_734_, 0, v___x_710_);
lean_ctor_set(v___x_734_, 1, v___x_733_);
v___x_735_ = l_Lean_Syntax_node1(v___x_710_, v___x_732_, v___x_734_);
v___x_736_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__38));
v___x_737_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_737_, 0, v___x_710_);
lean_ctor_set(v___x_737_, 1, v___x_736_);
v___x_738_ = l_Lean_Syntax_node3(v___x_710_, v___x_729_, v___x_731_, v___x_735_, v___x_737_);
v___x_739_ = l_Lean_Syntax_node1(v___x_710_, v___x_714_, v___x_738_);
lean_inc(v___x_739_);
v___x_740_ = l_Lean_Syntax_node2(v___x_710_, v___x_723_, v___x_728_, v___x_739_);
lean_inc_ref(v___x_722_);
v___x_741_ = l_Lean_Syntax_node2(v___x_710_, v___x_721_, v___x_722_, v___x_740_);
v___x_742_ = l_Lean_Syntax_node1(v___x_710_, v___x_714_, v___x_741_);
v___x_743_ = l_Lean_Syntax_node1(v___x_710_, v___x_719_, v___x_742_);
v___x_744_ = l_Lean_Syntax_node1(v___x_710_, v___x_718_, v___x_743_);
lean_inc_ref_n(v___x_717_, 2);
v___x_745_ = l_Lean_Syntax_node2(v___x_710_, v___x_715_, v___x_717_, v___x_744_);
v___x_746_ = lean_obj_once(&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__8, &l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__8_once, _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__8);
v___x_747_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__9));
v___x_748_ = l_Lean_addMacroScope(v_quotContext_706_, v___x_747_, v_currMacroScope_707_);
v___x_749_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__12));
v___x_750_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_750_, 0, v___x_710_);
lean_ctor_set(v___x_750_, 1, v___x_746_);
lean_ctor_set(v___x_750_, 2, v___x_748_);
lean_ctor_set(v___x_750_, 3, v___x_749_);
v___x_751_ = l_Lean_Syntax_node2(v___x_710_, v___x_723_, v___x_750_, v___x_739_);
v___x_752_ = l_Lean_Syntax_node2(v___x_710_, v___x_721_, v___x_722_, v___x_751_);
v___x_753_ = l_Lean_Syntax_node1(v___x_710_, v___x_714_, v___x_752_);
v___x_754_ = l_Lean_Syntax_node1(v___x_710_, v___x_719_, v___x_753_);
v___x_755_ = l_Lean_Syntax_node1(v___x_710_, v___x_718_, v___x_754_);
v___x_756_ = l_Lean_Syntax_node2(v___x_710_, v___x_715_, v___x_717_, v___x_755_);
v___x_757_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__46));
v___x_758_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__47));
v___x_759_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_759_, 0, v___x_710_);
lean_ctor_set(v___x_759_, 1, v___x_757_);
v___x_760_ = lean_obj_once(&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48, &l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48_once, _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48);
v___x_761_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_761_, 0, v___x_710_);
lean_ctor_set(v___x_761_, 1, v___x_714_);
lean_ctor_set(v___x_761_, 2, v___x_760_);
v___x_762_ = l_Lean_Syntax_node2(v___x_710_, v___x_758_, v___x_759_, v___x_761_);
v___x_763_ = l_Lean_Syntax_node1(v___x_710_, v___x_714_, v___x_762_);
v___x_764_ = l_Lean_Syntax_node1(v___x_710_, v___x_719_, v___x_763_);
v___x_765_ = l_Lean_Syntax_node1(v___x_710_, v___x_718_, v___x_764_);
v___x_766_ = l_Lean_Syntax_node2(v___x_710_, v___x_715_, v___x_717_, v___x_765_);
v___x_767_ = l_Lean_Syntax_node3(v___x_710_, v___x_714_, v___x_745_, v___x_756_, v___x_766_);
v___x_768_ = l_Lean_Syntax_node2(v___x_710_, v___x_712_, v___x_713_, v___x_767_);
v___x_769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_769_, 0, v___x_768_);
lean_ctor_set(v___x_769_, 1, v_a_701_);
return v___x_769_;
}
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___boxed(lean_object* v_x_770_, lean_object* v_a_771_, lean_object* v_a_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2(v_x_770_, v_a_771_, v_a_772_);
lean_dec_ref(v_a_771_);
return v_res_773_;
}
}
lean_object* l_Std_IterM_TerminationMeasures_instWellFoundedRelationProductive___redArg(){
_start:
{
lean_object* v___x_775_; 
v___x_775_ = lean_box(0);
return v___x_775_;
}
}
LEAN_EXPORT void l_Std_IterM_TerminationMeasures_instWellFoundedRelationProductive___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_776_;
v_res_776_ = l_Std_IterM_TerminationMeasures_instWellFoundedRelationProductive___redArg();
stack->m_obj
 = v_res_776_;
}
LEAN_EXPORT lean_object* l_Std_IterM_TerminationMeasures_instWellFoundedRelationProductive___redArg___boxed(lean_object* v___dummy_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_Std_IterM_TerminationMeasures_instWellFoundedRelationProductive___redArg();
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_TerminationMeasures_instWellFoundedRelationProductive(lean_object* v_00_u03b1_779_, lean_object* v_m_780_, lean_object* v_00_u03b2_781_, lean_object* v_inst_782_, lean_object* v_inst_783_){
_start:
{
lean_object* v___x_784_; 
v___x_784_ = lean_box(0);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_TerminationMeasures_instWellFoundedRelationProductive___boxed(lean_object* v_00_u03b1_785_, lean_object* v_m_786_, lean_object* v_00_u03b2_787_, lean_object* v_inst_788_, lean_object* v_inst_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l_Std_IterM_TerminationMeasures_instWellFoundedRelationProductive(v_00_u03b1_785_, v_m_786_, v_00_u03b2_787_, v_inst_788_, v_inst_789_);
lean_dec(v_inst_788_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySkips___redArg(lean_object* v_it_791_){
_start:
{
lean_inc(v_it_791_);
return v_it_791_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySkips___redArg___boxed(lean_object* v_it_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l_Std_IterM_finitelyManySkips___redArg(v_it_792_);
lean_dec(v_it_792_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySkips(lean_object* v_00_u03b1_794_, lean_object* v_m_795_, lean_object* v_00_u03b2_796_, lean_object* v_inst_797_, lean_object* v_inst_798_, lean_object* v_it_799_){
_start:
{
lean_inc(v_it_799_);
return v_it_799_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySkips___boxed(lean_object* v_00_u03b1_800_, lean_object* v_m_801_, lean_object* v_00_u03b2_802_, lean_object* v_inst_803_, lean_object* v_inst_804_, lean_object* v_it_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Std_IterM_finitelyManySkips(v_00_u03b1_800_, v_m_801_, v_00_u03b2_802_, v_inst_803_, v_inst_804_, v_it_805_);
lean_dec(v_it_805_);
lean_dec(v_inst_803_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySkips_x21___redArg(lean_object* v_it_807_){
_start:
{
lean_inc(v_it_807_);
return v_it_807_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySkips_x21___redArg___boxed(lean_object* v_it_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_Std_IterM_finitelyManySkips_x21___redArg(v_it_808_);
lean_dec(v_it_808_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySkips_x21(lean_object* v_00_u03b1_810_, lean_object* v_m_811_, lean_object* v_00_u03b2_812_, lean_object* v_inst_813_, lean_object* v_it_814_){
_start:
{
lean_inc(v_it_814_);
return v_it_814_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySkips_x21___boxed(lean_object* v_00_u03b1_815_, lean_object* v_m_816_, lean_object* v_00_u03b2_817_, lean_object* v_inst_818_, lean_object* v_it_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l_Std_IterM_finitelyManySkips_x21(v_00_u03b1_815_, v_m_816_, v_00_u03b2_817_, v_inst_818_, v_it_819_);
lean_dec(v_it_819_);
lean_dec(v_inst_818_);
return v_res_820_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__1(void){
_start:
{
lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_822_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__0));
v___x_823_ = l_String_toRawSubstring_x27(v___x_822_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3(lean_object* v_x_842_, lean_object* v_a_843_, lean_object* v_a_844_){
_start:
{
lean_object* v___x_845_; uint8_t v___x_846_; 
v___x_845_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__1));
v___x_846_ = l_Lean_Syntax_isOfKind(v_x_842_, v___x_845_);
if (v___x_846_ == 0)
{
lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_847_ = lean_box(1);
v___x_848_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_848_, 0, v___x_847_);
lean_ctor_set(v___x_848_, 1, v_a_844_);
return v___x_848_;
}
else
{
lean_object* v_quotContext_849_; lean_object* v_currMacroScope_850_; lean_object* v_ref_851_; uint8_t v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
v_quotContext_849_ = lean_ctor_get(v_a_843_, 1);
v_currMacroScope_850_ = lean_ctor_get(v_a_843_, 2);
v_ref_851_ = lean_ctor_get(v_a_843_, 5);
v___x_852_ = 0;
v___x_853_ = l_Lean_SourceInfo_fromRef(v_ref_851_, v___x_852_);
v___x_854_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__5));
v___x_855_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__6));
lean_inc_n(v___x_853_, 24);
v___x_856_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_856_, 0, v___x_853_);
lean_ctor_set(v___x_856_, 1, v___x_854_);
v___x_857_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__8));
v___x_858_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__10));
v___x_859_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__11));
v___x_860_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_860_, 0, v___x_853_);
lean_ctor_set(v___x_860_, 1, v___x_859_);
v___x_861_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__13));
v___x_862_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__15));
v___x_863_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__16));
v___x_864_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__17));
v___x_865_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_865_, 0, v___x_853_);
lean_ctor_set(v___x_865_, 1, v___x_863_);
v___x_866_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__20));
v___x_867_ = lean_obj_once(&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__1, &l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__1_once, _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__1);
v___x_868_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__3));
lean_inc(v_currMacroScope_850_);
lean_inc(v_quotContext_849_);
v___x_869_ = l_Lean_addMacroScope(v_quotContext_849_, v___x_868_, v_currMacroScope_850_);
v___x_870_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__6));
v___x_871_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_871_, 0, v___x_853_);
lean_ctor_set(v___x_871_, 1, v___x_867_);
lean_ctor_set(v___x_871_, 2, v___x_869_);
lean_ctor_set(v___x_871_, 3, v___x_870_);
v___x_872_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__33));
v___x_873_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__34));
v___x_874_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_874_, 0, v___x_853_);
lean_ctor_set(v___x_874_, 1, v___x_873_);
v___x_875_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__36));
v___x_876_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__37));
v___x_877_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_877_, 0, v___x_853_);
lean_ctor_set(v___x_877_, 1, v___x_876_);
v___x_878_ = l_Lean_Syntax_node1(v___x_853_, v___x_875_, v___x_877_);
v___x_879_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__38));
v___x_880_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_880_, 0, v___x_853_);
lean_ctor_set(v___x_880_, 1, v___x_879_);
v___x_881_ = l_Lean_Syntax_node3(v___x_853_, v___x_872_, v___x_874_, v___x_878_, v___x_880_);
v___x_882_ = l_Lean_Syntax_node1(v___x_853_, v___x_857_, v___x_881_);
v___x_883_ = l_Lean_Syntax_node2(v___x_853_, v___x_866_, v___x_871_, v___x_882_);
v___x_884_ = l_Lean_Syntax_node2(v___x_853_, v___x_864_, v___x_865_, v___x_883_);
v___x_885_ = l_Lean_Syntax_node1(v___x_853_, v___x_857_, v___x_884_);
v___x_886_ = l_Lean_Syntax_node1(v___x_853_, v___x_862_, v___x_885_);
v___x_887_ = l_Lean_Syntax_node1(v___x_853_, v___x_861_, v___x_886_);
lean_inc_ref(v___x_860_);
v___x_888_ = l_Lean_Syntax_node2(v___x_853_, v___x_858_, v___x_860_, v___x_887_);
v___x_889_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__46));
v___x_890_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__47));
v___x_891_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_891_, 0, v___x_853_);
lean_ctor_set(v___x_891_, 1, v___x_889_);
v___x_892_ = lean_obj_once(&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48, &l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48_once, _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48);
v___x_893_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_893_, 0, v___x_853_);
lean_ctor_set(v___x_893_, 1, v___x_857_);
lean_ctor_set(v___x_893_, 2, v___x_892_);
v___x_894_ = l_Lean_Syntax_node2(v___x_853_, v___x_890_, v___x_891_, v___x_893_);
v___x_895_ = l_Lean_Syntax_node1(v___x_853_, v___x_857_, v___x_894_);
v___x_896_ = l_Lean_Syntax_node1(v___x_853_, v___x_862_, v___x_895_);
v___x_897_ = l_Lean_Syntax_node1(v___x_853_, v___x_861_, v___x_896_);
v___x_898_ = l_Lean_Syntax_node2(v___x_853_, v___x_858_, v___x_860_, v___x_897_);
v___x_899_ = l_Lean_Syntax_node2(v___x_853_, v___x_857_, v___x_888_, v___x_898_);
v___x_900_ = l_Lean_Syntax_node2(v___x_853_, v___x_855_, v___x_856_, v___x_899_);
v___x_901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_900_);
lean_ctor_set(v___x_901_, 1, v_a_844_);
return v___x_901_;
}
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___boxed(lean_object* v_x_902_, lean_object* v_a_903_, lean_object* v_a_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3(v_x_902_, v_a_903_, v_a_904_);
lean_dec_ref(v_a_903_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySkips___redArg(lean_object* v_it_906_){
_start:
{
lean_inc(v_it_906_);
return v_it_906_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySkips___redArg___boxed(lean_object* v_it_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l_Std_Iter_finitelyManySkips___redArg(v_it_907_);
lean_dec(v_it_907_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySkips(lean_object* v_00_u03b1_909_, lean_object* v_00_u03b2_910_, lean_object* v_inst_911_, lean_object* v_inst_912_, lean_object* v_it_913_){
_start:
{
lean_inc(v_it_913_);
return v_it_913_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySkips___boxed(lean_object* v_00_u03b1_914_, lean_object* v_00_u03b2_915_, lean_object* v_inst_916_, lean_object* v_inst_917_, lean_object* v_it_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_Std_Iter_finitelyManySkips(v_00_u03b1_914_, v_00_u03b2_915_, v_inst_916_, v_inst_917_, v_it_918_);
lean_dec(v_it_918_);
lean_dec(v_inst_916_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySkips_x21___redArg(lean_object* v_it_920_){
_start:
{
lean_inc(v_it_920_);
return v_it_920_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySkips_x21___redArg___boxed(lean_object* v_it_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_Std_Iter_finitelyManySkips_x21___redArg(v_it_921_);
lean_dec(v_it_921_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySkips_x21(lean_object* v_00_u03b1_923_, lean_object* v_00_u03b2_924_, lean_object* v_inst_925_, lean_object* v_it_926_){
_start:
{
lean_inc(v_it_926_);
return v_it_926_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySkips_x21___boxed(lean_object* v_00_u03b1_927_, lean_object* v_00_u03b2_928_, lean_object* v_inst_929_, lean_object* v_it_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l_Std_Iter_finitelyManySkips_x21(v_00_u03b1_927_, v_00_u03b2_928_, v_inst_929_, v_it_930_);
lean_dec(v_it_930_);
lean_dec(v_inst_929_);
return v_res_931_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__1(void){
_start:
{
lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_933_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__0));
v___x_934_ = l_String_toRawSubstring_x27(v___x_933_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4(lean_object* v_x_952_, lean_object* v_a_953_, lean_object* v_a_954_){
_start:
{
lean_object* v___x_955_; uint8_t v___x_956_; 
v___x_955_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__1));
v___x_956_ = l_Lean_Syntax_isOfKind(v_x_952_, v___x_955_);
if (v___x_956_ == 0)
{
lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_957_ = lean_box(1);
v___x_958_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_958_, 0, v___x_957_);
lean_ctor_set(v___x_958_, 1, v_a_954_);
return v___x_958_;
}
else
{
lean_object* v_quotContext_959_; lean_object* v_currMacroScope_960_; lean_object* v_ref_961_; uint8_t v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v_quotContext_959_ = lean_ctor_get(v_a_953_, 1);
v_currMacroScope_960_ = lean_ctor_get(v_a_953_, 2);
v_ref_961_ = lean_ctor_get(v_a_953_, 5);
v___x_962_ = 0;
v___x_963_ = l_Lean_SourceInfo_fromRef(v_ref_961_, v___x_962_);
v___x_964_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__5));
v___x_965_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__6));
lean_inc_n(v___x_963_, 24);
v___x_966_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_963_);
lean_ctor_set(v___x_966_, 1, v___x_964_);
v___x_967_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__8));
v___x_968_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__10));
v___x_969_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__11));
v___x_970_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_970_, 0, v___x_963_);
lean_ctor_set(v___x_970_, 1, v___x_969_);
v___x_971_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__13));
v___x_972_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__15));
v___x_973_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__16));
v___x_974_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__17));
v___x_975_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_975_, 0, v___x_963_);
lean_ctor_set(v___x_975_, 1, v___x_973_);
v___x_976_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__20));
v___x_977_ = lean_obj_once(&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__1, &l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__1_once, _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__1);
v___x_978_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__2));
lean_inc(v_currMacroScope_960_);
lean_inc(v_quotContext_959_);
v___x_979_ = l_Lean_addMacroScope(v_quotContext_959_, v___x_978_, v_currMacroScope_960_);
v___x_980_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__5));
v___x_981_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_981_, 0, v___x_963_);
lean_ctor_set(v___x_981_, 1, v___x_977_);
lean_ctor_set(v___x_981_, 2, v___x_979_);
lean_ctor_set(v___x_981_, 3, v___x_980_);
v___x_982_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__33));
v___x_983_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__34));
v___x_984_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_963_);
lean_ctor_set(v___x_984_, 1, v___x_983_);
v___x_985_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__36));
v___x_986_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__37));
v___x_987_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_987_, 0, v___x_963_);
lean_ctor_set(v___x_987_, 1, v___x_986_);
v___x_988_ = l_Lean_Syntax_node1(v___x_963_, v___x_985_, v___x_987_);
v___x_989_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__38));
v___x_990_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_990_, 0, v___x_963_);
lean_ctor_set(v___x_990_, 1, v___x_989_);
v___x_991_ = l_Lean_Syntax_node3(v___x_963_, v___x_982_, v___x_984_, v___x_988_, v___x_990_);
v___x_992_ = l_Lean_Syntax_node1(v___x_963_, v___x_967_, v___x_991_);
v___x_993_ = l_Lean_Syntax_node2(v___x_963_, v___x_976_, v___x_981_, v___x_992_);
v___x_994_ = l_Lean_Syntax_node2(v___x_963_, v___x_974_, v___x_975_, v___x_993_);
v___x_995_ = l_Lean_Syntax_node1(v___x_963_, v___x_967_, v___x_994_);
v___x_996_ = l_Lean_Syntax_node1(v___x_963_, v___x_972_, v___x_995_);
v___x_997_ = l_Lean_Syntax_node1(v___x_963_, v___x_971_, v___x_996_);
lean_inc_ref(v___x_970_);
v___x_998_ = l_Lean_Syntax_node2(v___x_963_, v___x_968_, v___x_970_, v___x_997_);
v___x_999_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__46));
v___x_1000_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__47));
v___x_1001_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_963_);
lean_ctor_set(v___x_1001_, 1, v___x_999_);
v___x_1002_ = lean_obj_once(&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48, &l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48_once, _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48);
v___x_1003_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1003_, 0, v___x_963_);
lean_ctor_set(v___x_1003_, 1, v___x_967_);
lean_ctor_set(v___x_1003_, 2, v___x_1002_);
v___x_1004_ = l_Lean_Syntax_node2(v___x_963_, v___x_1000_, v___x_1001_, v___x_1003_);
v___x_1005_ = l_Lean_Syntax_node1(v___x_963_, v___x_967_, v___x_1004_);
v___x_1006_ = l_Lean_Syntax_node1(v___x_963_, v___x_972_, v___x_1005_);
v___x_1007_ = l_Lean_Syntax_node1(v___x_963_, v___x_971_, v___x_1006_);
v___x_1008_ = l_Lean_Syntax_node2(v___x_963_, v___x_968_, v___x_970_, v___x_1007_);
v___x_1009_ = l_Lean_Syntax_node2(v___x_963_, v___x_967_, v___x_998_, v___x_1008_);
v___x_1010_ = l_Lean_Syntax_node2(v___x_963_, v___x_965_, v___x_966_, v___x_1009_);
v___x_1011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1010_);
lean_ctor_set(v___x_1011_, 1, v_a_954_);
return v___x_1011_;
}
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___boxed(lean_object* v_x_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4(v_x_1012_, v_a_1013_, v_a_1014_);
lean_dec_ref(v_a_1013_);
return v_res_1015_;
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
