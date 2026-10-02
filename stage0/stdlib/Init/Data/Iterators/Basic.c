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
LEAN_EXPORT lean_object* l_Std_IterStep_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterStep_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterStep_ctorIdx(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterStep_ctorIdx___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Basic_0__Std_IterStep_successor_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Basic_0__Std_IterStep_successor_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_IterStep_ctorIdx___redArg(lean_object* v_x_47_){
_start:
{
switch(lean_obj_tag(v_x_47_))
{
case 0:
{
lean_object* v___x_48_; 
v___x_48_ = lean_unsigned_to_nat(0u);
return v___x_48_;
}
case 1:
{
lean_object* v___x_49_; 
v___x_49_ = lean_unsigned_to_nat(1u);
return v___x_49_;
}
default: 
{
lean_object* v___x_50_; 
v___x_50_ = lean_unsigned_to_nat(2u);
return v___x_50_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_ctorIdx___redArg___boxed(lean_object* v_x_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Std_IterStep_ctorIdx___redArg(v_x_51_);
lean_dec(v_x_51_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_ctorIdx(lean_object* v_00_u03b1_53_, lean_object* v_00_u03b2_54_, lean_object* v_x_55_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l_Std_IterStep_ctorIdx___redArg(v_x_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_ctorIdx___boxed(lean_object* v_00_u03b1_57_, lean_object* v_00_u03b2_58_, lean_object* v_x_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Std_IterStep_ctorIdx(v_00_u03b1_57_, v_00_u03b2_58_, v_x_59_);
lean_dec(v_x_59_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_ctorElim___redArg(lean_object* v_t_61_, lean_object* v_k_62_){
_start:
{
switch(lean_obj_tag(v_t_61_))
{
case 0:
{
lean_object* v_it_63_; lean_object* v_out_64_; lean_object* v___x_65_; 
v_it_63_ = lean_ctor_get(v_t_61_, 0);
lean_inc(v_it_63_);
v_out_64_ = lean_ctor_get(v_t_61_, 1);
lean_inc(v_out_64_);
lean_dec_ref_known(v_t_61_, 2);
v___x_65_ = lean_apply_2(v_k_62_, v_it_63_, v_out_64_);
return v___x_65_;
}
case 1:
{
lean_object* v_it_66_; lean_object* v___x_67_; 
v_it_66_ = lean_ctor_get(v_t_61_, 0);
lean_inc(v_it_66_);
lean_dec_ref_known(v_t_61_, 1);
v___x_67_ = lean_apply_1(v_k_62_, v_it_66_);
return v___x_67_;
}
default: 
{
return v_k_62_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_ctorElim(lean_object* v_00_u03b1_68_, lean_object* v_00_u03b2_69_, lean_object* v_motive_70_, lean_object* v_ctorIdx_71_, lean_object* v_t_72_, lean_object* v_h_73_, lean_object* v_k_74_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = l_Std_IterStep_ctorElim___redArg(v_t_72_, v_k_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_ctorElim___boxed(lean_object* v_00_u03b1_76_, lean_object* v_00_u03b2_77_, lean_object* v_motive_78_, lean_object* v_ctorIdx_79_, lean_object* v_t_80_, lean_object* v_h_81_, lean_object* v_k_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_Std_IterStep_ctorElim(v_00_u03b1_76_, v_00_u03b2_77_, v_motive_78_, v_ctorIdx_79_, v_t_80_, v_h_81_, v_k_82_);
lean_dec(v_ctorIdx_79_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_yield_elim___redArg(lean_object* v_t_84_, lean_object* v_yield_85_){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = l_Std_IterStep_ctorElim___redArg(v_t_84_, v_yield_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_yield_elim(lean_object* v_00_u03b1_87_, lean_object* v_00_u03b2_88_, lean_object* v_motive_89_, lean_object* v_t_90_, lean_object* v_h_91_, lean_object* v_yield_92_){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = l_Std_IterStep_ctorElim___redArg(v_t_90_, v_yield_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_skip_elim___redArg(lean_object* v_t_94_, lean_object* v_skip_95_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = l_Std_IterStep_ctorElim___redArg(v_t_94_, v_skip_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_skip_elim(lean_object* v_00_u03b1_97_, lean_object* v_00_u03b2_98_, lean_object* v_motive_99_, lean_object* v_t_100_, lean_object* v_h_101_, lean_object* v_skip_102_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = l_Std_IterStep_ctorElim___redArg(v_t_100_, v_skip_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_done_elim___redArg(lean_object* v_t_104_, lean_object* v_done_105_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = l_Std_IterStep_ctorElim___redArg(v_t_104_, v_done_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_done_elim(lean_object* v_00_u03b1_107_, lean_object* v_00_u03b2_108_, lean_object* v_motive_109_, lean_object* v_t_110_, lean_object* v_h_111_, lean_object* v_done_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = l_Std_IterStep_ctorElim___redArg(v_t_110_, v_done_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_successor___redArg(lean_object* v_x_114_){
_start:
{
switch(lean_obj_tag(v_x_114_))
{
case 0:
{
lean_object* v_it_115_; lean_object* v___x_116_; 
v_it_115_ = lean_ctor_get(v_x_114_, 0);
lean_inc(v_it_115_);
lean_dec_ref_known(v_x_114_, 2);
v___x_116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_116_, 0, v_it_115_);
return v___x_116_;
}
case 1:
{
lean_object* v_it_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_124_; 
v_it_117_ = lean_ctor_get(v_x_114_, 0);
v_isSharedCheck_124_ = !lean_is_exclusive(v_x_114_);
if (v_isSharedCheck_124_ == 0)
{
v___x_119_ = v_x_114_;
v_isShared_120_ = v_isSharedCheck_124_;
goto v_resetjp_118_;
}
else
{
lean_inc(v_it_117_);
lean_dec(v_x_114_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_124_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
lean_object* v___x_122_; 
if (v_isShared_120_ == 0)
{
v___x_122_ = v___x_119_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v_it_117_);
v___x_122_ = v_reuseFailAlloc_123_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
return v___x_122_;
}
}
}
default: 
{
lean_object* v___x_125_; 
v___x_125_ = lean_box(0);
return v___x_125_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_successor(lean_object* v_00_u03b1_126_, lean_object* v_00_u03b2_127_, lean_object* v_x_128_){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = l_Std_IterStep_successor___redArg(v_x_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_mapIterator___redArg(lean_object* v_f_130_, lean_object* v_x_131_){
_start:
{
switch(lean_obj_tag(v_x_131_))
{
case 0:
{
lean_object* v_it_132_; lean_object* v_out_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_141_; 
v_it_132_ = lean_ctor_get(v_x_131_, 0);
v_out_133_ = lean_ctor_get(v_x_131_, 1);
v_isSharedCheck_141_ = !lean_is_exclusive(v_x_131_);
if (v_isSharedCheck_141_ == 0)
{
v___x_135_ = v_x_131_;
v_isShared_136_ = v_isSharedCheck_141_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_out_133_);
lean_inc(v_it_132_);
lean_dec(v_x_131_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_141_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v___x_137_; lean_object* v___x_139_; 
v___x_137_ = lean_apply_1(v_f_130_, v_it_132_);
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 0, v___x_137_);
v___x_139_ = v___x_135_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v___x_137_);
lean_ctor_set(v_reuseFailAlloc_140_, 1, v_out_133_);
v___x_139_ = v_reuseFailAlloc_140_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
return v___x_139_;
}
}
}
case 1:
{
lean_object* v_it_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_150_; 
v_it_142_ = lean_ctor_get(v_x_131_, 0);
v_isSharedCheck_150_ = !lean_is_exclusive(v_x_131_);
if (v_isSharedCheck_150_ == 0)
{
v___x_144_ = v_x_131_;
v_isShared_145_ = v_isSharedCheck_150_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_it_142_);
lean_dec(v_x_131_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_150_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
lean_object* v___x_146_; lean_object* v___x_148_; 
v___x_146_ = lean_apply_1(v_f_130_, v_it_142_);
if (v_isShared_145_ == 0)
{
lean_ctor_set(v___x_144_, 0, v___x_146_);
v___x_148_ = v___x_144_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v___x_146_);
v___x_148_ = v_reuseFailAlloc_149_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
return v___x_148_;
}
}
}
default: 
{
lean_object* v___x_151_; 
lean_dec(v_f_130_);
v___x_151_ = lean_box(2);
return v___x_151_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_mapIterator(lean_object* v_00_u03b1_152_, lean_object* v_00_u03b2_153_, lean_object* v_00_u03b1_x27_154_, lean_object* v_f_155_, lean_object* v_x_156_){
_start:
{
switch(lean_obj_tag(v_x_156_))
{
case 0:
{
lean_object* v_it_157_; lean_object* v_out_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_166_; 
v_it_157_ = lean_ctor_get(v_x_156_, 0);
v_out_158_ = lean_ctor_get(v_x_156_, 1);
v_isSharedCheck_166_ = !lean_is_exclusive(v_x_156_);
if (v_isSharedCheck_166_ == 0)
{
v___x_160_ = v_x_156_;
v_isShared_161_ = v_isSharedCheck_166_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_out_158_);
lean_inc(v_it_157_);
lean_dec(v_x_156_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_166_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v___x_162_; lean_object* v___x_164_; 
v___x_162_ = lean_apply_1(v_f_155_, v_it_157_);
if (v_isShared_161_ == 0)
{
lean_ctor_set(v___x_160_, 0, v___x_162_);
v___x_164_ = v___x_160_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v___x_162_);
lean_ctor_set(v_reuseFailAlloc_165_, 1, v_out_158_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
}
case 1:
{
lean_object* v_it_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_175_; 
v_it_167_ = lean_ctor_get(v_x_156_, 0);
v_isSharedCheck_175_ = !lean_is_exclusive(v_x_156_);
if (v_isSharedCheck_175_ == 0)
{
v___x_169_ = v_x_156_;
v_isShared_170_ = v_isSharedCheck_175_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_it_167_);
lean_dec(v_x_156_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_175_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v___x_171_; lean_object* v___x_173_; 
v___x_171_ = lean_apply_1(v_f_155_, v_it_167_);
if (v_isShared_170_ == 0)
{
lean_ctor_set(v___x_169_, 0, v___x_171_);
v___x_173_ = v___x_169_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v___x_171_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
return v___x_173_;
}
}
}
default: 
{
lean_object* v___x_176_; 
lean_dec(v_f_155_);
v___x_176_ = lean_box(2);
return v___x_176_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PlausibleIterStep_yield___redArg(lean_object* v_it_x27_177_, lean_object* v_out_178_){
_start:
{
lean_object* v___x_179_; 
v___x_179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_179_, 0, v_it_x27_177_);
lean_ctor_set(v___x_179_, 1, v_out_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Std_PlausibleIterStep_yield(lean_object* v_00_u03b1_180_, lean_object* v_00_u03b2_181_, lean_object* v_IsPlausibleStep_182_, lean_object* v_it_x27_183_, lean_object* v_out_184_, lean_object* v_h_185_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_186_, 0, v_it_x27_183_);
lean_ctor_set(v___x_186_, 1, v_out_184_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Std_PlausibleIterStep_skip___redArg(lean_object* v_it_x27_187_){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_188_, 0, v_it_x27_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Std_PlausibleIterStep_skip(lean_object* v_00_u03b1_189_, lean_object* v_00_u03b2_190_, lean_object* v_IsPlausibleStep_191_, lean_object* v_it_x27_192_, lean_object* v_h_193_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_194_, 0, v_it_x27_192_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Std_PlausibleIterStep_done___redArg(){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = lean_box(2);
return v___x_196_;
}
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
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Basic_0__Std_IterStep_successor_match__1_splitter___redArg(lean_object* v_x_357_, lean_object* v_h__1_358_, lean_object* v_h__2_359_, lean_object* v_h__3_360_){
_start:
{
switch(lean_obj_tag(v_x_357_))
{
case 0:
{
lean_object* v_it_361_; lean_object* v_out_362_; lean_object* v___x_363_; 
lean_dec(v_h__3_360_);
lean_dec(v_h__2_359_);
v_it_361_ = lean_ctor_get(v_x_357_, 0);
lean_inc(v_it_361_);
v_out_362_ = lean_ctor_get(v_x_357_, 1);
lean_inc(v_out_362_);
lean_dec_ref_known(v_x_357_, 2);
v___x_363_ = lean_apply_2(v_h__1_358_, v_it_361_, v_out_362_);
return v___x_363_;
}
case 1:
{
lean_object* v_it_364_; lean_object* v___x_365_; 
lean_dec(v_h__3_360_);
lean_dec(v_h__1_358_);
v_it_364_ = lean_ctor_get(v_x_357_, 0);
lean_inc(v_it_364_);
lean_dec_ref_known(v_x_357_, 1);
v___x_365_ = lean_apply_1(v_h__2_359_, v_it_364_);
return v___x_365_;
}
default: 
{
lean_object* v___x_366_; lean_object* v___x_367_; 
lean_dec(v_h__2_359_);
lean_dec(v_h__1_358_);
v___x_366_ = lean_box(0);
v___x_367_ = lean_apply_1(v_h__3_360_, v___x_366_);
return v___x_367_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Basic_0__Std_IterStep_successor_match__1_splitter(lean_object* v_00_u03b1_368_, lean_object* v_00_u03b2_369_, lean_object* v_motive_370_, lean_object* v_x_371_, lean_object* v_h__1_372_, lean_object* v_h__2_373_, lean_object* v_h__3_374_){
_start:
{
switch(lean_obj_tag(v_x_371_))
{
case 0:
{
lean_object* v_it_375_; lean_object* v_out_376_; lean_object* v___x_377_; 
lean_dec(v_h__3_374_);
lean_dec(v_h__2_373_);
v_it_375_ = lean_ctor_get(v_x_371_, 0);
lean_inc(v_it_375_);
v_out_376_ = lean_ctor_get(v_x_371_, 1);
lean_inc(v_out_376_);
lean_dec_ref_known(v_x_371_, 2);
v___x_377_ = lean_apply_2(v_h__1_372_, v_it_375_, v_out_376_);
return v___x_377_;
}
case 1:
{
lean_object* v_it_378_; lean_object* v___x_379_; 
lean_dec(v_h__3_374_);
lean_dec(v_h__1_372_);
v_it_378_ = lean_ctor_get(v_x_371_, 0);
lean_inc(v_it_378_);
lean_dec_ref_known(v_x_371_, 1);
v___x_379_ = lean_apply_1(v_h__2_373_, v_it_378_);
return v___x_379_;
}
default: 
{
lean_object* v___x_380_; lean_object* v___x_381_; 
lean_dec(v_h__2_373_);
lean_dec(v_h__1_372_);
v___x_380_ = lean_box(0);
v___x_381_ = lean_apply_1(v_h__3_374_, v___x_380_);
return v___x_381_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iter_step___redArg(lean_object* v_inst_382_, lean_object* v_it_383_){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = lean_apply_1(v_inst_382_, v_it_383_);
switch(lean_obj_tag(v___x_384_))
{
case 0:
{
lean_object* v_it_385_; lean_object* v_out_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_393_; 
v_it_385_ = lean_ctor_get(v___x_384_, 0);
v_out_386_ = lean_ctor_get(v___x_384_, 1);
v_isSharedCheck_393_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_393_ == 0)
{
v___x_388_ = v___x_384_;
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_out_386_);
lean_inc(v_it_385_);
lean_dec(v___x_384_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_391_; 
if (v_isShared_389_ == 0)
{
v___x_391_ = v___x_388_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_it_385_);
lean_ctor_set(v_reuseFailAlloc_392_, 1, v_out_386_);
v___x_391_ = v_reuseFailAlloc_392_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
return v___x_391_;
}
}
}
case 1:
{
lean_object* v_it_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_401_; 
v_it_394_ = lean_ctor_get(v___x_384_, 0);
v_isSharedCheck_401_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_401_ == 0)
{
v___x_396_ = v___x_384_;
v_isShared_397_ = v_isSharedCheck_401_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_it_394_);
lean_dec(v___x_384_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_401_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_399_; 
if (v_isShared_397_ == 0)
{
v___x_399_ = v___x_396_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v_it_394_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
return v___x_399_;
}
}
}
default: 
{
lean_object* v___x_402_; 
v___x_402_ = lean_box(2);
return v___x_402_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iter_step(lean_object* v_00_u03b1_403_, lean_object* v_00_u03b2_404_, lean_object* v_inst_405_, lean_object* v_it_406_){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = lean_apply_1(v_inst_405_, v_it_406_);
switch(lean_obj_tag(v___x_407_))
{
case 0:
{
lean_object* v_it_408_; lean_object* v_out_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_416_; 
v_it_408_ = lean_ctor_get(v___x_407_, 0);
v_out_409_ = lean_ctor_get(v___x_407_, 1);
v_isSharedCheck_416_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_416_ == 0)
{
v___x_411_ = v___x_407_;
v_isShared_412_ = v_isSharedCheck_416_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_out_409_);
lean_inc(v_it_408_);
lean_dec(v___x_407_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_416_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_414_; 
if (v_isShared_412_ == 0)
{
v___x_414_ = v___x_411_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v_it_408_);
lean_ctor_set(v_reuseFailAlloc_415_, 1, v_out_409_);
v___x_414_ = v_reuseFailAlloc_415_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
return v___x_414_;
}
}
}
case 1:
{
lean_object* v_it_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_424_; 
v_it_417_ = lean_ctor_get(v___x_407_, 0);
v_isSharedCheck_424_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_424_ == 0)
{
v___x_419_ = v___x_407_;
v_isShared_420_ = v_isSharedCheck_424_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_it_417_);
lean_dec(v___x_407_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_424_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v___x_422_; 
if (v_isShared_420_ == 0)
{
v___x_422_ = v___x_419_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v_it_417_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
return v___x_422_;
}
}
}
default: 
{
lean_object* v___x_425_; 
v___x_425_ = lean_box(2);
return v___x_425_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_IterM_TerminationMeasures_instWellFoundedRelationFinite___redArg(){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = lean_box(0);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_TerminationMeasures_instWellFoundedRelationFinite___redArg___boxed(lean_object* v___dummy_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_Std_IterM_TerminationMeasures_instWellFoundedRelationFinite___redArg();
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_TerminationMeasures_instWellFoundedRelationFinite(lean_object* v_00_u03b1_430_, lean_object* v_m_431_, lean_object* v_00_u03b2_432_, lean_object* v_inst_433_, lean_object* v_inst_434_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = lean_box(0);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_TerminationMeasures_instWellFoundedRelationFinite___boxed(lean_object* v_00_u03b1_436_, lean_object* v_m_437_, lean_object* v_00_u03b2_438_, lean_object* v_inst_439_, lean_object* v_inst_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Std_IterM_TerminationMeasures_instWellFoundedRelationFinite(v_00_u03b1_436_, v_m_437_, v_00_u03b2_438_, v_inst_439_, v_inst_440_);
lean_dec(v_inst_439_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySteps___redArg(lean_object* v_it_442_){
_start:
{
lean_inc(v_it_442_);
return v_it_442_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySteps___redArg___boxed(lean_object* v_it_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Std_IterM_finitelyManySteps___redArg(v_it_443_);
lean_dec(v_it_443_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySteps(lean_object* v_00_u03b1_445_, lean_object* v_m_446_, lean_object* v_00_u03b2_447_, lean_object* v_inst_448_, lean_object* v_inst_449_, lean_object* v_it_450_){
_start:
{
lean_inc(v_it_450_);
return v_it_450_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySteps___boxed(lean_object* v_00_u03b1_451_, lean_object* v_m_452_, lean_object* v_00_u03b2_453_, lean_object* v_inst_454_, lean_object* v_inst_455_, lean_object* v_it_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_Std_IterM_finitelyManySteps(v_00_u03b1_451_, v_m_452_, v_00_u03b2_453_, v_inst_454_, v_inst_455_, v_it_456_);
lean_dec(v_it_456_);
lean_dec(v_inst_454_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySteps_x21___redArg(lean_object* v_it_458_){
_start:
{
lean_inc(v_it_458_);
return v_it_458_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySteps_x21___redArg___boxed(lean_object* v_it_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l_Std_IterM_finitelyManySteps_x21___redArg(v_it_459_);
lean_dec(v_it_459_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySteps_x21(lean_object* v_00_u03b1_461_, lean_object* v_m_462_, lean_object* v_00_u03b2_463_, lean_object* v_inst_464_, lean_object* v_it_465_){
_start:
{
lean_inc(v_it_465_);
return v_it_465_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySteps_x21___boxed(lean_object* v_00_u03b1_466_, lean_object* v_m_467_, lean_object* v_00_u03b2_468_, lean_object* v_inst_469_, lean_object* v_it_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_Std_IterM_finitelyManySteps_x21(v_00_u03b1_466_, v_m_467_, v_00_u03b2_468_, v_inst_469_, v_it_470_);
lean_dec(v_it_470_);
lean_dec(v_inst_469_);
return v_res_471_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__22(void){
_start:
{
lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_517_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__21));
v___x_518_ = l_String_toRawSubstring_x27(v___x_517_);
return v___x_518_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__40(void){
_start:
{
lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_554_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__39));
v___x_555_ = l_String_toRawSubstring_x27(v___x_554_);
return v___x_555_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48(void){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l_Array_mkArray0___redArg();
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1(lean_object* v_x_581_, lean_object* v_a_582_, lean_object* v_a_583_){
_start:
{
lean_object* v___x_584_; uint8_t v___x_585_; 
v___x_584_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__1));
v___x_585_ = l_Lean_Syntax_isOfKind(v_x_581_, v___x_584_);
if (v___x_585_ == 0)
{
lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_586_ = lean_box(1);
v___x_587_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_587_, 0, v___x_586_);
lean_ctor_set(v___x_587_, 1, v_a_583_);
return v___x_587_;
}
else
{
lean_object* v_quotContext_588_; lean_object* v_currMacroScope_589_; lean_object* v_ref_590_; uint8_t v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v_quotContext_588_ = lean_ctor_get(v_a_582_, 1);
v_currMacroScope_589_ = lean_ctor_get(v_a_582_, 2);
v_ref_590_ = lean_ctor_get(v_a_582_, 5);
v___x_591_ = 0;
v___x_592_ = l_Lean_SourceInfo_fromRef(v_ref_590_, v___x_591_);
v___x_593_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__5));
v___x_594_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__6));
lean_inc_n(v___x_592_, 31);
v___x_595_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_595_, 0, v___x_592_);
lean_ctor_set(v___x_595_, 1, v___x_593_);
v___x_596_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__8));
v___x_597_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__10));
v___x_598_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__11));
v___x_599_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_599_, 0, v___x_592_);
lean_ctor_set(v___x_599_, 1, v___x_598_);
v___x_600_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__13));
v___x_601_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__15));
v___x_602_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__16));
v___x_603_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__17));
v___x_604_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_604_, 0, v___x_592_);
lean_ctor_set(v___x_604_, 1, v___x_602_);
v___x_605_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__20));
v___x_606_ = lean_obj_once(&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__22, &l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__22_once, _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__22);
v___x_607_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__27));
lean_inc_n(v_currMacroScope_589_, 2);
lean_inc_n(v_quotContext_588_, 2);
v___x_608_ = l_Lean_addMacroScope(v_quotContext_588_, v___x_607_, v_currMacroScope_589_);
v___x_609_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__31));
v___x_610_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_610_, 0, v___x_592_);
lean_ctor_set(v___x_610_, 1, v___x_606_);
lean_ctor_set(v___x_610_, 2, v___x_608_);
lean_ctor_set(v___x_610_, 3, v___x_609_);
v___x_611_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__33));
v___x_612_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__34));
v___x_613_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_613_, 0, v___x_592_);
lean_ctor_set(v___x_613_, 1, v___x_612_);
v___x_614_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__36));
v___x_615_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__37));
v___x_616_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_616_, 0, v___x_592_);
lean_ctor_set(v___x_616_, 1, v___x_615_);
v___x_617_ = l_Lean_Syntax_node1(v___x_592_, v___x_614_, v___x_616_);
v___x_618_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__38));
v___x_619_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_619_, 0, v___x_592_);
lean_ctor_set(v___x_619_, 1, v___x_618_);
v___x_620_ = l_Lean_Syntax_node3(v___x_592_, v___x_611_, v___x_613_, v___x_617_, v___x_619_);
v___x_621_ = l_Lean_Syntax_node1(v___x_592_, v___x_596_, v___x_620_);
lean_inc(v___x_621_);
v___x_622_ = l_Lean_Syntax_node2(v___x_592_, v___x_605_, v___x_610_, v___x_621_);
lean_inc_ref(v___x_604_);
v___x_623_ = l_Lean_Syntax_node2(v___x_592_, v___x_603_, v___x_604_, v___x_622_);
v___x_624_ = l_Lean_Syntax_node1(v___x_592_, v___x_596_, v___x_623_);
v___x_625_ = l_Lean_Syntax_node1(v___x_592_, v___x_601_, v___x_624_);
v___x_626_ = l_Lean_Syntax_node1(v___x_592_, v___x_600_, v___x_625_);
lean_inc_ref_n(v___x_599_, 2);
v___x_627_ = l_Lean_Syntax_node2(v___x_592_, v___x_597_, v___x_599_, v___x_626_);
v___x_628_ = lean_obj_once(&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__40, &l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__40_once, _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__40);
v___x_629_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__42));
v___x_630_ = l_Lean_addMacroScope(v_quotContext_588_, v___x_629_, v_currMacroScope_589_);
v___x_631_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__45));
v___x_632_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_632_, 0, v___x_592_);
lean_ctor_set(v___x_632_, 1, v___x_628_);
lean_ctor_set(v___x_632_, 2, v___x_630_);
lean_ctor_set(v___x_632_, 3, v___x_631_);
v___x_633_ = l_Lean_Syntax_node2(v___x_592_, v___x_605_, v___x_632_, v___x_621_);
v___x_634_ = l_Lean_Syntax_node2(v___x_592_, v___x_603_, v___x_604_, v___x_633_);
v___x_635_ = l_Lean_Syntax_node1(v___x_592_, v___x_596_, v___x_634_);
v___x_636_ = l_Lean_Syntax_node1(v___x_592_, v___x_601_, v___x_635_);
v___x_637_ = l_Lean_Syntax_node1(v___x_592_, v___x_600_, v___x_636_);
v___x_638_ = l_Lean_Syntax_node2(v___x_592_, v___x_597_, v___x_599_, v___x_637_);
v___x_639_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__46));
v___x_640_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__47));
v___x_641_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_641_, 0, v___x_592_);
lean_ctor_set(v___x_641_, 1, v___x_639_);
v___x_642_ = lean_obj_once(&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48, &l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48_once, _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48);
v___x_643_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_643_, 0, v___x_592_);
lean_ctor_set(v___x_643_, 1, v___x_596_);
lean_ctor_set(v___x_643_, 2, v___x_642_);
v___x_644_ = l_Lean_Syntax_node2(v___x_592_, v___x_640_, v___x_641_, v___x_643_);
v___x_645_ = l_Lean_Syntax_node1(v___x_592_, v___x_596_, v___x_644_);
v___x_646_ = l_Lean_Syntax_node1(v___x_592_, v___x_601_, v___x_645_);
v___x_647_ = l_Lean_Syntax_node1(v___x_592_, v___x_600_, v___x_646_);
v___x_648_ = l_Lean_Syntax_node2(v___x_592_, v___x_597_, v___x_599_, v___x_647_);
v___x_649_ = l_Lean_Syntax_node3(v___x_592_, v___x_596_, v___x_627_, v___x_638_, v___x_648_);
v___x_650_ = l_Lean_Syntax_node2(v___x_592_, v___x_594_, v___x_595_, v___x_649_);
v___x_651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_651_, 0, v___x_650_);
lean_ctor_set(v___x_651_, 1, v_a_583_);
return v___x_651_;
}
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___boxed(lean_object* v_x_652_, lean_object* v_a_653_, lean_object* v_a_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1(v_x_652_, v_a_653_, v_a_654_);
lean_dec_ref(v_a_653_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySteps___redArg(lean_object* v_it_656_){
_start:
{
lean_inc(v_it_656_);
return v_it_656_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySteps___redArg___boxed(lean_object* v_it_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l_Std_Iter_finitelyManySteps___redArg(v_it_657_);
lean_dec(v_it_657_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySteps(lean_object* v_00_u03b1_659_, lean_object* v_00_u03b2_660_, lean_object* v_inst_661_, lean_object* v_inst_662_, lean_object* v_it_663_){
_start:
{
lean_inc(v_it_663_);
return v_it_663_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySteps___boxed(lean_object* v_00_u03b1_664_, lean_object* v_00_u03b2_665_, lean_object* v_inst_666_, lean_object* v_inst_667_, lean_object* v_it_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l_Std_Iter_finitelyManySteps(v_00_u03b1_664_, v_00_u03b2_665_, v_inst_666_, v_inst_667_, v_it_668_);
lean_dec(v_it_668_);
lean_dec(v_inst_666_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySteps_x21___redArg(lean_object* v_it_670_){
_start:
{
lean_inc(v_it_670_);
return v_it_670_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySteps_x21___redArg___boxed(lean_object* v_it_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l_Std_Iter_finitelyManySteps_x21___redArg(v_it_671_);
lean_dec(v_it_671_);
return v_res_672_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySteps_x21(lean_object* v_00_u03b1_673_, lean_object* v_00_u03b2_674_, lean_object* v_inst_675_, lean_object* v_it_676_){
_start:
{
lean_inc(v_it_676_);
return v_it_676_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySteps_x21___boxed(lean_object* v_00_u03b1_677_, lean_object* v_00_u03b2_678_, lean_object* v_inst_679_, lean_object* v_it_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Std_Iter_finitelyManySteps_x21(v_00_u03b1_677_, v_00_u03b2_678_, v_inst_679_, v_it_680_);
lean_dec(v_it_680_);
lean_dec(v_inst_679_);
return v_res_681_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__1(void){
_start:
{
lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_683_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__0));
v___x_684_ = l_String_toRawSubstring_x27(v___x_683_);
return v___x_684_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__8(void){
_start:
{
lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_704_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__7));
v___x_705_ = l_String_toRawSubstring_x27(v___x_704_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2(lean_object* v_x_723_, lean_object* v_a_724_, lean_object* v_a_725_){
_start:
{
lean_object* v___x_726_; uint8_t v___x_727_; 
v___x_726_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__1));
v___x_727_ = l_Lean_Syntax_isOfKind(v_x_723_, v___x_726_);
if (v___x_727_ == 0)
{
lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_728_ = lean_box(1);
v___x_729_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_729_, 0, v___x_728_);
lean_ctor_set(v___x_729_, 1, v_a_725_);
return v___x_729_;
}
else
{
lean_object* v_quotContext_730_; lean_object* v_currMacroScope_731_; lean_object* v_ref_732_; uint8_t v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
v_quotContext_730_ = lean_ctor_get(v_a_724_, 1);
v_currMacroScope_731_ = lean_ctor_get(v_a_724_, 2);
v_ref_732_ = lean_ctor_get(v_a_724_, 5);
v___x_733_ = 0;
v___x_734_ = l_Lean_SourceInfo_fromRef(v_ref_732_, v___x_733_);
v___x_735_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__5));
v___x_736_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__6));
lean_inc_n(v___x_734_, 31);
v___x_737_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_737_, 0, v___x_734_);
lean_ctor_set(v___x_737_, 1, v___x_735_);
v___x_738_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__8));
v___x_739_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__10));
v___x_740_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__11));
v___x_741_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_741_, 0, v___x_734_);
lean_ctor_set(v___x_741_, 1, v___x_740_);
v___x_742_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__13));
v___x_743_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__15));
v___x_744_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__16));
v___x_745_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__17));
v___x_746_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_746_, 0, v___x_734_);
lean_ctor_set(v___x_746_, 1, v___x_744_);
v___x_747_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__20));
v___x_748_ = lean_obj_once(&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__1, &l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__1_once, _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__1);
v___x_749_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__3));
lean_inc_n(v_currMacroScope_731_, 2);
lean_inc_n(v_quotContext_730_, 2);
v___x_750_ = l_Lean_addMacroScope(v_quotContext_730_, v___x_749_, v_currMacroScope_731_);
v___x_751_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__6));
v___x_752_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_752_, 0, v___x_734_);
lean_ctor_set(v___x_752_, 1, v___x_748_);
lean_ctor_set(v___x_752_, 2, v___x_750_);
lean_ctor_set(v___x_752_, 3, v___x_751_);
v___x_753_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__33));
v___x_754_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__34));
v___x_755_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_755_, 0, v___x_734_);
lean_ctor_set(v___x_755_, 1, v___x_754_);
v___x_756_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__36));
v___x_757_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__37));
v___x_758_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_758_, 0, v___x_734_);
lean_ctor_set(v___x_758_, 1, v___x_757_);
v___x_759_ = l_Lean_Syntax_node1(v___x_734_, v___x_756_, v___x_758_);
v___x_760_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__38));
v___x_761_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_761_, 0, v___x_734_);
lean_ctor_set(v___x_761_, 1, v___x_760_);
v___x_762_ = l_Lean_Syntax_node3(v___x_734_, v___x_753_, v___x_755_, v___x_759_, v___x_761_);
v___x_763_ = l_Lean_Syntax_node1(v___x_734_, v___x_738_, v___x_762_);
lean_inc(v___x_763_);
v___x_764_ = l_Lean_Syntax_node2(v___x_734_, v___x_747_, v___x_752_, v___x_763_);
lean_inc_ref(v___x_746_);
v___x_765_ = l_Lean_Syntax_node2(v___x_734_, v___x_745_, v___x_746_, v___x_764_);
v___x_766_ = l_Lean_Syntax_node1(v___x_734_, v___x_738_, v___x_765_);
v___x_767_ = l_Lean_Syntax_node1(v___x_734_, v___x_743_, v___x_766_);
v___x_768_ = l_Lean_Syntax_node1(v___x_734_, v___x_742_, v___x_767_);
lean_inc_ref_n(v___x_741_, 2);
v___x_769_ = l_Lean_Syntax_node2(v___x_734_, v___x_739_, v___x_741_, v___x_768_);
v___x_770_ = lean_obj_once(&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__8, &l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__8_once, _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__8);
v___x_771_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__9));
v___x_772_ = l_Lean_addMacroScope(v_quotContext_730_, v___x_771_, v_currMacroScope_731_);
v___x_773_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__12));
v___x_774_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_774_, 0, v___x_734_);
lean_ctor_set(v___x_774_, 1, v___x_770_);
lean_ctor_set(v___x_774_, 2, v___x_772_);
lean_ctor_set(v___x_774_, 3, v___x_773_);
v___x_775_ = l_Lean_Syntax_node2(v___x_734_, v___x_747_, v___x_774_, v___x_763_);
v___x_776_ = l_Lean_Syntax_node2(v___x_734_, v___x_745_, v___x_746_, v___x_775_);
v___x_777_ = l_Lean_Syntax_node1(v___x_734_, v___x_738_, v___x_776_);
v___x_778_ = l_Lean_Syntax_node1(v___x_734_, v___x_743_, v___x_777_);
v___x_779_ = l_Lean_Syntax_node1(v___x_734_, v___x_742_, v___x_778_);
v___x_780_ = l_Lean_Syntax_node2(v___x_734_, v___x_739_, v___x_741_, v___x_779_);
v___x_781_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__46));
v___x_782_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__47));
v___x_783_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_783_, 0, v___x_734_);
lean_ctor_set(v___x_783_, 1, v___x_781_);
v___x_784_ = lean_obj_once(&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48, &l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48_once, _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48);
v___x_785_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_785_, 0, v___x_734_);
lean_ctor_set(v___x_785_, 1, v___x_738_);
lean_ctor_set(v___x_785_, 2, v___x_784_);
v___x_786_ = l_Lean_Syntax_node2(v___x_734_, v___x_782_, v___x_783_, v___x_785_);
v___x_787_ = l_Lean_Syntax_node1(v___x_734_, v___x_738_, v___x_786_);
v___x_788_ = l_Lean_Syntax_node1(v___x_734_, v___x_743_, v___x_787_);
v___x_789_ = l_Lean_Syntax_node1(v___x_734_, v___x_742_, v___x_788_);
v___x_790_ = l_Lean_Syntax_node2(v___x_734_, v___x_739_, v___x_741_, v___x_789_);
v___x_791_ = l_Lean_Syntax_node3(v___x_734_, v___x_738_, v___x_769_, v___x_780_, v___x_790_);
v___x_792_ = l_Lean_Syntax_node2(v___x_734_, v___x_736_, v___x_737_, v___x_791_);
v___x_793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_793_, 0, v___x_792_);
lean_ctor_set(v___x_793_, 1, v_a_725_);
return v___x_793_;
}
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___boxed(lean_object* v_x_794_, lean_object* v_a_795_, lean_object* v_a_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2(v_x_794_, v_a_795_, v_a_796_);
lean_dec_ref(v_a_795_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_TerminationMeasures_instWellFoundedRelationProductive___redArg(){
_start:
{
lean_object* v___x_799_; 
v___x_799_ = lean_box(0);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_TerminationMeasures_instWellFoundedRelationProductive___redArg___boxed(lean_object* v___dummy_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l_Std_IterM_TerminationMeasures_instWellFoundedRelationProductive___redArg();
return v_res_801_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_TerminationMeasures_instWellFoundedRelationProductive(lean_object* v_00_u03b1_802_, lean_object* v_m_803_, lean_object* v_00_u03b2_804_, lean_object* v_inst_805_, lean_object* v_inst_806_){
_start:
{
lean_object* v___x_807_; 
v___x_807_ = lean_box(0);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_TerminationMeasures_instWellFoundedRelationProductive___boxed(lean_object* v_00_u03b1_808_, lean_object* v_m_809_, lean_object* v_00_u03b2_810_, lean_object* v_inst_811_, lean_object* v_inst_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l_Std_IterM_TerminationMeasures_instWellFoundedRelationProductive(v_00_u03b1_808_, v_m_809_, v_00_u03b2_810_, v_inst_811_, v_inst_812_);
lean_dec(v_inst_811_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySkips___redArg(lean_object* v_it_814_){
_start:
{
lean_inc(v_it_814_);
return v_it_814_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySkips___redArg___boxed(lean_object* v_it_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l_Std_IterM_finitelyManySkips___redArg(v_it_815_);
lean_dec(v_it_815_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySkips(lean_object* v_00_u03b1_817_, lean_object* v_m_818_, lean_object* v_00_u03b2_819_, lean_object* v_inst_820_, lean_object* v_inst_821_, lean_object* v_it_822_){
_start:
{
lean_inc(v_it_822_);
return v_it_822_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySkips___boxed(lean_object* v_00_u03b1_823_, lean_object* v_m_824_, lean_object* v_00_u03b2_825_, lean_object* v_inst_826_, lean_object* v_inst_827_, lean_object* v_it_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l_Std_IterM_finitelyManySkips(v_00_u03b1_823_, v_m_824_, v_00_u03b2_825_, v_inst_826_, v_inst_827_, v_it_828_);
lean_dec(v_it_828_);
lean_dec(v_inst_826_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySkips_x21___redArg(lean_object* v_it_830_){
_start:
{
lean_inc(v_it_830_);
return v_it_830_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySkips_x21___redArg___boxed(lean_object* v_it_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_Std_IterM_finitelyManySkips_x21___redArg(v_it_831_);
lean_dec(v_it_831_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySkips_x21(lean_object* v_00_u03b1_833_, lean_object* v_m_834_, lean_object* v_00_u03b2_835_, lean_object* v_inst_836_, lean_object* v_it_837_){
_start:
{
lean_inc(v_it_837_);
return v_it_837_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySkips_x21___boxed(lean_object* v_00_u03b1_838_, lean_object* v_m_839_, lean_object* v_00_u03b2_840_, lean_object* v_inst_841_, lean_object* v_it_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l_Std_IterM_finitelyManySkips_x21(v_00_u03b1_838_, v_m_839_, v_00_u03b2_840_, v_inst_841_, v_it_842_);
lean_dec(v_it_842_);
lean_dec(v_inst_841_);
return v_res_843_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__1(void){
_start:
{
lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_845_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__0));
v___x_846_ = l_String_toRawSubstring_x27(v___x_845_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3(lean_object* v_x_865_, lean_object* v_a_866_, lean_object* v_a_867_){
_start:
{
lean_object* v___x_868_; uint8_t v___x_869_; 
v___x_868_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__1));
v___x_869_ = l_Lean_Syntax_isOfKind(v_x_865_, v___x_868_);
if (v___x_869_ == 0)
{
lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_870_ = lean_box(1);
v___x_871_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_871_, 0, v___x_870_);
lean_ctor_set(v___x_871_, 1, v_a_867_);
return v___x_871_;
}
else
{
lean_object* v_quotContext_872_; lean_object* v_currMacroScope_873_; lean_object* v_ref_874_; uint8_t v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v_quotContext_872_ = lean_ctor_get(v_a_866_, 1);
v_currMacroScope_873_ = lean_ctor_get(v_a_866_, 2);
v_ref_874_ = lean_ctor_get(v_a_866_, 5);
v___x_875_ = 0;
v___x_876_ = l_Lean_SourceInfo_fromRef(v_ref_874_, v___x_875_);
v___x_877_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__5));
v___x_878_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__6));
lean_inc_n(v___x_876_, 24);
v___x_879_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_879_, 0, v___x_876_);
lean_ctor_set(v___x_879_, 1, v___x_877_);
v___x_880_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__8));
v___x_881_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__10));
v___x_882_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__11));
v___x_883_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_883_, 0, v___x_876_);
lean_ctor_set(v___x_883_, 1, v___x_882_);
v___x_884_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__13));
v___x_885_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__15));
v___x_886_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__16));
v___x_887_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__17));
v___x_888_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_888_, 0, v___x_876_);
lean_ctor_set(v___x_888_, 1, v___x_886_);
v___x_889_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__20));
v___x_890_ = lean_obj_once(&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__1, &l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__1_once, _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__1);
v___x_891_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__3));
lean_inc(v_currMacroScope_873_);
lean_inc(v_quotContext_872_);
v___x_892_ = l_Lean_addMacroScope(v_quotContext_872_, v___x_891_, v_currMacroScope_873_);
v___x_893_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__6));
v___x_894_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_894_, 0, v___x_876_);
lean_ctor_set(v___x_894_, 1, v___x_890_);
lean_ctor_set(v___x_894_, 2, v___x_892_);
lean_ctor_set(v___x_894_, 3, v___x_893_);
v___x_895_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__33));
v___x_896_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__34));
v___x_897_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_897_, 0, v___x_876_);
lean_ctor_set(v___x_897_, 1, v___x_896_);
v___x_898_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__36));
v___x_899_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__37));
v___x_900_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_876_);
lean_ctor_set(v___x_900_, 1, v___x_899_);
v___x_901_ = l_Lean_Syntax_node1(v___x_876_, v___x_898_, v___x_900_);
v___x_902_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__38));
v___x_903_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_903_, 0, v___x_876_);
lean_ctor_set(v___x_903_, 1, v___x_902_);
v___x_904_ = l_Lean_Syntax_node3(v___x_876_, v___x_895_, v___x_897_, v___x_901_, v___x_903_);
v___x_905_ = l_Lean_Syntax_node1(v___x_876_, v___x_880_, v___x_904_);
v___x_906_ = l_Lean_Syntax_node2(v___x_876_, v___x_889_, v___x_894_, v___x_905_);
v___x_907_ = l_Lean_Syntax_node2(v___x_876_, v___x_887_, v___x_888_, v___x_906_);
v___x_908_ = l_Lean_Syntax_node1(v___x_876_, v___x_880_, v___x_907_);
v___x_909_ = l_Lean_Syntax_node1(v___x_876_, v___x_885_, v___x_908_);
v___x_910_ = l_Lean_Syntax_node1(v___x_876_, v___x_884_, v___x_909_);
lean_inc_ref(v___x_883_);
v___x_911_ = l_Lean_Syntax_node2(v___x_876_, v___x_881_, v___x_883_, v___x_910_);
v___x_912_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__46));
v___x_913_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__47));
v___x_914_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_914_, 0, v___x_876_);
lean_ctor_set(v___x_914_, 1, v___x_912_);
v___x_915_ = lean_obj_once(&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48, &l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48_once, _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48);
v___x_916_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_916_, 0, v___x_876_);
lean_ctor_set(v___x_916_, 1, v___x_880_);
lean_ctor_set(v___x_916_, 2, v___x_915_);
v___x_917_ = l_Lean_Syntax_node2(v___x_876_, v___x_913_, v___x_914_, v___x_916_);
v___x_918_ = l_Lean_Syntax_node1(v___x_876_, v___x_880_, v___x_917_);
v___x_919_ = l_Lean_Syntax_node1(v___x_876_, v___x_885_, v___x_918_);
v___x_920_ = l_Lean_Syntax_node1(v___x_876_, v___x_884_, v___x_919_);
v___x_921_ = l_Lean_Syntax_node2(v___x_876_, v___x_881_, v___x_883_, v___x_920_);
v___x_922_ = l_Lean_Syntax_node2(v___x_876_, v___x_880_, v___x_911_, v___x_921_);
v___x_923_ = l_Lean_Syntax_node2(v___x_876_, v___x_878_, v___x_879_, v___x_922_);
v___x_924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_924_, 0, v___x_923_);
lean_ctor_set(v___x_924_, 1, v_a_867_);
return v___x_924_;
}
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___boxed(lean_object* v_x_925_, lean_object* v_a_926_, lean_object* v_a_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3(v_x_925_, v_a_926_, v_a_927_);
lean_dec_ref(v_a_926_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySkips___redArg(lean_object* v_it_929_){
_start:
{
lean_inc(v_it_929_);
return v_it_929_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySkips___redArg___boxed(lean_object* v_it_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l_Std_Iter_finitelyManySkips___redArg(v_it_930_);
lean_dec(v_it_930_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySkips(lean_object* v_00_u03b1_932_, lean_object* v_00_u03b2_933_, lean_object* v_inst_934_, lean_object* v_inst_935_, lean_object* v_it_936_){
_start:
{
lean_inc(v_it_936_);
return v_it_936_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySkips___boxed(lean_object* v_00_u03b1_937_, lean_object* v_00_u03b2_938_, lean_object* v_inst_939_, lean_object* v_inst_940_, lean_object* v_it_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l_Std_Iter_finitelyManySkips(v_00_u03b1_937_, v_00_u03b2_938_, v_inst_939_, v_inst_940_, v_it_941_);
lean_dec(v_it_941_);
lean_dec(v_inst_939_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySkips_x21___redArg(lean_object* v_it_943_){
_start:
{
lean_inc(v_it_943_);
return v_it_943_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySkips_x21___redArg___boxed(lean_object* v_it_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_Std_Iter_finitelyManySkips_x21___redArg(v_it_944_);
lean_dec(v_it_944_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySkips_x21(lean_object* v_00_u03b1_946_, lean_object* v_00_u03b2_947_, lean_object* v_inst_948_, lean_object* v_it_949_){
_start:
{
lean_inc(v_it_949_);
return v_it_949_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySkips_x21___boxed(lean_object* v_00_u03b1_950_, lean_object* v_00_u03b2_951_, lean_object* v_inst_952_, lean_object* v_it_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l_Std_Iter_finitelyManySkips_x21(v_00_u03b1_950_, v_00_u03b2_951_, v_inst_952_, v_it_953_);
lean_dec(v_it_953_);
lean_dec(v_inst_952_);
return v_res_954_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__1(void){
_start:
{
lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_956_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__0));
v___x_957_ = l_String_toRawSubstring_x27(v___x_956_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4(lean_object* v_x_975_, lean_object* v_a_976_, lean_object* v_a_977_){
_start:
{
lean_object* v___x_978_; uint8_t v___x_979_; 
v___x_978_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__1));
v___x_979_ = l_Lean_Syntax_isOfKind(v_x_975_, v___x_978_);
if (v___x_979_ == 0)
{
lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_980_ = lean_box(1);
v___x_981_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_981_, 0, v___x_980_);
lean_ctor_set(v___x_981_, 1, v_a_977_);
return v___x_981_;
}
else
{
lean_object* v_quotContext_982_; lean_object* v_currMacroScope_983_; lean_object* v_ref_984_; uint8_t v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
v_quotContext_982_ = lean_ctor_get(v_a_976_, 1);
v_currMacroScope_983_ = lean_ctor_get(v_a_976_, 2);
v_ref_984_ = lean_ctor_get(v_a_976_, 5);
v___x_985_ = 0;
v___x_986_ = l_Lean_SourceInfo_fromRef(v_ref_984_, v___x_985_);
v___x_987_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__5));
v___x_988_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__6));
lean_inc_n(v___x_986_, 24);
v___x_989_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_989_, 0, v___x_986_);
lean_ctor_set(v___x_989_, 1, v___x_987_);
v___x_990_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__8));
v___x_991_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__10));
v___x_992_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__11));
v___x_993_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_993_, 0, v___x_986_);
lean_ctor_set(v___x_993_, 1, v___x_992_);
v___x_994_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__13));
v___x_995_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__15));
v___x_996_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__16));
v___x_997_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__17));
v___x_998_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_998_, 0, v___x_986_);
lean_ctor_set(v___x_998_, 1, v___x_996_);
v___x_999_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__20));
v___x_1000_ = lean_obj_once(&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__1, &l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__1_once, _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__1);
v___x_1001_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__2));
lean_inc(v_currMacroScope_983_);
lean_inc(v_quotContext_982_);
v___x_1002_ = l_Lean_addMacroScope(v_quotContext_982_, v___x_1001_, v_currMacroScope_983_);
v___x_1003_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__5));
v___x_1004_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1004_, 0, v___x_986_);
lean_ctor_set(v___x_1004_, 1, v___x_1000_);
lean_ctor_set(v___x_1004_, 2, v___x_1002_);
lean_ctor_set(v___x_1004_, 3, v___x_1003_);
v___x_1005_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__33));
v___x_1006_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__34));
v___x_1007_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_986_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
v___x_1008_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__36));
v___x_1009_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__37));
v___x_1010_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_986_);
lean_ctor_set(v___x_1010_, 1, v___x_1009_);
v___x_1011_ = l_Lean_Syntax_node1(v___x_986_, v___x_1008_, v___x_1010_);
v___x_1012_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__38));
v___x_1013_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1013_, 0, v___x_986_);
lean_ctor_set(v___x_1013_, 1, v___x_1012_);
v___x_1014_ = l_Lean_Syntax_node3(v___x_986_, v___x_1005_, v___x_1007_, v___x_1011_, v___x_1013_);
v___x_1015_ = l_Lean_Syntax_node1(v___x_986_, v___x_990_, v___x_1014_);
v___x_1016_ = l_Lean_Syntax_node2(v___x_986_, v___x_999_, v___x_1004_, v___x_1015_);
v___x_1017_ = l_Lean_Syntax_node2(v___x_986_, v___x_997_, v___x_998_, v___x_1016_);
v___x_1018_ = l_Lean_Syntax_node1(v___x_986_, v___x_990_, v___x_1017_);
v___x_1019_ = l_Lean_Syntax_node1(v___x_986_, v___x_995_, v___x_1018_);
v___x_1020_ = l_Lean_Syntax_node1(v___x_986_, v___x_994_, v___x_1019_);
lean_inc_ref(v___x_993_);
v___x_1021_ = l_Lean_Syntax_node2(v___x_986_, v___x_991_, v___x_993_, v___x_1020_);
v___x_1022_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__46));
v___x_1023_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__47));
v___x_1024_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_986_);
lean_ctor_set(v___x_1024_, 1, v___x_1022_);
v___x_1025_ = lean_obj_once(&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48, &l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48_once, _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48);
v___x_1026_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1026_, 0, v___x_986_);
lean_ctor_set(v___x_1026_, 1, v___x_990_);
lean_ctor_set(v___x_1026_, 2, v___x_1025_);
v___x_1027_ = l_Lean_Syntax_node2(v___x_986_, v___x_1023_, v___x_1024_, v___x_1026_);
v___x_1028_ = l_Lean_Syntax_node1(v___x_986_, v___x_990_, v___x_1027_);
v___x_1029_ = l_Lean_Syntax_node1(v___x_986_, v___x_995_, v___x_1028_);
v___x_1030_ = l_Lean_Syntax_node1(v___x_986_, v___x_994_, v___x_1029_);
v___x_1031_ = l_Lean_Syntax_node2(v___x_986_, v___x_991_, v___x_993_, v___x_1030_);
v___x_1032_ = l_Lean_Syntax_node2(v___x_986_, v___x_990_, v___x_1021_, v___x_1031_);
v___x_1033_ = l_Lean_Syntax_node2(v___x_986_, v___x_988_, v___x_989_, v___x_1032_);
v___x_1034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1033_);
lean_ctor_set(v___x_1034_, 1, v_a_977_);
return v___x_1034_;
}
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___boxed(lean_object* v_x_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4(v_x_1035_, v_a_1036_, v_a_1037_);
lean_dec_ref(v_a_1036_);
return v_res_1038_;
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
