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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Basic_0__Std_Internal_idOpaque___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Basic_0__Std_Internal_idOpaque___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Init_Data_Iterators_Basic_0__Std_Internal_idOpaque___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Iterators_Basic_0__Std_Internal_idOpaque___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Iterators_Basic_0__Std_Internal_idOpaque___closed__0 = (const lean_object*)&l___private_Init_Data_Iterators_Basic_0__Std_Internal_idOpaque___closed__0_value;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Basic_0__Std_Internal_idOpaque___lam__0(lean_object* v___y_1_){
_start:
{
lean_inc(v___y_1_);
return v___y_1_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Basic_0__Std_Internal_idOpaque___lam__0___boxed(lean_object* v___y_2_){
_start:
{
lean_object* v_res_3_; 
v_res_3_ = l___private_Init_Data_Iterators_Basic_0__Std_Internal_idOpaque___lam__0(v___y_2_);
lean_dec(v___y_2_);
return v_res_3_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Basic_0__Std_Internal_idOpaque(lean_object* v_00_u03b1_5_){
_start:
{
lean_object* v___f_6_; 
v___f_6_ = ((lean_object*)(l___private_Init_Data_Iterators_Basic_0__Std_Internal_idOpaque___closed__0));
return v___f_6_;
}
}
LEAN_EXPORT lean_object* l_Std_Shrink_deflate___redArg(lean_object* v_x_7_){
_start:
{
lean_inc(v_x_7_);
return v_x_7_;
}
}
LEAN_EXPORT lean_object* l_Std_Shrink_deflate___redArg___boxed(lean_object* v_x_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Std_Shrink_deflate___redArg(v_x_8_);
lean_dec(v_x_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Std_Shrink_deflate(lean_object* v_00_u03b1_10_, lean_object* v_x_11_){
_start:
{
lean_inc(v_x_11_);
return v_x_11_;
}
}
LEAN_EXPORT lean_object* l_Std_Shrink_deflate___boxed(lean_object* v_00_u03b1_12_, lean_object* v_x_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Std_Shrink_deflate(v_00_u03b1_12_, v_x_13_);
lean_dec(v_x_13_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Std_Shrink_inflate___redArg(lean_object* v_x_15_){
_start:
{
lean_inc(v_x_15_);
return v_x_15_;
}
}
LEAN_EXPORT lean_object* l_Std_Shrink_inflate___redArg___boxed(lean_object* v_x_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l_Std_Shrink_inflate___redArg(v_x_16_);
lean_dec(v_x_16_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l_Std_Shrink_inflate(lean_object* v_00_u03b1_18_, lean_object* v_x_19_){
_start:
{
lean_inc(v_x_19_);
return v_x_19_;
}
}
LEAN_EXPORT lean_object* l_Std_Shrink_inflate___boxed(lean_object* v_00_u03b1_20_, lean_object* v_x_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Std_Shrink_inflate(v_00_u03b1_20_, v_x_21_);
lean_dec(v_x_21_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toIterM___redArg(lean_object* v_it_23_){
_start:
{
lean_inc(v_it_23_);
return v_it_23_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toIterM___redArg___boxed(lean_object* v_it_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Std_Iter_toIterM___redArg(v_it_24_);
lean_dec(v_it_24_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toIterM(lean_object* v_00_u03b1_26_, lean_object* v_00_u03b2_27_, lean_object* v_it_28_){
_start:
{
lean_inc(v_it_28_);
return v_it_28_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toIterM___boxed(lean_object* v_00_u03b1_29_, lean_object* v_00_u03b2_30_, lean_object* v_it_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Std_Iter_toIterM(v_00_u03b1_29_, v_00_u03b2_30_, v_it_31_);
lean_dec(v_it_31_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toIter___redArg(lean_object* v_it_33_){
_start:
{
lean_inc(v_it_33_);
return v_it_33_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toIter___redArg___boxed(lean_object* v_it_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_Std_IterM_toIter___redArg(v_it_34_);
lean_dec(v_it_34_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toIter(lean_object* v_00_u03b1_36_, lean_object* v_00_u03b2_37_, lean_object* v_it_38_){
_start:
{
lean_inc(v_it_38_);
return v_it_38_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toIter___boxed(lean_object* v_00_u03b1_39_, lean_object* v_00_u03b2_40_, lean_object* v_it_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_Std_IterM_toIter(v_00_u03b1_39_, v_00_u03b2_40_, v_it_41_);
lean_dec(v_it_41_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_ctorIdx___redArg(lean_object* v_x_43_){
_start:
{
switch(lean_obj_tag(v_x_43_))
{
case 0:
{
lean_object* v___x_44_; 
v___x_44_ = lean_unsigned_to_nat(0u);
return v___x_44_;
}
case 1:
{
lean_object* v___x_45_; 
v___x_45_ = lean_unsigned_to_nat(1u);
return v___x_45_;
}
default: 
{
lean_object* v___x_46_; 
v___x_46_ = lean_unsigned_to_nat(2u);
return v___x_46_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_ctorIdx___redArg___boxed(lean_object* v_x_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l_Std_IterStep_ctorIdx___redArg(v_x_47_);
lean_dec(v_x_47_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_ctorIdx(lean_object* v_00_u03b1_49_, lean_object* v_00_u03b2_50_, lean_object* v_x_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l_Std_IterStep_ctorIdx___redArg(v_x_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_ctorIdx___boxed(lean_object* v_00_u03b1_53_, lean_object* v_00_u03b2_54_, lean_object* v_x_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Std_IterStep_ctorIdx(v_00_u03b1_53_, v_00_u03b2_54_, v_x_55_);
lean_dec(v_x_55_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_ctorElim___redArg(lean_object* v_t_57_, lean_object* v_k_58_){
_start:
{
switch(lean_obj_tag(v_t_57_))
{
case 0:
{
lean_object* v_it_59_; lean_object* v_out_60_; lean_object* v___x_61_; 
v_it_59_ = lean_ctor_get(v_t_57_, 0);
lean_inc(v_it_59_);
v_out_60_ = lean_ctor_get(v_t_57_, 1);
lean_inc(v_out_60_);
lean_dec_ref(v_t_57_);
v___x_61_ = lean_apply_2(v_k_58_, v_it_59_, v_out_60_);
return v___x_61_;
}
case 1:
{
lean_object* v_it_62_; lean_object* v___x_63_; 
v_it_62_ = lean_ctor_get(v_t_57_, 0);
lean_inc(v_it_62_);
lean_dec_ref(v_t_57_);
v___x_63_ = lean_apply_1(v_k_58_, v_it_62_);
return v___x_63_;
}
default: 
{
return v_k_58_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_ctorElim(lean_object* v_00_u03b1_64_, lean_object* v_00_u03b2_65_, lean_object* v_motive_66_, lean_object* v_ctorIdx_67_, lean_object* v_t_68_, lean_object* v_h_69_, lean_object* v_k_70_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = l_Std_IterStep_ctorElim___redArg(v_t_68_, v_k_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_ctorElim___boxed(lean_object* v_00_u03b1_72_, lean_object* v_00_u03b2_73_, lean_object* v_motive_74_, lean_object* v_ctorIdx_75_, lean_object* v_t_76_, lean_object* v_h_77_, lean_object* v_k_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l_Std_IterStep_ctorElim(v_00_u03b1_72_, v_00_u03b2_73_, v_motive_74_, v_ctorIdx_75_, v_t_76_, v_h_77_, v_k_78_);
lean_dec(v_ctorIdx_75_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_yield_elim___redArg(lean_object* v_t_80_, lean_object* v_yield_81_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = l_Std_IterStep_ctorElim___redArg(v_t_80_, v_yield_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_yield_elim(lean_object* v_00_u03b1_83_, lean_object* v_00_u03b2_84_, lean_object* v_motive_85_, lean_object* v_t_86_, lean_object* v_h_87_, lean_object* v_yield_88_){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = l_Std_IterStep_ctorElim___redArg(v_t_86_, v_yield_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_skip_elim___redArg(lean_object* v_t_90_, lean_object* v_skip_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l_Std_IterStep_ctorElim___redArg(v_t_90_, v_skip_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_skip_elim(lean_object* v_00_u03b1_93_, lean_object* v_00_u03b2_94_, lean_object* v_motive_95_, lean_object* v_t_96_, lean_object* v_h_97_, lean_object* v_skip_98_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = l_Std_IterStep_ctorElim___redArg(v_t_96_, v_skip_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_done_elim___redArg(lean_object* v_t_100_, lean_object* v_done_101_){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = l_Std_IterStep_ctorElim___redArg(v_t_100_, v_done_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_done_elim(lean_object* v_00_u03b1_103_, lean_object* v_00_u03b2_104_, lean_object* v_motive_105_, lean_object* v_t_106_, lean_object* v_h_107_, lean_object* v_done_108_){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = l_Std_IterStep_ctorElim___redArg(v_t_106_, v_done_108_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_successor___redArg(lean_object* v_x_110_){
_start:
{
switch(lean_obj_tag(v_x_110_))
{
case 0:
{
lean_object* v_it_111_; lean_object* v___x_112_; 
v_it_111_ = lean_ctor_get(v_x_110_, 0);
lean_inc(v_it_111_);
lean_dec_ref(v_x_110_);
v___x_112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_112_, 0, v_it_111_);
return v___x_112_;
}
case 1:
{
lean_object* v_it_113_; lean_object* v___x_115_; uint8_t v_isShared_116_; uint8_t v_isSharedCheck_120_; 
v_it_113_ = lean_ctor_get(v_x_110_, 0);
v_isSharedCheck_120_ = !lean_is_exclusive(v_x_110_);
if (v_isSharedCheck_120_ == 0)
{
v___x_115_ = v_x_110_;
v_isShared_116_ = v_isSharedCheck_120_;
goto v_resetjp_114_;
}
else
{
lean_inc(v_it_113_);
lean_dec(v_x_110_);
v___x_115_ = lean_box(0);
v_isShared_116_ = v_isSharedCheck_120_;
goto v_resetjp_114_;
}
v_resetjp_114_:
{
lean_object* v___x_118_; 
if (v_isShared_116_ == 0)
{
v___x_118_ = v___x_115_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v_it_113_);
v___x_118_ = v_reuseFailAlloc_119_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
return v___x_118_;
}
}
}
default: 
{
lean_object* v___x_121_; 
v___x_121_ = lean_box(0);
return v___x_121_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_successor(lean_object* v_00_u03b1_122_, lean_object* v_00_u03b2_123_, lean_object* v_x_124_){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = l_Std_IterStep_successor___redArg(v_x_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_mapIterator___redArg(lean_object* v_f_126_, lean_object* v_x_127_){
_start:
{
switch(lean_obj_tag(v_x_127_))
{
case 0:
{
lean_object* v_it_128_; lean_object* v_out_129_; lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_137_; 
v_it_128_ = lean_ctor_get(v_x_127_, 0);
v_out_129_ = lean_ctor_get(v_x_127_, 1);
v_isSharedCheck_137_ = !lean_is_exclusive(v_x_127_);
if (v_isSharedCheck_137_ == 0)
{
v___x_131_ = v_x_127_;
v_isShared_132_ = v_isSharedCheck_137_;
goto v_resetjp_130_;
}
else
{
lean_inc(v_out_129_);
lean_inc(v_it_128_);
lean_dec(v_x_127_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_137_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
lean_object* v___x_133_; lean_object* v___x_135_; 
v___x_133_ = lean_apply_1(v_f_126_, v_it_128_);
if (v_isShared_132_ == 0)
{
lean_ctor_set(v___x_131_, 0, v___x_133_);
v___x_135_ = v___x_131_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v___x_133_);
lean_ctor_set(v_reuseFailAlloc_136_, 1, v_out_129_);
v___x_135_ = v_reuseFailAlloc_136_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
return v___x_135_;
}
}
}
case 1:
{
lean_object* v_it_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_146_; 
v_it_138_ = lean_ctor_get(v_x_127_, 0);
v_isSharedCheck_146_ = !lean_is_exclusive(v_x_127_);
if (v_isSharedCheck_146_ == 0)
{
v___x_140_ = v_x_127_;
v_isShared_141_ = v_isSharedCheck_146_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_it_138_);
lean_dec(v_x_127_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_146_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_142_; lean_object* v___x_144_; 
v___x_142_ = lean_apply_1(v_f_126_, v_it_138_);
if (v_isShared_141_ == 0)
{
lean_ctor_set(v___x_140_, 0, v___x_142_);
v___x_144_ = v___x_140_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v___x_142_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
}
default: 
{
lean_object* v___x_147_; 
lean_dec(v_f_126_);
v___x_147_ = lean_box(2);
return v___x_147_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_IterStep_mapIterator(lean_object* v_00_u03b1_148_, lean_object* v_00_u03b2_149_, lean_object* v_00_u03b1_x27_150_, lean_object* v_f_151_, lean_object* v_x_152_){
_start:
{
switch(lean_obj_tag(v_x_152_))
{
case 0:
{
lean_object* v_it_153_; lean_object* v_out_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_162_; 
v_it_153_ = lean_ctor_get(v_x_152_, 0);
v_out_154_ = lean_ctor_get(v_x_152_, 1);
v_isSharedCheck_162_ = !lean_is_exclusive(v_x_152_);
if (v_isSharedCheck_162_ == 0)
{
v___x_156_ = v_x_152_;
v_isShared_157_ = v_isSharedCheck_162_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_out_154_);
lean_inc(v_it_153_);
lean_dec(v_x_152_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_162_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_158_; lean_object* v___x_160_; 
v___x_158_ = lean_apply_1(v_f_151_, v_it_153_);
if (v_isShared_157_ == 0)
{
lean_ctor_set(v___x_156_, 0, v___x_158_);
v___x_160_ = v___x_156_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v___x_158_);
lean_ctor_set(v_reuseFailAlloc_161_, 1, v_out_154_);
v___x_160_ = v_reuseFailAlloc_161_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
return v___x_160_;
}
}
}
case 1:
{
lean_object* v_it_163_; lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_171_; 
v_it_163_ = lean_ctor_get(v_x_152_, 0);
v_isSharedCheck_171_ = !lean_is_exclusive(v_x_152_);
if (v_isSharedCheck_171_ == 0)
{
v___x_165_ = v_x_152_;
v_isShared_166_ = v_isSharedCheck_171_;
goto v_resetjp_164_;
}
else
{
lean_inc(v_it_163_);
lean_dec(v_x_152_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_171_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
lean_object* v___x_167_; lean_object* v___x_169_; 
v___x_167_ = lean_apply_1(v_f_151_, v_it_163_);
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 0, v___x_167_);
v___x_169_ = v___x_165_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v___x_167_);
v___x_169_ = v_reuseFailAlloc_170_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
return v___x_169_;
}
}
}
default: 
{
lean_object* v___x_172_; 
lean_dec(v_f_151_);
v___x_172_ = lean_box(2);
return v___x_172_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PlausibleIterStep_yield___redArg(lean_object* v_it_x27_173_, lean_object* v_out_174_){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_175_, 0, v_it_x27_173_);
lean_ctor_set(v___x_175_, 1, v_out_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Std_PlausibleIterStep_yield(lean_object* v_00_u03b1_176_, lean_object* v_00_u03b2_177_, lean_object* v_IsPlausibleStep_178_, lean_object* v_it_x27_179_, lean_object* v_out_180_, lean_object* v_h_181_){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_182_, 0, v_it_x27_179_);
lean_ctor_set(v___x_182_, 1, v_out_180_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Std_PlausibleIterStep_skip___redArg(lean_object* v_it_x27_183_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_184_, 0, v_it_x27_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Std_PlausibleIterStep_skip(lean_object* v_00_u03b1_185_, lean_object* v_00_u03b2_186_, lean_object* v_IsPlausibleStep_187_, lean_object* v_it_x27_188_, lean_object* v_h_189_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_190_, 0, v_it_x27_188_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Std_PlausibleIterStep_done(lean_object* v_00_u03b1_191_, lean_object* v_00_u03b2_192_, lean_object* v_IsPlausibleStep_193_, lean_object* v_h_194_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = lean_box(2);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Std_PlausibleIterStep_casesOn___redArg(lean_object* v_s_196_, lean_object* v_yield_197_, lean_object* v_skip_198_, lean_object* v_done_199_){
_start:
{
switch(lean_obj_tag(v_s_196_))
{
case 0:
{
lean_object* v_it_200_; lean_object* v_out_201_; lean_object* v___x_202_; 
lean_dec(v_done_199_);
lean_dec(v_skip_198_);
v_it_200_ = lean_ctor_get(v_s_196_, 0);
lean_inc(v_it_200_);
v_out_201_ = lean_ctor_get(v_s_196_, 1);
lean_inc(v_out_201_);
lean_dec_ref(v_s_196_);
v___x_202_ = lean_apply_3(v_yield_197_, v_it_200_, v_out_201_, lean_box(0));
return v___x_202_;
}
case 1:
{
lean_object* v_it_203_; lean_object* v___x_204_; 
lean_dec(v_done_199_);
lean_dec(v_yield_197_);
v_it_203_ = lean_ctor_get(v_s_196_, 0);
lean_inc(v_it_203_);
lean_dec_ref(v_s_196_);
v___x_204_ = lean_apply_2(v_skip_198_, v_it_203_, lean_box(0));
return v___x_204_;
}
default: 
{
lean_object* v___x_205_; 
lean_dec(v_skip_198_);
lean_dec(v_yield_197_);
v___x_205_ = lean_apply_1(v_done_199_, lean_box(0));
return v___x_205_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PlausibleIterStep_casesOn(lean_object* v_00_u03b1_206_, lean_object* v_00_u03b2_207_, lean_object* v_IsPlausibleStep_208_, lean_object* v_motive_209_, lean_object* v_s_210_, lean_object* v_yield_211_, lean_object* v_skip_212_, lean_object* v_done_213_){
_start:
{
switch(lean_obj_tag(v_s_210_))
{
case 0:
{
lean_object* v_it_214_; lean_object* v_out_215_; lean_object* v___x_216_; 
lean_dec(v_done_213_);
lean_dec(v_skip_212_);
v_it_214_ = lean_ctor_get(v_s_210_, 0);
lean_inc(v_it_214_);
v_out_215_ = lean_ctor_get(v_s_210_, 1);
lean_inc(v_out_215_);
lean_dec_ref(v_s_210_);
v___x_216_ = lean_apply_3(v_yield_211_, v_it_214_, v_out_215_, lean_box(0));
return v___x_216_;
}
case 1:
{
lean_object* v_it_217_; lean_object* v___x_218_; 
lean_dec(v_done_213_);
lean_dec(v_yield_211_);
v_it_217_ = lean_ctor_get(v_s_210_, 0);
lean_inc(v_it_217_);
lean_dec_ref(v_s_210_);
v___x_218_ = lean_apply_2(v_skip_212_, v_it_217_, lean_box(0));
return v___x_218_;
}
default: 
{
lean_object* v___x_219_; 
lean_dec(v_skip_212_);
lean_dec(v_yield_211_);
v___x_219_ = lean_apply_1(v_done_213_, lean_box(0));
return v___x_219_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_IterM_mk_x27___redArg(lean_object* v_it_220_){
_start:
{
lean_inc(v_it_220_);
return v_it_220_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_mk_x27___redArg___boxed(lean_object* v_it_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Std_IterM_mk_x27___redArg(v_it_221_);
lean_dec(v_it_221_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_mk_x27(lean_object* v_00_u03b1_223_, lean_object* v_m_224_, lean_object* v_00_u03b2_225_, lean_object* v_it_226_){
_start:
{
lean_inc(v_it_226_);
return v_it_226_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_mk_x27___boxed(lean_object* v_00_u03b1_227_, lean_object* v_m_228_, lean_object* v_00_u03b2_229_, lean_object* v_it_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Std_IterM_mk_x27(v_00_u03b1_227_, v_m_228_, v_00_u03b2_229_, v_it_230_);
lean_dec(v_it_230_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_toIterM___redArg(lean_object* v_internalState_232_){
_start:
{
lean_inc(v_internalState_232_);
return v_internalState_232_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_toIterM___redArg___boxed(lean_object* v_internalState_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l_Std_Iterators_toIterM___redArg(v_internalState_233_);
lean_dec(v_internalState_233_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_toIterM(lean_object* v_00_u03b1_235_, lean_object* v_m_236_, lean_object* v_00_u03b2_237_, lean_object* v_internalState_238_){
_start:
{
lean_inc(v_internalState_238_);
return v_internalState_238_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_toIterM___boxed(lean_object* v_00_u03b1_239_, lean_object* v_m_240_, lean_object* v_00_u03b2_241_, lean_object* v_internalState_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_Std_Iterators_toIterM(v_00_u03b1_239_, v_m_240_, v_00_u03b2_241_, v_internalState_242_);
lean_dec(v_internalState_242_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_step___redArg(lean_object* v_inst_244_, lean_object* v_it_245_){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = lean_apply_1(v_inst_244_, v_it_245_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_step(lean_object* v_00_u03b1_247_, lean_object* v_m_248_, lean_object* v_00_u03b2_249_, lean_object* v_inst_250_, lean_object* v_it_251_){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = lean_apply_1(v_inst_250_, v_it_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Step_toMonadic___redArg(lean_object* v_step_253_){
_start:
{
switch(lean_obj_tag(v_step_253_))
{
case 0:
{
lean_object* v_it_254_; lean_object* v_out_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_262_; 
v_it_254_ = lean_ctor_get(v_step_253_, 0);
v_out_255_ = lean_ctor_get(v_step_253_, 1);
v_isSharedCheck_262_ = !lean_is_exclusive(v_step_253_);
if (v_isSharedCheck_262_ == 0)
{
v___x_257_ = v_step_253_;
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_out_255_);
lean_inc(v_it_254_);
lean_dec(v_step_253_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_260_; 
if (v_isShared_258_ == 0)
{
v___x_260_ = v___x_257_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_it_254_);
lean_ctor_set(v_reuseFailAlloc_261_, 1, v_out_255_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
}
case 1:
{
lean_object* v_it_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_270_; 
v_it_263_ = lean_ctor_get(v_step_253_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v_step_253_);
if (v_isSharedCheck_270_ == 0)
{
v___x_265_ = v_step_253_;
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_it_263_);
lean_dec(v_step_253_);
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
v_reuseFailAlloc_269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_it_263_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
}
default: 
{
lean_object* v___x_271_; 
v___x_271_ = lean_box(2);
return v___x_271_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Step_toMonadic(lean_object* v_00_u03b1_272_, lean_object* v_00_u03b2_273_, lean_object* v_inst_274_, lean_object* v_it_275_, lean_object* v_step_276_){
_start:
{
switch(lean_obj_tag(v_step_276_))
{
case 0:
{
lean_object* v_it_277_; lean_object* v_out_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_285_; 
v_it_277_ = lean_ctor_get(v_step_276_, 0);
v_out_278_ = lean_ctor_get(v_step_276_, 1);
v_isSharedCheck_285_ = !lean_is_exclusive(v_step_276_);
if (v_isSharedCheck_285_ == 0)
{
v___x_280_ = v_step_276_;
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_out_278_);
lean_inc(v_it_277_);
lean_dec(v_step_276_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_283_; 
if (v_isShared_281_ == 0)
{
v___x_283_ = v___x_280_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v_it_277_);
lean_ctor_set(v_reuseFailAlloc_284_, 1, v_out_278_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
case 1:
{
lean_object* v_it_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_293_; 
v_it_286_ = lean_ctor_get(v_step_276_, 0);
v_isSharedCheck_293_ = !lean_is_exclusive(v_step_276_);
if (v_isSharedCheck_293_ == 0)
{
v___x_288_ = v_step_276_;
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_it_286_);
lean_dec(v_step_276_);
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
v_reuseFailAlloc_292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_it_286_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
default: 
{
lean_object* v___x_294_; 
v___x_294_ = lean_box(2);
return v___x_294_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Step_toMonadic___boxed(lean_object* v_00_u03b1_295_, lean_object* v_00_u03b2_296_, lean_object* v_inst_297_, lean_object* v_it_298_, lean_object* v_step_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Std_Iter_Step_toMonadic(v_00_u03b1_295_, v_00_u03b2_296_, v_inst_297_, v_it_298_, v_step_299_);
lean_dec(v_it_298_);
lean_dec(v_inst_297_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Step_toPure___redArg(lean_object* v_step_301_){
_start:
{
switch(lean_obj_tag(v_step_301_))
{
case 0:
{
lean_object* v_it_302_; lean_object* v_out_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_310_; 
v_it_302_ = lean_ctor_get(v_step_301_, 0);
v_out_303_ = lean_ctor_get(v_step_301_, 1);
v_isSharedCheck_310_ = !lean_is_exclusive(v_step_301_);
if (v_isSharedCheck_310_ == 0)
{
v___x_305_ = v_step_301_;
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_out_303_);
lean_inc(v_it_302_);
lean_dec(v_step_301_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_308_; 
if (v_isShared_306_ == 0)
{
v___x_308_ = v___x_305_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_it_302_);
lean_ctor_set(v_reuseFailAlloc_309_, 1, v_out_303_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
return v___x_308_;
}
}
}
case 1:
{
lean_object* v_it_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_318_; 
v_it_311_ = lean_ctor_get(v_step_301_, 0);
v_isSharedCheck_318_ = !lean_is_exclusive(v_step_301_);
if (v_isSharedCheck_318_ == 0)
{
v___x_313_ = v_step_301_;
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_it_311_);
lean_dec(v_step_301_);
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
v_reuseFailAlloc_317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_it_311_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
return v___x_316_;
}
}
}
default: 
{
lean_object* v___x_319_; 
v___x_319_ = lean_box(2);
return v___x_319_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Step_toPure(lean_object* v_00_u03b1_320_, lean_object* v_00_u03b2_321_, lean_object* v_inst_322_, lean_object* v_it_323_, lean_object* v_step_324_){
_start:
{
switch(lean_obj_tag(v_step_324_))
{
case 0:
{
lean_object* v_it_325_; lean_object* v_out_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_333_; 
v_it_325_ = lean_ctor_get(v_step_324_, 0);
v_out_326_ = lean_ctor_get(v_step_324_, 1);
v_isSharedCheck_333_ = !lean_is_exclusive(v_step_324_);
if (v_isSharedCheck_333_ == 0)
{
v___x_328_ = v_step_324_;
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_out_326_);
lean_inc(v_it_325_);
lean_dec(v_step_324_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_331_; 
if (v_isShared_329_ == 0)
{
v___x_331_ = v___x_328_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_it_325_);
lean_ctor_set(v_reuseFailAlloc_332_, 1, v_out_326_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
}
case 1:
{
lean_object* v_it_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_341_; 
v_it_334_ = lean_ctor_get(v_step_324_, 0);
v_isSharedCheck_341_ = !lean_is_exclusive(v_step_324_);
if (v_isSharedCheck_341_ == 0)
{
v___x_336_ = v_step_324_;
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_it_334_);
lean_dec(v_step_324_);
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
v_reuseFailAlloc_340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v_it_334_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
}
default: 
{
lean_object* v___x_342_; 
v___x_342_ = lean_box(2);
return v___x_342_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Step_toPure___boxed(lean_object* v_00_u03b1_343_, lean_object* v_00_u03b2_344_, lean_object* v_inst_345_, lean_object* v_it_346_, lean_object* v_step_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Std_IterM_Step_toPure(v_00_u03b1_343_, v_00_u03b2_344_, v_inst_345_, v_it_346_, v_step_347_);
lean_dec(v_it_346_);
lean_dec(v_inst_345_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Basic_0__Std_IterStep_successor_match__1_splitter___redArg(lean_object* v_x_349_, lean_object* v_h__1_350_, lean_object* v_h__2_351_, lean_object* v_h__3_352_){
_start:
{
switch(lean_obj_tag(v_x_349_))
{
case 0:
{
lean_object* v_it_353_; lean_object* v_out_354_; lean_object* v___x_355_; 
lean_dec(v_h__3_352_);
lean_dec(v_h__2_351_);
v_it_353_ = lean_ctor_get(v_x_349_, 0);
lean_inc(v_it_353_);
v_out_354_ = lean_ctor_get(v_x_349_, 1);
lean_inc(v_out_354_);
lean_dec_ref(v_x_349_);
v___x_355_ = lean_apply_2(v_h__1_350_, v_it_353_, v_out_354_);
return v___x_355_;
}
case 1:
{
lean_object* v_it_356_; lean_object* v___x_357_; 
lean_dec(v_h__3_352_);
lean_dec(v_h__1_350_);
v_it_356_ = lean_ctor_get(v_x_349_, 0);
lean_inc(v_it_356_);
lean_dec_ref(v_x_349_);
v___x_357_ = lean_apply_1(v_h__2_351_, v_it_356_);
return v___x_357_;
}
default: 
{
lean_object* v___x_358_; lean_object* v___x_359_; 
lean_dec(v_h__2_351_);
lean_dec(v_h__1_350_);
v___x_358_ = lean_box(0);
v___x_359_ = lean_apply_1(v_h__3_352_, v___x_358_);
return v___x_359_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Basic_0__Std_IterStep_successor_match__1_splitter(lean_object* v_00_u03b1_360_, lean_object* v_00_u03b2_361_, lean_object* v_motive_362_, lean_object* v_x_363_, lean_object* v_h__1_364_, lean_object* v_h__2_365_, lean_object* v_h__3_366_){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = l___private_Init_Data_Iterators_Basic_0__Std_IterStep_successor_match__1_splitter___redArg(v_x_363_, v_h__1_364_, v_h__2_365_, v_h__3_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_step___redArg(lean_object* v_inst_368_, lean_object* v_it_369_){
_start:
{
lean_object* v___x_370_; 
v___x_370_ = lean_apply_1(v_inst_368_, v_it_369_);
switch(lean_obj_tag(v___x_370_))
{
case 0:
{
lean_object* v_it_371_; lean_object* v_out_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_379_; 
v_it_371_ = lean_ctor_get(v___x_370_, 0);
v_out_372_ = lean_ctor_get(v___x_370_, 1);
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_379_ == 0)
{
v___x_374_ = v___x_370_;
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_out_372_);
lean_inc(v_it_371_);
lean_dec(v___x_370_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_377_; 
if (v_isShared_375_ == 0)
{
v___x_377_ = v___x_374_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_it_371_);
lean_ctor_set(v_reuseFailAlloc_378_, 1, v_out_372_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
}
case 1:
{
lean_object* v_it_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_387_; 
v_it_380_ = lean_ctor_get(v___x_370_, 0);
v_isSharedCheck_387_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_387_ == 0)
{
v___x_382_ = v___x_370_;
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_it_380_);
lean_dec(v___x_370_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_385_; 
if (v_isShared_383_ == 0)
{
v___x_385_ = v___x_382_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v_it_380_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
}
}
}
default: 
{
lean_object* v___x_388_; 
v___x_388_ = lean_box(2);
return v___x_388_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iter_step(lean_object* v_00_u03b1_389_, lean_object* v_00_u03b2_390_, lean_object* v_inst_391_, lean_object* v_it_392_){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = lean_apply_1(v_inst_391_, v_it_392_);
switch(lean_obj_tag(v___x_393_))
{
case 0:
{
lean_object* v_it_394_; lean_object* v_out_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_402_; 
v_it_394_ = lean_ctor_get(v___x_393_, 0);
v_out_395_ = lean_ctor_get(v___x_393_, 1);
v_isSharedCheck_402_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_402_ == 0)
{
v___x_397_ = v___x_393_;
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_out_395_);
lean_inc(v_it_394_);
lean_dec(v___x_393_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_400_; 
if (v_isShared_398_ == 0)
{
v___x_400_ = v___x_397_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_it_394_);
lean_ctor_set(v_reuseFailAlloc_401_, 1, v_out_395_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
}
}
}
case 1:
{
lean_object* v_it_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_410_; 
v_it_403_ = lean_ctor_get(v___x_393_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_410_ == 0)
{
v___x_405_ = v___x_393_;
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_it_403_);
lean_dec(v___x_393_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_408_; 
if (v_isShared_406_ == 0)
{
v___x_408_ = v___x_405_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v_it_403_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
default: 
{
lean_object* v___x_411_; 
v___x_411_ = lean_box(2);
return v___x_411_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_IterM_TerminationMeasures_instWellFoundedRelationFinite(lean_object* v_00_u03b1_412_, lean_object* v_m_413_, lean_object* v_00_u03b2_414_, lean_object* v_inst_415_, lean_object* v_inst_416_){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = lean_box(0);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_TerminationMeasures_instWellFoundedRelationFinite___boxed(lean_object* v_00_u03b1_418_, lean_object* v_m_419_, lean_object* v_00_u03b2_420_, lean_object* v_inst_421_, lean_object* v_inst_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Std_IterM_TerminationMeasures_instWellFoundedRelationFinite(v_00_u03b1_418_, v_m_419_, v_00_u03b2_420_, v_inst_421_, v_inst_422_);
lean_dec(v_inst_421_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySteps___redArg(lean_object* v_it_424_){
_start:
{
lean_inc(v_it_424_);
return v_it_424_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySteps___redArg___boxed(lean_object* v_it_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Std_IterM_finitelyManySteps___redArg(v_it_425_);
lean_dec(v_it_425_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySteps(lean_object* v_00_u03b1_427_, lean_object* v_m_428_, lean_object* v_00_u03b2_429_, lean_object* v_inst_430_, lean_object* v_inst_431_, lean_object* v_it_432_){
_start:
{
lean_inc(v_it_432_);
return v_it_432_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySteps___boxed(lean_object* v_00_u03b1_433_, lean_object* v_m_434_, lean_object* v_00_u03b2_435_, lean_object* v_inst_436_, lean_object* v_inst_437_, lean_object* v_it_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_Std_IterM_finitelyManySteps(v_00_u03b1_433_, v_m_434_, v_00_u03b2_435_, v_inst_436_, v_inst_437_, v_it_438_);
lean_dec(v_it_438_);
lean_dec(v_inst_436_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySteps_x21___redArg(lean_object* v_it_440_){
_start:
{
lean_inc(v_it_440_);
return v_it_440_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySteps_x21___redArg___boxed(lean_object* v_it_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_Std_IterM_finitelyManySteps_x21___redArg(v_it_441_);
lean_dec(v_it_441_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySteps_x21(lean_object* v_00_u03b1_443_, lean_object* v_m_444_, lean_object* v_00_u03b2_445_, lean_object* v_inst_446_, lean_object* v_it_447_){
_start:
{
lean_inc(v_it_447_);
return v_it_447_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySteps_x21___boxed(lean_object* v_00_u03b1_448_, lean_object* v_m_449_, lean_object* v_00_u03b2_450_, lean_object* v_inst_451_, lean_object* v_it_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l_Std_IterM_finitelyManySteps_x21(v_00_u03b1_448_, v_m_449_, v_00_u03b2_450_, v_inst_451_, v_it_452_);
lean_dec(v_it_452_);
lean_dec(v_inst_451_);
return v_res_453_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__22(void){
_start:
{
lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_499_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__21));
v___x_500_ = l_String_toRawSubstring_x27(v___x_499_);
return v___x_500_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__40(void){
_start:
{
lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_536_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__39));
v___x_537_ = l_String_toRawSubstring_x27(v___x_536_);
return v___x_537_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48(void){
_start:
{
lean_object* v___x_562_; 
v___x_562_ = l_Array_mkArray0(lean_box(0));
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1(lean_object* v_x_563_, lean_object* v_a_564_, lean_object* v_a_565_){
_start:
{
lean_object* v___x_566_; uint8_t v___x_567_; 
v___x_566_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__1));
v___x_567_ = l_Lean_Syntax_isOfKind(v_x_563_, v___x_566_);
if (v___x_567_ == 0)
{
lean_object* v___x_568_; lean_object* v___x_569_; 
lean_dec_ref(v_a_564_);
v___x_568_ = lean_box(1);
v___x_569_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_569_, 0, v___x_568_);
lean_ctor_set(v___x_569_, 1, v_a_565_);
return v___x_569_;
}
else
{
lean_object* v_quotContext_570_; lean_object* v_currMacroScope_571_; lean_object* v_ref_572_; uint8_t v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v_quotContext_570_ = lean_ctor_get(v_a_564_, 1);
lean_inc(v_quotContext_570_);
v_currMacroScope_571_ = lean_ctor_get(v_a_564_, 2);
lean_inc(v_currMacroScope_571_);
v_ref_572_ = lean_ctor_get(v_a_564_, 5);
lean_inc(v_ref_572_);
lean_dec_ref(v_a_564_);
v___x_573_ = 0;
v___x_574_ = l_Lean_SourceInfo_fromRef(v_ref_572_, v___x_573_);
lean_dec(v_ref_572_);
v___x_575_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__5));
v___x_576_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__6));
lean_inc(v___x_574_);
v___x_577_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_574_);
lean_ctor_set(v___x_577_, 1, v___x_575_);
v___x_578_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__8));
v___x_579_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__10));
v___x_580_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__11));
lean_inc(v___x_574_);
v___x_581_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_581_, 0, v___x_574_);
lean_ctor_set(v___x_581_, 1, v___x_580_);
v___x_582_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__13));
v___x_583_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__15));
v___x_584_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__16));
v___x_585_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__17));
lean_inc(v___x_574_);
v___x_586_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_586_, 0, v___x_574_);
lean_ctor_set(v___x_586_, 1, v___x_584_);
v___x_587_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__20));
v___x_588_ = lean_obj_once(&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__22, &l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__22_once, _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__22);
v___x_589_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__27));
lean_inc(v_currMacroScope_571_);
lean_inc(v_quotContext_570_);
v___x_590_ = l_Lean_addMacroScope(v_quotContext_570_, v___x_589_, v_currMacroScope_571_);
v___x_591_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__31));
lean_inc(v___x_574_);
v___x_592_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_592_, 0, v___x_574_);
lean_ctor_set(v___x_592_, 1, v___x_588_);
lean_ctor_set(v___x_592_, 2, v___x_590_);
lean_ctor_set(v___x_592_, 3, v___x_591_);
v___x_593_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__33));
v___x_594_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__34));
lean_inc(v___x_574_);
v___x_595_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_595_, 0, v___x_574_);
lean_ctor_set(v___x_595_, 1, v___x_594_);
v___x_596_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__36));
v___x_597_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__37));
lean_inc(v___x_574_);
v___x_598_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_598_, 0, v___x_574_);
lean_ctor_set(v___x_598_, 1, v___x_597_);
lean_inc(v___x_574_);
v___x_599_ = l_Lean_Syntax_node1(v___x_574_, v___x_596_, v___x_598_);
v___x_600_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__38));
lean_inc(v___x_574_);
v___x_601_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_601_, 0, v___x_574_);
lean_ctor_set(v___x_601_, 1, v___x_600_);
lean_inc(v___x_574_);
v___x_602_ = l_Lean_Syntax_node3(v___x_574_, v___x_593_, v___x_595_, v___x_599_, v___x_601_);
lean_inc(v___x_574_);
v___x_603_ = l_Lean_Syntax_node1(v___x_574_, v___x_578_, v___x_602_);
lean_inc(v___x_603_);
lean_inc(v___x_574_);
v___x_604_ = l_Lean_Syntax_node2(v___x_574_, v___x_587_, v___x_592_, v___x_603_);
lean_inc_ref(v___x_586_);
lean_inc(v___x_574_);
v___x_605_ = l_Lean_Syntax_node2(v___x_574_, v___x_585_, v___x_586_, v___x_604_);
lean_inc(v___x_574_);
v___x_606_ = l_Lean_Syntax_node1(v___x_574_, v___x_578_, v___x_605_);
lean_inc(v___x_574_);
v___x_607_ = l_Lean_Syntax_node1(v___x_574_, v___x_583_, v___x_606_);
lean_inc(v___x_574_);
v___x_608_ = l_Lean_Syntax_node1(v___x_574_, v___x_582_, v___x_607_);
lean_inc_ref(v___x_581_);
lean_inc(v___x_574_);
v___x_609_ = l_Lean_Syntax_node2(v___x_574_, v___x_579_, v___x_581_, v___x_608_);
v___x_610_ = lean_obj_once(&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__40, &l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__40_once, _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__40);
v___x_611_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__42));
v___x_612_ = l_Lean_addMacroScope(v_quotContext_570_, v___x_611_, v_currMacroScope_571_);
v___x_613_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__45));
lean_inc(v___x_574_);
v___x_614_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_614_, 0, v___x_574_);
lean_ctor_set(v___x_614_, 1, v___x_610_);
lean_ctor_set(v___x_614_, 2, v___x_612_);
lean_ctor_set(v___x_614_, 3, v___x_613_);
lean_inc(v___x_574_);
v___x_615_ = l_Lean_Syntax_node2(v___x_574_, v___x_587_, v___x_614_, v___x_603_);
lean_inc(v___x_574_);
v___x_616_ = l_Lean_Syntax_node2(v___x_574_, v___x_585_, v___x_586_, v___x_615_);
lean_inc(v___x_574_);
v___x_617_ = l_Lean_Syntax_node1(v___x_574_, v___x_578_, v___x_616_);
lean_inc(v___x_574_);
v___x_618_ = l_Lean_Syntax_node1(v___x_574_, v___x_583_, v___x_617_);
lean_inc(v___x_574_);
v___x_619_ = l_Lean_Syntax_node1(v___x_574_, v___x_582_, v___x_618_);
lean_inc_ref(v___x_581_);
lean_inc(v___x_574_);
v___x_620_ = l_Lean_Syntax_node2(v___x_574_, v___x_579_, v___x_581_, v___x_619_);
v___x_621_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__46));
v___x_622_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__47));
lean_inc(v___x_574_);
v___x_623_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_623_, 0, v___x_574_);
lean_ctor_set(v___x_623_, 1, v___x_621_);
v___x_624_ = lean_obj_once(&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48, &l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48_once, _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48);
lean_inc(v___x_574_);
v___x_625_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_625_, 0, v___x_574_);
lean_ctor_set(v___x_625_, 1, v___x_578_);
lean_ctor_set(v___x_625_, 2, v___x_624_);
lean_inc(v___x_574_);
v___x_626_ = l_Lean_Syntax_node2(v___x_574_, v___x_622_, v___x_623_, v___x_625_);
lean_inc(v___x_574_);
v___x_627_ = l_Lean_Syntax_node1(v___x_574_, v___x_578_, v___x_626_);
lean_inc(v___x_574_);
v___x_628_ = l_Lean_Syntax_node1(v___x_574_, v___x_583_, v___x_627_);
lean_inc(v___x_574_);
v___x_629_ = l_Lean_Syntax_node1(v___x_574_, v___x_582_, v___x_628_);
lean_inc(v___x_574_);
v___x_630_ = l_Lean_Syntax_node2(v___x_574_, v___x_579_, v___x_581_, v___x_629_);
lean_inc(v___x_574_);
v___x_631_ = l_Lean_Syntax_node3(v___x_574_, v___x_578_, v___x_609_, v___x_620_, v___x_630_);
v___x_632_ = l_Lean_Syntax_node2(v___x_574_, v___x_576_, v___x_577_, v___x_631_);
v___x_633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
lean_ctor_set(v___x_633_, 1, v_a_565_);
return v___x_633_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySteps___redArg(lean_object* v_it_634_){
_start:
{
lean_inc(v_it_634_);
return v_it_634_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySteps___redArg___boxed(lean_object* v_it_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l_Std_Iter_finitelyManySteps___redArg(v_it_635_);
lean_dec(v_it_635_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySteps(lean_object* v_00_u03b1_637_, lean_object* v_00_u03b2_638_, lean_object* v_inst_639_, lean_object* v_inst_640_, lean_object* v_it_641_){
_start:
{
lean_inc(v_it_641_);
return v_it_641_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySteps___boxed(lean_object* v_00_u03b1_642_, lean_object* v_00_u03b2_643_, lean_object* v_inst_644_, lean_object* v_inst_645_, lean_object* v_it_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l_Std_Iter_finitelyManySteps(v_00_u03b1_642_, v_00_u03b2_643_, v_inst_644_, v_inst_645_, v_it_646_);
lean_dec(v_it_646_);
lean_dec(v_inst_644_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySteps_x21___redArg(lean_object* v_it_648_){
_start:
{
lean_inc(v_it_648_);
return v_it_648_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySteps_x21___redArg___boxed(lean_object* v_it_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l_Std_Iter_finitelyManySteps_x21___redArg(v_it_649_);
lean_dec(v_it_649_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySteps_x21(lean_object* v_00_u03b1_651_, lean_object* v_00_u03b2_652_, lean_object* v_inst_653_, lean_object* v_it_654_){
_start:
{
lean_inc(v_it_654_);
return v_it_654_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySteps_x21___boxed(lean_object* v_00_u03b1_655_, lean_object* v_00_u03b2_656_, lean_object* v_inst_657_, lean_object* v_it_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_Std_Iter_finitelyManySteps_x21(v_00_u03b1_655_, v_00_u03b2_656_, v_inst_657_, v_it_658_);
lean_dec(v_it_658_);
lean_dec(v_inst_657_);
return v_res_659_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__1(void){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_661_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__0));
v___x_662_ = l_String_toRawSubstring_x27(v___x_661_);
return v___x_662_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__8(void){
_start:
{
lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_682_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__7));
v___x_683_ = l_String_toRawSubstring_x27(v___x_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2(lean_object* v_x_701_, lean_object* v_a_702_, lean_object* v_a_703_){
_start:
{
lean_object* v___x_704_; uint8_t v___x_705_; 
v___x_704_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__1));
v___x_705_ = l_Lean_Syntax_isOfKind(v_x_701_, v___x_704_);
if (v___x_705_ == 0)
{
lean_object* v___x_706_; lean_object* v___x_707_; 
lean_dec_ref(v_a_702_);
v___x_706_ = lean_box(1);
v___x_707_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_707_, 0, v___x_706_);
lean_ctor_set(v___x_707_, 1, v_a_703_);
return v___x_707_;
}
else
{
lean_object* v_quotContext_708_; lean_object* v_currMacroScope_709_; lean_object* v_ref_710_; uint8_t v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
v_quotContext_708_ = lean_ctor_get(v_a_702_, 1);
lean_inc(v_quotContext_708_);
v_currMacroScope_709_ = lean_ctor_get(v_a_702_, 2);
lean_inc(v_currMacroScope_709_);
v_ref_710_ = lean_ctor_get(v_a_702_, 5);
lean_inc(v_ref_710_);
lean_dec_ref(v_a_702_);
v___x_711_ = 0;
v___x_712_ = l_Lean_SourceInfo_fromRef(v_ref_710_, v___x_711_);
lean_dec(v_ref_710_);
v___x_713_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__5));
v___x_714_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__6));
lean_inc(v___x_712_);
v___x_715_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_715_, 0, v___x_712_);
lean_ctor_set(v___x_715_, 1, v___x_713_);
v___x_716_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__8));
v___x_717_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__10));
v___x_718_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__11));
lean_inc(v___x_712_);
v___x_719_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_719_, 0, v___x_712_);
lean_ctor_set(v___x_719_, 1, v___x_718_);
v___x_720_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__13));
v___x_721_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__15));
v___x_722_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__16));
v___x_723_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__17));
lean_inc(v___x_712_);
v___x_724_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_724_, 0, v___x_712_);
lean_ctor_set(v___x_724_, 1, v___x_722_);
v___x_725_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__20));
v___x_726_ = lean_obj_once(&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__1, &l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__1_once, _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__1);
v___x_727_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__3));
lean_inc(v_currMacroScope_709_);
lean_inc(v_quotContext_708_);
v___x_728_ = l_Lean_addMacroScope(v_quotContext_708_, v___x_727_, v_currMacroScope_709_);
v___x_729_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__6));
lean_inc(v___x_712_);
v___x_730_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_730_, 0, v___x_712_);
lean_ctor_set(v___x_730_, 1, v___x_726_);
lean_ctor_set(v___x_730_, 2, v___x_728_);
lean_ctor_set(v___x_730_, 3, v___x_729_);
v___x_731_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__33));
v___x_732_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__34));
lean_inc(v___x_712_);
v___x_733_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_733_, 0, v___x_712_);
lean_ctor_set(v___x_733_, 1, v___x_732_);
v___x_734_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__36));
v___x_735_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__37));
lean_inc(v___x_712_);
v___x_736_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_736_, 0, v___x_712_);
lean_ctor_set(v___x_736_, 1, v___x_735_);
lean_inc(v___x_712_);
v___x_737_ = l_Lean_Syntax_node1(v___x_712_, v___x_734_, v___x_736_);
v___x_738_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__38));
lean_inc(v___x_712_);
v___x_739_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_739_, 0, v___x_712_);
lean_ctor_set(v___x_739_, 1, v___x_738_);
lean_inc(v___x_712_);
v___x_740_ = l_Lean_Syntax_node3(v___x_712_, v___x_731_, v___x_733_, v___x_737_, v___x_739_);
lean_inc(v___x_712_);
v___x_741_ = l_Lean_Syntax_node1(v___x_712_, v___x_716_, v___x_740_);
lean_inc(v___x_741_);
lean_inc(v___x_712_);
v___x_742_ = l_Lean_Syntax_node2(v___x_712_, v___x_725_, v___x_730_, v___x_741_);
lean_inc_ref(v___x_724_);
lean_inc(v___x_712_);
v___x_743_ = l_Lean_Syntax_node2(v___x_712_, v___x_723_, v___x_724_, v___x_742_);
lean_inc(v___x_712_);
v___x_744_ = l_Lean_Syntax_node1(v___x_712_, v___x_716_, v___x_743_);
lean_inc(v___x_712_);
v___x_745_ = l_Lean_Syntax_node1(v___x_712_, v___x_721_, v___x_744_);
lean_inc(v___x_712_);
v___x_746_ = l_Lean_Syntax_node1(v___x_712_, v___x_720_, v___x_745_);
lean_inc_ref(v___x_719_);
lean_inc(v___x_712_);
v___x_747_ = l_Lean_Syntax_node2(v___x_712_, v___x_717_, v___x_719_, v___x_746_);
v___x_748_ = lean_obj_once(&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__8, &l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__8_once, _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__8);
v___x_749_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__9));
v___x_750_ = l_Lean_addMacroScope(v_quotContext_708_, v___x_749_, v_currMacroScope_709_);
v___x_751_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__12));
lean_inc(v___x_712_);
v___x_752_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_752_, 0, v___x_712_);
lean_ctor_set(v___x_752_, 1, v___x_748_);
lean_ctor_set(v___x_752_, 2, v___x_750_);
lean_ctor_set(v___x_752_, 3, v___x_751_);
lean_inc(v___x_712_);
v___x_753_ = l_Lean_Syntax_node2(v___x_712_, v___x_725_, v___x_752_, v___x_741_);
lean_inc(v___x_712_);
v___x_754_ = l_Lean_Syntax_node2(v___x_712_, v___x_723_, v___x_724_, v___x_753_);
lean_inc(v___x_712_);
v___x_755_ = l_Lean_Syntax_node1(v___x_712_, v___x_716_, v___x_754_);
lean_inc(v___x_712_);
v___x_756_ = l_Lean_Syntax_node1(v___x_712_, v___x_721_, v___x_755_);
lean_inc(v___x_712_);
v___x_757_ = l_Lean_Syntax_node1(v___x_712_, v___x_720_, v___x_756_);
lean_inc_ref(v___x_719_);
lean_inc(v___x_712_);
v___x_758_ = l_Lean_Syntax_node2(v___x_712_, v___x_717_, v___x_719_, v___x_757_);
v___x_759_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__46));
v___x_760_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__47));
lean_inc(v___x_712_);
v___x_761_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_761_, 0, v___x_712_);
lean_ctor_set(v___x_761_, 1, v___x_759_);
v___x_762_ = lean_obj_once(&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48, &l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48_once, _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48);
lean_inc(v___x_712_);
v___x_763_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_763_, 0, v___x_712_);
lean_ctor_set(v___x_763_, 1, v___x_716_);
lean_ctor_set(v___x_763_, 2, v___x_762_);
lean_inc(v___x_712_);
v___x_764_ = l_Lean_Syntax_node2(v___x_712_, v___x_760_, v___x_761_, v___x_763_);
lean_inc(v___x_712_);
v___x_765_ = l_Lean_Syntax_node1(v___x_712_, v___x_716_, v___x_764_);
lean_inc(v___x_712_);
v___x_766_ = l_Lean_Syntax_node1(v___x_712_, v___x_721_, v___x_765_);
lean_inc(v___x_712_);
v___x_767_ = l_Lean_Syntax_node1(v___x_712_, v___x_720_, v___x_766_);
lean_inc(v___x_712_);
v___x_768_ = l_Lean_Syntax_node2(v___x_712_, v___x_717_, v___x_719_, v___x_767_);
lean_inc(v___x_712_);
v___x_769_ = l_Lean_Syntax_node3(v___x_712_, v___x_716_, v___x_747_, v___x_758_, v___x_768_);
v___x_770_ = l_Lean_Syntax_node2(v___x_712_, v___x_714_, v___x_715_, v___x_769_);
v___x_771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_771_, 0, v___x_770_);
lean_ctor_set(v___x_771_, 1, v_a_703_);
return v___x_771_;
}
}
}
LEAN_EXPORT lean_object* l_Std_IterM_TerminationMeasures_instWellFoundedRelationProductive(lean_object* v_00_u03b1_772_, lean_object* v_m_773_, lean_object* v_00_u03b2_774_, lean_object* v_inst_775_, lean_object* v_inst_776_){
_start:
{
lean_object* v___x_777_; 
v___x_777_ = lean_box(0);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_TerminationMeasures_instWellFoundedRelationProductive___boxed(lean_object* v_00_u03b1_778_, lean_object* v_m_779_, lean_object* v_00_u03b2_780_, lean_object* v_inst_781_, lean_object* v_inst_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_Std_IterM_TerminationMeasures_instWellFoundedRelationProductive(v_00_u03b1_778_, v_m_779_, v_00_u03b2_780_, v_inst_781_, v_inst_782_);
lean_dec(v_inst_781_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySkips___redArg(lean_object* v_it_784_){
_start:
{
lean_inc(v_it_784_);
return v_it_784_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySkips___redArg___boxed(lean_object* v_it_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l_Std_IterM_finitelyManySkips___redArg(v_it_785_);
lean_dec(v_it_785_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySkips(lean_object* v_00_u03b1_787_, lean_object* v_m_788_, lean_object* v_00_u03b2_789_, lean_object* v_inst_790_, lean_object* v_inst_791_, lean_object* v_it_792_){
_start:
{
lean_inc(v_it_792_);
return v_it_792_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySkips___boxed(lean_object* v_00_u03b1_793_, lean_object* v_m_794_, lean_object* v_00_u03b2_795_, lean_object* v_inst_796_, lean_object* v_inst_797_, lean_object* v_it_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_Std_IterM_finitelyManySkips(v_00_u03b1_793_, v_m_794_, v_00_u03b2_795_, v_inst_796_, v_inst_797_, v_it_798_);
lean_dec(v_it_798_);
lean_dec(v_inst_796_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySkips_x21___redArg(lean_object* v_it_800_){
_start:
{
lean_inc(v_it_800_);
return v_it_800_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySkips_x21___redArg___boxed(lean_object* v_it_801_){
_start:
{
lean_object* v_res_802_; 
v_res_802_ = l_Std_IterM_finitelyManySkips_x21___redArg(v_it_801_);
lean_dec(v_it_801_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySkips_x21(lean_object* v_00_u03b1_803_, lean_object* v_m_804_, lean_object* v_00_u03b2_805_, lean_object* v_inst_806_, lean_object* v_it_807_){
_start:
{
lean_inc(v_it_807_);
return v_it_807_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_finitelyManySkips_x21___boxed(lean_object* v_00_u03b1_808_, lean_object* v_m_809_, lean_object* v_00_u03b2_810_, lean_object* v_inst_811_, lean_object* v_it_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l_Std_IterM_finitelyManySkips_x21(v_00_u03b1_808_, v_m_809_, v_00_u03b2_810_, v_inst_811_, v_it_812_);
lean_dec(v_it_812_);
lean_dec(v_inst_811_);
return v_res_813_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__1(void){
_start:
{
lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_815_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__0));
v___x_816_ = l_String_toRawSubstring_x27(v___x_815_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3(lean_object* v_x_835_, lean_object* v_a_836_, lean_object* v_a_837_){
_start:
{
lean_object* v___x_838_; uint8_t v___x_839_; 
v___x_838_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__1));
v___x_839_ = l_Lean_Syntax_isOfKind(v_x_835_, v___x_838_);
if (v___x_839_ == 0)
{
lean_object* v___x_840_; lean_object* v___x_841_; 
lean_dec_ref(v_a_836_);
v___x_840_ = lean_box(1);
v___x_841_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_841_, 0, v___x_840_);
lean_ctor_set(v___x_841_, 1, v_a_837_);
return v___x_841_;
}
else
{
lean_object* v_quotContext_842_; lean_object* v_currMacroScope_843_; lean_object* v_ref_844_; uint8_t v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v_quotContext_842_ = lean_ctor_get(v_a_836_, 1);
lean_inc(v_quotContext_842_);
v_currMacroScope_843_ = lean_ctor_get(v_a_836_, 2);
lean_inc(v_currMacroScope_843_);
v_ref_844_ = lean_ctor_get(v_a_836_, 5);
lean_inc(v_ref_844_);
lean_dec_ref(v_a_836_);
v___x_845_ = 0;
v___x_846_ = l_Lean_SourceInfo_fromRef(v_ref_844_, v___x_845_);
lean_dec(v_ref_844_);
v___x_847_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__5));
v___x_848_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__6));
lean_inc(v___x_846_);
v___x_849_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_849_, 0, v___x_846_);
lean_ctor_set(v___x_849_, 1, v___x_847_);
v___x_850_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__8));
v___x_851_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__10));
v___x_852_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__11));
lean_inc(v___x_846_);
v___x_853_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_853_, 0, v___x_846_);
lean_ctor_set(v___x_853_, 1, v___x_852_);
v___x_854_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__13));
v___x_855_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__15));
v___x_856_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__16));
v___x_857_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__17));
lean_inc(v___x_846_);
v___x_858_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_858_, 0, v___x_846_);
lean_ctor_set(v___x_858_, 1, v___x_856_);
v___x_859_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__20));
v___x_860_ = lean_obj_once(&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__1, &l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__1_once, _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__1);
v___x_861_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__3));
v___x_862_ = l_Lean_addMacroScope(v_quotContext_842_, v___x_861_, v_currMacroScope_843_);
v___x_863_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__6));
lean_inc(v___x_846_);
v___x_864_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_864_, 0, v___x_846_);
lean_ctor_set(v___x_864_, 1, v___x_860_);
lean_ctor_set(v___x_864_, 2, v___x_862_);
lean_ctor_set(v___x_864_, 3, v___x_863_);
v___x_865_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__33));
v___x_866_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__34));
lean_inc(v___x_846_);
v___x_867_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_867_, 0, v___x_846_);
lean_ctor_set(v___x_867_, 1, v___x_866_);
v___x_868_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__36));
v___x_869_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__37));
lean_inc(v___x_846_);
v___x_870_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_870_, 0, v___x_846_);
lean_ctor_set(v___x_870_, 1, v___x_869_);
lean_inc(v___x_846_);
v___x_871_ = l_Lean_Syntax_node1(v___x_846_, v___x_868_, v___x_870_);
v___x_872_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__38));
lean_inc(v___x_846_);
v___x_873_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_873_, 0, v___x_846_);
lean_ctor_set(v___x_873_, 1, v___x_872_);
lean_inc(v___x_846_);
v___x_874_ = l_Lean_Syntax_node3(v___x_846_, v___x_865_, v___x_867_, v___x_871_, v___x_873_);
lean_inc(v___x_846_);
v___x_875_ = l_Lean_Syntax_node1(v___x_846_, v___x_850_, v___x_874_);
lean_inc(v___x_846_);
v___x_876_ = l_Lean_Syntax_node2(v___x_846_, v___x_859_, v___x_864_, v___x_875_);
lean_inc(v___x_846_);
v___x_877_ = l_Lean_Syntax_node2(v___x_846_, v___x_857_, v___x_858_, v___x_876_);
lean_inc(v___x_846_);
v___x_878_ = l_Lean_Syntax_node1(v___x_846_, v___x_850_, v___x_877_);
lean_inc(v___x_846_);
v___x_879_ = l_Lean_Syntax_node1(v___x_846_, v___x_855_, v___x_878_);
lean_inc(v___x_846_);
v___x_880_ = l_Lean_Syntax_node1(v___x_846_, v___x_854_, v___x_879_);
lean_inc_ref(v___x_853_);
lean_inc(v___x_846_);
v___x_881_ = l_Lean_Syntax_node2(v___x_846_, v___x_851_, v___x_853_, v___x_880_);
v___x_882_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__46));
v___x_883_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__47));
lean_inc(v___x_846_);
v___x_884_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_884_, 0, v___x_846_);
lean_ctor_set(v___x_884_, 1, v___x_882_);
v___x_885_ = lean_obj_once(&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48, &l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48_once, _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48);
lean_inc(v___x_846_);
v___x_886_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_886_, 0, v___x_846_);
lean_ctor_set(v___x_886_, 1, v___x_850_);
lean_ctor_set(v___x_886_, 2, v___x_885_);
lean_inc(v___x_846_);
v___x_887_ = l_Lean_Syntax_node2(v___x_846_, v___x_883_, v___x_884_, v___x_886_);
lean_inc(v___x_846_);
v___x_888_ = l_Lean_Syntax_node1(v___x_846_, v___x_850_, v___x_887_);
lean_inc(v___x_846_);
v___x_889_ = l_Lean_Syntax_node1(v___x_846_, v___x_855_, v___x_888_);
lean_inc(v___x_846_);
v___x_890_ = l_Lean_Syntax_node1(v___x_846_, v___x_854_, v___x_889_);
lean_inc(v___x_846_);
v___x_891_ = l_Lean_Syntax_node2(v___x_846_, v___x_851_, v___x_853_, v___x_890_);
lean_inc(v___x_846_);
v___x_892_ = l_Lean_Syntax_node2(v___x_846_, v___x_850_, v___x_881_, v___x_891_);
v___x_893_ = l_Lean_Syntax_node2(v___x_846_, v___x_848_, v___x_849_, v___x_892_);
v___x_894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_894_, 0, v___x_893_);
lean_ctor_set(v___x_894_, 1, v_a_837_);
return v___x_894_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySkips___redArg(lean_object* v_it_895_){
_start:
{
lean_inc(v_it_895_);
return v_it_895_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySkips___redArg___boxed(lean_object* v_it_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l_Std_Iter_finitelyManySkips___redArg(v_it_896_);
lean_dec(v_it_896_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySkips(lean_object* v_00_u03b1_898_, lean_object* v_00_u03b2_899_, lean_object* v_inst_900_, lean_object* v_inst_901_, lean_object* v_it_902_){
_start:
{
lean_inc(v_it_902_);
return v_it_902_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySkips___boxed(lean_object* v_00_u03b1_903_, lean_object* v_00_u03b2_904_, lean_object* v_inst_905_, lean_object* v_inst_906_, lean_object* v_it_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l_Std_Iter_finitelyManySkips(v_00_u03b1_903_, v_00_u03b2_904_, v_inst_905_, v_inst_906_, v_it_907_);
lean_dec(v_it_907_);
lean_dec(v_inst_905_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySkips_x21___redArg(lean_object* v_it_909_){
_start:
{
lean_inc(v_it_909_);
return v_it_909_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySkips_x21___redArg___boxed(lean_object* v_it_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_Std_Iter_finitelyManySkips_x21___redArg(v_it_910_);
lean_dec(v_it_910_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySkips_x21(lean_object* v_00_u03b1_912_, lean_object* v_00_u03b2_913_, lean_object* v_inst_914_, lean_object* v_it_915_){
_start:
{
lean_inc(v_it_915_);
return v_it_915_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_finitelyManySkips_x21___boxed(lean_object* v_00_u03b1_916_, lean_object* v_00_u03b2_917_, lean_object* v_inst_918_, lean_object* v_it_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l_Std_Iter_finitelyManySkips_x21(v_00_u03b1_916_, v_00_u03b2_917_, v_inst_918_, v_it_919_);
lean_dec(v_it_919_);
lean_dec(v_inst_918_);
return v_res_920_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__1(void){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_922_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__0));
v___x_923_ = l_String_toRawSubstring_x27(v___x_922_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4(lean_object* v_x_941_, lean_object* v_a_942_, lean_object* v_a_943_){
_start:
{
lean_object* v___x_944_; uint8_t v___x_945_; 
v___x_944_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__1));
v___x_945_ = l_Lean_Syntax_isOfKind(v_x_941_, v___x_944_);
if (v___x_945_ == 0)
{
lean_object* v___x_946_; lean_object* v___x_947_; 
lean_dec_ref(v_a_942_);
v___x_946_ = lean_box(1);
v___x_947_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_947_, 0, v___x_946_);
lean_ctor_set(v___x_947_, 1, v_a_943_);
return v___x_947_;
}
else
{
lean_object* v_quotContext_948_; lean_object* v_currMacroScope_949_; lean_object* v_ref_950_; uint8_t v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; 
v_quotContext_948_ = lean_ctor_get(v_a_942_, 1);
lean_inc(v_quotContext_948_);
v_currMacroScope_949_ = lean_ctor_get(v_a_942_, 2);
lean_inc(v_currMacroScope_949_);
v_ref_950_ = lean_ctor_get(v_a_942_, 5);
lean_inc(v_ref_950_);
lean_dec_ref(v_a_942_);
v___x_951_ = 0;
v___x_952_ = l_Lean_SourceInfo_fromRef(v_ref_950_, v___x_951_);
lean_dec(v_ref_950_);
v___x_953_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__5));
v___x_954_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__6));
lean_inc(v___x_952_);
v___x_955_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_955_, 0, v___x_952_);
lean_ctor_set(v___x_955_, 1, v___x_953_);
v___x_956_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__8));
v___x_957_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__10));
v___x_958_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__11));
lean_inc(v___x_952_);
v___x_959_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_959_, 0, v___x_952_);
lean_ctor_set(v___x_959_, 1, v___x_958_);
v___x_960_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__13));
v___x_961_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__15));
v___x_962_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__16));
v___x_963_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__17));
lean_inc(v___x_952_);
v___x_964_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_952_);
lean_ctor_set(v___x_964_, 1, v___x_962_);
v___x_965_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__20));
v___x_966_ = lean_obj_once(&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__1, &l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__1_once, _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__1);
v___x_967_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__2));
v___x_968_ = l_Lean_addMacroScope(v_quotContext_948_, v___x_967_, v_currMacroScope_949_);
v___x_969_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__5));
lean_inc(v___x_952_);
v___x_970_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_970_, 0, v___x_952_);
lean_ctor_set(v___x_970_, 1, v___x_966_);
lean_ctor_set(v___x_970_, 2, v___x_968_);
lean_ctor_set(v___x_970_, 3, v___x_969_);
v___x_971_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__33));
v___x_972_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__34));
lean_inc(v___x_952_);
v___x_973_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_973_, 0, v___x_952_);
lean_ctor_set(v___x_973_, 1, v___x_972_);
v___x_974_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__36));
v___x_975_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__37));
lean_inc(v___x_952_);
v___x_976_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_976_, 0, v___x_952_);
lean_ctor_set(v___x_976_, 1, v___x_975_);
lean_inc(v___x_952_);
v___x_977_ = l_Lean_Syntax_node1(v___x_952_, v___x_974_, v___x_976_);
v___x_978_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__38));
lean_inc(v___x_952_);
v___x_979_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_979_, 0, v___x_952_);
lean_ctor_set(v___x_979_, 1, v___x_978_);
lean_inc(v___x_952_);
v___x_980_ = l_Lean_Syntax_node3(v___x_952_, v___x_971_, v___x_973_, v___x_977_, v___x_979_);
lean_inc(v___x_952_);
v___x_981_ = l_Lean_Syntax_node1(v___x_952_, v___x_956_, v___x_980_);
lean_inc(v___x_952_);
v___x_982_ = l_Lean_Syntax_node2(v___x_952_, v___x_965_, v___x_970_, v___x_981_);
lean_inc(v___x_952_);
v___x_983_ = l_Lean_Syntax_node2(v___x_952_, v___x_963_, v___x_964_, v___x_982_);
lean_inc(v___x_952_);
v___x_984_ = l_Lean_Syntax_node1(v___x_952_, v___x_956_, v___x_983_);
lean_inc(v___x_952_);
v___x_985_ = l_Lean_Syntax_node1(v___x_952_, v___x_961_, v___x_984_);
lean_inc(v___x_952_);
v___x_986_ = l_Lean_Syntax_node1(v___x_952_, v___x_960_, v___x_985_);
lean_inc_ref(v___x_959_);
lean_inc(v___x_952_);
v___x_987_ = l_Lean_Syntax_node2(v___x_952_, v___x_957_, v___x_959_, v___x_986_);
v___x_988_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__46));
v___x_989_ = ((lean_object*)(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__47));
lean_inc(v___x_952_);
v___x_990_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_990_, 0, v___x_952_);
lean_ctor_set(v___x_990_, 1, v___x_988_);
v___x_991_ = lean_obj_once(&l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48, &l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48_once, _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48);
lean_inc(v___x_952_);
v___x_992_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_992_, 0, v___x_952_);
lean_ctor_set(v___x_992_, 1, v___x_956_);
lean_ctor_set(v___x_992_, 2, v___x_991_);
lean_inc(v___x_952_);
v___x_993_ = l_Lean_Syntax_node2(v___x_952_, v___x_989_, v___x_990_, v___x_992_);
lean_inc(v___x_952_);
v___x_994_ = l_Lean_Syntax_node1(v___x_952_, v___x_956_, v___x_993_);
lean_inc(v___x_952_);
v___x_995_ = l_Lean_Syntax_node1(v___x_952_, v___x_961_, v___x_994_);
lean_inc(v___x_952_);
v___x_996_ = l_Lean_Syntax_node1(v___x_952_, v___x_960_, v___x_995_);
lean_inc(v___x_952_);
v___x_997_ = l_Lean_Syntax_node2(v___x_952_, v___x_957_, v___x_959_, v___x_996_);
lean_inc(v___x_952_);
v___x_998_ = l_Lean_Syntax_node2(v___x_952_, v___x_956_, v___x_987_, v___x_997_);
v___x_999_ = l_Lean_Syntax_node2(v___x_952_, v___x_954_, v___x_955_, v___x_998_);
v___x_1000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___x_999_);
lean_ctor_set(v___x_1000_, 1, v_a_943_);
return v___x_1000_;
}
}
}
lean_object* runtime_initialize_Init_NotationExtra(uint8_t builtin);
lean_object* runtime_initialize_Init_WFTactics(uint8_t builtin);
lean_object* runtime_initialize_Init_Ext(uint8_t builtin);
lean_object* runtime_initialize_Init_PropLemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Iterators_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
