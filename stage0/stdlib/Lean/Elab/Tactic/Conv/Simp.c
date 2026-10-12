// Lean compiler output
// Module: Lean.Elab.Tactic.Conv.Simp
// Imports: public import Lean.Elab.Tactic.Split public import Lean.Elab.Tactic.Conv.Basic public import Lean.Elab.Tactic.SimpTrace
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
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSimpTheorems___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_mkSimpContext(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Conv_getLhs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Conv_changeLhs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Result_getProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Conv_updateLhs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_mkSimpCallStx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray3___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Meta_dsimp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_Meta_Split_simpMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_applySimpResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_applySimpResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__1;
static lean_once_cell_t l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__2;
static lean_once_cell_t l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__3;
static lean_once_cell_t l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__4;
static lean_once_cell_t l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__5;
static lean_once_cell_t l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___lam__1(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Conv_evalSimp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_getSimpTheorems___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimp___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Conv"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__5_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(235, 165, 42, 136, 187, 206, 234, 202)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__6_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "evalSimp"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__8_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__8_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(118, 221, 105, 79, 88, 54, 74, 185)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__8_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(20) << 1) | 1)),((lean_object*)(((size_t)(47) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(24) << 1) | 1)),((lean_object*)(((size_t)(24) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__0_value),((lean_object*)(((size_t)(47) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__1_value),((lean_object*)(((size_t)(24) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(20) << 1) | 1)),((lean_object*)(((size_t)(51) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(20) << 1) | 1)),((lean_object*)(((size_t)(59) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__3_value),((lean_object*)(((size_t)(51) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__4_value),((lean_object*)(((size_t)(59) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___boxed(lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tactic"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(99, 76, 33, 121, 85, 143, 17, 224)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Try this:"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__5_value;
static const lean_array_object l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__6_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "only"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__9_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__10;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "simpArgs"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__11_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "simpTrace"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 24, 207, 89, 155, 142, 251, 55)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "evalSimpTrace"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(237, 89, 177, 67, 170, 210, 173, 232)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "simpMatch"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(151, 31, 17, 130, 102, 107, 154, 37)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "evalSimpMatch"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(74, 229, 254, 188, 202, 148, 18, 189)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(26) << 1) | 1)),((lean_object*)(((size_t)(52) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(27) << 1) | 1)),((lean_object*)(((size_t)(48) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__0_value),((lean_object*)(((size_t)(52) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__1_value),((lean_object*)(((size_t)(48) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(26) << 1) | 1)),((lean_object*)(((size_t)(56) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(26) << 1) | 1)),((lean_object*)(((size_t)(69) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__3_value),((lean_object*)(((size_t)(56) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__4_value),((lean_object*)(((size_t)(69) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___boxed(lean_object*);
static const lean_array_object l_Lean_Elab_Tactic_Conv_evalDSimp___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalDSimp___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalDSimp___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimp___lam__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimp___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "dsimp"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 35, 2, 104, 74, 78, 120, 9)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "evalDSimp"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(230, 180, 75, 129, 95, 56, 151, 69)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(29) << 1) | 1)),((lean_object*)(((size_t)(48) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(31) << 1) | 1)),((lean_object*)(((size_t)(48) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__0_value),((lean_object*)(((size_t)(48) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__1_value),((lean_object*)(((size_t)(48) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(29) << 1) | 1)),((lean_object*)(((size_t)(52) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(29) << 1) | 1)),((lean_object*)(((size_t)(61) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__3_value),((lean_object*)(((size_t)(52) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__4_value),((lean_object*)(((size_t)(61) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalDSimpTrace___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "dsimpArgs"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalDSimpTrace___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalDSimpTrace___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimpTrace___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimpTrace___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "dsimpTrace"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(68, 139, 45, 80, 126, 130, 141, 19)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimpTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimpTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "evalDSimpTrace"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(137, 138, 90, 54, 138, 230, 31, 100)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___boxed(lean_object*);
lean_object* l_Lean_Elab_Tactic_Conv_applySimpResult(lean_object* v_result_1_, lean_object* v_a_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_, lean_object* v_a_9_){
_start:
{
lean_object* v_proof_x3f_11_; 
v_proof_x3f_11_ = lean_ctor_get(v_result_1_, 1);
if (lean_obj_tag(v_proof_x3f_11_) == 0)
{
lean_object* v_expr_12_; lean_object* v___x_13_; 
v_expr_12_ = lean_ctor_get(v_result_1_, 0);
lean_inc_ref(v_expr_12_);
lean_dec_ref(v_result_1_);
v___x_13_ = l_Lean_Elab_Tactic_Conv_changeLhs(v_expr_12_, v_a_2_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_);
return v___x_13_;
}
else
{
lean_object* v_expr_14_; lean_object* v___x_15_; 
v_expr_14_ = lean_ctor_get(v_result_1_, 0);
lean_inc_ref(v_expr_14_);
v___x_15_ = l_Lean_Meta_Simp_Result_getProof(v_result_1_, v_a_6_, v_a_7_, v_a_8_, v_a_9_);
if (lean_obj_tag(v___x_15_) == 0)
{
lean_object* v_a_16_; lean_object* v___x_17_; 
v_a_16_ = lean_ctor_get(v___x_15_, 0);
lean_inc(v_a_16_);
lean_dec_ref_known(v___x_15_, 1);
v___x_17_ = l_Lean_Elab_Tactic_Conv_updateLhs(v_expr_14_, v_a_16_, v_a_2_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_);
return v___x_17_;
}
else
{
lean_object* v_a_18_; lean_object* v___x_20_; uint8_t v_isShared_21_; uint8_t v_isSharedCheck_25_; 
lean_dec_ref(v_expr_14_);
v_a_18_ = lean_ctor_get(v___x_15_, 0);
v_isSharedCheck_25_ = !lean_is_exclusive(v___x_15_);
if (v_isSharedCheck_25_ == 0)
{
v___x_20_ = v___x_15_;
v_isShared_21_ = v_isSharedCheck_25_;
goto v_resetjp_19_;
}
else
{
lean_inc(v_a_18_);
lean_dec(v___x_15_);
v___x_20_ = lean_box(0);
v_isShared_21_ = v_isSharedCheck_25_;
goto v_resetjp_19_;
}
v_resetjp_19_:
{
lean_object* v___x_23_; 
if (v_isShared_21_ == 0)
{
v___x_23_ = v___x_20_;
goto v_reusejp_22_;
}
else
{
lean_object* v_reuseFailAlloc_24_; 
v_reuseFailAlloc_24_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_24_, 0, v_a_18_);
v___x_23_ = v_reuseFailAlloc_24_;
goto v_reusejp_22_;
}
v_reusejp_22_:
{
return v___x_23_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_applySimpResult_0interp(lean_interpreter_value* stack)
{
lean_object* v_result_1_ = stack[0].m_obj;
lean_object* v_a_2_ = stack[1].m_obj;
lean_object* v_a_3_ = stack[2].m_obj;
lean_object* v_a_4_ = stack[3].m_obj;
lean_object* v_a_5_ = stack[4].m_obj;
lean_object* v_a_6_ = stack[5].m_obj;
lean_object* v_a_7_ = stack[6].m_obj;
lean_object* v_a_8_ = stack[7].m_obj;
lean_object* v_a_9_ = stack[8].m_obj;
lean_object* v_res_26_;
v_res_26_ = l_Lean_Elab_Tactic_Conv_applySimpResult(v_result_1_, v_a_2_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_);
stack->m_obj
 = v_res_26_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_applySimpResult___boxed(lean_object* v_result_27_, lean_object* v_a_28_, lean_object* v_a_29_, lean_object* v_a_30_, lean_object* v_a_31_, lean_object* v_a_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_Elab_Tactic_Conv_applySimpResult(v_result_27_, v_a_28_, v_a_29_, v_a_30_, v_a_31_, v_a_32_, v_a_33_, v_a_34_, v_a_35_);
lean_dec(v_a_35_);
lean_dec_ref(v_a_34_);
lean_dec(v_a_33_);
lean_dec_ref(v_a_32_);
lean_dec(v_a_31_);
lean_dec_ref(v_a_30_);
lean_dec(v_a_29_);
lean_dec_ref(v_a_28_);
return v_res_37_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__0(void){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_38_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__1(void){
_start:
{
lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_39_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__0, &l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__0);
v___x_40_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_40_, 0, v___x_39_);
return v___x_40_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__2(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_41_ = lean_unsigned_to_nat(0u);
v___x_42_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__1, &l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__1);
v___x_43_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_43_, 0, v___x_42_);
lean_ctor_set(v___x_43_, 1, v___x_41_);
return v___x_43_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__3(void){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_44_ = lean_unsigned_to_nat(32u);
v___x_45_ = lean_mk_empty_array_with_capacity(v___x_44_);
v___x_46_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_46_, 0, v___x_45_);
return v___x_46_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__4(void){
_start:
{
size_t v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_47_ = ((size_t)5ULL);
v___x_48_ = lean_unsigned_to_nat(0u);
v___x_49_ = lean_unsigned_to_nat(32u);
v___x_50_ = lean_mk_empty_array_with_capacity(v___x_49_);
v___x_51_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__3, &l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__3);
v___x_52_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_52_, 0, v___x_51_);
lean_ctor_set(v___x_52_, 1, v___x_50_);
lean_ctor_set(v___x_52_, 2, v___x_48_);
lean_ctor_set(v___x_52_, 3, v___x_48_);
lean_ctor_set_usize(v___x_52_, 4, v___x_47_);
return v___x_52_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__5(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_53_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__4, &l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__4_once, _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__4);
v___x_54_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__1, &l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__1);
v___x_55_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_55_, 0, v___x_54_);
lean_ctor_set(v___x_55_, 1, v___x_54_);
lean_ctor_set(v___x_55_, 2, v___x_54_);
lean_ctor_set(v___x_55_, 3, v___x_53_);
return v___x_55_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6(void){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_56_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__5, &l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__5);
v___x_57_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__2, &l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__2);
v___x_58_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_58_, 0, v___x_57_);
lean_ctor_set(v___x_58_, 1, v___x_56_);
return v___x_58_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___lam__0(lean_object* v_a_59_, lean_object* v_ctx_60_, lean_object* v_simprocs_61_, lean_object* v_d_x3f_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_72_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6, &l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6);
v___x_73_ = l_Lean_Meta_simp(v_a_59_, v_ctx_60_, v_simprocs_61_, v_d_x3f_62_, v___x_72_, v___y_67_, v___y_68_, v___y_69_, v___y_70_);
return v___x_73_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_evalSimp___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_59_ = stack[0].m_obj;
lean_object* v_ctx_60_ = stack[1].m_obj;
lean_object* v_simprocs_61_ = stack[2].m_obj;
lean_object* v_d_x3f_62_ = stack[3].m_obj;
lean_object* v___y_63_ = stack[4].m_obj;
lean_object* v___y_64_ = stack[5].m_obj;
lean_object* v___y_65_ = stack[6].m_obj;
lean_object* v___y_66_ = stack[7].m_obj;
lean_object* v___y_67_ = stack[8].m_obj;
lean_object* v___y_68_ = stack[9].m_obj;
lean_object* v___y_69_ = stack[10].m_obj;
lean_object* v___y_70_ = stack[11].m_obj;
lean_object* v_res_74_;
v_res_74_ = l_Lean_Elab_Tactic_Conv_evalSimp___lam__0(v_a_59_, v_ctx_60_, v_simprocs_61_, v_d_x3f_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_, v___y_67_, v___y_68_, v___y_69_, v___y_70_);
stack->m_obj
 = v_res_74_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___boxed(lean_object* v_a_75_, lean_object* v_ctx_76_, lean_object* v_simprocs_77_, lean_object* v_d_x3f_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Lean_Elab_Tactic_Conv_evalSimp___lam__0(v_a_75_, v_ctx_76_, v_simprocs_77_, v_d_x3f_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_);
lean_dec(v___y_86_);
lean_dec_ref(v___y_85_);
lean_dec(v___y_84_);
lean_dec_ref(v___y_83_);
lean_dec(v___y_82_);
lean_dec_ref(v___y_81_);
lean_dec(v___y_80_);
lean_dec_ref(v___y_79_);
return v_res_88_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___lam__1(lean_object* v_stx_89_, uint8_t v___x_90_, uint8_t v___x_91_, lean_object* v___x_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = l_Lean_Elab_Tactic_mkSimpContext(v_stx_89_, v___x_90_, v___x_91_, v___x_90_, v___x_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_);
if (lean_obj_tag(v___x_102_) == 0)
{
lean_object* v_a_103_; lean_object* v_ctx_104_; lean_object* v_simprocs_105_; lean_object* v_dischargeWrapper_106_; lean_object* v___x_107_; 
v_a_103_ = lean_ctor_get(v___x_102_, 0);
lean_inc(v_a_103_);
lean_dec_ref_known(v___x_102_, 1);
v_ctx_104_ = lean_ctor_get(v_a_103_, 0);
lean_inc_ref(v_ctx_104_);
v_simprocs_105_ = lean_ctor_get(v_a_103_, 1);
lean_inc_ref(v_simprocs_105_);
v_dischargeWrapper_106_ = lean_ctor_get(v_a_103_, 2);
lean_inc(v_dischargeWrapper_106_);
lean_dec(v_a_103_);
v___x_107_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_94_, v___y_97_, v___y_98_, v___y_99_, v___y_100_);
if (lean_obj_tag(v___x_107_) == 0)
{
lean_object* v_a_108_; lean_object* v___f_109_; lean_object* v___x_110_; 
v_a_108_ = lean_ctor_get(v___x_107_, 0);
lean_inc(v_a_108_);
lean_dec_ref_known(v___x_107_, 1);
v___f_109_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___boxed), 13, 3);
lean_closure_set(v___f_109_, 0, v_a_108_);
lean_closure_set(v___f_109_, 1, v_ctx_104_);
lean_closure_set(v___f_109_, 2, v_simprocs_105_);
v___x_110_ = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(v_dischargeWrapper_106_, v___f_109_, v___y_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_);
lean_dec(v_dischargeWrapper_106_);
if (lean_obj_tag(v___x_110_) == 0)
{
lean_object* v_a_111_; lean_object* v_fst_112_; lean_object* v___x_113_; 
v_a_111_ = lean_ctor_get(v___x_110_, 0);
lean_inc(v_a_111_);
lean_dec_ref_known(v___x_110_, 1);
v_fst_112_ = lean_ctor_get(v_a_111_, 0);
lean_inc(v_fst_112_);
lean_dec(v_a_111_);
v___x_113_ = l_Lean_Elab_Tactic_Conv_applySimpResult(v_fst_112_, v___y_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_);
return v___x_113_;
}
else
{
lean_object* v_a_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_121_; 
v_a_114_ = lean_ctor_get(v___x_110_, 0);
v_isSharedCheck_121_ = !lean_is_exclusive(v___x_110_);
if (v_isSharedCheck_121_ == 0)
{
v___x_116_ = v___x_110_;
v_isShared_117_ = v_isSharedCheck_121_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_a_114_);
lean_dec(v___x_110_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_121_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
lean_object* v___x_119_; 
if (v_isShared_117_ == 0)
{
v___x_119_ = v___x_116_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v_a_114_);
v___x_119_ = v_reuseFailAlloc_120_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
return v___x_119_;
}
}
}
}
else
{
lean_object* v_a_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_129_; 
lean_dec(v_dischargeWrapper_106_);
lean_dec_ref(v_simprocs_105_);
lean_dec_ref(v_ctx_104_);
v_a_122_ = lean_ctor_get(v___x_107_, 0);
v_isSharedCheck_129_ = !lean_is_exclusive(v___x_107_);
if (v_isSharedCheck_129_ == 0)
{
v___x_124_ = v___x_107_;
v_isShared_125_ = v_isSharedCheck_129_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_a_122_);
lean_dec(v___x_107_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_129_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___x_127_; 
if (v_isShared_125_ == 0)
{
v___x_127_ = v___x_124_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v_a_122_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
return v___x_127_;
}
}
}
}
else
{
lean_object* v_a_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_137_; 
v_a_130_ = lean_ctor_get(v___x_102_, 0);
v_isSharedCheck_137_ = !lean_is_exclusive(v___x_102_);
if (v_isSharedCheck_137_ == 0)
{
v___x_132_ = v___x_102_;
v_isShared_133_ = v_isSharedCheck_137_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_a_130_);
lean_dec(v___x_102_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_137_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v___x_135_; 
if (v_isShared_133_ == 0)
{
v___x_135_ = v___x_132_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v_a_130_);
v___x_135_ = v_reuseFailAlloc_136_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
return v___x_135_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_evalSimp___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_89_ = stack[0].m_obj;
uint8_t v___x_90_ = stack[1].m_num;
uint8_t v___x_91_ = stack[2].m_num;
lean_object* v___x_92_ = stack[3].m_obj;
lean_object* v___y_93_ = stack[4].m_obj;
lean_object* v___y_94_ = stack[5].m_obj;
lean_object* v___y_95_ = stack[6].m_obj;
lean_object* v___y_96_ = stack[7].m_obj;
lean_object* v___y_97_ = stack[8].m_obj;
lean_object* v___y_98_ = stack[9].m_obj;
lean_object* v___y_99_ = stack[10].m_obj;
lean_object* v___y_100_ = stack[11].m_obj;
lean_object* v_res_138_;
v_res_138_ = l_Lean_Elab_Tactic_Conv_evalSimp___lam__1(v_stx_89_, v___x_90_, v___x_91_, v___x_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_);
stack->m_obj
 = v_res_138_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___lam__1___boxed(lean_object* v_stx_139_, lean_object* v___x_140_, lean_object* v___x_141_, lean_object* v___x_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_){
_start:
{
uint8_t v___x_806__boxed_152_; uint8_t v___x_807__boxed_153_; lean_object* v_res_154_; 
v___x_806__boxed_152_ = lean_unbox(v___x_140_);
v___x_807__boxed_153_ = lean_unbox(v___x_141_);
v_res_154_ = l_Lean_Elab_Tactic_Conv_evalSimp___lam__1(v_stx_139_, v___x_806__boxed_152_, v___x_807__boxed_153_, v___x_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_);
lean_dec(v___y_150_);
lean_dec_ref(v___y_149_);
lean_dec(v___y_148_);
lean_dec_ref(v___y_147_);
lean_dec(v___y_146_);
lean_dec_ref(v___y_145_);
lean_dec(v___y_144_);
lean_dec_ref(v___y_143_);
lean_dec(v_stx_139_);
return v_res_154_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_evalSimp(lean_object* v_stx_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_){
_start:
{
uint8_t v___x_166_; uint8_t v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___f_171_; lean_object* v___x_172_; 
v___x_166_ = 0;
v___x_167_ = 0;
v___x_168_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimp___closed__0));
v___x_169_ = lean_box(v___x_166_);
v___x_170_ = lean_box(v___x_167_);
v___f_171_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalSimp___lam__1___boxed), 13, 4);
lean_closure_set(v___f_171_, 0, v_stx_156_);
lean_closure_set(v___f_171_, 1, v___x_169_);
lean_closure_set(v___f_171_, 2, v___x_170_);
lean_closure_set(v___f_171_, 3, v___x_168_);
v___x_172_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_171_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_, v_a_164_);
return v___x_172_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_evalSimp_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_156_ = stack[0].m_obj;
lean_object* v_a_157_ = stack[1].m_obj;
lean_object* v_a_158_ = stack[2].m_obj;
lean_object* v_a_159_ = stack[3].m_obj;
lean_object* v_a_160_ = stack[4].m_obj;
lean_object* v_a_161_ = stack[5].m_obj;
lean_object* v_a_162_ = stack[6].m_obj;
lean_object* v_a_163_ = stack[7].m_obj;
lean_object* v_a_164_ = stack[8].m_obj;
lean_object* v_res_173_;
v_res_173_ = l_Lean_Elab_Tactic_Conv_evalSimp(v_stx_156_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_, v_a_164_);
stack->m_obj
 = v_res_173_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___boxed(lean_object* v_stx_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_Lean_Elab_Tactic_Conv_evalSimp(v_stx_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_);
lean_dec(v_a_182_);
lean_dec_ref(v_a_181_);
lean_dec(v_a_180_);
lean_dec_ref(v_a_179_);
lean_dec(v_a_178_);
lean_dec_ref(v_a_177_);
lean_dec(v_a_176_);
lean_dec_ref(v_a_175_);
return v_res_184_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1(){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_205_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_206_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__5));
v___x_207_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__8));
v___x_208_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalSimp___boxed), 10, 0);
v___x_209_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_205_, v___x_206_, v___x_207_, v___x_208_);
return v___x_209_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_210_;
v_res_210_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1();
stack->m_obj
 = v_res_210_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___boxed(lean_object* v_a_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1();
return v_res_212_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3(){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_238_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__8));
v___x_239_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__6));
v___x_240_ = l_Lean_addBuiltinDeclarationRanges(v___x_238_, v___x_239_);
return v___x_240_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_241_;
v_res_241_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3();
stack->m_obj
 = v_res_241_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___boxed(lean_object* v_a_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3();
return v_res_243_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_244_ = lean_box(0);
v___x_245_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_246_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_246_, 0, v___x_245_);
lean_ctor_set(v___x_246_, 1, v___x_244_);
return v___x_246_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg(){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_248_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg___closed__0);
v___x_249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_249_, 0, v___x_248_);
return v___x_249_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_250_;
v_res_250_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
stack->m_obj
 = v_res_250_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg___boxed(lean_object* v___y_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
return v_res_252_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0(lean_object* v_00_u03b1_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
return v___x_263_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_254_ = stack[1].m_obj;
lean_object* v___y_255_ = stack[2].m_obj;
lean_object* v___y_256_ = stack[3].m_obj;
lean_object* v___y_257_ = stack[4].m_obj;
lean_object* v___y_258_ = stack[5].m_obj;
lean_object* v___y_259_ = stack[6].m_obj;
lean_object* v___y_260_ = stack[7].m_obj;
lean_object* v___y_261_ = stack[8].m_obj;
lean_object* v_res_264_;
v_res_264_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0(lean_box(0), v___y_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_);
stack->m_obj
 = v_res_264_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___boxed(lean_object* v_00_u03b1_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0(v_00_u03b1_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
lean_dec(v___y_271_);
lean_dec_ref(v___y_270_);
lean_dec(v___y_269_);
lean_dec_ref(v___y_268_);
lean_dec(v___y_267_);
lean_dec_ref(v___y_266_);
return v_res_275_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__0(lean_object* v___x_276_, lean_object* v_a_277_, lean_object* v_ctx_278_, lean_object* v_simprocs_279_, lean_object* v_d_x3f_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_){
_start:
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; size_t v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_290_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__1, &l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__1);
lean_inc_n(v___x_276_, 2);
v___x_291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
lean_ctor_set(v___x_291_, 1, v___x_276_);
v___x_292_ = lean_unsigned_to_nat(32u);
v___x_293_ = lean_mk_empty_array_with_capacity(v___x_292_);
v___x_294_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__3, &l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__3);
v___x_295_ = ((size_t)5ULL);
v___x_296_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_296_, 0, v___x_294_);
lean_ctor_set(v___x_296_, 1, v___x_293_);
lean_ctor_set(v___x_296_, 2, v___x_276_);
lean_ctor_set(v___x_296_, 3, v___x_276_);
lean_ctor_set_usize(v___x_296_, 4, v___x_295_);
v___x_297_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_297_, 0, v___x_290_);
lean_ctor_set(v___x_297_, 1, v___x_290_);
lean_ctor_set(v___x_297_, 2, v___x_290_);
lean_ctor_set(v___x_297_, 3, v___x_296_);
v___x_298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_298_, 0, v___x_291_);
lean_ctor_set(v___x_298_, 1, v___x_297_);
v___x_299_ = l_Lean_Meta_simp(v_a_277_, v_ctx_278_, v_simprocs_279_, v_d_x3f_280_, v___x_298_, v___y_285_, v___y_286_, v___y_287_, v___y_288_);
lean_dec_ref_known(v___x_298_, 2);
return v___x_299_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_276_ = stack[0].m_obj;
lean_object* v_a_277_ = stack[1].m_obj;
lean_object* v_ctx_278_ = stack[2].m_obj;
lean_object* v_simprocs_279_ = stack[3].m_obj;
lean_object* v_d_x3f_280_ = stack[4].m_obj;
lean_object* v___y_281_ = stack[5].m_obj;
lean_object* v___y_282_ = stack[6].m_obj;
lean_object* v___y_283_ = stack[7].m_obj;
lean_object* v___y_284_ = stack[8].m_obj;
lean_object* v___y_285_ = stack[9].m_obj;
lean_object* v___y_286_ = stack[10].m_obj;
lean_object* v___y_287_ = stack[11].m_obj;
lean_object* v___y_288_ = stack[12].m_obj;
lean_object* v_res_300_;
v_res_300_ = l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__0(v___x_276_, v_a_277_, v_ctx_278_, v_simprocs_279_, v_d_x3f_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_);
stack->m_obj
 = v_res_300_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__0___boxed(lean_object* v___x_301_, lean_object* v_a_302_, lean_object* v_ctx_303_, lean_object* v_simprocs_304_, lean_object* v_d_x3f_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__0(v___x_301_, v_a_302_, v_ctx_303_, v_simprocs_304_, v_d_x3f_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_);
lean_dec(v___y_313_);
lean_dec_ref(v___y_312_);
lean_dec(v___y_311_);
lean_dec_ref(v___y_310_);
lean_dec(v___y_309_);
lean_dec_ref(v___y_308_);
lean_dec(v___y_307_);
lean_dec_ref(v___y_306_);
return v_res_315_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__10(void){
_start:
{
lean_object* v___x_329_; 
v___x_329_ = l_Array_mkArray0___redArg();
return v___x_329_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1(uint8_t v___x_331_, lean_object* v_stx_332_, lean_object* v___x_333_, lean_object* v___x_334_, lean_object* v___x_335_, uint8_t v___x_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_){
_start:
{
if (v___x_331_ == 0)
{
lean_object* v___x_346_; 
lean_dec_ref(v___x_335_);
lean_dec_ref(v___x_334_);
lean_dec_ref(v___x_333_);
v___x_346_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
return v___x_346_;
}
else
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; uint8_t v___x_351_; 
v___x_347_ = lean_unsigned_to_nat(1u);
v___x_348_ = l_Lean_Syntax_getArg(v_stx_332_, v___x_347_);
v___x_349_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__0));
lean_inc_ref(v___x_335_);
lean_inc_ref(v___x_334_);
lean_inc_ref(v___x_333_);
v___x_350_ = l_Lean_Name_mkStr4(v___x_333_, v___x_334_, v___x_335_, v___x_349_);
lean_inc(v___x_348_);
v___x_351_ = l_Lean_Syntax_isOfKind(v___x_348_, v___x_350_);
lean_dec(v___x_350_);
if (v___x_351_ == 0)
{
lean_object* v___x_352_; 
lean_dec(v___x_348_);
lean_dec_ref(v___x_335_);
lean_dec_ref(v___x_334_);
lean_dec_ref(v___x_333_);
v___x_352_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
return v___x_352_;
}
else
{
lean_object* v___x_353_; lean_object* v_tk_354_; lean_object* v___y_356_; lean_object* v___y_357_; lean_object* v___y_358_; lean_object* v___y_359_; lean_object* v___y_360_; lean_object* v___y_361_; lean_object* v___y_362_; uint8_t v___y_363_; lean_object* v___y_364_; lean_object* v___y_365_; lean_object* v___y_366_; lean_object* v___y_367_; lean_object* v___y_368_; lean_object* v___y_369_; lean_object* v___y_370_; lean_object* v___y_371_; lean_object* v___y_372_; lean_object* v___y_373_; lean_object* v___y_452_; lean_object* v___y_453_; lean_object* v___y_454_; lean_object* v___y_455_; lean_object* v___y_456_; lean_object* v___y_457_; lean_object* v___y_458_; uint8_t v___y_459_; lean_object* v___y_460_; lean_object* v___y_461_; lean_object* v___y_462_; lean_object* v___y_463_; lean_object* v___y_464_; lean_object* v___y_465_; lean_object* v___y_466_; lean_object* v___y_467_; lean_object* v___y_468_; lean_object* v___y_469_; lean_object* v___y_482_; lean_object* v___y_483_; lean_object* v___y_484_; lean_object* v___y_485_; lean_object* v___y_486_; lean_object* v___y_487_; uint8_t v___y_488_; lean_object* v___y_489_; lean_object* v___y_490_; lean_object* v___y_491_; lean_object* v___y_492_; lean_object* v___y_493_; lean_object* v___y_494_; lean_object* v___y_495_; lean_object* v___y_496_; lean_object* v___y_497_; lean_object* v___y_498_; lean_object* v___y_499_; lean_object* v___y_509_; lean_object* v___y_510_; lean_object* v___y_511_; lean_object* v___y_512_; lean_object* v___y_513_; lean_object* v___y_514_; lean_object* v___y_515_; lean_object* v___y_516_; lean_object* v___y_517_; lean_object* v___y_518_; lean_object* v___y_519_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___y_535_; lean_object* v_args_536_; lean_object* v___y_537_; lean_object* v___y_538_; lean_object* v___y_539_; lean_object* v___y_540_; lean_object* v___y_541_; lean_object* v___y_542_; lean_object* v___y_543_; lean_object* v___y_544_; lean_object* v_o_556_; lean_object* v___y_557_; lean_object* v___y_558_; lean_object* v___y_559_; lean_object* v___y_560_; lean_object* v___y_561_; lean_object* v___y_562_; lean_object* v___y_563_; lean_object* v___y_564_; lean_object* v___x_579_; lean_object* v___x_580_; uint8_t v___x_581_; 
v___x_353_ = lean_unsigned_to_nat(0u);
v_tk_354_ = l_Lean_Syntax_getArg(v_stx_332_, v___x_353_);
v___x_532_ = lean_unsigned_to_nat(2u);
v___x_533_ = l_Lean_Syntax_getArg(v_stx_332_, v___x_532_);
v___x_579_ = lean_unsigned_to_nat(3u);
v___x_580_ = l_Lean_Syntax_getArg(v_stx_332_, v___x_579_);
v___x_581_ = l_Lean_Syntax_isNone(v___x_580_);
if (v___x_581_ == 0)
{
uint8_t v___x_582_; 
lean_inc(v___x_580_);
v___x_582_ = l_Lean_Syntax_matchesNull(v___x_580_, v___x_347_);
if (v___x_582_ == 0)
{
lean_object* v___x_583_; 
lean_dec(v___x_580_);
lean_dec(v___x_533_);
lean_dec(v_tk_354_);
lean_dec(v___x_348_);
lean_dec_ref(v___x_335_);
lean_dec_ref(v___x_334_);
lean_dec_ref(v___x_333_);
v___x_583_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
return v___x_583_;
}
else
{
lean_object* v_o_584_; lean_object* v___x_585_; 
v_o_584_ = l_Lean_Syntax_getArg(v___x_580_, v___x_353_);
lean_dec(v___x_580_);
v___x_585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_585_, 0, v_o_584_);
v_o_556_ = v___x_585_;
v___y_557_ = v___y_337_;
v___y_558_ = v___y_338_;
v___y_559_ = v___y_339_;
v___y_560_ = v___y_340_;
v___y_561_ = v___y_341_;
v___y_562_ = v___y_342_;
v___y_563_ = v___y_343_;
v___y_564_ = v___y_344_;
goto v___jp_555_;
}
}
else
{
lean_object* v___x_586_; 
lean_dec(v___x_580_);
v___x_586_ = lean_box(0);
v_o_556_ = v___x_586_;
v___y_557_ = v___y_337_;
v___y_558_ = v___y_338_;
v___y_559_ = v___y_339_;
v___y_560_ = v___y_340_;
v___y_561_ = v___y_341_;
v___y_562_ = v___y_342_;
v___y_563_ = v___y_343_;
v___y_564_ = v___y_344_;
goto v___jp_555_;
}
v___jp_355_:
{
lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; uint8_t v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
lean_inc_ref_n(v___y_358_, 2);
v___x_374_ = l_Array_append___redArg(v___y_358_, v___y_373_);
lean_dec_ref(v___y_373_);
lean_inc_n(v___y_372_, 2);
lean_inc_n(v___y_359_, 2);
v___x_375_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_375_, 0, v___y_359_);
lean_ctor_set(v___x_375_, 1, v___y_372_);
lean_ctor_set(v___x_375_, 2, v___x_374_);
v___x_376_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_376_, 0, v___y_359_);
lean_ctor_set(v___x_376_, 1, v___y_372_);
lean_ctor_set(v___x_376_, 2, v___y_358_);
v___x_377_ = l_Lean_Syntax_node6(v___y_359_, v___y_357_, v___y_370_, v___x_348_, v___y_361_, v___y_364_, v___x_375_, v___x_376_);
v___x_378_ = 0;
v___x_379_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimp___closed__0));
v___x_380_ = l_Lean_Elab_Tactic_mkSimpContext(v___x_377_, v___y_363_, v___x_378_, v___y_363_, v___x_379_, v___y_368_, v___y_371_, v___y_365_, v___y_362_, v___y_369_, v___y_366_, v___y_360_, v___y_367_);
if (lean_obj_tag(v___x_380_) == 0)
{
lean_object* v_a_381_; lean_object* v_ctx_382_; lean_object* v_simprocs_383_; lean_object* v_dischargeWrapper_384_; lean_object* v___x_385_; 
v_a_381_ = lean_ctor_get(v___x_380_, 0);
lean_inc(v_a_381_);
lean_dec_ref_known(v___x_380_, 1);
v_ctx_382_ = lean_ctor_get(v_a_381_, 0);
lean_inc_ref(v_ctx_382_);
v_simprocs_383_ = lean_ctor_get(v_a_381_, 1);
lean_inc_ref(v_simprocs_383_);
v_dischargeWrapper_384_ = lean_ctor_get(v_a_381_, 2);
lean_inc(v_dischargeWrapper_384_);
lean_dec(v_a_381_);
v___x_385_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_371_, v___y_369_, v___y_366_, v___y_360_, v___y_367_);
if (lean_obj_tag(v___x_385_) == 0)
{
lean_object* v_a_386_; lean_object* v___f_387_; lean_object* v___x_388_; 
v_a_386_ = lean_ctor_get(v___x_385_, 0);
lean_inc(v_a_386_);
lean_dec_ref_known(v___x_385_, 1);
v___f_387_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__0___boxed), 14, 4);
lean_closure_set(v___f_387_, 0, v___x_353_);
lean_closure_set(v___f_387_, 1, v_a_386_);
lean_closure_set(v___f_387_, 2, v_ctx_382_);
lean_closure_set(v___f_387_, 3, v_simprocs_383_);
v___x_388_ = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(v_dischargeWrapper_384_, v___f_387_, v___y_368_, v___y_371_, v___y_365_, v___y_362_, v___y_369_, v___y_366_, v___y_360_, v___y_367_);
lean_dec(v_dischargeWrapper_384_);
if (lean_obj_tag(v___x_388_) == 0)
{
lean_object* v_a_389_; lean_object* v_fst_390_; lean_object* v_snd_391_; lean_object* v___x_392_; 
v_a_389_ = lean_ctor_get(v___x_388_, 0);
lean_inc(v_a_389_);
lean_dec_ref_known(v___x_388_, 1);
v_fst_390_ = lean_ctor_get(v_a_389_, 0);
lean_inc(v_fst_390_);
v_snd_391_ = lean_ctor_get(v_a_389_, 1);
lean_inc(v_snd_391_);
lean_dec(v_a_389_);
v___x_392_ = l_Lean_Elab_Tactic_Conv_applySimpResult(v_fst_390_, v___y_368_, v___y_371_, v___y_365_, v___y_362_, v___y_369_, v___y_366_, v___y_360_, v___y_367_);
if (lean_obj_tag(v___x_392_) == 0)
{
lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_425_; 
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_425_ == 0)
{
lean_object* v_unused_426_; 
v_unused_426_ = lean_ctor_get(v___x_392_, 0);
lean_dec(v_unused_426_);
v___x_394_ = v___x_392_;
v_isShared_395_ = v_isSharedCheck_425_;
goto v_resetjp_393_;
}
else
{
lean_dec(v___x_392_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_425_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v_usedTheorems_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_423_; 
v_usedTheorems_396_ = lean_ctor_get(v_snd_391_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v_snd_391_);
if (v_isSharedCheck_423_ == 0)
{
lean_object* v_unused_424_; 
v_unused_424_ = lean_ctor_get(v_snd_391_, 1);
lean_dec(v_unused_424_);
v___x_398_ = v_snd_391_;
v_isShared_399_ = v_isSharedCheck_423_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_usedTheorems_396_);
lean_dec(v_snd_391_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_423_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_400_; 
v___x_400_ = l_Lean_Elab_Tactic_mkSimpCallStx(v___x_377_, v_usedTheorems_396_, v___y_369_, v___y_366_, v___y_360_, v___y_367_);
lean_dec_ref(v_usedTheorems_396_);
if (lean_obj_tag(v___x_400_) == 0)
{
lean_object* v_a_401_; lean_object* v___x_402_; lean_object* v___x_404_; 
v_a_401_ = lean_ctor_get(v___x_400_, 0);
lean_inc(v_a_401_);
lean_dec_ref_known(v___x_400_, 1);
v___x_402_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__2));
if (v_isShared_399_ == 0)
{
lean_ctor_set(v___x_398_, 1, v_a_401_);
lean_ctor_set(v___x_398_, 0, v___x_402_);
v___x_404_ = v___x_398_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v___x_402_);
lean_ctor_set(v_reuseFailAlloc_414_, 1, v_a_401_);
v___x_404_ = v_reuseFailAlloc_414_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_408_; 
v___x_405_ = lean_box(0);
v___x_406_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_406_, 0, v___x_404_);
lean_ctor_set(v___x_406_, 1, v___x_405_);
lean_ctor_set(v___x_406_, 2, v___x_405_);
lean_ctor_set(v___x_406_, 3, v___x_405_);
lean_ctor_set(v___x_406_, 4, v___x_405_);
lean_ctor_set(v___x_406_, 5, v___x_405_);
lean_inc(v___y_356_);
if (v_isShared_395_ == 0)
{
lean_ctor_set_tag(v___x_394_, 1);
lean_ctor_set(v___x_394_, 0, v___y_356_);
v___x_408_ = v___x_394_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v___y_356_);
v___x_408_ = v_reuseFailAlloc_413_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
lean_object* v___x_409_; uint8_t v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_409_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__3));
v___x_410_ = 4;
v___x_411_ = l_Lean_MessageData_nil;
v___x_412_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_354_, v___x_406_, v___x_408_, v___x_409_, v___x_405_, v___x_410_, v___x_411_, v___y_360_, v___y_367_);
return v___x_412_;
}
}
}
else
{
lean_object* v_a_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_422_; 
lean_del_object(v___x_398_);
lean_del_object(v___x_394_);
lean_dec(v_tk_354_);
v_a_415_ = lean_ctor_get(v___x_400_, 0);
v_isSharedCheck_422_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_422_ == 0)
{
v___x_417_ = v___x_400_;
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_a_415_);
lean_dec(v___x_400_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_420_; 
if (v_isShared_418_ == 0)
{
v___x_420_ = v___x_417_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_a_415_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
}
}
}
}
else
{
lean_dec(v_snd_391_);
lean_dec(v___x_377_);
lean_dec(v_tk_354_);
return v___x_392_;
}
}
else
{
lean_object* v_a_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_434_; 
lean_dec(v___x_377_);
lean_dec(v_tk_354_);
v_a_427_ = lean_ctor_get(v___x_388_, 0);
v_isSharedCheck_434_ = !lean_is_exclusive(v___x_388_);
if (v_isSharedCheck_434_ == 0)
{
v___x_429_ = v___x_388_;
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_a_427_);
lean_dec(v___x_388_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_432_; 
if (v_isShared_430_ == 0)
{
v___x_432_ = v___x_429_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_a_427_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
}
}
else
{
lean_object* v_a_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_442_; 
lean_dec(v_dischargeWrapper_384_);
lean_dec_ref(v_simprocs_383_);
lean_dec_ref(v_ctx_382_);
lean_dec(v___x_377_);
lean_dec(v_tk_354_);
v_a_435_ = lean_ctor_get(v___x_385_, 0);
v_isSharedCheck_442_ = !lean_is_exclusive(v___x_385_);
if (v_isSharedCheck_442_ == 0)
{
v___x_437_ = v___x_385_;
v_isShared_438_ = v_isSharedCheck_442_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_a_435_);
lean_dec(v___x_385_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_442_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_440_; 
if (v_isShared_438_ == 0)
{
v___x_440_ = v___x_437_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v_a_435_);
v___x_440_ = v_reuseFailAlloc_441_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
return v___x_440_;
}
}
}
}
else
{
lean_object* v_a_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_450_; 
lean_dec(v___x_377_);
lean_dec(v_tk_354_);
v_a_443_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_450_ == 0)
{
v___x_445_ = v___x_380_;
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_a_443_);
lean_dec(v___x_380_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_448_; 
if (v_isShared_446_ == 0)
{
v___x_448_ = v___x_445_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v_a_443_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
}
}
v___jp_451_:
{
lean_object* v___x_470_; lean_object* v___x_471_; 
lean_inc_ref(v___y_454_);
v___x_470_ = l_Array_append___redArg(v___y_454_, v___y_469_);
lean_dec_ref(v___y_469_);
lean_inc(v___y_468_);
lean_inc(v___y_455_);
v___x_471_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_471_, 0, v___y_455_);
lean_ctor_set(v___x_471_, 1, v___y_468_);
lean_ctor_set(v___x_471_, 2, v___x_470_);
if (lean_obj_tag(v___y_461_) == 1)
{
lean_object* v_val_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v_val_472_ = lean_ctor_get(v___y_461_, 0);
lean_inc(v_val_472_);
lean_dec_ref_known(v___y_461_, 1);
v___x_473_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__4));
lean_inc_n(v___y_455_, 3);
v___x_474_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_474_, 0, v___y_455_);
lean_ctor_set(v___x_474_, 1, v___x_473_);
lean_inc_ref(v___y_454_);
v___x_475_ = l_Array_append___redArg(v___y_454_, v_val_472_);
lean_dec(v_val_472_);
lean_inc(v___y_468_);
v___x_476_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_476_, 0, v___y_455_);
lean_ctor_set(v___x_476_, 1, v___y_468_);
lean_ctor_set(v___x_476_, 2, v___x_475_);
v___x_477_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__5));
v___x_478_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_478_, 0, v___y_455_);
lean_ctor_set(v___x_478_, 1, v___x_477_);
v___x_479_ = l_Array_mkArray3___redArg(v___x_474_, v___x_476_, v___x_478_);
v___y_356_ = v___y_452_;
v___y_357_ = v___y_453_;
v___y_358_ = v___y_454_;
v___y_359_ = v___y_455_;
v___y_360_ = v___y_456_;
v___y_361_ = v___y_457_;
v___y_362_ = v___y_458_;
v___y_363_ = v___y_459_;
v___y_364_ = v___x_471_;
v___y_365_ = v___y_460_;
v___y_366_ = v___y_462_;
v___y_367_ = v___y_463_;
v___y_368_ = v___y_464_;
v___y_369_ = v___y_465_;
v___y_370_ = v___y_467_;
v___y_371_ = v___y_466_;
v___y_372_ = v___y_468_;
v___y_373_ = v___x_479_;
goto v___jp_355_;
}
else
{
lean_object* v___x_480_; 
lean_dec(v___y_461_);
v___x_480_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__6));
v___y_356_ = v___y_452_;
v___y_357_ = v___y_453_;
v___y_358_ = v___y_454_;
v___y_359_ = v___y_455_;
v___y_360_ = v___y_456_;
v___y_361_ = v___y_457_;
v___y_362_ = v___y_458_;
v___y_363_ = v___y_459_;
v___y_364_ = v___x_471_;
v___y_365_ = v___y_460_;
v___y_366_ = v___y_462_;
v___y_367_ = v___y_463_;
v___y_368_ = v___y_464_;
v___y_369_ = v___y_465_;
v___y_370_ = v___y_467_;
v___y_371_ = v___y_466_;
v___y_372_ = v___y_468_;
v___y_373_ = v___x_480_;
goto v___jp_355_;
}
}
v___jp_481_:
{
lean_object* v___x_500_; lean_object* v___x_501_; 
lean_inc_ref(v___y_484_);
v___x_500_ = l_Array_append___redArg(v___y_484_, v___y_499_);
lean_dec_ref(v___y_499_);
lean_inc(v___y_498_);
lean_inc(v___y_485_);
v___x_501_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_501_, 0, v___y_485_);
lean_ctor_set(v___x_501_, 1, v___y_498_);
lean_ctor_set(v___x_501_, 2, v___x_500_);
if (lean_obj_tag(v___y_495_) == 1)
{
lean_object* v_val_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v_val_502_ = lean_ctor_get(v___y_495_, 0);
lean_inc(v_val_502_);
lean_dec_ref_known(v___y_495_, 1);
v___x_503_ = l_Lean_SourceInfo_fromRef(v_val_502_, v___x_336_);
lean_dec(v_val_502_);
v___x_504_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__7));
v___x_505_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_505_, 0, v___x_503_);
lean_ctor_set(v___x_505_, 1, v___x_504_);
v___x_506_ = l_Array_mkArray1___redArg(v___x_505_);
v___y_452_ = v___y_482_;
v___y_453_ = v___y_483_;
v___y_454_ = v___y_484_;
v___y_455_ = v___y_485_;
v___y_456_ = v___y_486_;
v___y_457_ = v___x_501_;
v___y_458_ = v___y_487_;
v___y_459_ = v___y_488_;
v___y_460_ = v___y_489_;
v___y_461_ = v___y_490_;
v___y_462_ = v___y_491_;
v___y_463_ = v___y_492_;
v___y_464_ = v___y_493_;
v___y_465_ = v___y_494_;
v___y_466_ = v___y_497_;
v___y_467_ = v___y_496_;
v___y_468_ = v___y_498_;
v___y_469_ = v___x_506_;
goto v___jp_451_;
}
else
{
lean_object* v___x_507_; 
lean_dec(v___y_495_);
v___x_507_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__6));
v___y_452_ = v___y_482_;
v___y_453_ = v___y_483_;
v___y_454_ = v___y_484_;
v___y_455_ = v___y_485_;
v___y_456_ = v___y_486_;
v___y_457_ = v___x_501_;
v___y_458_ = v___y_487_;
v___y_459_ = v___y_488_;
v___y_460_ = v___y_489_;
v___y_461_ = v___y_490_;
v___y_462_ = v___y_491_;
v___y_463_ = v___y_492_;
v___y_464_ = v___y_493_;
v___y_465_ = v___y_494_;
v___y_466_ = v___y_497_;
v___y_467_ = v___y_496_;
v___y_468_ = v___y_498_;
v___y_469_ = v___x_507_;
goto v___jp_451_;
}
}
v___jp_508_:
{
lean_object* v_ref_520_; uint8_t v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
v_ref_520_ = lean_ctor_get(v___y_514_, 2);
v___x_521_ = 0;
v___x_522_ = l_Lean_SourceInfo_fromRef(v_ref_520_, v___x_521_);
v___x_523_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__4));
v___x_524_ = l_Lean_Name_mkStr4(v___x_333_, v___x_334_, v___x_335_, v___x_523_);
v___x_525_ = l_Lean_SourceInfo_fromRef(v_tk_354_, v___x_336_);
v___x_526_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_526_, 0, v___x_525_);
lean_ctor_set(v___x_526_, 1, v___x_523_);
v___x_527_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__9));
v___x_528_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__10, &l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__10_once, _init_l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__10);
if (lean_obj_tag(v___y_519_) == 1)
{
lean_object* v_val_529_; lean_object* v___x_530_; 
v_val_529_ = lean_ctor_get(v___y_519_, 0);
lean_inc(v_val_529_);
lean_dec_ref_known(v___y_519_, 1);
v___x_530_ = l_Array_mkArray1___redArg(v_val_529_);
v___y_482_ = v_ref_520_;
v___y_483_ = v___x_524_;
v___y_484_ = v___x_528_;
v___y_485_ = v___x_522_;
v___y_486_ = v___y_514_;
v___y_487_ = v___y_515_;
v___y_488_ = v___x_521_;
v___y_489_ = v___y_516_;
v___y_490_ = v___y_518_;
v___y_491_ = v___y_517_;
v___y_492_ = v___y_509_;
v___y_493_ = v___y_510_;
v___y_494_ = v___y_511_;
v___y_495_ = v___y_513_;
v___y_496_ = v___x_526_;
v___y_497_ = v___y_512_;
v___y_498_ = v___x_527_;
v___y_499_ = v___x_530_;
goto v___jp_481_;
}
else
{
lean_object* v___x_531_; 
lean_dec(v___y_519_);
v___x_531_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__6));
v___y_482_ = v_ref_520_;
v___y_483_ = v___x_524_;
v___y_484_ = v___x_528_;
v___y_485_ = v___x_522_;
v___y_486_ = v___y_514_;
v___y_487_ = v___y_515_;
v___y_488_ = v___x_521_;
v___y_489_ = v___y_516_;
v___y_490_ = v___y_518_;
v___y_491_ = v___y_517_;
v___y_492_ = v___y_509_;
v___y_493_ = v___y_510_;
v___y_494_ = v___y_511_;
v___y_495_ = v___y_513_;
v___y_496_ = v___x_526_;
v___y_497_ = v___y_512_;
v___y_498_ = v___x_527_;
v___y_499_ = v___x_531_;
goto v___jp_481_;
}
}
v___jp_534_:
{
lean_object* v___x_545_; 
v___x_545_ = l_Lean_Syntax_getOptional_x3f(v___x_533_);
lean_dec(v___x_533_);
if (lean_obj_tag(v___x_545_) == 0)
{
lean_object* v___x_546_; 
v___x_546_ = lean_box(0);
v___y_509_ = v___y_544_;
v___y_510_ = v___y_537_;
v___y_511_ = v___y_541_;
v___y_512_ = v___y_538_;
v___y_513_ = v___y_535_;
v___y_514_ = v___y_543_;
v___y_515_ = v___y_540_;
v___y_516_ = v___y_539_;
v___y_517_ = v___y_542_;
v___y_518_ = v_args_536_;
v___y_519_ = v___x_546_;
goto v___jp_508_;
}
else
{
lean_object* v_val_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_554_; 
v_val_547_ = lean_ctor_get(v___x_545_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_545_);
if (v_isSharedCheck_554_ == 0)
{
v___x_549_ = v___x_545_;
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_val_547_);
lean_dec(v___x_545_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_552_; 
if (v_isShared_550_ == 0)
{
v___x_552_ = v___x_549_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_val_547_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
v___y_509_ = v___y_544_;
v___y_510_ = v___y_537_;
v___y_511_ = v___y_541_;
v___y_512_ = v___y_538_;
v___y_513_ = v___y_535_;
v___y_514_ = v___y_543_;
v___y_515_ = v___y_540_;
v___y_516_ = v___y_539_;
v___y_517_ = v___y_542_;
v___y_518_ = v_args_536_;
v___y_519_ = v___x_552_;
goto v___jp_508_;
}
}
}
}
v___jp_555_:
{
lean_object* v___x_565_; lean_object* v___x_566_; uint8_t v___x_567_; 
v___x_565_ = lean_unsigned_to_nat(4u);
v___x_566_ = l_Lean_Syntax_getArg(v_stx_332_, v___x_565_);
v___x_567_ = l_Lean_Syntax_isNone(v___x_566_);
if (v___x_567_ == 0)
{
uint8_t v___x_568_; 
lean_inc(v___x_566_);
v___x_568_ = l_Lean_Syntax_matchesNull(v___x_566_, v___x_347_);
if (v___x_568_ == 0)
{
lean_object* v___x_569_; 
lean_dec(v___x_566_);
lean_dec(v_o_556_);
lean_dec(v___x_533_);
lean_dec(v_tk_354_);
lean_dec(v___x_348_);
lean_dec_ref(v___x_335_);
lean_dec_ref(v___x_334_);
lean_dec_ref(v___x_333_);
v___x_569_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
return v___x_569_;
}
else
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; uint8_t v___x_573_; 
v___x_570_ = l_Lean_Syntax_getArg(v___x_566_, v___x_353_);
lean_dec(v___x_566_);
v___x_571_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__11));
lean_inc_ref(v___x_335_);
lean_inc_ref(v___x_334_);
lean_inc_ref(v___x_333_);
v___x_572_ = l_Lean_Name_mkStr4(v___x_333_, v___x_334_, v___x_335_, v___x_571_);
lean_inc(v___x_570_);
v___x_573_ = l_Lean_Syntax_isOfKind(v___x_570_, v___x_572_);
lean_dec(v___x_572_);
if (v___x_573_ == 0)
{
lean_object* v___x_574_; 
lean_dec(v___x_570_);
lean_dec(v_o_556_);
lean_dec(v___x_533_);
lean_dec(v_tk_354_);
lean_dec(v___x_348_);
lean_dec_ref(v___x_335_);
lean_dec_ref(v___x_334_);
lean_dec_ref(v___x_333_);
v___x_574_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
return v___x_574_;
}
else
{
lean_object* v___x_575_; lean_object* v_args_576_; lean_object* v___x_577_; 
v___x_575_ = l_Lean_Syntax_getArg(v___x_570_, v___x_347_);
lean_dec(v___x_570_);
v_args_576_ = l_Lean_Syntax_getArgs(v___x_575_);
lean_dec(v___x_575_);
v___x_577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_577_, 0, v_args_576_);
v___y_535_ = v_o_556_;
v_args_536_ = v___x_577_;
v___y_537_ = v___y_557_;
v___y_538_ = v___y_558_;
v___y_539_ = v___y_559_;
v___y_540_ = v___y_560_;
v___y_541_ = v___y_561_;
v___y_542_ = v___y_562_;
v___y_543_ = v___y_563_;
v___y_544_ = v___y_564_;
goto v___jp_534_;
}
}
}
else
{
lean_object* v___x_578_; 
lean_dec(v___x_566_);
v___x_578_ = lean_box(0);
v___y_535_ = v_o_556_;
v_args_536_ = v___x_578_;
v___y_537_ = v___y_557_;
v___y_538_ = v___y_558_;
v___y_539_ = v___y_559_;
v___y_540_ = v___y_560_;
v___y_541_ = v___y_561_;
v___y_542_ = v___y_562_;
v___y_543_ = v___y_563_;
v___y_544_ = v___y_564_;
goto v___jp_534_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_331_ = stack[0].m_num;
lean_object* v_stx_332_ = stack[1].m_obj;
lean_object* v___x_333_ = stack[2].m_obj;
lean_object* v___x_334_ = stack[3].m_obj;
lean_object* v___x_335_ = stack[4].m_obj;
uint8_t v___x_336_ = stack[5].m_num;
lean_object* v___y_337_ = stack[6].m_obj;
lean_object* v___y_338_ = stack[7].m_obj;
lean_object* v___y_339_ = stack[8].m_obj;
lean_object* v___y_340_ = stack[9].m_obj;
lean_object* v___y_341_ = stack[10].m_obj;
lean_object* v___y_342_ = stack[11].m_obj;
lean_object* v___y_343_ = stack[12].m_obj;
lean_object* v___y_344_ = stack[13].m_obj;
lean_object* v_res_587_;
v_res_587_ = l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1(v___x_331_, v_stx_332_, v___x_333_, v___x_334_, v___x_335_, v___x_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_);
stack->m_obj
 = v_res_587_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___boxed(lean_object* v___x_588_, lean_object* v_stx_589_, lean_object* v___x_590_, lean_object* v___x_591_, lean_object* v___x_592_, lean_object* v___x_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_){
_start:
{
uint8_t v___x_5663__boxed_603_; uint8_t v___x_5667__boxed_604_; lean_object* v_res_605_; 
v___x_5663__boxed_603_ = lean_unbox(v___x_588_);
v___x_5667__boxed_604_ = lean_unbox(v___x_593_);
v_res_605_ = l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1(v___x_5663__boxed_603_, v_stx_589_, v___x_590_, v___x_591_, v___x_592_, v___x_5667__boxed_604_, v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_);
lean_dec(v___y_601_);
lean_dec_ref(v___y_600_);
lean_dec(v___y_599_);
lean_dec_ref(v___y_598_);
lean_dec(v___y_597_);
lean_dec_ref(v___y_596_);
lean_dec(v___y_595_);
lean_dec_ref(v___y_594_);
lean_dec(v_stx_589_);
return v_res_605_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace(lean_object* v_stx_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; uint8_t v___x_627_; uint8_t v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___y_631_; lean_object* v___x_632_; 
v___x_623_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__0));
v___x_624_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__1));
v___x_625_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__2));
v___x_626_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__1));
lean_inc(v_stx_613_);
v___x_627_ = l_Lean_Syntax_isOfKind(v_stx_613_, v___x_626_);
v___x_628_ = 1;
v___x_629_ = lean_box(v___x_627_);
v___x_630_ = lean_box(v___x_628_);
v___y_631_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___boxed), 15, 6);
lean_closure_set(v___y_631_, 0, v___x_629_);
lean_closure_set(v___y_631_, 1, v_stx_613_);
lean_closure_set(v___y_631_, 2, v___x_623_);
lean_closure_set(v___y_631_, 3, v___x_624_);
lean_closure_set(v___y_631_, 4, v___x_625_);
lean_closure_set(v___y_631_, 5, v___x_630_);
v___x_632_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___y_631_, v_a_614_, v_a_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_, v_a_620_, v_a_621_);
return v___x_632_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_evalSimpTrace_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_613_ = stack[0].m_obj;
lean_object* v_a_614_ = stack[1].m_obj;
lean_object* v_a_615_ = stack[2].m_obj;
lean_object* v_a_616_ = stack[3].m_obj;
lean_object* v_a_617_ = stack[4].m_obj;
lean_object* v_a_618_ = stack[5].m_obj;
lean_object* v_a_619_ = stack[6].m_obj;
lean_object* v_a_620_ = stack[7].m_obj;
lean_object* v_a_621_ = stack[8].m_obj;
lean_object* v_res_633_;
v_res_633_ = l_Lean_Elab_Tactic_Conv_evalSimpTrace(v_stx_613_, v_a_614_, v_a_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_, v_a_620_, v_a_621_);
stack->m_obj
 = v_res_633_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___boxed(lean_object* v_stx_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l_Lean_Elab_Tactic_Conv_evalSimpTrace(v_stx_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_);
lean_dec(v_a_642_);
lean_dec_ref(v_a_641_);
lean_dec(v_a_640_);
lean_dec_ref(v_a_639_);
lean_dec(v_a_638_);
lean_dec_ref(v_a_637_);
lean_dec(v_a_636_);
lean_dec_ref(v_a_635_);
return v_res_644_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1(){
_start:
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_653_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_654_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__1));
v___x_655_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__1));
v___x_656_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___boxed), 10, 0);
v___x_657_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_653_, v___x_654_, v___x_655_, v___x_656_);
return v___x_657_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_658_;
v_res_658_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1();
stack->m_obj
 = v_res_658_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___boxed(lean_object* v_a_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1();
return v_res_660_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg___lam__0(lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_){
_start:
{
lean_object* v___x_670_; 
v___x_670_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_662_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
if (lean_obj_tag(v___x_670_) == 0)
{
lean_object* v_a_671_; lean_object* v___x_672_; 
v_a_671_ = lean_ctor_get(v___x_670_, 0);
lean_inc(v_a_671_);
lean_dec_ref_known(v___x_670_, 1);
v___x_672_ = l_Lean_Meta_Split_simpMatch(v_a_671_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
if (lean_obj_tag(v___x_672_) == 0)
{
lean_object* v_a_673_; lean_object* v___x_674_; 
v_a_673_ = lean_ctor_get(v___x_672_, 0);
lean_inc(v_a_673_);
lean_dec_ref_known(v___x_672_, 1);
v___x_674_ = l_Lean_Elab_Tactic_Conv_applySimpResult(v_a_673_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
return v___x_674_;
}
else
{
lean_object* v_a_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_682_; 
v_a_675_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_682_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_682_ == 0)
{
v___x_677_ = v___x_672_;
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_a_675_);
lean_dec(v___x_672_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_680_; 
if (v_isShared_678_ == 0)
{
v___x_680_ = v___x_677_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_a_675_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
}
}
else
{
lean_object* v_a_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_690_; 
v_a_683_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_690_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_690_ == 0)
{
v___x_685_ = v___x_670_;
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_a_683_);
lean_dec(v___x_670_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_688_; 
if (v_isShared_686_ == 0)
{
v___x_688_ = v___x_685_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_a_683_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
return v___x_688_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_661_ = stack[0].m_obj;
lean_object* v___y_662_ = stack[1].m_obj;
lean_object* v___y_663_ = stack[2].m_obj;
lean_object* v___y_664_ = stack[3].m_obj;
lean_object* v___y_665_ = stack[4].m_obj;
lean_object* v___y_666_ = stack[5].m_obj;
lean_object* v___y_667_ = stack[6].m_obj;
lean_object* v___y_668_ = stack[7].m_obj;
lean_object* v_res_691_;
v_res_691_ = l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg___lam__0(v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
stack->m_obj
 = v_res_691_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg___lam__0___boxed(lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg___lam__0(v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_);
lean_dec(v___y_699_);
lean_dec_ref(v___y_698_);
lean_dec(v___y_697_);
lean_dec_ref(v___y_696_);
lean_dec(v___y_695_);
lean_dec_ref(v___y_694_);
lean_dec(v___y_693_);
lean_dec_ref(v___y_692_);
return v_res_701_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg(lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_){
_start:
{
lean_object* v___f_712_; lean_object* v___x_713_; 
v___f_712_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg___closed__0));
v___x_713_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_712_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_);
return v___x_713_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_703_ = stack[0].m_obj;
lean_object* v_a_704_ = stack[1].m_obj;
lean_object* v_a_705_ = stack[2].m_obj;
lean_object* v_a_706_ = stack[3].m_obj;
lean_object* v_a_707_ = stack[4].m_obj;
lean_object* v_a_708_ = stack[5].m_obj;
lean_object* v_a_709_ = stack[6].m_obj;
lean_object* v_a_710_ = stack[7].m_obj;
lean_object* v_res_714_;
v_res_714_ = l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg(v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_);
stack->m_obj
 = v_res_714_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg___boxed(lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg(v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_);
lean_dec(v_a_722_);
lean_dec_ref(v_a_721_);
lean_dec(v_a_720_);
lean_dec_ref(v_a_719_);
lean_dec(v_a_718_);
lean_dec_ref(v_a_717_);
lean_dec(v_a_716_);
lean_dec_ref(v_a_715_);
return v_res_724_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch(lean_object* v_x_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg(v_a_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_);
return v___x_735_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_evalSimpMatch_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_725_ = stack[0].m_obj;
lean_object* v_a_726_ = stack[1].m_obj;
lean_object* v_a_727_ = stack[2].m_obj;
lean_object* v_a_728_ = stack[3].m_obj;
lean_object* v_a_729_ = stack[4].m_obj;
lean_object* v_a_730_ = stack[5].m_obj;
lean_object* v_a_731_ = stack[6].m_obj;
lean_object* v_a_732_ = stack[7].m_obj;
lean_object* v_a_733_ = stack[8].m_obj;
lean_object* v_res_736_;
v_res_736_ = l_Lean_Elab_Tactic_Conv_evalSimpMatch(v_x_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_);
stack->m_obj
 = v_res_736_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch___boxed(lean_object* v_x_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_Lean_Elab_Tactic_Conv_evalSimpMatch(v_x_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_, v_a_742_, v_a_743_, v_a_744_, v_a_745_);
lean_dec(v_a_745_);
lean_dec_ref(v_a_744_);
lean_dec(v_a_743_);
lean_dec_ref(v_a_742_);
lean_dec(v_a_741_);
lean_dec_ref(v_a_740_);
lean_dec(v_a_739_);
lean_dec_ref(v_a_738_);
lean_dec(v_x_737_);
return v_res_747_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1(){
_start:
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_763_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_764_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__1));
v___x_765_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__3));
v___x_766_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalSimpMatch___boxed), 10, 0);
v___x_767_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_763_, v___x_764_, v___x_765_, v___x_766_);
return v___x_767_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_768_;
v_res_768_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1();
stack->m_obj
 = v_res_768_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___boxed(lean_object* v_a_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1();
return v_res_770_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3(){
_start:
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_797_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__3));
v___x_798_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__6));
v___x_799_ = l_Lean_addBuiltinDeclarationRanges(v___x_797_, v___x_798_);
return v___x_799_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_800_;
v_res_800_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3();
stack->m_obj
 = v_res_800_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___boxed(lean_object* v_a_801_){
_start:
{
lean_object* v_res_802_; 
v_res_802_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3();
return v_res_802_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_evalDSimp___lam__0(lean_object* v_stx_805_, uint8_t v___x_806_, uint8_t v___x_807_, lean_object* v___x_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_){
_start:
{
lean_object* v___x_818_; 
v___x_818_ = l_Lean_Elab_Tactic_mkSimpContext(v_stx_805_, v___x_806_, v___x_807_, v___x_806_, v___x_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_);
if (lean_obj_tag(v___x_818_) == 0)
{
lean_object* v_a_819_; lean_object* v_ctx_820_; lean_object* v___x_821_; 
v_a_819_ = lean_ctor_get(v___x_818_, 0);
lean_inc(v_a_819_);
lean_dec_ref_known(v___x_818_, 1);
v_ctx_820_ = lean_ctor_get(v_a_819_, 0);
lean_inc_ref(v_ctx_820_);
lean_dec(v_a_819_);
v___x_821_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_810_, v___y_813_, v___y_814_, v___y_815_, v___y_816_);
if (lean_obj_tag(v___x_821_) == 0)
{
lean_object* v_a_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
v_a_822_ = lean_ctor_get(v___x_821_, 0);
lean_inc(v_a_822_);
lean_dec_ref_known(v___x_821_, 1);
v___x_823_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalDSimp___lam__0___closed__0));
v___x_824_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6, &l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6);
v___x_825_ = l_Lean_Meta_dsimp(v_a_822_, v_ctx_820_, v___x_823_, v___x_824_, v___y_813_, v___y_814_, v___y_815_, v___y_816_);
if (lean_obj_tag(v___x_825_) == 0)
{
lean_object* v_a_826_; lean_object* v_fst_827_; lean_object* v___x_828_; 
v_a_826_ = lean_ctor_get(v___x_825_, 0);
lean_inc(v_a_826_);
lean_dec_ref_known(v___x_825_, 1);
v_fst_827_ = lean_ctor_get(v_a_826_, 0);
lean_inc(v_fst_827_);
lean_dec(v_a_826_);
v___x_828_ = l_Lean_Elab_Tactic_Conv_changeLhs(v_fst_827_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_);
return v___x_828_;
}
else
{
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_836_; 
v_a_829_ = lean_ctor_get(v___x_825_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_825_);
if (v_isSharedCheck_836_ == 0)
{
v___x_831_ = v___x_825_;
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_825_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_834_; 
if (v_isShared_832_ == 0)
{
v___x_834_ = v___x_831_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_a_829_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
}
else
{
lean_object* v_a_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_844_; 
lean_dec_ref(v_ctx_820_);
v_a_837_ = lean_ctor_get(v___x_821_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_844_ == 0)
{
v___x_839_ = v___x_821_;
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_a_837_);
lean_dec(v___x_821_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_842_; 
if (v_isShared_840_ == 0)
{
v___x_842_ = v___x_839_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_a_837_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
}
}
else
{
lean_object* v_a_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_852_; 
v_a_845_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_852_ == 0)
{
v___x_847_ = v___x_818_;
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_a_845_);
lean_dec(v___x_818_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_850_; 
if (v_isShared_848_ == 0)
{
v___x_850_ = v___x_847_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_a_845_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_evalDSimp___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_805_ = stack[0].m_obj;
uint8_t v___x_806_ = stack[1].m_num;
uint8_t v___x_807_ = stack[2].m_num;
lean_object* v___x_808_ = stack[3].m_obj;
lean_object* v___y_809_ = stack[4].m_obj;
lean_object* v___y_810_ = stack[5].m_obj;
lean_object* v___y_811_ = stack[6].m_obj;
lean_object* v___y_812_ = stack[7].m_obj;
lean_object* v___y_813_ = stack[8].m_obj;
lean_object* v___y_814_ = stack[9].m_obj;
lean_object* v___y_815_ = stack[10].m_obj;
lean_object* v___y_816_ = stack[11].m_obj;
lean_object* v_res_853_;
v_res_853_ = l_Lean_Elab_Tactic_Conv_evalDSimp___lam__0(v_stx_805_, v___x_806_, v___x_807_, v___x_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_);
stack->m_obj
 = v_res_853_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimp___lam__0___boxed(lean_object* v_stx_854_, lean_object* v___x_855_, lean_object* v___x_856_, lean_object* v___x_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_){
_start:
{
uint8_t v___x_590__boxed_867_; uint8_t v___x_591__boxed_868_; lean_object* v_res_869_; 
v___x_590__boxed_867_ = lean_unbox(v___x_855_);
v___x_591__boxed_868_ = lean_unbox(v___x_856_);
v_res_869_ = l_Lean_Elab_Tactic_Conv_evalDSimp___lam__0(v_stx_854_, v___x_590__boxed_867_, v___x_591__boxed_868_, v___x_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec(v___y_861_);
lean_dec_ref(v___y_860_);
lean_dec(v___y_859_);
lean_dec_ref(v___y_858_);
lean_dec(v_stx_854_);
return v_res_869_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_evalDSimp(lean_object* v_stx_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_){
_start:
{
uint8_t v___x_880_; uint8_t v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___f_885_; lean_object* v___x_886_; 
v___x_880_ = 0;
v___x_881_ = 2;
v___x_882_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimp___closed__0));
v___x_883_ = lean_box(v___x_880_);
v___x_884_ = lean_box(v___x_881_);
v___f_885_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalDSimp___lam__0___boxed), 13, 4);
lean_closure_set(v___f_885_, 0, v_stx_870_);
lean_closure_set(v___f_885_, 1, v___x_883_);
lean_closure_set(v___f_885_, 2, v___x_884_);
lean_closure_set(v___f_885_, 3, v___x_882_);
v___x_886_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_885_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_);
return v___x_886_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_evalDSimp_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_870_ = stack[0].m_obj;
lean_object* v_a_871_ = stack[1].m_obj;
lean_object* v_a_872_ = stack[2].m_obj;
lean_object* v_a_873_ = stack[3].m_obj;
lean_object* v_a_874_ = stack[4].m_obj;
lean_object* v_a_875_ = stack[5].m_obj;
lean_object* v_a_876_ = stack[6].m_obj;
lean_object* v_a_877_ = stack[7].m_obj;
lean_object* v_a_878_ = stack[8].m_obj;
lean_object* v_res_887_;
v_res_887_ = l_Lean_Elab_Tactic_Conv_evalDSimp(v_stx_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_);
stack->m_obj
 = v_res_887_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimp___boxed(lean_object* v_stx_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_){
_start:
{
lean_object* v_res_898_; 
v_res_898_ = l_Lean_Elab_Tactic_Conv_evalDSimp(v_stx_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_);
lean_dec(v_a_896_);
lean_dec_ref(v_a_895_);
lean_dec(v_a_894_);
lean_dec_ref(v_a_893_);
lean_dec(v_a_892_);
lean_dec_ref(v_a_891_);
lean_dec(v_a_890_);
lean_dec_ref(v_a_889_);
return v_res_898_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1(){
_start:
{
lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_914_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_915_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__1));
v___x_916_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__3));
v___x_917_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalDSimp___boxed), 10, 0);
v___x_918_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_914_, v___x_915_, v___x_916_, v___x_917_);
return v___x_918_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_919_;
v_res_919_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1();
stack->m_obj
 = v_res_919_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___boxed(lean_object* v_a_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1();
return v_res_921_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3(){
_start:
{
lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_947_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__3));
v___x_948_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__6));
v___x_949_ = l_Lean_addBuiltinDeclarationRanges(v___x_947_, v___x_948_);
return v___x_949_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_950_;
v_res_950_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3();
stack->m_obj
 = v_res_950_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___boxed(lean_object* v_a_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3();
return v_res_952_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_evalDSimpTrace___lam__0(uint8_t v___x_954_, lean_object* v_stx_955_, lean_object* v___x_956_, lean_object* v___x_957_, lean_object* v___x_958_, uint8_t v___x_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_){
_start:
{
if (v___x_954_ == 0)
{
lean_object* v___x_969_; 
lean_dec_ref(v___x_958_);
lean_dec_ref(v___x_957_);
lean_dec_ref(v___x_956_);
v___x_969_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
return v___x_969_;
}
else
{
lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; uint8_t v___x_974_; 
v___x_970_ = lean_unsigned_to_nat(1u);
v___x_971_ = l_Lean_Syntax_getArg(v_stx_955_, v___x_970_);
v___x_972_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__0));
lean_inc_ref(v___x_958_);
lean_inc_ref(v___x_957_);
lean_inc_ref(v___x_956_);
v___x_973_ = l_Lean_Name_mkStr4(v___x_956_, v___x_957_, v___x_958_, v___x_972_);
lean_inc(v___x_971_);
v___x_974_ = l_Lean_Syntax_isOfKind(v___x_971_, v___x_973_);
lean_dec(v___x_973_);
if (v___x_974_ == 0)
{
lean_object* v___x_975_; 
lean_dec(v___x_971_);
lean_dec_ref(v___x_958_);
lean_dec_ref(v___x_957_);
lean_dec_ref(v___x_956_);
v___x_975_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
return v___x_975_;
}
else
{
lean_object* v___x_976_; lean_object* v_tk_977_; lean_object* v___y_979_; lean_object* v___y_980_; lean_object* v___y_981_; lean_object* v___y_982_; uint8_t v___y_983_; lean_object* v___y_984_; lean_object* v___y_985_; lean_object* v___y_986_; lean_object* v___y_987_; lean_object* v___y_988_; lean_object* v___y_989_; lean_object* v___y_990_; lean_object* v___y_991_; lean_object* v___y_992_; lean_object* v___y_993_; lean_object* v___y_994_; lean_object* v___y_995_; lean_object* v___y_996_; lean_object* v___y_1073_; lean_object* v___y_1074_; lean_object* v___y_1075_; lean_object* v___y_1076_; lean_object* v___y_1077_; uint8_t v___y_1078_; lean_object* v___y_1079_; lean_object* v___y_1080_; lean_object* v___y_1081_; lean_object* v___y_1082_; lean_object* v___y_1083_; lean_object* v___y_1084_; lean_object* v___y_1085_; lean_object* v___y_1086_; lean_object* v___y_1087_; lean_object* v___y_1088_; lean_object* v___y_1089_; lean_object* v___y_1090_; lean_object* v___y_1103_; lean_object* v_args_1104_; lean_object* v___y_1105_; lean_object* v___y_1106_; lean_object* v___y_1107_; lean_object* v___y_1108_; lean_object* v___y_1109_; lean_object* v___y_1110_; lean_object* v___y_1111_; lean_object* v___y_1112_; lean_object* v_o_1130_; lean_object* v___y_1131_; lean_object* v___y_1132_; lean_object* v___y_1133_; lean_object* v___y_1134_; lean_object* v___y_1135_; lean_object* v___y_1136_; lean_object* v___y_1137_; lean_object* v___y_1138_; lean_object* v___x_1153_; lean_object* v___x_1154_; uint8_t v___x_1155_; 
v___x_976_ = lean_unsigned_to_nat(0u);
v_tk_977_ = l_Lean_Syntax_getArg(v_stx_955_, v___x_976_);
v___x_1153_ = lean_unsigned_to_nat(2u);
v___x_1154_ = l_Lean_Syntax_getArg(v_stx_955_, v___x_1153_);
v___x_1155_ = l_Lean_Syntax_isNone(v___x_1154_);
if (v___x_1155_ == 0)
{
uint8_t v___x_1156_; 
lean_inc(v___x_1154_);
v___x_1156_ = l_Lean_Syntax_matchesNull(v___x_1154_, v___x_970_);
if (v___x_1156_ == 0)
{
lean_object* v___x_1157_; 
lean_dec(v___x_1154_);
lean_dec(v_tk_977_);
lean_dec(v___x_971_);
lean_dec_ref(v___x_958_);
lean_dec_ref(v___x_957_);
lean_dec_ref(v___x_956_);
v___x_1157_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
return v___x_1157_;
}
else
{
lean_object* v_o_1158_; lean_object* v___x_1159_; 
v_o_1158_ = l_Lean_Syntax_getArg(v___x_1154_, v___x_976_);
lean_dec(v___x_1154_);
v___x_1159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1159_, 0, v_o_1158_);
v_o_1130_ = v___x_1159_;
v___y_1131_ = v___y_960_;
v___y_1132_ = v___y_961_;
v___y_1133_ = v___y_962_;
v___y_1134_ = v___y_963_;
v___y_1135_ = v___y_964_;
v___y_1136_ = v___y_965_;
v___y_1137_ = v___y_966_;
v___y_1138_ = v___y_967_;
goto v___jp_1129_;
}
}
else
{
lean_object* v___x_1160_; 
lean_dec(v___x_1154_);
v___x_1160_ = lean_box(0);
v_o_1130_ = v___x_1160_;
v___y_1131_ = v___y_960_;
v___y_1132_ = v___y_961_;
v___y_1133_ = v___y_962_;
v___y_1134_ = v___y_963_;
v___y_1135_ = v___y_964_;
v___y_1136_ = v___y_965_;
v___y_1137_ = v___y_966_;
v___y_1138_ = v___y_967_;
goto v___jp_1129_;
}
v___jp_978_:
{
lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; uint8_t v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
lean_inc_ref(v___y_988_);
v___x_997_ = l_Array_append___redArg(v___y_988_, v___y_996_);
lean_dec_ref(v___y_996_);
lean_inc(v___y_989_);
lean_inc(v___y_992_);
v___x_998_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_998_, 0, v___y_992_);
lean_ctor_set(v___x_998_, 1, v___y_989_);
lean_ctor_set(v___x_998_, 2, v___x_997_);
lean_inc(v___y_982_);
v___x_999_ = l_Lean_Syntax_node6(v___y_992_, v___y_980_, v___y_994_, v___x_971_, v___y_982_, v___y_991_, v___x_998_, v___y_982_);
v___x_1000_ = 2;
v___x_1001_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimp___closed__0));
v___x_1002_ = l_Lean_Elab_Tactic_mkSimpContext(v___x_999_, v___y_983_, v___x_1000_, v___y_983_, v___x_1001_, v___y_995_, v___y_981_, v___y_979_, v___y_990_, v___y_987_, v___y_986_, v___y_984_, v___y_985_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_object* v_a_1003_; lean_object* v_ctx_1004_; lean_object* v___x_1005_; 
v_a_1003_ = lean_ctor_get(v___x_1002_, 0);
lean_inc(v_a_1003_);
lean_dec_ref_known(v___x_1002_, 1);
v_ctx_1004_ = lean_ctor_get(v_a_1003_, 0);
lean_inc_ref(v_ctx_1004_);
lean_dec(v_a_1003_);
v___x_1005_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_981_, v___y_987_, v___y_986_, v___y_984_, v___y_985_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_object* v_a_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
v_a_1006_ = lean_ctor_get(v___x_1005_, 0);
lean_inc(v_a_1006_);
lean_dec_ref_known(v___x_1005_, 1);
v___x_1007_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalDSimp___lam__0___closed__0));
v___x_1008_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6, &l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6);
v___x_1009_ = l_Lean_Meta_dsimp(v_a_1006_, v_ctx_1004_, v___x_1007_, v___x_1008_, v___y_987_, v___y_986_, v___y_984_, v___y_985_);
if (lean_obj_tag(v___x_1009_) == 0)
{
lean_object* v_a_1010_; lean_object* v_fst_1011_; lean_object* v_snd_1012_; lean_object* v___x_1013_; 
v_a_1010_ = lean_ctor_get(v___x_1009_, 0);
lean_inc(v_a_1010_);
lean_dec_ref_known(v___x_1009_, 1);
v_fst_1011_ = lean_ctor_get(v_a_1010_, 0);
lean_inc(v_fst_1011_);
v_snd_1012_ = lean_ctor_get(v_a_1010_, 1);
lean_inc(v_snd_1012_);
lean_dec(v_a_1010_);
v___x_1013_ = l_Lean_Elab_Tactic_Conv_changeLhs(v_fst_1011_, v___y_995_, v___y_981_, v___y_979_, v___y_990_, v___y_987_, v___y_986_, v___y_984_, v___y_985_);
if (lean_obj_tag(v___x_1013_) == 0)
{
lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1046_; 
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1046_ == 0)
{
lean_object* v_unused_1047_; 
v_unused_1047_ = lean_ctor_get(v___x_1013_, 0);
lean_dec(v_unused_1047_);
v___x_1015_ = v___x_1013_;
v_isShared_1016_ = v_isSharedCheck_1046_;
goto v_resetjp_1014_;
}
else
{
lean_dec(v___x_1013_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1046_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v_usedTheorems_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1044_; 
v_usedTheorems_1017_ = lean_ctor_get(v_snd_1012_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v_snd_1012_);
if (v_isSharedCheck_1044_ == 0)
{
lean_object* v_unused_1045_; 
v_unused_1045_ = lean_ctor_get(v_snd_1012_, 1);
lean_dec(v_unused_1045_);
v___x_1019_ = v_snd_1012_;
v_isShared_1020_ = v_isSharedCheck_1044_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_usedTheorems_1017_);
lean_dec(v_snd_1012_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1044_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1021_; 
v___x_1021_ = l_Lean_Elab_Tactic_mkSimpCallStx(v___x_999_, v_usedTheorems_1017_, v___y_987_, v___y_986_, v___y_984_, v___y_985_);
lean_dec_ref(v_usedTheorems_1017_);
if (lean_obj_tag(v___x_1021_) == 0)
{
lean_object* v_a_1022_; lean_object* v___x_1023_; lean_object* v___x_1025_; 
v_a_1022_ = lean_ctor_get(v___x_1021_, 0);
lean_inc(v_a_1022_);
lean_dec_ref_known(v___x_1021_, 1);
v___x_1023_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__2));
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 1, v_a_1022_);
lean_ctor_set(v___x_1019_, 0, v___x_1023_);
v___x_1025_ = v___x_1019_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v___x_1023_);
lean_ctor_set(v_reuseFailAlloc_1035_, 1, v_a_1022_);
v___x_1025_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1029_; 
v___x_1026_ = lean_box(0);
v___x_1027_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1025_);
lean_ctor_set(v___x_1027_, 1, v___x_1026_);
lean_ctor_set(v___x_1027_, 2, v___x_1026_);
lean_ctor_set(v___x_1027_, 3, v___x_1026_);
lean_ctor_set(v___x_1027_, 4, v___x_1026_);
lean_ctor_set(v___x_1027_, 5, v___x_1026_);
lean_inc(v___y_993_);
if (v_isShared_1016_ == 0)
{
lean_ctor_set_tag(v___x_1015_, 1);
lean_ctor_set(v___x_1015_, 0, v___y_993_);
v___x_1029_ = v___x_1015_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v___y_993_);
v___x_1029_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
lean_object* v___x_1030_; uint8_t v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1030_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__3));
v___x_1031_ = 4;
v___x_1032_ = l_Lean_MessageData_nil;
v___x_1033_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_977_, v___x_1027_, v___x_1029_, v___x_1030_, v___x_1026_, v___x_1031_, v___x_1032_, v___y_984_, v___y_985_);
return v___x_1033_;
}
}
}
else
{
lean_object* v_a_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1043_; 
lean_del_object(v___x_1019_);
lean_del_object(v___x_1015_);
lean_dec(v_tk_977_);
v_a_1036_ = lean_ctor_get(v___x_1021_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_1021_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1038_ = v___x_1021_;
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_a_1036_);
lean_dec(v___x_1021_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1041_; 
if (v_isShared_1039_ == 0)
{
v___x_1041_ = v___x_1038_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_a_1036_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
}
}
}
else
{
lean_dec(v_snd_1012_);
lean_dec(v___x_999_);
lean_dec(v_tk_977_);
return v___x_1013_;
}
}
else
{
lean_object* v_a_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1055_; 
lean_dec(v___x_999_);
lean_dec(v_tk_977_);
v_a_1048_ = lean_ctor_get(v___x_1009_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1050_ = v___x_1009_;
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_a_1048_);
lean_dec(v___x_1009_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1053_; 
if (v_isShared_1051_ == 0)
{
v___x_1053_ = v___x_1050_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v_a_1048_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
}
}
else
{
lean_object* v_a_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1063_; 
lean_dec_ref(v_ctx_1004_);
lean_dec(v___x_999_);
lean_dec(v_tk_977_);
v_a_1056_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1058_ = v___x_1005_;
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_a_1056_);
lean_dec(v___x_1005_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1061_; 
if (v_isShared_1059_ == 0)
{
v___x_1061_ = v___x_1058_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_a_1056_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
}
else
{
lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1071_; 
lean_dec(v___x_999_);
lean_dec(v_tk_977_);
v_a_1064_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1066_ = v___x_1002_;
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v___x_1002_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1069_; 
if (v_isShared_1067_ == 0)
{
v___x_1069_ = v___x_1066_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_a_1064_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
}
v___jp_1072_:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; 
lean_inc_ref(v___y_1084_);
v___x_1091_ = l_Array_append___redArg(v___y_1084_, v___y_1090_);
lean_dec_ref(v___y_1090_);
lean_inc(v___y_1085_);
lean_inc(v___y_1086_);
v___x_1092_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1092_, 0, v___y_1086_);
lean_ctor_set(v___x_1092_, 1, v___y_1085_);
lean_ctor_set(v___x_1092_, 2, v___x_1091_);
if (lean_obj_tag(v___y_1077_) == 1)
{
lean_object* v_val_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; 
v_val_1093_ = lean_ctor_get(v___y_1077_, 0);
lean_inc(v_val_1093_);
lean_dec_ref_known(v___y_1077_, 1);
v___x_1094_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__4));
lean_inc_n(v___y_1086_, 3);
v___x_1095_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1095_, 0, v___y_1086_);
lean_ctor_set(v___x_1095_, 1, v___x_1094_);
lean_inc_ref(v___y_1084_);
v___x_1096_ = l_Array_append___redArg(v___y_1084_, v_val_1093_);
lean_dec(v_val_1093_);
lean_inc(v___y_1085_);
v___x_1097_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1097_, 0, v___y_1086_);
lean_ctor_set(v___x_1097_, 1, v___y_1085_);
lean_ctor_set(v___x_1097_, 2, v___x_1096_);
v___x_1098_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__5));
v___x_1099_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1099_, 0, v___y_1086_);
lean_ctor_set(v___x_1099_, 1, v___x_1098_);
v___x_1100_ = l_Array_mkArray3___redArg(v___x_1095_, v___x_1097_, v___x_1099_);
v___y_979_ = v___y_1073_;
v___y_980_ = v___y_1074_;
v___y_981_ = v___y_1075_;
v___y_982_ = v___y_1076_;
v___y_983_ = v___y_1078_;
v___y_984_ = v___y_1079_;
v___y_985_ = v___y_1080_;
v___y_986_ = v___y_1081_;
v___y_987_ = v___y_1082_;
v___y_988_ = v___y_1084_;
v___y_989_ = v___y_1085_;
v___y_990_ = v___y_1083_;
v___y_991_ = v___x_1092_;
v___y_992_ = v___y_1086_;
v___y_993_ = v___y_1089_;
v___y_994_ = v___y_1088_;
v___y_995_ = v___y_1087_;
v___y_996_ = v___x_1100_;
goto v___jp_978_;
}
else
{
lean_object* v___x_1101_; 
lean_dec(v___y_1077_);
v___x_1101_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__6));
v___y_979_ = v___y_1073_;
v___y_980_ = v___y_1074_;
v___y_981_ = v___y_1075_;
v___y_982_ = v___y_1076_;
v___y_983_ = v___y_1078_;
v___y_984_ = v___y_1079_;
v___y_985_ = v___y_1080_;
v___y_986_ = v___y_1081_;
v___y_987_ = v___y_1082_;
v___y_988_ = v___y_1084_;
v___y_989_ = v___y_1085_;
v___y_990_ = v___y_1083_;
v___y_991_ = v___x_1092_;
v___y_992_ = v___y_1086_;
v___y_993_ = v___y_1089_;
v___y_994_ = v___y_1088_;
v___y_995_ = v___y_1087_;
v___y_996_ = v___x_1101_;
goto v___jp_978_;
}
}
v___jp_1102_:
{
lean_object* v_ref_1113_; uint8_t v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; 
v_ref_1113_ = lean_ctor_get(v___y_1111_, 2);
v___x_1114_ = 0;
v___x_1115_ = l_Lean_SourceInfo_fromRef(v_ref_1113_, v___x_1114_);
v___x_1116_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__0));
v___x_1117_ = l_Lean_Name_mkStr4(v___x_956_, v___x_957_, v___x_958_, v___x_1116_);
v___x_1118_ = l_Lean_SourceInfo_fromRef(v_tk_977_, v___x_959_);
v___x_1119_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1118_);
lean_ctor_set(v___x_1119_, 1, v___x_1116_);
v___x_1120_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__9));
v___x_1121_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__10, &l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__10_once, _init_l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__10);
lean_inc(v___x_1115_);
v___x_1122_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1115_);
lean_ctor_set(v___x_1122_, 1, v___x_1120_);
lean_ctor_set(v___x_1122_, 2, v___x_1121_);
if (lean_obj_tag(v___y_1103_) == 1)
{
lean_object* v_val_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
v_val_1123_ = lean_ctor_get(v___y_1103_, 0);
lean_inc(v_val_1123_);
lean_dec_ref_known(v___y_1103_, 1);
v___x_1124_ = l_Lean_SourceInfo_fromRef(v_val_1123_, v___x_959_);
lean_dec(v_val_1123_);
v___x_1125_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__7));
v___x_1126_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1124_);
lean_ctor_set(v___x_1126_, 1, v___x_1125_);
v___x_1127_ = l_Array_mkArray1___redArg(v___x_1126_);
v___y_1073_ = v___y_1107_;
v___y_1074_ = v___x_1117_;
v___y_1075_ = v___y_1106_;
v___y_1076_ = v___x_1122_;
v___y_1077_ = v_args_1104_;
v___y_1078_ = v___x_1114_;
v___y_1079_ = v___y_1111_;
v___y_1080_ = v___y_1112_;
v___y_1081_ = v___y_1110_;
v___y_1082_ = v___y_1109_;
v___y_1083_ = v___y_1108_;
v___y_1084_ = v___x_1121_;
v___y_1085_ = v___x_1120_;
v___y_1086_ = v___x_1115_;
v___y_1087_ = v___y_1105_;
v___y_1088_ = v___x_1119_;
v___y_1089_ = v_ref_1113_;
v___y_1090_ = v___x_1127_;
goto v___jp_1072_;
}
else
{
lean_object* v___x_1128_; 
lean_dec(v___y_1103_);
v___x_1128_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__6));
v___y_1073_ = v___y_1107_;
v___y_1074_ = v___x_1117_;
v___y_1075_ = v___y_1106_;
v___y_1076_ = v___x_1122_;
v___y_1077_ = v_args_1104_;
v___y_1078_ = v___x_1114_;
v___y_1079_ = v___y_1111_;
v___y_1080_ = v___y_1112_;
v___y_1081_ = v___y_1110_;
v___y_1082_ = v___y_1109_;
v___y_1083_ = v___y_1108_;
v___y_1084_ = v___x_1121_;
v___y_1085_ = v___x_1120_;
v___y_1086_ = v___x_1115_;
v___y_1087_ = v___y_1105_;
v___y_1088_ = v___x_1119_;
v___y_1089_ = v_ref_1113_;
v___y_1090_ = v___x_1128_;
goto v___jp_1072_;
}
}
v___jp_1129_:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; uint8_t v___x_1141_; 
v___x_1139_ = lean_unsigned_to_nat(3u);
v___x_1140_ = l_Lean_Syntax_getArg(v_stx_955_, v___x_1139_);
v___x_1141_ = l_Lean_Syntax_isNone(v___x_1140_);
if (v___x_1141_ == 0)
{
uint8_t v___x_1142_; 
lean_inc(v___x_1140_);
v___x_1142_ = l_Lean_Syntax_matchesNull(v___x_1140_, v___x_970_);
if (v___x_1142_ == 0)
{
lean_object* v___x_1143_; 
lean_dec(v___x_1140_);
lean_dec(v_o_1130_);
lean_dec(v_tk_977_);
lean_dec(v___x_971_);
lean_dec_ref(v___x_958_);
lean_dec_ref(v___x_957_);
lean_dec_ref(v___x_956_);
v___x_1143_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
return v___x_1143_;
}
else
{
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; uint8_t v___x_1147_; 
v___x_1144_ = l_Lean_Syntax_getArg(v___x_1140_, v___x_976_);
lean_dec(v___x_1140_);
v___x_1145_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalDSimpTrace___lam__0___closed__0));
lean_inc_ref(v___x_958_);
lean_inc_ref(v___x_957_);
lean_inc_ref(v___x_956_);
v___x_1146_ = l_Lean_Name_mkStr4(v___x_956_, v___x_957_, v___x_958_, v___x_1145_);
lean_inc(v___x_1144_);
v___x_1147_ = l_Lean_Syntax_isOfKind(v___x_1144_, v___x_1146_);
lean_dec(v___x_1146_);
if (v___x_1147_ == 0)
{
lean_object* v___x_1148_; 
lean_dec(v___x_1144_);
lean_dec(v_o_1130_);
lean_dec(v_tk_977_);
lean_dec(v___x_971_);
lean_dec_ref(v___x_958_);
lean_dec_ref(v___x_957_);
lean_dec_ref(v___x_956_);
v___x_1148_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
return v___x_1148_;
}
else
{
lean_object* v___x_1149_; lean_object* v_args_1150_; lean_object* v___x_1151_; 
v___x_1149_ = l_Lean_Syntax_getArg(v___x_1144_, v___x_970_);
lean_dec(v___x_1144_);
v_args_1150_ = l_Lean_Syntax_getArgs(v___x_1149_);
lean_dec(v___x_1149_);
v___x_1151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1151_, 0, v_args_1150_);
v___y_1103_ = v_o_1130_;
v_args_1104_ = v___x_1151_;
v___y_1105_ = v___y_1131_;
v___y_1106_ = v___y_1132_;
v___y_1107_ = v___y_1133_;
v___y_1108_ = v___y_1134_;
v___y_1109_ = v___y_1135_;
v___y_1110_ = v___y_1136_;
v___y_1111_ = v___y_1137_;
v___y_1112_ = v___y_1138_;
goto v___jp_1102_;
}
}
}
else
{
lean_object* v___x_1152_; 
lean_dec(v___x_1140_);
v___x_1152_ = lean_box(0);
v___y_1103_ = v_o_1130_;
v_args_1104_ = v___x_1152_;
v___y_1105_ = v___y_1131_;
v___y_1106_ = v___y_1132_;
v___y_1107_ = v___y_1133_;
v___y_1108_ = v___y_1134_;
v___y_1109_ = v___y_1135_;
v___y_1110_ = v___y_1136_;
v___y_1111_ = v___y_1137_;
v___y_1112_ = v___y_1138_;
goto v___jp_1102_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_evalDSimpTrace___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_954_ = stack[0].m_num;
lean_object* v_stx_955_ = stack[1].m_obj;
lean_object* v___x_956_ = stack[2].m_obj;
lean_object* v___x_957_ = stack[3].m_obj;
lean_object* v___x_958_ = stack[4].m_obj;
uint8_t v___x_959_ = stack[5].m_num;
lean_object* v___y_960_ = stack[6].m_obj;
lean_object* v___y_961_ = stack[7].m_obj;
lean_object* v___y_962_ = stack[8].m_obj;
lean_object* v___y_963_ = stack[9].m_obj;
lean_object* v___y_964_ = stack[10].m_obj;
lean_object* v___y_965_ = stack[11].m_obj;
lean_object* v___y_966_ = stack[12].m_obj;
lean_object* v___y_967_ = stack[13].m_obj;
lean_object* v_res_1161_;
v_res_1161_ = l_Lean_Elab_Tactic_Conv_evalDSimpTrace___lam__0(v___x_954_, v_stx_955_, v___x_956_, v___x_957_, v___x_958_, v___x_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_);
stack->m_obj
 = v_res_1161_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimpTrace___lam__0___boxed(lean_object* v___x_1162_, lean_object* v_stx_1163_, lean_object* v___x_1164_, lean_object* v___x_1165_, lean_object* v___x_1166_, lean_object* v___x_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
uint8_t v___x_4927__boxed_1177_; uint8_t v___x_4931__boxed_1178_; lean_object* v_res_1179_; 
v___x_4927__boxed_1177_ = lean_unbox(v___x_1162_);
v___x_4931__boxed_1178_ = lean_unbox(v___x_1167_);
v_res_1179_ = l_Lean_Elab_Tactic_Conv_evalDSimpTrace___lam__0(v___x_4927__boxed_1177_, v_stx_1163_, v___x_1164_, v___x_1165_, v___x_1166_, v___x_4931__boxed_1178_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_);
lean_dec(v___y_1175_);
lean_dec_ref(v___y_1174_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1168_);
lean_dec(v_stx_1163_);
return v_res_1179_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_evalDSimpTrace(lean_object* v_stx_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_){
_start:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; uint8_t v___x_1201_; uint8_t v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___y_1205_; lean_object* v___x_1206_; 
v___x_1197_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__0));
v___x_1198_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__1));
v___x_1199_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__2));
v___x_1200_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__1));
lean_inc(v_stx_1187_);
v___x_1201_ = l_Lean_Syntax_isOfKind(v_stx_1187_, v___x_1200_);
v___x_1202_ = 1;
v___x_1203_ = lean_box(v___x_1201_);
v___x_1204_ = lean_box(v___x_1202_);
v___y_1205_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalDSimpTrace___lam__0___boxed), 15, 6);
lean_closure_set(v___y_1205_, 0, v___x_1203_);
lean_closure_set(v___y_1205_, 1, v_stx_1187_);
lean_closure_set(v___y_1205_, 2, v___x_1197_);
lean_closure_set(v___y_1205_, 3, v___x_1198_);
lean_closure_set(v___y_1205_, 4, v___x_1199_);
lean_closure_set(v___y_1205_, 5, v___x_1204_);
v___x_1206_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___y_1205_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_);
return v___x_1206_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_evalDSimpTrace_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_1187_ = stack[0].m_obj;
lean_object* v_a_1188_ = stack[1].m_obj;
lean_object* v_a_1189_ = stack[2].m_obj;
lean_object* v_a_1190_ = stack[3].m_obj;
lean_object* v_a_1191_ = stack[4].m_obj;
lean_object* v_a_1192_ = stack[5].m_obj;
lean_object* v_a_1193_ = stack[6].m_obj;
lean_object* v_a_1194_ = stack[7].m_obj;
lean_object* v_a_1195_ = stack[8].m_obj;
lean_object* v_res_1207_;
v_res_1207_ = l_Lean_Elab_Tactic_Conv_evalDSimpTrace(v_stx_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_);
stack->m_obj
 = v_res_1207_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimpTrace___boxed(lean_object* v_stx_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l_Lean_Elab_Tactic_Conv_evalDSimpTrace(v_stx_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_);
lean_dec(v_a_1216_);
lean_dec_ref(v_a_1215_);
lean_dec(v_a_1214_);
lean_dec_ref(v_a_1213_);
lean_dec(v_a_1212_);
lean_dec_ref(v_a_1211_);
lean_dec(v_a_1210_);
lean_dec_ref(v_a_1209_);
return v_res_1218_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1(){
_start:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1227_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1228_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__1));
v___x_1229_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__1));
v___x_1230_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalDSimpTrace___boxed), 10, 0);
v___x_1231_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1227_, v___x_1228_, v___x_1229_, v___x_1230_);
return v___x_1231_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1232_;
v_res_1232_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1();
stack->m_obj
 = v_res_1232_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___boxed(lean_object* v_a_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1();
return v_res_1234_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Split(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Conv_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_SimpTrace(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Conv_Simp(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Tactic_Split(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Conv_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_SimpTrace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Conv_Simp(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Split(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Conv_Basic(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_SimpTrace(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Conv_Simp(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Split(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Conv_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_SimpTrace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Conv_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Conv_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Conv_Simp(builtin);
}
#ifdef __cplusplus
}
#endif
