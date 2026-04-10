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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Conv_changeLhs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Result_getProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Conv_updateLhs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_mkSimpCallStx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Array_mkArray3___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_applySimpResult(lean_object* v_result_1_, lean_object* v_a_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_, lean_object* v_a_9_){
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
lean_dec_ref(v___x_15_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_applySimpResult___boxed(lean_object* v_result_26_, lean_object* v_a_27_, lean_object* v_a_28_, lean_object* v_a_29_, lean_object* v_a_30_, lean_object* v_a_31_, lean_object* v_a_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_Lean_Elab_Tactic_Conv_applySimpResult(v_result_26_, v_a_27_, v_a_28_, v_a_29_, v_a_30_, v_a_31_, v_a_32_, v_a_33_, v_a_34_);
lean_dec(v_a_34_);
lean_dec_ref(v_a_33_);
lean_dec(v_a_32_);
lean_dec_ref(v_a_31_);
lean_dec(v_a_30_);
lean_dec_ref(v_a_29_);
lean_dec(v_a_28_);
lean_dec_ref(v_a_27_);
return v_res_36_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__0(void){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_37_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__1(void){
_start:
{
lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_38_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__0, &l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__0);
v___x_39_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_39_, 0, v___x_38_);
return v___x_39_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__2(void){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_40_ = lean_unsigned_to_nat(0u);
v___x_41_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__1, &l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__1);
v___x_42_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_42_, 0, v___x_41_);
lean_ctor_set(v___x_42_, 1, v___x_40_);
return v___x_42_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__3(void){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_43_ = lean_unsigned_to_nat(32u);
v___x_44_ = lean_mk_empty_array_with_capacity(v___x_43_);
v___x_45_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_45_, 0, v___x_44_);
return v___x_45_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__4(void){
_start:
{
size_t v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_46_ = ((size_t)5ULL);
v___x_47_ = lean_unsigned_to_nat(0u);
v___x_48_ = lean_unsigned_to_nat(32u);
v___x_49_ = lean_mk_empty_array_with_capacity(v___x_48_);
v___x_50_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__3, &l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__3);
v___x_51_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_51_, 0, v___x_50_);
lean_ctor_set(v___x_51_, 1, v___x_49_);
lean_ctor_set(v___x_51_, 2, v___x_47_);
lean_ctor_set(v___x_51_, 3, v___x_47_);
lean_ctor_set_usize(v___x_51_, 4, v___x_46_);
return v___x_51_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__5(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_52_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__4, &l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__4_once, _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__4);
v___x_53_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__1, &l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__1);
v___x_54_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_54_, 0, v___x_53_);
lean_ctor_set(v___x_54_, 1, v___x_53_);
lean_ctor_set(v___x_54_, 2, v___x_53_);
lean_ctor_set(v___x_54_, 3, v___x_52_);
return v___x_54_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6(void){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_55_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__5, &l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__5);
v___x_56_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__2, &l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__2);
v___x_57_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_57_, 0, v___x_56_);
lean_ctor_set(v___x_57_, 1, v___x_55_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___lam__0(lean_object* v_a_58_, lean_object* v_ctx_59_, lean_object* v_simprocs_60_, lean_object* v_d_x3f_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_71_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6, &l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6);
v___x_72_ = l_Lean_Meta_simp(v_a_58_, v_ctx_59_, v_simprocs_60_, v_d_x3f_61_, v___x_71_, v___y_66_, v___y_67_, v___y_68_, v___y_69_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___boxed(lean_object* v_a_73_, lean_object* v_ctx_74_, lean_object* v_simprocs_75_, lean_object* v_d_x3f_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Lean_Elab_Tactic_Conv_evalSimp___lam__0(v_a_73_, v_ctx_74_, v_simprocs_75_, v_d_x3f_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_);
lean_dec(v___y_84_);
lean_dec_ref(v___y_83_);
lean_dec(v___y_82_);
lean_dec_ref(v___y_81_);
lean_dec(v___y_80_);
lean_dec_ref(v___y_79_);
lean_dec(v___y_78_);
lean_dec_ref(v___y_77_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___lam__1(lean_object* v_stx_87_, uint8_t v___x_88_, uint8_t v___x_89_, lean_object* v___x_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = l_Lean_Elab_Tactic_mkSimpContext(v_stx_87_, v___x_88_, v___x_89_, v___x_88_, v___x_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_);
if (lean_obj_tag(v___x_100_) == 0)
{
lean_object* v_a_101_; lean_object* v_ctx_102_; lean_object* v_simprocs_103_; lean_object* v_dischargeWrapper_104_; lean_object* v___x_105_; 
v_a_101_ = lean_ctor_get(v___x_100_, 0);
lean_inc(v_a_101_);
lean_dec_ref(v___x_100_);
v_ctx_102_ = lean_ctor_get(v_a_101_, 0);
lean_inc_ref(v_ctx_102_);
v_simprocs_103_ = lean_ctor_get(v_a_101_, 1);
lean_inc_ref(v_simprocs_103_);
v_dischargeWrapper_104_ = lean_ctor_get(v_a_101_, 2);
lean_inc(v_dischargeWrapper_104_);
lean_dec(v_a_101_);
v___x_105_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_92_, v___y_95_, v___y_96_, v___y_97_, v___y_98_);
if (lean_obj_tag(v___x_105_) == 0)
{
lean_object* v_a_106_; lean_object* v___f_107_; lean_object* v___x_108_; 
v_a_106_ = lean_ctor_get(v___x_105_, 0);
lean_inc(v_a_106_);
lean_dec_ref(v___x_105_);
v___f_107_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___boxed), 13, 3);
lean_closure_set(v___f_107_, 0, v_a_106_);
lean_closure_set(v___f_107_, 1, v_ctx_102_);
lean_closure_set(v___f_107_, 2, v_simprocs_103_);
v___x_108_ = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(v_dischargeWrapper_104_, v___f_107_, v___y_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_);
lean_dec(v_dischargeWrapper_104_);
if (lean_obj_tag(v___x_108_) == 0)
{
lean_object* v_a_109_; lean_object* v_fst_110_; lean_object* v___x_111_; 
v_a_109_ = lean_ctor_get(v___x_108_, 0);
lean_inc(v_a_109_);
lean_dec_ref(v___x_108_);
v_fst_110_ = lean_ctor_get(v_a_109_, 0);
lean_inc(v_fst_110_);
lean_dec(v_a_109_);
v___x_111_ = l_Lean_Elab_Tactic_Conv_applySimpResult(v_fst_110_, v___y_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_);
return v___x_111_;
}
else
{
lean_object* v_a_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_119_; 
v_a_112_ = lean_ctor_get(v___x_108_, 0);
v_isSharedCheck_119_ = !lean_is_exclusive(v___x_108_);
if (v_isSharedCheck_119_ == 0)
{
v___x_114_ = v___x_108_;
v_isShared_115_ = v_isSharedCheck_119_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_a_112_);
lean_dec(v___x_108_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_119_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v___x_117_; 
if (v_isShared_115_ == 0)
{
v___x_117_ = v___x_114_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v_a_112_);
v___x_117_ = v_reuseFailAlloc_118_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
return v___x_117_;
}
}
}
}
else
{
lean_object* v_a_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_127_; 
lean_dec(v_dischargeWrapper_104_);
lean_dec_ref(v_simprocs_103_);
lean_dec_ref(v_ctx_102_);
v_a_120_ = lean_ctor_get(v___x_105_, 0);
v_isSharedCheck_127_ = !lean_is_exclusive(v___x_105_);
if (v_isSharedCheck_127_ == 0)
{
v___x_122_ = v___x_105_;
v_isShared_123_ = v_isSharedCheck_127_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_a_120_);
lean_dec(v___x_105_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_127_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_125_; 
if (v_isShared_123_ == 0)
{
v___x_125_ = v___x_122_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v_a_120_);
v___x_125_ = v_reuseFailAlloc_126_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
return v___x_125_;
}
}
}
}
else
{
lean_object* v_a_128_; lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_135_; 
v_a_128_ = lean_ctor_get(v___x_100_, 0);
v_isSharedCheck_135_ = !lean_is_exclusive(v___x_100_);
if (v_isSharedCheck_135_ == 0)
{
v___x_130_ = v___x_100_;
v_isShared_131_ = v_isSharedCheck_135_;
goto v_resetjp_129_;
}
else
{
lean_inc(v_a_128_);
lean_dec(v___x_100_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_135_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
lean_object* v___x_133_; 
if (v_isShared_131_ == 0)
{
v___x_133_ = v___x_130_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v_a_128_);
v___x_133_ = v_reuseFailAlloc_134_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
return v___x_133_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___lam__1___boxed(lean_object* v_stx_136_, lean_object* v___x_137_, lean_object* v___x_138_, lean_object* v___x_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_){
_start:
{
uint8_t v___x_754__boxed_149_; uint8_t v___x_755__boxed_150_; lean_object* v_res_151_; 
v___x_754__boxed_149_ = lean_unbox(v___x_137_);
v___x_755__boxed_150_ = lean_unbox(v___x_138_);
v_res_151_ = l_Lean_Elab_Tactic_Conv_evalSimp___lam__1(v_stx_136_, v___x_754__boxed_149_, v___x_755__boxed_150_, v___x_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_);
lean_dec(v___y_147_);
lean_dec_ref(v___y_146_);
lean_dec(v___y_145_);
lean_dec_ref(v___y_144_);
lean_dec(v___y_143_);
lean_dec_ref(v___y_142_);
lean_dec(v___y_141_);
lean_dec_ref(v___y_140_);
lean_dec(v_stx_136_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimp(lean_object* v_stx_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_){
_start:
{
uint8_t v___x_163_; uint8_t v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___f_168_; lean_object* v___x_169_; 
v___x_163_ = 0;
v___x_164_ = 0;
v___x_165_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimp___closed__0));
v___x_166_ = lean_box(v___x_163_);
v___x_167_ = lean_box(v___x_164_);
v___f_168_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalSimp___lam__1___boxed), 13, 4);
lean_closure_set(v___f_168_, 0, v_stx_153_);
lean_closure_set(v___f_168_, 1, v___x_166_);
lean_closure_set(v___f_168_, 2, v___x_167_);
lean_closure_set(v___f_168_, 3, v___x_165_);
v___x_169_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_168_, v_a_154_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___boxed(lean_object* v_stx_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Lean_Elab_Tactic_Conv_evalSimp(v_stx_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_);
lean_dec(v_a_178_);
lean_dec_ref(v_a_177_);
lean_dec(v_a_176_);
lean_dec_ref(v_a_175_);
lean_dec(v_a_174_);
lean_dec_ref(v_a_173_);
lean_dec(v_a_172_);
lean_dec_ref(v_a_171_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1(){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_201_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_202_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__5));
v___x_203_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__8));
v___x_204_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalSimp___boxed), 10, 0);
v___x_205_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_201_, v___x_202_, v___x_203_, v___x_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___boxed(lean_object* v_a_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1();
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3(){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_233_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__8));
v___x_234_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__6));
v___x_235_ = l_Lean_addBuiltinDeclarationRanges(v___x_233_, v___x_234_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___boxed(lean_object* v_a_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3();
return v_res_237_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_238_ = lean_box(0);
v___x_239_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_240_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
lean_ctor_set(v___x_240_, 1, v___x_238_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg(){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_242_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg___closed__0);
v___x_243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg___boxed(lean_object* v___y_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0(lean_object* v_00_u03b1_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_){
_start:
{
lean_object* v___x_256_; 
v___x_256_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___boxed(lean_object* v_00_u03b1_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0(v_00_u03b1_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_);
lean_dec(v___y_265_);
lean_dec_ref(v___y_264_);
lean_dec(v___y_263_);
lean_dec_ref(v___y_262_);
lean_dec(v___y_261_);
lean_dec_ref(v___y_260_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__0(lean_object* v___x_268_, lean_object* v_a_269_, lean_object* v_ctx_270_, lean_object* v_simprocs_271_, lean_object* v_d_x3f_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; size_t v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_282_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__1, &l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__1);
lean_inc_n(v___x_268_, 2);
v___x_283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_283_, 0, v___x_282_);
lean_ctor_set(v___x_283_, 1, v___x_268_);
v___x_284_ = lean_unsigned_to_nat(32u);
v___x_285_ = lean_mk_empty_array_with_capacity(v___x_284_);
v___x_286_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__3, &l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__3);
v___x_287_ = ((size_t)5ULL);
v___x_288_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_288_, 0, v___x_286_);
lean_ctor_set(v___x_288_, 1, v___x_285_);
lean_ctor_set(v___x_288_, 2, v___x_268_);
lean_ctor_set(v___x_288_, 3, v___x_268_);
lean_ctor_set_usize(v___x_288_, 4, v___x_287_);
v___x_289_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_289_, 0, v___x_282_);
lean_ctor_set(v___x_289_, 1, v___x_282_);
lean_ctor_set(v___x_289_, 2, v___x_282_);
lean_ctor_set(v___x_289_, 3, v___x_288_);
v___x_290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_290_, 0, v___x_283_);
lean_ctor_set(v___x_290_, 1, v___x_289_);
v___x_291_ = l_Lean_Meta_simp(v_a_269_, v_ctx_270_, v_simprocs_271_, v_d_x3f_272_, v___x_290_, v___y_277_, v___y_278_, v___y_279_, v___y_280_);
lean_dec_ref(v___x_290_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__0___boxed(lean_object* v___x_292_, lean_object* v_a_293_, lean_object* v_ctx_294_, lean_object* v_simprocs_295_, lean_object* v_d_x3f_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__0(v___x_292_, v_a_293_, v_ctx_294_, v_simprocs_295_, v_d_x3f_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_);
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
lean_dec(v___y_300_);
lean_dec_ref(v___y_299_);
lean_dec(v___y_298_);
lean_dec_ref(v___y_297_);
return v_res_306_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__10(void){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = l_Array_mkArray0(lean_box(0));
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1(uint8_t v___x_322_, lean_object* v_stx_323_, lean_object* v___x_324_, lean_object* v___x_325_, lean_object* v___x_326_, uint8_t v___x_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_){
_start:
{
if (v___x_322_ == 0)
{
lean_object* v___x_337_; 
lean_dec_ref(v___x_326_);
lean_dec_ref(v___x_325_);
lean_dec_ref(v___x_324_);
v___x_337_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
return v___x_337_;
}
else
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; uint8_t v___x_342_; 
v___x_338_ = lean_unsigned_to_nat(1u);
v___x_339_ = l_Lean_Syntax_getArg(v_stx_323_, v___x_338_);
v___x_340_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__0));
lean_inc_ref(v___x_326_);
lean_inc_ref(v___x_325_);
lean_inc_ref(v___x_324_);
v___x_341_ = l_Lean_Name_mkStr4(v___x_324_, v___x_325_, v___x_326_, v___x_340_);
lean_inc(v___x_339_);
v___x_342_ = l_Lean_Syntax_isOfKind(v___x_339_, v___x_341_);
lean_dec(v___x_341_);
if (v___x_342_ == 0)
{
lean_object* v___x_343_; 
lean_dec(v___x_339_);
lean_dec_ref(v___x_326_);
lean_dec_ref(v___x_325_);
lean_dec_ref(v___x_324_);
v___x_343_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
return v___x_343_;
}
else
{
lean_object* v___x_344_; lean_object* v_tk_345_; lean_object* v___y_347_; lean_object* v___y_348_; lean_object* v___y_349_; lean_object* v___y_350_; lean_object* v___y_351_; lean_object* v___y_352_; lean_object* v___y_353_; lean_object* v___y_354_; lean_object* v___y_355_; lean_object* v___y_356_; lean_object* v___y_357_; lean_object* v___y_358_; uint8_t v___y_359_; lean_object* v___y_360_; lean_object* v___y_361_; lean_object* v___y_362_; lean_object* v___y_363_; lean_object* v___y_364_; lean_object* v___y_442_; lean_object* v___y_443_; lean_object* v___y_444_; lean_object* v___y_445_; lean_object* v___y_446_; lean_object* v___y_447_; lean_object* v___y_448_; lean_object* v___y_449_; lean_object* v___y_450_; lean_object* v___y_451_; lean_object* v___y_452_; lean_object* v___y_453_; lean_object* v___y_454_; uint8_t v___y_455_; lean_object* v___y_456_; lean_object* v___y_457_; lean_object* v___y_458_; lean_object* v___y_459_; lean_object* v___y_472_; lean_object* v___y_473_; lean_object* v___y_474_; lean_object* v___y_475_; lean_object* v___y_476_; lean_object* v___y_477_; lean_object* v___y_478_; lean_object* v___y_479_; lean_object* v___y_480_; lean_object* v___y_481_; lean_object* v___y_482_; lean_object* v___y_483_; lean_object* v___y_484_; uint8_t v___y_485_; lean_object* v___y_486_; lean_object* v___y_487_; lean_object* v___y_488_; lean_object* v___y_489_; lean_object* v___y_499_; lean_object* v___y_500_; lean_object* v___y_501_; lean_object* v___y_502_; lean_object* v___y_503_; lean_object* v___y_504_; lean_object* v___y_505_; lean_object* v___y_506_; lean_object* v___y_507_; lean_object* v___y_508_; lean_object* v___y_509_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___y_525_; lean_object* v_args_526_; lean_object* v___y_527_; lean_object* v___y_528_; lean_object* v___y_529_; lean_object* v___y_530_; lean_object* v___y_531_; lean_object* v___y_532_; lean_object* v___y_533_; lean_object* v___y_534_; lean_object* v_o_546_; lean_object* v___y_547_; lean_object* v___y_548_; lean_object* v___y_549_; lean_object* v___y_550_; lean_object* v___y_551_; lean_object* v___y_552_; lean_object* v___y_553_; lean_object* v___y_554_; lean_object* v___x_569_; lean_object* v___x_570_; uint8_t v___x_571_; 
v___x_344_ = lean_unsigned_to_nat(0u);
v_tk_345_ = l_Lean_Syntax_getArg(v_stx_323_, v___x_344_);
v___x_522_ = lean_unsigned_to_nat(2u);
v___x_523_ = l_Lean_Syntax_getArg(v_stx_323_, v___x_522_);
v___x_569_ = lean_unsigned_to_nat(3u);
v___x_570_ = l_Lean_Syntax_getArg(v_stx_323_, v___x_569_);
v___x_571_ = l_Lean_Syntax_isNone(v___x_570_);
if (v___x_571_ == 0)
{
uint8_t v___x_572_; 
lean_inc(v___x_570_);
v___x_572_ = l_Lean_Syntax_matchesNull(v___x_570_, v___x_338_);
if (v___x_572_ == 0)
{
lean_object* v___x_573_; 
lean_dec(v___x_570_);
lean_dec(v___x_523_);
lean_dec(v_tk_345_);
lean_dec(v___x_339_);
lean_dec_ref(v___x_326_);
lean_dec_ref(v___x_325_);
lean_dec_ref(v___x_324_);
v___x_573_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
return v___x_573_;
}
else
{
lean_object* v_o_574_; lean_object* v___x_575_; 
v_o_574_ = l_Lean_Syntax_getArg(v___x_570_, v___x_344_);
lean_dec(v___x_570_);
v___x_575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_575_, 0, v_o_574_);
v_o_546_ = v___x_575_;
v___y_547_ = v___y_328_;
v___y_548_ = v___y_329_;
v___y_549_ = v___y_330_;
v___y_550_ = v___y_331_;
v___y_551_ = v___y_332_;
v___y_552_ = v___y_333_;
v___y_553_ = v___y_334_;
v___y_554_ = v___y_335_;
goto v___jp_545_;
}
}
else
{
lean_object* v___x_576_; 
lean_dec(v___x_570_);
v___x_576_ = lean_box(0);
v_o_546_ = v___x_576_;
v___y_547_ = v___y_328_;
v___y_548_ = v___y_329_;
v___y_549_ = v___y_330_;
v___y_550_ = v___y_331_;
v___y_551_ = v___y_332_;
v___y_552_ = v___y_333_;
v___y_553_ = v___y_334_;
v___y_554_ = v___y_335_;
goto v___jp_545_;
}
v___jp_346_:
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; uint8_t v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
lean_inc_ref_n(v___y_352_, 2);
v___x_365_ = l_Array_append___redArg(v___y_352_, v___y_364_);
lean_dec_ref(v___y_364_);
lean_inc_n(v___y_362_, 2);
lean_inc_n(v___y_353_, 2);
v___x_366_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_366_, 0, v___y_353_);
lean_ctor_set(v___x_366_, 1, v___y_362_);
lean_ctor_set(v___x_366_, 2, v___x_365_);
v___x_367_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_367_, 0, v___y_353_);
lean_ctor_set(v___x_367_, 1, v___y_362_);
lean_ctor_set(v___x_367_, 2, v___y_352_);
v___x_368_ = l_Lean_Syntax_node6(v___y_353_, v___y_348_, v___y_354_, v___x_339_, v___y_356_, v___y_360_, v___x_366_, v___x_367_);
v___x_369_ = 0;
v___x_370_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimp___closed__0));
v___x_371_ = l_Lean_Elab_Tactic_mkSimpContext(v___x_368_, v___y_359_, v___x_369_, v___y_359_, v___x_370_, v___y_361_, v___y_358_, v___y_351_, v___y_363_, v___y_355_, v___y_350_, v___y_357_, v___y_347_);
if (lean_obj_tag(v___x_371_) == 0)
{
lean_object* v_a_372_; lean_object* v_ctx_373_; lean_object* v_simprocs_374_; lean_object* v_dischargeWrapper_375_; lean_object* v___x_376_; 
v_a_372_ = lean_ctor_get(v___x_371_, 0);
lean_inc(v_a_372_);
lean_dec_ref(v___x_371_);
v_ctx_373_ = lean_ctor_get(v_a_372_, 0);
lean_inc_ref(v_ctx_373_);
v_simprocs_374_ = lean_ctor_get(v_a_372_, 1);
lean_inc_ref(v_simprocs_374_);
v_dischargeWrapper_375_ = lean_ctor_get(v_a_372_, 2);
lean_inc(v_dischargeWrapper_375_);
lean_dec(v_a_372_);
v___x_376_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_358_, v___y_355_, v___y_350_, v___y_357_, v___y_347_);
if (lean_obj_tag(v___x_376_) == 0)
{
lean_object* v_a_377_; lean_object* v___f_378_; lean_object* v___x_379_; 
v_a_377_ = lean_ctor_get(v___x_376_, 0);
lean_inc(v_a_377_);
lean_dec_ref(v___x_376_);
v___f_378_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__0___boxed), 14, 4);
lean_closure_set(v___f_378_, 0, v___x_344_);
lean_closure_set(v___f_378_, 1, v_a_377_);
lean_closure_set(v___f_378_, 2, v_ctx_373_);
lean_closure_set(v___f_378_, 3, v_simprocs_374_);
v___x_379_ = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(v_dischargeWrapper_375_, v___f_378_, v___y_361_, v___y_358_, v___y_351_, v___y_363_, v___y_355_, v___y_350_, v___y_357_, v___y_347_);
lean_dec(v_dischargeWrapper_375_);
if (lean_obj_tag(v___x_379_) == 0)
{
lean_object* v_a_380_; lean_object* v_fst_381_; lean_object* v_snd_382_; lean_object* v___x_383_; 
v_a_380_ = lean_ctor_get(v___x_379_, 0);
lean_inc(v_a_380_);
lean_dec_ref(v___x_379_);
v_fst_381_ = lean_ctor_get(v_a_380_, 0);
lean_inc(v_fst_381_);
v_snd_382_ = lean_ctor_get(v_a_380_, 1);
lean_inc(v_snd_382_);
lean_dec(v_a_380_);
v___x_383_ = l_Lean_Elab_Tactic_Conv_applySimpResult(v_fst_381_, v___y_361_, v___y_358_, v___y_351_, v___y_363_, v___y_355_, v___y_350_, v___y_357_, v___y_347_);
if (lean_obj_tag(v___x_383_) == 0)
{
lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_415_; 
v_isSharedCheck_415_ = !lean_is_exclusive(v___x_383_);
if (v_isSharedCheck_415_ == 0)
{
lean_object* v_unused_416_; 
v_unused_416_ = lean_ctor_get(v___x_383_, 0);
lean_dec(v_unused_416_);
v___x_385_ = v___x_383_;
v_isShared_386_ = v_isSharedCheck_415_;
goto v_resetjp_384_;
}
else
{
lean_dec(v___x_383_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_415_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v_usedTheorems_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_413_; 
v_usedTheorems_387_ = lean_ctor_get(v_snd_382_, 0);
v_isSharedCheck_413_ = !lean_is_exclusive(v_snd_382_);
if (v_isSharedCheck_413_ == 0)
{
lean_object* v_unused_414_; 
v_unused_414_ = lean_ctor_get(v_snd_382_, 1);
lean_dec(v_unused_414_);
v___x_389_ = v_snd_382_;
v_isShared_390_ = v_isSharedCheck_413_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_usedTheorems_387_);
lean_dec(v_snd_382_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_413_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_391_; 
v___x_391_ = l_Lean_Elab_Tactic_mkSimpCallStx(v___x_368_, v_usedTheorems_387_, v___y_355_, v___y_350_, v___y_357_, v___y_347_);
lean_dec_ref(v_usedTheorems_387_);
if (lean_obj_tag(v___x_391_) == 0)
{
lean_object* v_a_392_; lean_object* v___x_393_; lean_object* v___x_395_; 
v_a_392_ = lean_ctor_get(v___x_391_, 0);
lean_inc(v_a_392_);
lean_dec_ref(v___x_391_);
v___x_393_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__2));
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 1, v_a_392_);
lean_ctor_set(v___x_389_, 0, v___x_393_);
v___x_395_ = v___x_389_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v___x_393_);
lean_ctor_set(v_reuseFailAlloc_404_, 1, v_a_392_);
v___x_395_ = v_reuseFailAlloc_404_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_399_; 
v___x_396_ = lean_box(0);
v___x_397_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_397_, 0, v___x_395_);
lean_ctor_set(v___x_397_, 1, v___x_396_);
lean_ctor_set(v___x_397_, 2, v___x_396_);
lean_ctor_set(v___x_397_, 3, v___x_396_);
lean_ctor_set(v___x_397_, 4, v___x_396_);
lean_ctor_set(v___x_397_, 5, v___x_396_);
lean_inc(v___y_349_);
if (v_isShared_386_ == 0)
{
lean_ctor_set_tag(v___x_385_, 1);
lean_ctor_set(v___x_385_, 0, v___y_349_);
v___x_399_ = v___x_385_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v___y_349_);
v___x_399_ = v_reuseFailAlloc_403_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
lean_object* v___x_400_; uint8_t v___x_401_; lean_object* v___x_402_; 
v___x_400_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__3));
v___x_401_ = 4;
v___x_402_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_345_, v___x_397_, v___x_399_, v___x_400_, v___x_396_, v___x_401_, v___y_357_, v___y_347_);
return v___x_402_;
}
}
}
else
{
lean_object* v_a_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_412_; 
lean_del_object(v___x_389_);
lean_del_object(v___x_385_);
lean_dec(v_tk_345_);
v_a_405_ = lean_ctor_get(v___x_391_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_412_ == 0)
{
v___x_407_ = v___x_391_;
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_a_405_);
lean_dec(v___x_391_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_410_; 
if (v_isShared_408_ == 0)
{
v___x_410_ = v___x_407_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_a_405_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
}
}
}
else
{
lean_dec(v_snd_382_);
lean_dec(v___x_368_);
lean_dec(v_tk_345_);
return v___x_383_;
}
}
else
{
lean_object* v_a_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_424_; 
lean_dec(v___x_368_);
lean_dec(v_tk_345_);
v_a_417_ = lean_ctor_get(v___x_379_, 0);
v_isSharedCheck_424_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_424_ == 0)
{
v___x_419_ = v___x_379_;
v_isShared_420_ = v_isSharedCheck_424_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_a_417_);
lean_dec(v___x_379_);
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
lean_ctor_set(v_reuseFailAlloc_423_, 0, v_a_417_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
return v___x_422_;
}
}
}
}
else
{
lean_object* v_a_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_432_; 
lean_dec(v_dischargeWrapper_375_);
lean_dec_ref(v_simprocs_374_);
lean_dec_ref(v_ctx_373_);
lean_dec(v___x_368_);
lean_dec(v_tk_345_);
v_a_425_ = lean_ctor_get(v___x_376_, 0);
v_isSharedCheck_432_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_432_ == 0)
{
v___x_427_ = v___x_376_;
v_isShared_428_ = v_isSharedCheck_432_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_a_425_);
lean_dec(v___x_376_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_432_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_430_; 
if (v_isShared_428_ == 0)
{
v___x_430_ = v___x_427_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_a_425_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
}
}
}
}
else
{
lean_object* v_a_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_440_; 
lean_dec(v___x_368_);
lean_dec(v_tk_345_);
v_a_433_ = lean_ctor_get(v___x_371_, 0);
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_440_ == 0)
{
v___x_435_ = v___x_371_;
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_a_433_);
lean_dec(v___x_371_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_438_; 
if (v_isShared_436_ == 0)
{
v___x_438_ = v___x_435_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_a_433_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
}
v___jp_441_:
{
lean_object* v___x_460_; lean_object* v___x_461_; 
lean_inc_ref(v___y_447_);
v___x_460_ = l_Array_append___redArg(v___y_447_, v___y_459_);
lean_dec_ref(v___y_459_);
lean_inc(v___y_458_);
lean_inc(v___y_448_);
v___x_461_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_461_, 0, v___y_448_);
lean_ctor_set(v___x_461_, 1, v___y_458_);
lean_ctor_set(v___x_461_, 2, v___x_460_);
if (lean_obj_tag(v___y_454_) == 1)
{
lean_object* v_val_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v_val_462_ = lean_ctor_get(v___y_454_, 0);
lean_inc(v_val_462_);
lean_dec_ref(v___y_454_);
v___x_463_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__4));
lean_inc_n(v___y_448_, 3);
v___x_464_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_464_, 0, v___y_448_);
lean_ctor_set(v___x_464_, 1, v___x_463_);
lean_inc_ref(v___y_447_);
v___x_465_ = l_Array_append___redArg(v___y_447_, v_val_462_);
lean_dec(v_val_462_);
lean_inc(v___y_458_);
v___x_466_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_466_, 0, v___y_448_);
lean_ctor_set(v___x_466_, 1, v___y_458_);
lean_ctor_set(v___x_466_, 2, v___x_465_);
v___x_467_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__5));
v___x_468_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_468_, 0, v___y_448_);
lean_ctor_set(v___x_468_, 1, v___x_467_);
v___x_469_ = l_Array_mkArray3___redArg(v___x_464_, v___x_466_, v___x_468_);
v___y_347_ = v___y_442_;
v___y_348_ = v___y_443_;
v___y_349_ = v___y_444_;
v___y_350_ = v___y_445_;
v___y_351_ = v___y_446_;
v___y_352_ = v___y_447_;
v___y_353_ = v___y_448_;
v___y_354_ = v___y_449_;
v___y_355_ = v___y_450_;
v___y_356_ = v___y_451_;
v___y_357_ = v___y_452_;
v___y_358_ = v___y_453_;
v___y_359_ = v___y_455_;
v___y_360_ = v___x_461_;
v___y_361_ = v___y_456_;
v___y_362_ = v___y_458_;
v___y_363_ = v___y_457_;
v___y_364_ = v___x_469_;
goto v___jp_346_;
}
else
{
lean_object* v___x_470_; 
lean_dec(v___y_454_);
v___x_470_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__6));
v___y_347_ = v___y_442_;
v___y_348_ = v___y_443_;
v___y_349_ = v___y_444_;
v___y_350_ = v___y_445_;
v___y_351_ = v___y_446_;
v___y_352_ = v___y_447_;
v___y_353_ = v___y_448_;
v___y_354_ = v___y_449_;
v___y_355_ = v___y_450_;
v___y_356_ = v___y_451_;
v___y_357_ = v___y_452_;
v___y_358_ = v___y_453_;
v___y_359_ = v___y_455_;
v___y_360_ = v___x_461_;
v___y_361_ = v___y_456_;
v___y_362_ = v___y_458_;
v___y_363_ = v___y_457_;
v___y_364_ = v___x_470_;
goto v___jp_346_;
}
}
v___jp_471_:
{
lean_object* v___x_490_; lean_object* v___x_491_; 
lean_inc_ref(v___y_477_);
v___x_490_ = l_Array_append___redArg(v___y_477_, v___y_489_);
lean_dec_ref(v___y_489_);
lean_inc(v___y_488_);
lean_inc(v___y_478_);
v___x_491_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_491_, 0, v___y_478_);
lean_ctor_set(v___x_491_, 1, v___y_488_);
lean_ctor_set(v___x_491_, 2, v___x_490_);
if (lean_obj_tag(v___y_479_) == 1)
{
lean_object* v_val_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v_val_492_ = lean_ctor_get(v___y_479_, 0);
lean_inc(v_val_492_);
lean_dec_ref(v___y_479_);
v___x_493_ = l_Lean_SourceInfo_fromRef(v_val_492_, v___x_327_);
lean_dec(v_val_492_);
v___x_494_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__7));
v___x_495_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_495_, 0, v___x_493_);
lean_ctor_set(v___x_495_, 1, v___x_494_);
v___x_496_ = l_Array_mkArray1___redArg(v___x_495_);
v___y_442_ = v___y_472_;
v___y_443_ = v___y_473_;
v___y_444_ = v___y_474_;
v___y_445_ = v___y_475_;
v___y_446_ = v___y_476_;
v___y_447_ = v___y_477_;
v___y_448_ = v___y_478_;
v___y_449_ = v___y_480_;
v___y_450_ = v___y_481_;
v___y_451_ = v___x_491_;
v___y_452_ = v___y_482_;
v___y_453_ = v___y_483_;
v___y_454_ = v___y_484_;
v___y_455_ = v___y_485_;
v___y_456_ = v___y_486_;
v___y_457_ = v___y_487_;
v___y_458_ = v___y_488_;
v___y_459_ = v___x_496_;
goto v___jp_441_;
}
else
{
lean_object* v___x_497_; 
lean_dec(v___y_479_);
v___x_497_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__6));
v___y_442_ = v___y_472_;
v___y_443_ = v___y_473_;
v___y_444_ = v___y_474_;
v___y_445_ = v___y_475_;
v___y_446_ = v___y_476_;
v___y_447_ = v___y_477_;
v___y_448_ = v___y_478_;
v___y_449_ = v___y_480_;
v___y_450_ = v___y_481_;
v___y_451_ = v___x_491_;
v___y_452_ = v___y_482_;
v___y_453_ = v___y_483_;
v___y_454_ = v___y_484_;
v___y_455_ = v___y_485_;
v___y_456_ = v___y_486_;
v___y_457_ = v___y_487_;
v___y_458_ = v___y_488_;
v___y_459_ = v___x_497_;
goto v___jp_441_;
}
}
v___jp_498_:
{
lean_object* v_ref_510_; uint8_t v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
v_ref_510_ = lean_ctor_get(v___y_504_, 5);
v___x_511_ = 0;
v___x_512_ = l_Lean_SourceInfo_fromRef(v_ref_510_, v___x_511_);
v___x_513_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__4));
v___x_514_ = l_Lean_Name_mkStr4(v___x_324_, v___x_325_, v___x_326_, v___x_513_);
v___x_515_ = l_Lean_SourceInfo_fromRef(v_tk_345_, v___x_327_);
v___x_516_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_516_, 0, v___x_515_);
lean_ctor_set(v___x_516_, 1, v___x_513_);
v___x_517_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__9));
v___x_518_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__10, &l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__10_once, _init_l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__10);
if (lean_obj_tag(v___y_509_) == 1)
{
lean_object* v_val_519_; lean_object* v___x_520_; 
v_val_519_ = lean_ctor_get(v___y_509_, 0);
lean_inc(v_val_519_);
lean_dec_ref(v___y_509_);
v___x_520_ = l_Array_mkArray1___redArg(v_val_519_);
v___y_472_ = v___y_499_;
v___y_473_ = v___x_514_;
v___y_474_ = v_ref_510_;
v___y_475_ = v___y_502_;
v___y_476_ = v___y_501_;
v___y_477_ = v___x_518_;
v___y_478_ = v___x_512_;
v___y_479_ = v___y_506_;
v___y_480_ = v___x_516_;
v___y_481_ = v___y_500_;
v___y_482_ = v___y_504_;
v___y_483_ = v___y_503_;
v___y_484_ = v___y_505_;
v___y_485_ = v___x_511_;
v___y_486_ = v___y_507_;
v___y_487_ = v___y_508_;
v___y_488_ = v___x_517_;
v___y_489_ = v___x_520_;
goto v___jp_471_;
}
else
{
lean_object* v___x_521_; 
lean_dec(v___y_509_);
v___x_521_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__6));
v___y_472_ = v___y_499_;
v___y_473_ = v___x_514_;
v___y_474_ = v_ref_510_;
v___y_475_ = v___y_502_;
v___y_476_ = v___y_501_;
v___y_477_ = v___x_518_;
v___y_478_ = v___x_512_;
v___y_479_ = v___y_506_;
v___y_480_ = v___x_516_;
v___y_481_ = v___y_500_;
v___y_482_ = v___y_504_;
v___y_483_ = v___y_503_;
v___y_484_ = v___y_505_;
v___y_485_ = v___x_511_;
v___y_486_ = v___y_507_;
v___y_487_ = v___y_508_;
v___y_488_ = v___x_517_;
v___y_489_ = v___x_521_;
goto v___jp_471_;
}
}
v___jp_524_:
{
lean_object* v___x_535_; 
v___x_535_ = l_Lean_Syntax_getOptional_x3f(v___x_523_);
lean_dec(v___x_523_);
if (lean_obj_tag(v___x_535_) == 0)
{
lean_object* v___x_536_; 
v___x_536_ = lean_box(0);
v___y_499_ = v___y_534_;
v___y_500_ = v___y_531_;
v___y_501_ = v___y_529_;
v___y_502_ = v___y_532_;
v___y_503_ = v___y_528_;
v___y_504_ = v___y_533_;
v___y_505_ = v_args_526_;
v___y_506_ = v___y_525_;
v___y_507_ = v___y_527_;
v___y_508_ = v___y_530_;
v___y_509_ = v___x_536_;
goto v___jp_498_;
}
else
{
lean_object* v_val_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_544_; 
v_val_537_ = lean_ctor_get(v___x_535_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v___x_535_);
if (v_isSharedCheck_544_ == 0)
{
v___x_539_ = v___x_535_;
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_val_537_);
lean_dec(v___x_535_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_542_; 
if (v_isShared_540_ == 0)
{
v___x_542_ = v___x_539_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_val_537_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
v___y_499_ = v___y_534_;
v___y_500_ = v___y_531_;
v___y_501_ = v___y_529_;
v___y_502_ = v___y_532_;
v___y_503_ = v___y_528_;
v___y_504_ = v___y_533_;
v___y_505_ = v_args_526_;
v___y_506_ = v___y_525_;
v___y_507_ = v___y_527_;
v___y_508_ = v___y_530_;
v___y_509_ = v___x_542_;
goto v___jp_498_;
}
}
}
}
v___jp_545_:
{
lean_object* v___x_555_; lean_object* v___x_556_; uint8_t v___x_557_; 
v___x_555_ = lean_unsigned_to_nat(4u);
v___x_556_ = l_Lean_Syntax_getArg(v_stx_323_, v___x_555_);
v___x_557_ = l_Lean_Syntax_isNone(v___x_556_);
if (v___x_557_ == 0)
{
uint8_t v___x_558_; 
lean_inc(v___x_556_);
v___x_558_ = l_Lean_Syntax_matchesNull(v___x_556_, v___x_338_);
if (v___x_558_ == 0)
{
lean_object* v___x_559_; 
lean_dec(v___x_556_);
lean_dec(v_o_546_);
lean_dec(v___x_523_);
lean_dec(v_tk_345_);
lean_dec(v___x_339_);
lean_dec_ref(v___x_326_);
lean_dec_ref(v___x_325_);
lean_dec_ref(v___x_324_);
v___x_559_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
return v___x_559_;
}
else
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; uint8_t v___x_563_; 
v___x_560_ = l_Lean_Syntax_getArg(v___x_556_, v___x_344_);
lean_dec(v___x_556_);
v___x_561_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__11));
lean_inc_ref(v___x_326_);
lean_inc_ref(v___x_325_);
lean_inc_ref(v___x_324_);
v___x_562_ = l_Lean_Name_mkStr4(v___x_324_, v___x_325_, v___x_326_, v___x_561_);
lean_inc(v___x_560_);
v___x_563_ = l_Lean_Syntax_isOfKind(v___x_560_, v___x_562_);
lean_dec(v___x_562_);
if (v___x_563_ == 0)
{
lean_object* v___x_564_; 
lean_dec(v___x_560_);
lean_dec(v_o_546_);
lean_dec(v___x_523_);
lean_dec(v_tk_345_);
lean_dec(v___x_339_);
lean_dec_ref(v___x_326_);
lean_dec_ref(v___x_325_);
lean_dec_ref(v___x_324_);
v___x_564_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
return v___x_564_;
}
else
{
lean_object* v___x_565_; lean_object* v_args_566_; lean_object* v___x_567_; 
v___x_565_ = l_Lean_Syntax_getArg(v___x_560_, v___x_338_);
lean_dec(v___x_560_);
v_args_566_ = l_Lean_Syntax_getArgs(v___x_565_);
lean_dec(v___x_565_);
v___x_567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_567_, 0, v_args_566_);
v___y_525_ = v_o_546_;
v_args_526_ = v___x_567_;
v___y_527_ = v___y_547_;
v___y_528_ = v___y_548_;
v___y_529_ = v___y_549_;
v___y_530_ = v___y_550_;
v___y_531_ = v___y_551_;
v___y_532_ = v___y_552_;
v___y_533_ = v___y_553_;
v___y_534_ = v___y_554_;
goto v___jp_524_;
}
}
}
else
{
lean_object* v___x_568_; 
lean_dec(v___x_556_);
v___x_568_ = lean_box(0);
v___y_525_ = v_o_546_;
v_args_526_ = v___x_568_;
v___y_527_ = v___y_547_;
v___y_528_ = v___y_548_;
v___y_529_ = v___y_549_;
v___y_530_ = v___y_550_;
v___y_531_ = v___y_551_;
v___y_532_ = v___y_552_;
v___y_533_ = v___y_553_;
v___y_534_ = v___y_554_;
goto v___jp_524_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___boxed(lean_object* v___x_577_, lean_object* v_stx_578_, lean_object* v___x_579_, lean_object* v___x_580_, lean_object* v___x_581_, lean_object* v___x_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_){
_start:
{
uint8_t v___x_6188__boxed_592_; uint8_t v___x_6192__boxed_593_; lean_object* v_res_594_; 
v___x_6188__boxed_592_ = lean_unbox(v___x_577_);
v___x_6192__boxed_593_ = lean_unbox(v___x_582_);
v_res_594_ = l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1(v___x_6188__boxed_592_, v_stx_578_, v___x_579_, v___x_580_, v___x_581_, v___x_6192__boxed_593_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_);
lean_dec(v___y_590_);
lean_dec_ref(v___y_589_);
lean_dec(v___y_588_);
lean_dec_ref(v___y_587_);
lean_dec(v___y_586_);
lean_dec_ref(v___y_585_);
lean_dec(v___y_584_);
lean_dec_ref(v___y_583_);
lean_dec(v_stx_578_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace(lean_object* v_stx_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; uint8_t v___x_616_; uint8_t v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___y_620_; lean_object* v___x_621_; 
v___x_612_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__0));
v___x_613_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__1));
v___x_614_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__2));
v___x_615_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__1));
lean_inc(v_stx_602_);
v___x_616_ = l_Lean_Syntax_isOfKind(v_stx_602_, v___x_615_);
v___x_617_ = 1;
v___x_618_ = lean_box(v___x_616_);
v___x_619_ = lean_box(v___x_617_);
v___y_620_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___boxed), 15, 6);
lean_closure_set(v___y_620_, 0, v___x_618_);
lean_closure_set(v___y_620_, 1, v_stx_602_);
lean_closure_set(v___y_620_, 2, v___x_612_);
lean_closure_set(v___y_620_, 3, v___x_613_);
lean_closure_set(v___y_620_, 4, v___x_614_);
lean_closure_set(v___y_620_, 5, v___x_619_);
v___x_621_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___y_620_, v_a_603_, v_a_604_, v_a_605_, v_a_606_, v_a_607_, v_a_608_, v_a_609_, v_a_610_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___boxed(lean_object* v_stx_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_Lean_Elab_Tactic_Conv_evalSimpTrace(v_stx_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_);
lean_dec(v_a_630_);
lean_dec_ref(v_a_629_);
lean_dec(v_a_628_);
lean_dec_ref(v_a_627_);
lean_dec(v_a_626_);
lean_dec_ref(v_a_625_);
lean_dec(v_a_624_);
lean_dec_ref(v_a_623_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1(){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_641_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_642_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__1));
v___x_643_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__1));
v___x_644_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___boxed), 10, 0);
v___x_645_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_641_, v___x_642_, v___x_643_, v___x_644_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___boxed(lean_object* v_a_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1();
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg___lam__0(lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_649_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
if (lean_obj_tag(v___x_657_) == 0)
{
lean_object* v_a_658_; lean_object* v___x_659_; 
v_a_658_ = lean_ctor_get(v___x_657_, 0);
lean_inc(v_a_658_);
lean_dec_ref(v___x_657_);
v___x_659_ = l_Lean_Meta_Split_simpMatch(v_a_658_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
if (lean_obj_tag(v___x_659_) == 0)
{
lean_object* v_a_660_; lean_object* v___x_661_; 
v_a_660_ = lean_ctor_get(v___x_659_, 0);
lean_inc(v_a_660_);
lean_dec_ref(v___x_659_);
v___x_661_ = l_Lean_Elab_Tactic_Conv_applySimpResult(v_a_660_, v___y_648_, v___y_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
return v___x_661_;
}
else
{
lean_object* v_a_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_669_; 
v_a_662_ = lean_ctor_get(v___x_659_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_669_ == 0)
{
v___x_664_ = v___x_659_;
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_a_662_);
lean_dec(v___x_659_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_667_; 
if (v_isShared_665_ == 0)
{
v___x_667_ = v___x_664_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_a_662_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
}
else
{
lean_object* v_a_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_677_; 
v_a_670_ = lean_ctor_get(v___x_657_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_677_ == 0)
{
v___x_672_ = v___x_657_;
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_a_670_);
lean_dec(v___x_657_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_675_; 
if (v_isShared_673_ == 0)
{
v___x_675_ = v___x_672_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_a_670_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg___lam__0___boxed(lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg___lam__0(v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
lean_dec(v___y_685_);
lean_dec_ref(v___y_684_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg(lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_){
_start:
{
lean_object* v___f_698_; lean_object* v___x_699_; 
v___f_698_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg___closed__0));
v___x_699_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_698_, v_a_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg___boxed(lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg(v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_);
lean_dec(v_a_707_);
lean_dec_ref(v_a_706_);
lean_dec(v_a_705_);
lean_dec_ref(v_a_704_);
lean_dec(v_a_703_);
lean_dec_ref(v_a_702_);
lean_dec(v_a_701_);
lean_dec_ref(v_a_700_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch(lean_object* v_x_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_){
_start:
{
lean_object* v___x_720_; 
v___x_720_ = l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg(v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch___boxed(lean_object* v_x_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l_Lean_Elab_Tactic_Conv_evalSimpMatch(v_x_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_);
lean_dec(v_a_729_);
lean_dec_ref(v_a_728_);
lean_dec(v_a_727_);
lean_dec_ref(v_a_726_);
lean_dec(v_a_725_);
lean_dec_ref(v_a_724_);
lean_dec(v_a_723_);
lean_dec_ref(v_a_722_);
lean_dec(v_x_721_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1(){
_start:
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_747_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_748_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__1));
v___x_749_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__3));
v___x_750_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalSimpMatch___boxed), 10, 0);
v___x_751_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_747_, v___x_748_, v___x_749_, v___x_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___boxed(lean_object* v_a_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1();
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3(){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_780_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__3));
v___x_781_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__6));
v___x_782_ = l_Lean_addBuiltinDeclarationRanges(v___x_780_, v___x_781_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___boxed(lean_object* v_a_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3();
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimp___lam__0(lean_object* v_stx_787_, uint8_t v___x_788_, uint8_t v___x_789_, lean_object* v___x_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_){
_start:
{
lean_object* v___x_800_; 
v___x_800_ = l_Lean_Elab_Tactic_mkSimpContext(v_stx_787_, v___x_788_, v___x_789_, v___x_788_, v___x_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_);
if (lean_obj_tag(v___x_800_) == 0)
{
lean_object* v_a_801_; lean_object* v_ctx_802_; lean_object* v___x_803_; 
v_a_801_ = lean_ctor_get(v___x_800_, 0);
lean_inc(v_a_801_);
lean_dec_ref(v___x_800_);
v_ctx_802_ = lean_ctor_get(v_a_801_, 0);
lean_inc_ref(v_ctx_802_);
lean_dec(v_a_801_);
v___x_803_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_792_, v___y_795_, v___y_796_, v___y_797_, v___y_798_);
if (lean_obj_tag(v___x_803_) == 0)
{
lean_object* v_a_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
v_a_804_ = lean_ctor_get(v___x_803_, 0);
lean_inc(v_a_804_);
lean_dec_ref(v___x_803_);
v___x_805_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalDSimp___lam__0___closed__0));
v___x_806_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6, &l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6);
v___x_807_ = l_Lean_Meta_dsimp(v_a_804_, v_ctx_802_, v___x_805_, v___x_806_, v___y_795_, v___y_796_, v___y_797_, v___y_798_);
if (lean_obj_tag(v___x_807_) == 0)
{
lean_object* v_a_808_; lean_object* v_fst_809_; lean_object* v___x_810_; 
v_a_808_ = lean_ctor_get(v___x_807_, 0);
lean_inc(v_a_808_);
lean_dec_ref(v___x_807_);
v_fst_809_ = lean_ctor_get(v_a_808_, 0);
lean_inc(v_fst_809_);
lean_dec(v_a_808_);
v___x_810_ = l_Lean_Elab_Tactic_Conv_changeLhs(v_fst_809_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_);
return v___x_810_;
}
else
{
lean_object* v_a_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_818_; 
v_a_811_ = lean_ctor_get(v___x_807_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_818_ == 0)
{
v___x_813_ = v___x_807_;
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_a_811_);
lean_dec(v___x_807_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_816_; 
if (v_isShared_814_ == 0)
{
v___x_816_ = v___x_813_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_a_811_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
}
}
else
{
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_826_; 
lean_dec_ref(v_ctx_802_);
v_a_819_ = lean_ctor_get(v___x_803_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_826_ == 0)
{
v___x_821_ = v___x_803_;
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_803_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_824_; 
if (v_isShared_822_ == 0)
{
v___x_824_ = v___x_821_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_a_819_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
else
{
lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_834_; 
v_a_827_ = lean_ctor_get(v___x_800_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_834_ == 0)
{
v___x_829_ = v___x_800_;
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_800_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_832_; 
if (v_isShared_830_ == 0)
{
v___x_832_ = v___x_829_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_a_827_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimp___lam__0___boxed(lean_object* v_stx_835_, lean_object* v___x_836_, lean_object* v___x_837_, lean_object* v___x_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_){
_start:
{
uint8_t v___x_586__boxed_848_; uint8_t v___x_587__boxed_849_; lean_object* v_res_850_; 
v___x_586__boxed_848_ = lean_unbox(v___x_836_);
v___x_587__boxed_849_ = lean_unbox(v___x_837_);
v_res_850_ = l_Lean_Elab_Tactic_Conv_evalDSimp___lam__0(v_stx_835_, v___x_586__boxed_848_, v___x_587__boxed_849_, v___x_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v___y_844_);
lean_dec_ref(v___y_843_);
lean_dec(v___y_842_);
lean_dec_ref(v___y_841_);
lean_dec(v___y_840_);
lean_dec_ref(v___y_839_);
lean_dec(v_stx_835_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimp(lean_object* v_stx_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_){
_start:
{
uint8_t v___x_861_; uint8_t v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___f_866_; lean_object* v___x_867_; 
v___x_861_ = 0;
v___x_862_ = 2;
v___x_863_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimp___closed__0));
v___x_864_ = lean_box(v___x_861_);
v___x_865_ = lean_box(v___x_862_);
v___f_866_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalDSimp___lam__0___boxed), 13, 4);
lean_closure_set(v___f_866_, 0, v_stx_851_);
lean_closure_set(v___f_866_, 1, v___x_864_);
lean_closure_set(v___f_866_, 2, v___x_865_);
lean_closure_set(v___f_866_, 3, v___x_863_);
v___x_867_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_866_, v_a_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_, v_a_859_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimp___boxed(lean_object* v_stx_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l_Lean_Elab_Tactic_Conv_evalDSimp(v_stx_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_);
lean_dec(v_a_876_);
lean_dec_ref(v_a_875_);
lean_dec(v_a_874_);
lean_dec_ref(v_a_873_);
lean_dec(v_a_872_);
lean_dec_ref(v_a_871_);
lean_dec(v_a_870_);
lean_dec_ref(v_a_869_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1(){
_start:
{
lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_894_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_895_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__1));
v___x_896_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__3));
v___x_897_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalDSimp___boxed), 10, 0);
v___x_898_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_894_, v___x_895_, v___x_896_, v___x_897_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___boxed(lean_object* v_a_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1();
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3(){
_start:
{
lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_926_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__3));
v___x_927_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__6));
v___x_928_ = l_Lean_addBuiltinDeclarationRanges(v___x_926_, v___x_927_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___boxed(lean_object* v_a_929_){
_start:
{
lean_object* v_res_930_; 
v_res_930_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3();
return v_res_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimpTrace___lam__0(uint8_t v___x_932_, lean_object* v_stx_933_, lean_object* v___x_934_, lean_object* v___x_935_, lean_object* v___x_936_, uint8_t v___x_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_){
_start:
{
if (v___x_932_ == 0)
{
lean_object* v___x_947_; 
lean_dec_ref(v___x_936_);
lean_dec_ref(v___x_935_);
lean_dec_ref(v___x_934_);
v___x_947_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
return v___x_947_;
}
else
{
lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; uint8_t v___x_952_; 
v___x_948_ = lean_unsigned_to_nat(1u);
v___x_949_ = l_Lean_Syntax_getArg(v_stx_933_, v___x_948_);
v___x_950_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__0));
lean_inc_ref(v___x_936_);
lean_inc_ref(v___x_935_);
lean_inc_ref(v___x_934_);
v___x_951_ = l_Lean_Name_mkStr4(v___x_934_, v___x_935_, v___x_936_, v___x_950_);
lean_inc(v___x_949_);
v___x_952_ = l_Lean_Syntax_isOfKind(v___x_949_, v___x_951_);
lean_dec(v___x_951_);
if (v___x_952_ == 0)
{
lean_object* v___x_953_; 
lean_dec(v___x_949_);
lean_dec_ref(v___x_936_);
lean_dec_ref(v___x_935_);
lean_dec_ref(v___x_934_);
v___x_953_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
return v___x_953_;
}
else
{
lean_object* v___x_954_; lean_object* v_tk_955_; lean_object* v___y_957_; lean_object* v___y_958_; lean_object* v___y_959_; lean_object* v___y_960_; lean_object* v___y_961_; lean_object* v___y_962_; lean_object* v___y_963_; lean_object* v___y_964_; lean_object* v___y_965_; lean_object* v___y_966_; lean_object* v___y_967_; lean_object* v___y_968_; lean_object* v___y_969_; uint8_t v___y_970_; lean_object* v___y_971_; lean_object* v___y_972_; lean_object* v___y_973_; lean_object* v___y_974_; lean_object* v___y_1050_; lean_object* v___y_1051_; lean_object* v___y_1052_; lean_object* v___y_1053_; lean_object* v___y_1054_; lean_object* v___y_1055_; lean_object* v___y_1056_; lean_object* v___y_1057_; lean_object* v___y_1058_; lean_object* v___y_1059_; lean_object* v___y_1060_; lean_object* v___y_1061_; lean_object* v___y_1062_; uint8_t v___y_1063_; lean_object* v___y_1064_; lean_object* v___y_1065_; lean_object* v___y_1066_; lean_object* v___y_1067_; lean_object* v___y_1080_; lean_object* v_args_1081_; lean_object* v___y_1082_; lean_object* v___y_1083_; lean_object* v___y_1084_; lean_object* v___y_1085_; lean_object* v___y_1086_; lean_object* v___y_1087_; lean_object* v___y_1088_; lean_object* v___y_1089_; lean_object* v_o_1107_; lean_object* v___y_1108_; lean_object* v___y_1109_; lean_object* v___y_1110_; lean_object* v___y_1111_; lean_object* v___y_1112_; lean_object* v___y_1113_; lean_object* v___y_1114_; lean_object* v___y_1115_; lean_object* v___x_1130_; lean_object* v___x_1131_; uint8_t v___x_1132_; 
v___x_954_ = lean_unsigned_to_nat(0u);
v_tk_955_ = l_Lean_Syntax_getArg(v_stx_933_, v___x_954_);
v___x_1130_ = lean_unsigned_to_nat(2u);
v___x_1131_ = l_Lean_Syntax_getArg(v_stx_933_, v___x_1130_);
v___x_1132_ = l_Lean_Syntax_isNone(v___x_1131_);
if (v___x_1132_ == 0)
{
uint8_t v___x_1133_; 
lean_inc(v___x_1131_);
v___x_1133_ = l_Lean_Syntax_matchesNull(v___x_1131_, v___x_948_);
if (v___x_1133_ == 0)
{
lean_object* v___x_1134_; 
lean_dec(v___x_1131_);
lean_dec(v_tk_955_);
lean_dec(v___x_949_);
lean_dec_ref(v___x_936_);
lean_dec_ref(v___x_935_);
lean_dec_ref(v___x_934_);
v___x_1134_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
return v___x_1134_;
}
else
{
lean_object* v_o_1135_; lean_object* v___x_1136_; 
v_o_1135_ = l_Lean_Syntax_getArg(v___x_1131_, v___x_954_);
lean_dec(v___x_1131_);
v___x_1136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1136_, 0, v_o_1135_);
v_o_1107_ = v___x_1136_;
v___y_1108_ = v___y_938_;
v___y_1109_ = v___y_939_;
v___y_1110_ = v___y_940_;
v___y_1111_ = v___y_941_;
v___y_1112_ = v___y_942_;
v___y_1113_ = v___y_943_;
v___y_1114_ = v___y_944_;
v___y_1115_ = v___y_945_;
goto v___jp_1106_;
}
}
else
{
lean_object* v___x_1137_; 
lean_dec(v___x_1131_);
v___x_1137_ = lean_box(0);
v_o_1107_ = v___x_1137_;
v___y_1108_ = v___y_938_;
v___y_1109_ = v___y_939_;
v___y_1110_ = v___y_940_;
v___y_1111_ = v___y_941_;
v___y_1112_ = v___y_942_;
v___y_1113_ = v___y_943_;
v___y_1114_ = v___y_944_;
v___y_1115_ = v___y_945_;
goto v___jp_1106_;
}
v___jp_956_:
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; uint8_t v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
lean_inc_ref(v___y_966_);
v___x_975_ = l_Array_append___redArg(v___y_966_, v___y_974_);
lean_dec_ref(v___y_974_);
lean_inc(v___y_967_);
lean_inc(v___y_973_);
v___x_976_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_976_, 0, v___y_973_);
lean_ctor_set(v___x_976_, 1, v___y_967_);
lean_ctor_set(v___x_976_, 2, v___x_975_);
lean_inc(v___y_971_);
v___x_977_ = l_Lean_Syntax_node6(v___y_973_, v___y_969_, v___y_963_, v___x_949_, v___y_971_, v___y_959_, v___x_976_, v___y_971_);
v___x_978_ = 2;
v___x_979_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimp___closed__0));
v___x_980_ = l_Lean_Elab_Tactic_mkSimpContext(v___x_977_, v___y_970_, v___x_978_, v___y_970_, v___x_979_, v___y_972_, v___y_958_, v___y_960_, v___y_961_, v___y_964_, v___y_965_, v___y_962_, v___y_957_);
if (lean_obj_tag(v___x_980_) == 0)
{
lean_object* v_a_981_; lean_object* v_ctx_982_; lean_object* v___x_983_; 
v_a_981_ = lean_ctor_get(v___x_980_, 0);
lean_inc(v_a_981_);
lean_dec_ref(v___x_980_);
v_ctx_982_ = lean_ctor_get(v_a_981_, 0);
lean_inc_ref(v_ctx_982_);
lean_dec(v_a_981_);
v___x_983_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_958_, v___y_964_, v___y_965_, v___y_962_, v___y_957_);
if (lean_obj_tag(v___x_983_) == 0)
{
lean_object* v_a_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
v_a_984_ = lean_ctor_get(v___x_983_, 0);
lean_inc(v_a_984_);
lean_dec_ref(v___x_983_);
v___x_985_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalDSimp___lam__0___closed__0));
v___x_986_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6, &l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6);
v___x_987_ = l_Lean_Meta_dsimp(v_a_984_, v_ctx_982_, v___x_985_, v___x_986_, v___y_964_, v___y_965_, v___y_962_, v___y_957_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v_a_988_; lean_object* v_fst_989_; lean_object* v_snd_990_; lean_object* v___x_991_; 
v_a_988_ = lean_ctor_get(v___x_987_, 0);
lean_inc(v_a_988_);
lean_dec_ref(v___x_987_);
v_fst_989_ = lean_ctor_get(v_a_988_, 0);
lean_inc(v_fst_989_);
v_snd_990_ = lean_ctor_get(v_a_988_, 1);
lean_inc(v_snd_990_);
lean_dec(v_a_988_);
v___x_991_ = l_Lean_Elab_Tactic_Conv_changeLhs(v_fst_989_, v___y_972_, v___y_958_, v___y_960_, v___y_961_, v___y_964_, v___y_965_, v___y_962_, v___y_957_);
if (lean_obj_tag(v___x_991_) == 0)
{
lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_1023_; 
v_isSharedCheck_1023_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_1023_ == 0)
{
lean_object* v_unused_1024_; 
v_unused_1024_ = lean_ctor_get(v___x_991_, 0);
lean_dec(v_unused_1024_);
v___x_993_ = v___x_991_;
v_isShared_994_ = v_isSharedCheck_1023_;
goto v_resetjp_992_;
}
else
{
lean_dec(v___x_991_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_1023_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v_usedTheorems_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1021_; 
v_usedTheorems_995_ = lean_ctor_get(v_snd_990_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v_snd_990_);
if (v_isSharedCheck_1021_ == 0)
{
lean_object* v_unused_1022_; 
v_unused_1022_ = lean_ctor_get(v_snd_990_, 1);
lean_dec(v_unused_1022_);
v___x_997_ = v_snd_990_;
v_isShared_998_ = v_isSharedCheck_1021_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_usedTheorems_995_);
lean_dec(v_snd_990_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1021_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_999_; 
v___x_999_ = l_Lean_Elab_Tactic_mkSimpCallStx(v___x_977_, v_usedTheorems_995_, v___y_964_, v___y_965_, v___y_962_, v___y_957_);
lean_dec_ref(v_usedTheorems_995_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v_a_1000_; lean_object* v___x_1001_; lean_object* v___x_1003_; 
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
lean_inc(v_a_1000_);
lean_dec_ref(v___x_999_);
v___x_1001_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__2));
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 1, v_a_1000_);
lean_ctor_set(v___x_997_, 0, v___x_1001_);
v___x_1003_ = v___x_997_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v___x_1001_);
lean_ctor_set(v_reuseFailAlloc_1012_, 1, v_a_1000_);
v___x_1003_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1007_; 
v___x_1004_ = lean_box(0);
v___x_1005_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1003_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
lean_ctor_set(v___x_1005_, 2, v___x_1004_);
lean_ctor_set(v___x_1005_, 3, v___x_1004_);
lean_ctor_set(v___x_1005_, 4, v___x_1004_);
lean_ctor_set(v___x_1005_, 5, v___x_1004_);
lean_inc(v___y_968_);
if (v_isShared_994_ == 0)
{
lean_ctor_set_tag(v___x_993_, 1);
lean_ctor_set(v___x_993_, 0, v___y_968_);
v___x_1007_ = v___x_993_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v___y_968_);
v___x_1007_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
lean_object* v___x_1008_; uint8_t v___x_1009_; lean_object* v___x_1010_; 
v___x_1008_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__3));
v___x_1009_ = 4;
v___x_1010_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_955_, v___x_1005_, v___x_1007_, v___x_1008_, v___x_1004_, v___x_1009_, v___y_962_, v___y_957_);
return v___x_1010_;
}
}
}
else
{
lean_object* v_a_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1020_; 
lean_del_object(v___x_997_);
lean_del_object(v___x_993_);
lean_dec(v_tk_955_);
v_a_1013_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1015_ = v___x_999_;
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_a_1013_);
lean_dec(v___x_999_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1018_; 
if (v_isShared_1016_ == 0)
{
v___x_1018_ = v___x_1015_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_a_1013_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
}
}
}
else
{
lean_dec(v_snd_990_);
lean_dec(v___x_977_);
lean_dec(v_tk_955_);
return v___x_991_;
}
}
else
{
lean_object* v_a_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1032_; 
lean_dec(v___x_977_);
lean_dec(v_tk_955_);
v_a_1025_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_1032_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_1027_ = v___x_987_;
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_a_1025_);
lean_dec(v___x_987_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1030_; 
if (v_isShared_1028_ == 0)
{
v___x_1030_ = v___x_1027_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_a_1025_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
return v___x_1030_;
}
}
}
}
else
{
lean_object* v_a_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1040_; 
lean_dec_ref(v_ctx_982_);
lean_dec(v___x_977_);
lean_dec(v_tk_955_);
v_a_1033_ = lean_ctor_get(v___x_983_, 0);
v_isSharedCheck_1040_ = !lean_is_exclusive(v___x_983_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1035_ = v___x_983_;
v_isShared_1036_ = v_isSharedCheck_1040_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_a_1033_);
lean_dec(v___x_983_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1040_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v___x_1038_; 
if (v_isShared_1036_ == 0)
{
v___x_1038_ = v___x_1035_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_a_1033_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
}
}
else
{
lean_object* v_a_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1048_; 
lean_dec(v___x_977_);
lean_dec(v_tk_955_);
v_a_1041_ = lean_ctor_get(v___x_980_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1043_ = v___x_980_;
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_a_1041_);
lean_dec(v___x_980_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1046_; 
if (v_isShared_1044_ == 0)
{
v___x_1046_ = v___x_1043_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_a_1041_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
}
}
v___jp_1049_:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; 
lean_inc_ref(v___y_1058_);
v___x_1068_ = l_Array_append___redArg(v___y_1058_, v___y_1067_);
lean_dec_ref(v___y_1067_);
lean_inc(v___y_1060_);
lean_inc(v___y_1066_);
v___x_1069_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1069_, 0, v___y_1066_);
lean_ctor_set(v___x_1069_, 1, v___y_1060_);
lean_ctor_set(v___x_1069_, 2, v___x_1068_);
if (lean_obj_tag(v___y_1059_) == 1)
{
lean_object* v_val_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; 
v_val_1070_ = lean_ctor_get(v___y_1059_, 0);
lean_inc(v_val_1070_);
lean_dec_ref(v___y_1059_);
v___x_1071_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__4));
lean_inc_n(v___y_1066_, 3);
v___x_1072_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___y_1066_);
lean_ctor_set(v___x_1072_, 1, v___x_1071_);
lean_inc_ref(v___y_1058_);
v___x_1073_ = l_Array_append___redArg(v___y_1058_, v_val_1070_);
lean_dec(v_val_1070_);
lean_inc(v___y_1060_);
v___x_1074_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1074_, 0, v___y_1066_);
lean_ctor_set(v___x_1074_, 1, v___y_1060_);
lean_ctor_set(v___x_1074_, 2, v___x_1073_);
v___x_1075_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__5));
v___x_1076_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1076_, 0, v___y_1066_);
lean_ctor_set(v___x_1076_, 1, v___x_1075_);
v___x_1077_ = l_Array_mkArray3___redArg(v___x_1072_, v___x_1074_, v___x_1076_);
v___y_957_ = v___y_1050_;
v___y_958_ = v___y_1051_;
v___y_959_ = v___x_1069_;
v___y_960_ = v___y_1052_;
v___y_961_ = v___y_1053_;
v___y_962_ = v___y_1054_;
v___y_963_ = v___y_1055_;
v___y_964_ = v___y_1056_;
v___y_965_ = v___y_1057_;
v___y_966_ = v___y_1058_;
v___y_967_ = v___y_1060_;
v___y_968_ = v___y_1061_;
v___y_969_ = v___y_1062_;
v___y_970_ = v___y_1063_;
v___y_971_ = v___y_1065_;
v___y_972_ = v___y_1064_;
v___y_973_ = v___y_1066_;
v___y_974_ = v___x_1077_;
goto v___jp_956_;
}
else
{
lean_object* v___x_1078_; 
lean_dec(v___y_1059_);
v___x_1078_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__6));
v___y_957_ = v___y_1050_;
v___y_958_ = v___y_1051_;
v___y_959_ = v___x_1069_;
v___y_960_ = v___y_1052_;
v___y_961_ = v___y_1053_;
v___y_962_ = v___y_1054_;
v___y_963_ = v___y_1055_;
v___y_964_ = v___y_1056_;
v___y_965_ = v___y_1057_;
v___y_966_ = v___y_1058_;
v___y_967_ = v___y_1060_;
v___y_968_ = v___y_1061_;
v___y_969_ = v___y_1062_;
v___y_970_ = v___y_1063_;
v___y_971_ = v___y_1065_;
v___y_972_ = v___y_1064_;
v___y_973_ = v___y_1066_;
v___y_974_ = v___x_1078_;
goto v___jp_956_;
}
}
v___jp_1079_:
{
lean_object* v_ref_1090_; uint8_t v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
v_ref_1090_ = lean_ctor_get(v___y_1088_, 5);
v___x_1091_ = 0;
v___x_1092_ = l_Lean_SourceInfo_fromRef(v_ref_1090_, v___x_1091_);
v___x_1093_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__0));
v___x_1094_ = l_Lean_Name_mkStr4(v___x_934_, v___x_935_, v___x_936_, v___x_1093_);
v___x_1095_ = l_Lean_SourceInfo_fromRef(v_tk_955_, v___x_937_);
v___x_1096_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1095_);
lean_ctor_set(v___x_1096_, 1, v___x_1093_);
v___x_1097_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__9));
v___x_1098_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__10, &l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__10_once, _init_l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__10);
lean_inc(v___x_1092_);
v___x_1099_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1092_);
lean_ctor_set(v___x_1099_, 1, v___x_1097_);
lean_ctor_set(v___x_1099_, 2, v___x_1098_);
if (lean_obj_tag(v___y_1080_) == 1)
{
lean_object* v_val_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
v_val_1100_ = lean_ctor_get(v___y_1080_, 0);
lean_inc(v_val_1100_);
lean_dec_ref(v___y_1080_);
v___x_1101_ = l_Lean_SourceInfo_fromRef(v_val_1100_, v___x_937_);
lean_dec(v_val_1100_);
v___x_1102_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__7));
v___x_1103_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1101_);
lean_ctor_set(v___x_1103_, 1, v___x_1102_);
v___x_1104_ = l_Array_mkArray1___redArg(v___x_1103_);
v___y_1050_ = v___y_1089_;
v___y_1051_ = v___y_1083_;
v___y_1052_ = v___y_1084_;
v___y_1053_ = v___y_1085_;
v___y_1054_ = v___y_1088_;
v___y_1055_ = v___x_1096_;
v___y_1056_ = v___y_1086_;
v___y_1057_ = v___y_1087_;
v___y_1058_ = v___x_1098_;
v___y_1059_ = v_args_1081_;
v___y_1060_ = v___x_1097_;
v___y_1061_ = v_ref_1090_;
v___y_1062_ = v___x_1094_;
v___y_1063_ = v___x_1091_;
v___y_1064_ = v___y_1082_;
v___y_1065_ = v___x_1099_;
v___y_1066_ = v___x_1092_;
v___y_1067_ = v___x_1104_;
goto v___jp_1049_;
}
else
{
lean_object* v___x_1105_; 
lean_dec(v___y_1080_);
v___x_1105_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__6));
v___y_1050_ = v___y_1089_;
v___y_1051_ = v___y_1083_;
v___y_1052_ = v___y_1084_;
v___y_1053_ = v___y_1085_;
v___y_1054_ = v___y_1088_;
v___y_1055_ = v___x_1096_;
v___y_1056_ = v___y_1086_;
v___y_1057_ = v___y_1087_;
v___y_1058_ = v___x_1098_;
v___y_1059_ = v_args_1081_;
v___y_1060_ = v___x_1097_;
v___y_1061_ = v_ref_1090_;
v___y_1062_ = v___x_1094_;
v___y_1063_ = v___x_1091_;
v___y_1064_ = v___y_1082_;
v___y_1065_ = v___x_1099_;
v___y_1066_ = v___x_1092_;
v___y_1067_ = v___x_1105_;
goto v___jp_1049_;
}
}
v___jp_1106_:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; uint8_t v___x_1118_; 
v___x_1116_ = lean_unsigned_to_nat(3u);
v___x_1117_ = l_Lean_Syntax_getArg(v_stx_933_, v___x_1116_);
v___x_1118_ = l_Lean_Syntax_isNone(v___x_1117_);
if (v___x_1118_ == 0)
{
uint8_t v___x_1119_; 
lean_inc(v___x_1117_);
v___x_1119_ = l_Lean_Syntax_matchesNull(v___x_1117_, v___x_948_);
if (v___x_1119_ == 0)
{
lean_object* v___x_1120_; 
lean_dec(v___x_1117_);
lean_dec(v_o_1107_);
lean_dec(v_tk_955_);
lean_dec(v___x_949_);
lean_dec_ref(v___x_936_);
lean_dec_ref(v___x_935_);
lean_dec_ref(v___x_934_);
v___x_1120_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
return v___x_1120_;
}
else
{
lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; uint8_t v___x_1124_; 
v___x_1121_ = l_Lean_Syntax_getArg(v___x_1117_, v___x_954_);
lean_dec(v___x_1117_);
v___x_1122_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalDSimpTrace___lam__0___closed__0));
lean_inc_ref(v___x_936_);
lean_inc_ref(v___x_935_);
lean_inc_ref(v___x_934_);
v___x_1123_ = l_Lean_Name_mkStr4(v___x_934_, v___x_935_, v___x_936_, v___x_1122_);
lean_inc(v___x_1121_);
v___x_1124_ = l_Lean_Syntax_isOfKind(v___x_1121_, v___x_1123_);
lean_dec(v___x_1123_);
if (v___x_1124_ == 0)
{
lean_object* v___x_1125_; 
lean_dec(v___x_1121_);
lean_dec(v_o_1107_);
lean_dec(v_tk_955_);
lean_dec(v___x_949_);
lean_dec_ref(v___x_936_);
lean_dec_ref(v___x_935_);
lean_dec_ref(v___x_934_);
v___x_1125_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
return v___x_1125_;
}
else
{
lean_object* v___x_1126_; lean_object* v_args_1127_; lean_object* v___x_1128_; 
v___x_1126_ = l_Lean_Syntax_getArg(v___x_1121_, v___x_948_);
lean_dec(v___x_1121_);
v_args_1127_ = l_Lean_Syntax_getArgs(v___x_1126_);
lean_dec(v___x_1126_);
v___x_1128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1128_, 0, v_args_1127_);
v___y_1080_ = v_o_1107_;
v_args_1081_ = v___x_1128_;
v___y_1082_ = v___y_1108_;
v___y_1083_ = v___y_1109_;
v___y_1084_ = v___y_1110_;
v___y_1085_ = v___y_1111_;
v___y_1086_ = v___y_1112_;
v___y_1087_ = v___y_1113_;
v___y_1088_ = v___y_1114_;
v___y_1089_ = v___y_1115_;
goto v___jp_1079_;
}
}
}
else
{
lean_object* v___x_1129_; 
lean_dec(v___x_1117_);
v___x_1129_ = lean_box(0);
v___y_1080_ = v_o_1107_;
v_args_1081_ = v___x_1129_;
v___y_1082_ = v___y_1108_;
v___y_1083_ = v___y_1109_;
v___y_1084_ = v___y_1110_;
v___y_1085_ = v___y_1111_;
v___y_1086_ = v___y_1112_;
v___y_1087_ = v___y_1113_;
v___y_1088_ = v___y_1114_;
v___y_1089_ = v___y_1115_;
goto v___jp_1079_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimpTrace___lam__0___boxed(lean_object* v___x_1138_, lean_object* v_stx_1139_, lean_object* v___x_1140_, lean_object* v___x_1141_, lean_object* v___x_1142_, lean_object* v___x_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_){
_start:
{
uint8_t v___x_5472__boxed_1153_; uint8_t v___x_5476__boxed_1154_; lean_object* v_res_1155_; 
v___x_5472__boxed_1153_ = lean_unbox(v___x_1138_);
v___x_5476__boxed_1154_ = lean_unbox(v___x_1143_);
v_res_1155_ = l_Lean_Elab_Tactic_Conv_evalDSimpTrace___lam__0(v___x_5472__boxed_1153_, v_stx_1139_, v___x_1140_, v___x_1141_, v___x_1142_, v___x_5476__boxed_1154_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_);
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
lean_dec(v___y_1145_);
lean_dec_ref(v___y_1144_);
lean_dec(v_stx_1139_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimpTrace(lean_object* v_stx_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_){
_start:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; uint8_t v___x_1177_; uint8_t v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___y_1181_; lean_object* v___x_1182_; 
v___x_1173_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__0));
v___x_1174_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__1));
v___x_1175_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__2));
v___x_1176_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__1));
lean_inc(v_stx_1163_);
v___x_1177_ = l_Lean_Syntax_isOfKind(v_stx_1163_, v___x_1176_);
v___x_1178_ = 1;
v___x_1179_ = lean_box(v___x_1177_);
v___x_1180_ = lean_box(v___x_1178_);
v___y_1181_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalDSimpTrace___lam__0___boxed), 15, 6);
lean_closure_set(v___y_1181_, 0, v___x_1179_);
lean_closure_set(v___y_1181_, 1, v_stx_1163_);
lean_closure_set(v___y_1181_, 2, v___x_1173_);
lean_closure_set(v___y_1181_, 3, v___x_1174_);
lean_closure_set(v___y_1181_, 4, v___x_1175_);
lean_closure_set(v___y_1181_, 5, v___x_1180_);
v___x_1182_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___y_1181_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_, v_a_1170_, v_a_1171_);
return v___x_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimpTrace___boxed(lean_object* v_stx_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_){
_start:
{
lean_object* v_res_1193_; 
v_res_1193_ = l_Lean_Elab_Tactic_Conv_evalDSimpTrace(v_stx_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_);
lean_dec(v_a_1191_);
lean_dec_ref(v_a_1190_);
lean_dec(v_a_1189_);
lean_dec_ref(v_a_1188_);
lean_dec(v_a_1187_);
lean_dec_ref(v_a_1186_);
lean_dec(v_a_1185_);
lean_dec_ref(v_a_1184_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1(){
_start:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1202_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1203_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__1));
v___x_1204_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__1));
v___x_1205_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalDSimpTrace___boxed), 10, 0);
v___x_1206_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1202_, v___x_1203_, v___x_1204_, v___x_1205_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___boxed(lean_object* v_a_1207_){
_start:
{
lean_object* v_res_1208_; 
v_res_1208_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1();
return v_res_1208_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Split(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Conv_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_SimpTrace(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Conv_Simp(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
