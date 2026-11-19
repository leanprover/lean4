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
lean_object* l_Lean_Meta_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_37_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___lam__0(lean_object* v_a_58_, lean_object* v_ctx_59_, lean_object* v_simprocs_60_, uint8_t v___x_61_, lean_object* v_d_x3f_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_72_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6, &l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6);
v___x_73_ = l_Lean_Meta_simp(v_a_58_, v_ctx_59_, v_simprocs_60_, v_d_x3f_62_, v___x_72_, v___x_61_, v___y_67_, v___y_68_, v___y_69_, v___y_70_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___boxed(lean_object* v_a_74_, lean_object* v_ctx_75_, lean_object* v_simprocs_76_, lean_object* v___x_77_, lean_object* v_d_x3f_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_){
_start:
{
uint8_t v___x_702__boxed_88_; lean_object* v_res_89_; 
v___x_702__boxed_88_ = lean_unbox(v___x_77_);
v_res_89_ = l_Lean_Elab_Tactic_Conv_evalSimp___lam__0(v_a_74_, v_ctx_75_, v_simprocs_76_, v___x_702__boxed_88_, v_d_x3f_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_);
lean_dec(v___y_86_);
lean_dec_ref(v___y_85_);
lean_dec(v___y_84_);
lean_dec_ref(v___y_83_);
lean_dec(v___y_82_);
lean_dec_ref(v___y_81_);
lean_dec(v___y_80_);
lean_dec_ref(v___y_79_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___lam__1(lean_object* v_stx_90_, uint8_t v___x_91_, uint8_t v___x_92_, lean_object* v___x_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = l_Lean_Elab_Tactic_mkSimpContext(v_stx_90_, v___x_91_, v___x_92_, v___x_91_, v___x_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_, v___y_101_);
if (lean_obj_tag(v___x_103_) == 0)
{
lean_object* v_a_104_; lean_object* v_ctx_105_; lean_object* v_simprocs_106_; lean_object* v_dischargeWrapper_107_; lean_object* v___x_108_; 
v_a_104_ = lean_ctor_get(v___x_103_, 0);
lean_inc(v_a_104_);
lean_dec_ref_known(v___x_103_, 1);
v_ctx_105_ = lean_ctor_get(v_a_104_, 0);
lean_inc_ref(v_ctx_105_);
v_simprocs_106_ = lean_ctor_get(v_a_104_, 1);
lean_inc_ref(v_simprocs_106_);
v_dischargeWrapper_107_ = lean_ctor_get(v_a_104_, 2);
lean_inc(v_dischargeWrapper_107_);
lean_dec(v_a_104_);
v___x_108_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_95_, v___y_98_, v___y_99_, v___y_100_, v___y_101_);
if (lean_obj_tag(v___x_108_) == 0)
{
lean_object* v_a_109_; lean_object* v___x_110_; lean_object* v___f_111_; lean_object* v___x_112_; 
v_a_109_ = lean_ctor_get(v___x_108_, 0);
lean_inc(v_a_109_);
lean_dec_ref_known(v___x_108_, 1);
v___x_110_ = lean_box(v___x_91_);
v___f_111_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___boxed), 14, 4);
lean_closure_set(v___f_111_, 0, v_a_109_);
lean_closure_set(v___f_111_, 1, v_ctx_105_);
lean_closure_set(v___f_111_, 2, v_simprocs_106_);
lean_closure_set(v___f_111_, 3, v___x_110_);
v___x_112_ = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(v_dischargeWrapper_107_, v___f_111_, v___y_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_, v___y_101_);
lean_dec(v_dischargeWrapper_107_);
if (lean_obj_tag(v___x_112_) == 0)
{
lean_object* v_a_113_; lean_object* v_fst_114_; lean_object* v___x_115_; 
v_a_113_ = lean_ctor_get(v___x_112_, 0);
lean_inc(v_a_113_);
lean_dec_ref_known(v___x_112_, 1);
v_fst_114_ = lean_ctor_get(v_a_113_, 0);
lean_inc(v_fst_114_);
lean_dec(v_a_113_);
v___x_115_ = l_Lean_Elab_Tactic_Conv_applySimpResult(v_fst_114_, v___y_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_, v___y_101_);
return v___x_115_;
}
else
{
lean_object* v_a_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_123_; 
v_a_116_ = lean_ctor_get(v___x_112_, 0);
v_isSharedCheck_123_ = !lean_is_exclusive(v___x_112_);
if (v_isSharedCheck_123_ == 0)
{
v___x_118_ = v___x_112_;
v_isShared_119_ = v_isSharedCheck_123_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_a_116_);
lean_dec(v___x_112_);
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
lean_ctor_set(v_reuseFailAlloc_122_, 0, v_a_116_);
v___x_121_ = v_reuseFailAlloc_122_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
return v___x_121_;
}
}
}
}
else
{
lean_object* v_a_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_131_; 
lean_dec(v_dischargeWrapper_107_);
lean_dec_ref(v_simprocs_106_);
lean_dec_ref(v_ctx_105_);
v_a_124_ = lean_ctor_get(v___x_108_, 0);
v_isSharedCheck_131_ = !lean_is_exclusive(v___x_108_);
if (v_isSharedCheck_131_ == 0)
{
v___x_126_ = v___x_108_;
v_isShared_127_ = v_isSharedCheck_131_;
goto v_resetjp_125_;
}
else
{
lean_inc(v_a_124_);
lean_dec(v___x_108_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_131_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v___x_129_; 
if (v_isShared_127_ == 0)
{
v___x_129_ = v___x_126_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v_a_124_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
}
}
else
{
lean_object* v_a_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_139_; 
v_a_132_ = lean_ctor_get(v___x_103_, 0);
v_isSharedCheck_139_ = !lean_is_exclusive(v___x_103_);
if (v_isSharedCheck_139_ == 0)
{
v___x_134_ = v___x_103_;
v_isShared_135_ = v_isSharedCheck_139_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_a_132_);
lean_dec(v___x_103_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_139_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
lean_object* v___x_137_; 
if (v_isShared_135_ == 0)
{
v___x_137_ = v___x_134_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v_a_132_);
v___x_137_ = v_reuseFailAlloc_138_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
return v___x_137_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimp___lam__1___boxed(lean_object* v_stx_140_, lean_object* v___x_141_, lean_object* v___x_142_, lean_object* v___x_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_){
_start:
{
uint8_t v___x_763__boxed_153_; uint8_t v___x_764__boxed_154_; lean_object* v_res_155_; 
v___x_763__boxed_153_ = lean_unbox(v___x_141_);
v___x_764__boxed_154_ = lean_unbox(v___x_142_);
v_res_155_ = l_Lean_Elab_Tactic_Conv_evalSimp___lam__1(v_stx_140_, v___x_763__boxed_153_, v___x_764__boxed_154_, v___x_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_);
lean_dec(v___y_151_);
lean_dec_ref(v___y_150_);
lean_dec(v___y_149_);
lean_dec_ref(v___y_148_);
lean_dec(v___y_147_);
lean_dec_ref(v___y_146_);
lean_dec(v___y_145_);
lean_dec_ref(v___y_144_);
lean_dec(v_stx_140_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimp(lean_object* v_stx_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_){
_start:
{
uint8_t v___x_167_; uint8_t v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___f_172_; lean_object* v___x_173_; 
v___x_167_ = 0;
v___x_168_ = 0;
v___x_169_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimp___closed__0));
v___x_170_ = lean_box(v___x_167_);
v___x_171_ = lean_box(v___x_168_);
v___f_172_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalSimp___lam__1___boxed), 13, 4);
lean_closure_set(v___f_172_, 0, v_stx_157_);
lean_closure_set(v___f_172_, 1, v___x_170_);
lean_closure_set(v___f_172_, 2, v___x_171_);
lean_closure_set(v___f_172_, 3, v___x_169_);
v___x_173_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_172_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_, v_a_164_, v_a_165_);
return v___x_173_;
}
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1(){
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___boxed(lean_object* v_a_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1();
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3(){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_237_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__8));
v___x_238_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__6));
v___x_239_ = l_Lean_addBuiltinDeclarationRanges(v___x_237_, v___x_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___boxed(lean_object* v_a_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3();
return v_res_241_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_242_ = lean_box(0);
v___x_243_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_244_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_244_, 0, v___x_243_);
lean_ctor_set(v___x_244_, 1, v___x_242_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg(){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_246_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg___closed__0);
v___x_247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg___boxed(lean_object* v___y_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0(lean_object* v_00_u03b1_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_){
_start:
{
lean_object* v___x_260_; 
v___x_260_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___boxed(lean_object* v_00_u03b1_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0(v_00_u03b1_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_);
lean_dec(v___y_269_);
lean_dec_ref(v___y_268_);
lean_dec(v___y_267_);
lean_dec_ref(v___y_266_);
lean_dec(v___y_265_);
lean_dec_ref(v___y_264_);
lean_dec(v___y_263_);
lean_dec_ref(v___y_262_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__0(lean_object* v___x_272_, lean_object* v_a_273_, lean_object* v_ctx_274_, lean_object* v_simprocs_275_, uint8_t v___x_276_, lean_object* v_d_x3f_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; size_t v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_287_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__1, &l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__1);
lean_inc_n(v___x_272_, 2);
v___x_288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_287_);
lean_ctor_set(v___x_288_, 1, v___x_272_);
v___x_289_ = lean_unsigned_to_nat(32u);
v___x_290_ = lean_mk_empty_array_with_capacity(v___x_289_);
v___x_291_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__3, &l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__3);
v___x_292_ = ((size_t)5ULL);
v___x_293_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_293_, 0, v___x_291_);
lean_ctor_set(v___x_293_, 1, v___x_290_);
lean_ctor_set(v___x_293_, 2, v___x_272_);
lean_ctor_set(v___x_293_, 3, v___x_272_);
lean_ctor_set_usize(v___x_293_, 4, v___x_292_);
v___x_294_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_294_, 0, v___x_287_);
lean_ctor_set(v___x_294_, 1, v___x_287_);
lean_ctor_set(v___x_294_, 2, v___x_287_);
lean_ctor_set(v___x_294_, 3, v___x_293_);
v___x_295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_295_, 0, v___x_288_);
lean_ctor_set(v___x_295_, 1, v___x_294_);
v___x_296_ = l_Lean_Meta_simp(v_a_273_, v_ctx_274_, v_simprocs_275_, v_d_x3f_277_, v___x_295_, v___x_276_, v___y_282_, v___y_283_, v___y_284_, v___y_285_);
lean_dec_ref_known(v___x_295_, 2);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__0___boxed(lean_object* v___x_297_, lean_object* v_a_298_, lean_object* v_ctx_299_, lean_object* v_simprocs_300_, lean_object* v___x_301_, lean_object* v_d_x3f_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_){
_start:
{
uint8_t v___x_5406__boxed_312_; lean_object* v_res_313_; 
v___x_5406__boxed_312_ = lean_unbox(v___x_301_);
v_res_313_ = l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__0(v___x_297_, v_a_298_, v_ctx_299_, v_simprocs_300_, v___x_5406__boxed_312_, v_d_x3f_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_);
lean_dec(v___y_310_);
lean_dec_ref(v___y_309_);
lean_dec(v___y_308_);
lean_dec_ref(v___y_307_);
lean_dec(v___y_306_);
lean_dec_ref(v___y_305_);
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
return v_res_313_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__10(void){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = l_Array_mkArray0___redArg();
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1(uint8_t v___x_329_, lean_object* v_stx_330_, lean_object* v___x_331_, lean_object* v___x_332_, lean_object* v___x_333_, uint8_t v___x_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_){
_start:
{
if (v___x_329_ == 0)
{
lean_object* v___x_344_; 
lean_dec_ref(v___x_333_);
lean_dec_ref(v___x_332_);
lean_dec_ref(v___x_331_);
v___x_344_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
return v___x_344_;
}
else
{
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; uint8_t v___x_349_; 
v___x_345_ = lean_unsigned_to_nat(1u);
v___x_346_ = l_Lean_Syntax_getArg(v_stx_330_, v___x_345_);
v___x_347_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__0));
lean_inc_ref(v___x_333_);
lean_inc_ref(v___x_332_);
lean_inc_ref(v___x_331_);
v___x_348_ = l_Lean_Name_mkStr4(v___x_331_, v___x_332_, v___x_333_, v___x_347_);
lean_inc(v___x_346_);
v___x_349_ = l_Lean_Syntax_isOfKind(v___x_346_, v___x_348_);
lean_dec(v___x_348_);
if (v___x_349_ == 0)
{
lean_object* v___x_350_; 
lean_dec(v___x_346_);
lean_dec_ref(v___x_333_);
lean_dec_ref(v___x_332_);
lean_dec_ref(v___x_331_);
v___x_350_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
return v___x_350_;
}
else
{
lean_object* v___x_351_; lean_object* v_tk_352_; uint8_t v___y_354_; lean_object* v___y_355_; lean_object* v___y_356_; lean_object* v___y_357_; uint8_t v___y_358_; lean_object* v___y_359_; lean_object* v___y_360_; lean_object* v___y_361_; lean_object* v___y_362_; lean_object* v___y_363_; lean_object* v___y_364_; lean_object* v___y_365_; lean_object* v___y_366_; lean_object* v___y_367_; lean_object* v___y_368_; lean_object* v___y_369_; lean_object* v___y_370_; lean_object* v___y_371_; lean_object* v___y_372_; uint8_t v___y_452_; lean_object* v___y_453_; lean_object* v___y_454_; uint8_t v___y_455_; lean_object* v___y_456_; lean_object* v___y_457_; lean_object* v___y_458_; lean_object* v___y_459_; lean_object* v___y_460_; lean_object* v___y_461_; lean_object* v___y_462_; lean_object* v___y_463_; lean_object* v___y_464_; lean_object* v___y_465_; lean_object* v___y_466_; lean_object* v___y_467_; lean_object* v___y_468_; lean_object* v___y_469_; lean_object* v___y_470_; lean_object* v___y_483_; uint8_t v___y_484_; lean_object* v___y_485_; lean_object* v___y_486_; lean_object* v___y_487_; lean_object* v___y_488_; lean_object* v___y_489_; lean_object* v___y_490_; lean_object* v___y_491_; lean_object* v___y_492_; lean_object* v___y_493_; lean_object* v___y_494_; lean_object* v___y_495_; lean_object* v___y_496_; lean_object* v___y_497_; lean_object* v___y_498_; lean_object* v___y_499_; lean_object* v___y_500_; lean_object* v___y_510_; lean_object* v___y_511_; lean_object* v___y_512_; lean_object* v___y_513_; lean_object* v___y_514_; lean_object* v___y_515_; lean_object* v___y_516_; lean_object* v___y_517_; lean_object* v___y_518_; lean_object* v___y_519_; lean_object* v___y_520_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___y_536_; lean_object* v_args_537_; lean_object* v___y_538_; lean_object* v___y_539_; lean_object* v___y_540_; lean_object* v___y_541_; lean_object* v___y_542_; lean_object* v___y_543_; lean_object* v___y_544_; lean_object* v___y_545_; lean_object* v_o_557_; lean_object* v___y_558_; lean_object* v___y_559_; lean_object* v___y_560_; lean_object* v___y_561_; lean_object* v___y_562_; lean_object* v___y_563_; lean_object* v___y_564_; lean_object* v___y_565_; lean_object* v___x_580_; lean_object* v___x_581_; uint8_t v___x_582_; 
v___x_351_ = lean_unsigned_to_nat(0u);
v_tk_352_ = l_Lean_Syntax_getArg(v_stx_330_, v___x_351_);
v___x_533_ = lean_unsigned_to_nat(2u);
v___x_534_ = l_Lean_Syntax_getArg(v_stx_330_, v___x_533_);
v___x_580_ = lean_unsigned_to_nat(3u);
v___x_581_ = l_Lean_Syntax_getArg(v_stx_330_, v___x_580_);
v___x_582_ = l_Lean_Syntax_isNone(v___x_581_);
if (v___x_582_ == 0)
{
uint8_t v___x_583_; 
lean_inc(v___x_581_);
v___x_583_ = l_Lean_Syntax_matchesNull(v___x_581_, v___x_345_);
if (v___x_583_ == 0)
{
lean_object* v___x_584_; 
lean_dec(v___x_581_);
lean_dec(v___x_534_);
lean_dec(v_tk_352_);
lean_dec(v___x_346_);
lean_dec_ref(v___x_333_);
lean_dec_ref(v___x_332_);
lean_dec_ref(v___x_331_);
v___x_584_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
return v___x_584_;
}
else
{
lean_object* v_o_585_; lean_object* v___x_586_; 
v_o_585_ = l_Lean_Syntax_getArg(v___x_581_, v___x_351_);
lean_dec(v___x_581_);
v___x_586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_586_, 0, v_o_585_);
v_o_557_ = v___x_586_;
v___y_558_ = v___y_335_;
v___y_559_ = v___y_336_;
v___y_560_ = v___y_337_;
v___y_561_ = v___y_338_;
v___y_562_ = v___y_339_;
v___y_563_ = v___y_340_;
v___y_564_ = v___y_341_;
v___y_565_ = v___y_342_;
goto v___jp_556_;
}
}
else
{
lean_object* v___x_587_; 
lean_dec(v___x_581_);
v___x_587_ = lean_box(0);
v_o_557_ = v___x_587_;
v___y_558_ = v___y_335_;
v___y_559_ = v___y_336_;
v___y_560_ = v___y_337_;
v___y_561_ = v___y_338_;
v___y_562_ = v___y_339_;
v___y_563_ = v___y_340_;
v___y_564_ = v___y_341_;
v___y_565_ = v___y_342_;
goto v___jp_556_;
}
v___jp_353_:
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; uint8_t v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
lean_inc_ref_n(v___y_361_, 2);
v___x_373_ = l_Array_append___redArg(v___y_361_, v___y_372_);
lean_dec_ref(v___y_372_);
lean_inc_n(v___y_368_, 2);
lean_inc_n(v___y_365_, 2);
v___x_374_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_374_, 0, v___y_365_);
lean_ctor_set(v___x_374_, 1, v___y_368_);
lean_ctor_set(v___x_374_, 2, v___x_373_);
v___x_375_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_375_, 0, v___y_365_);
lean_ctor_set(v___x_375_, 1, v___y_368_);
lean_ctor_set(v___x_375_, 2, v___y_361_);
v___x_376_ = l_Lean_Syntax_node6(v___y_365_, v___y_364_, v___y_356_, v___x_346_, v___y_360_, v___y_355_, v___x_374_, v___x_375_);
v___x_377_ = 0;
v___x_378_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimp___closed__0));
v___x_379_ = l_Lean_Elab_Tactic_mkSimpContext(v___x_376_, v___y_358_, v___x_377_, v___y_358_, v___x_378_, v___y_357_, v___y_362_, v___y_359_, v___y_371_, v___y_366_, v___y_370_, v___y_369_, v___y_367_);
if (lean_obj_tag(v___x_379_) == 0)
{
lean_object* v_a_380_; lean_object* v_ctx_381_; lean_object* v_simprocs_382_; lean_object* v_dischargeWrapper_383_; lean_object* v___x_384_; 
v_a_380_ = lean_ctor_get(v___x_379_, 0);
lean_inc(v_a_380_);
lean_dec_ref_known(v___x_379_, 1);
v_ctx_381_ = lean_ctor_get(v_a_380_, 0);
lean_inc_ref(v_ctx_381_);
v_simprocs_382_ = lean_ctor_get(v_a_380_, 1);
lean_inc_ref(v_simprocs_382_);
v_dischargeWrapper_383_ = lean_ctor_get(v_a_380_, 2);
lean_inc(v_dischargeWrapper_383_);
lean_dec(v_a_380_);
v___x_384_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_362_, v___y_366_, v___y_370_, v___y_369_, v___y_367_);
if (lean_obj_tag(v___x_384_) == 0)
{
lean_object* v_a_385_; lean_object* v___x_386_; lean_object* v___f_387_; lean_object* v___x_388_; 
v_a_385_ = lean_ctor_get(v___x_384_, 0);
lean_inc(v_a_385_);
lean_dec_ref_known(v___x_384_, 1);
v___x_386_ = lean_box(v___y_354_);
v___f_387_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__0___boxed), 15, 5);
lean_closure_set(v___f_387_, 0, v___x_351_);
lean_closure_set(v___f_387_, 1, v_a_385_);
lean_closure_set(v___f_387_, 2, v_ctx_381_);
lean_closure_set(v___f_387_, 3, v_simprocs_382_);
lean_closure_set(v___f_387_, 4, v___x_386_);
v___x_388_ = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(v_dischargeWrapper_383_, v___f_387_, v___y_357_, v___y_362_, v___y_359_, v___y_371_, v___y_366_, v___y_370_, v___y_369_, v___y_367_);
lean_dec(v_dischargeWrapper_383_);
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
v___x_392_ = l_Lean_Elab_Tactic_Conv_applySimpResult(v_fst_390_, v___y_357_, v___y_362_, v___y_359_, v___y_371_, v___y_366_, v___y_370_, v___y_369_, v___y_367_);
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
v___x_400_ = l_Lean_Elab_Tactic_mkSimpCallStx(v___x_376_, v_usedTheorems_396_, v___y_366_, v___y_370_, v___y_369_, v___y_367_);
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
lean_inc(v___y_363_);
if (v_isShared_395_ == 0)
{
lean_ctor_set_tag(v___x_394_, 1);
lean_ctor_set(v___x_394_, 0, v___y_363_);
v___x_408_ = v___x_394_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v___y_363_);
v___x_408_ = v_reuseFailAlloc_413_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
lean_object* v___x_409_; uint8_t v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_409_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__3));
v___x_410_ = 4;
v___x_411_ = l_Lean_MessageData_nil;
v___x_412_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_352_, v___x_406_, v___x_408_, v___x_409_, v___x_405_, v___x_410_, v___x_411_, v___y_369_, v___y_367_);
return v___x_412_;
}
}
}
else
{
lean_object* v_a_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_422_; 
lean_del_object(v___x_398_);
lean_del_object(v___x_394_);
lean_dec(v_tk_352_);
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
lean_dec(v___x_376_);
lean_dec(v_tk_352_);
return v___x_392_;
}
}
else
{
lean_object* v_a_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_434_; 
lean_dec(v___x_376_);
lean_dec(v_tk_352_);
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
lean_dec(v_dischargeWrapper_383_);
lean_dec_ref(v_simprocs_382_);
lean_dec_ref(v_ctx_381_);
lean_dec(v___x_376_);
lean_dec(v_tk_352_);
v_a_435_ = lean_ctor_get(v___x_384_, 0);
v_isSharedCheck_442_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_442_ == 0)
{
v___x_437_ = v___x_384_;
v_isShared_438_ = v_isSharedCheck_442_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_a_435_);
lean_dec(v___x_384_);
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
lean_dec(v___x_376_);
lean_dec(v_tk_352_);
v_a_443_ = lean_ctor_get(v___x_379_, 0);
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_450_ == 0)
{
v___x_445_ = v___x_379_;
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_a_443_);
lean_dec(v___x_379_);
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
lean_object* v___x_471_; lean_object* v___x_472_; 
lean_inc_ref(v___y_458_);
v___x_471_ = l_Array_append___redArg(v___y_458_, v___y_470_);
lean_dec_ref(v___y_470_);
lean_inc(v___y_465_);
lean_inc(v___y_462_);
v___x_472_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_472_, 0, v___y_462_);
lean_ctor_set(v___x_472_, 1, v___y_465_);
lean_ctor_set(v___x_472_, 2, v___x_471_);
if (lean_obj_tag(v___y_466_) == 1)
{
lean_object* v_val_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v_val_473_ = lean_ctor_get(v___y_466_, 0);
lean_inc(v_val_473_);
lean_dec_ref_known(v___y_466_, 1);
v___x_474_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__4));
lean_inc_n(v___y_462_, 3);
v___x_475_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_475_, 0, v___y_462_);
lean_ctor_set(v___x_475_, 1, v___x_474_);
lean_inc_ref(v___y_458_);
v___x_476_ = l_Array_append___redArg(v___y_458_, v_val_473_);
lean_dec(v_val_473_);
lean_inc(v___y_465_);
v___x_477_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_477_, 0, v___y_462_);
lean_ctor_set(v___x_477_, 1, v___y_465_);
lean_ctor_set(v___x_477_, 2, v___x_476_);
v___x_478_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__5));
v___x_479_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_479_, 0, v___y_462_);
lean_ctor_set(v___x_479_, 1, v___x_478_);
v___x_480_ = l_Array_mkArray3___redArg(v___x_475_, v___x_477_, v___x_479_);
v___y_354_ = v___y_452_;
v___y_355_ = v___x_472_;
v___y_356_ = v___y_453_;
v___y_357_ = v___y_454_;
v___y_358_ = v___y_455_;
v___y_359_ = v___y_456_;
v___y_360_ = v___y_457_;
v___y_361_ = v___y_458_;
v___y_362_ = v___y_459_;
v___y_363_ = v___y_460_;
v___y_364_ = v___y_461_;
v___y_365_ = v___y_462_;
v___y_366_ = v___y_463_;
v___y_367_ = v___y_464_;
v___y_368_ = v___y_465_;
v___y_369_ = v___y_467_;
v___y_370_ = v___y_469_;
v___y_371_ = v___y_468_;
v___y_372_ = v___x_480_;
goto v___jp_353_;
}
else
{
lean_object* v___x_481_; 
lean_dec(v___y_466_);
v___x_481_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__6));
v___y_354_ = v___y_452_;
v___y_355_ = v___x_472_;
v___y_356_ = v___y_453_;
v___y_357_ = v___y_454_;
v___y_358_ = v___y_455_;
v___y_359_ = v___y_456_;
v___y_360_ = v___y_457_;
v___y_361_ = v___y_458_;
v___y_362_ = v___y_459_;
v___y_363_ = v___y_460_;
v___y_364_ = v___y_461_;
v___y_365_ = v___y_462_;
v___y_366_ = v___y_463_;
v___y_367_ = v___y_464_;
v___y_368_ = v___y_465_;
v___y_369_ = v___y_467_;
v___y_370_ = v___y_469_;
v___y_371_ = v___y_468_;
v___y_372_ = v___x_481_;
goto v___jp_353_;
}
}
v___jp_482_:
{
lean_object* v___x_501_; lean_object* v___x_502_; 
lean_inc_ref(v___y_488_);
v___x_501_ = l_Array_append___redArg(v___y_488_, v___y_500_);
lean_dec_ref(v___y_500_);
lean_inc(v___y_495_);
lean_inc(v___y_492_);
v___x_502_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_502_, 0, v___y_492_);
lean_ctor_set(v___x_502_, 1, v___y_495_);
lean_ctor_set(v___x_502_, 2, v___x_501_);
if (lean_obj_tag(v___y_491_) == 1)
{
lean_object* v_val_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v_val_503_ = lean_ctor_get(v___y_491_, 0);
lean_inc(v_val_503_);
lean_dec_ref_known(v___y_491_, 1);
v___x_504_ = l_Lean_SourceInfo_fromRef(v_val_503_, v___x_334_);
lean_dec(v_val_503_);
v___x_505_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__7));
v___x_506_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_506_, 0, v___x_504_);
lean_ctor_set(v___x_506_, 1, v___x_505_);
v___x_507_ = l_Array_mkArray1___redArg(v___x_506_);
v___y_452_ = v___y_484_;
v___y_453_ = v___y_485_;
v___y_454_ = v___y_486_;
v___y_455_ = v___y_484_;
v___y_456_ = v___y_487_;
v___y_457_ = v___x_502_;
v___y_458_ = v___y_488_;
v___y_459_ = v___y_489_;
v___y_460_ = v___y_483_;
v___y_461_ = v___y_490_;
v___y_462_ = v___y_492_;
v___y_463_ = v___y_493_;
v___y_464_ = v___y_494_;
v___y_465_ = v___y_495_;
v___y_466_ = v___y_496_;
v___y_467_ = v___y_497_;
v___y_468_ = v___y_499_;
v___y_469_ = v___y_498_;
v___y_470_ = v___x_507_;
goto v___jp_451_;
}
else
{
lean_object* v___x_508_; 
lean_dec(v___y_491_);
v___x_508_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__6));
v___y_452_ = v___y_484_;
v___y_453_ = v___y_485_;
v___y_454_ = v___y_486_;
v___y_455_ = v___y_484_;
v___y_456_ = v___y_487_;
v___y_457_ = v___x_502_;
v___y_458_ = v___y_488_;
v___y_459_ = v___y_489_;
v___y_460_ = v___y_483_;
v___y_461_ = v___y_490_;
v___y_462_ = v___y_492_;
v___y_463_ = v___y_493_;
v___y_464_ = v___y_494_;
v___y_465_ = v___y_495_;
v___y_466_ = v___y_496_;
v___y_467_ = v___y_497_;
v___y_468_ = v___y_499_;
v___y_469_ = v___y_498_;
v___y_470_ = v___x_508_;
goto v___jp_451_;
}
}
v___jp_509_:
{
lean_object* v_ref_521_; uint8_t v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v_ref_521_ = lean_ctor_get(v___y_517_, 2);
v___x_522_ = 0;
v___x_523_ = l_Lean_SourceInfo_fromRef(v_ref_521_, v___x_522_);
v___x_524_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__4));
v___x_525_ = l_Lean_Name_mkStr4(v___x_331_, v___x_332_, v___x_333_, v___x_524_);
v___x_526_ = l_Lean_SourceInfo_fromRef(v_tk_352_, v___x_334_);
v___x_527_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_527_, 0, v___x_526_);
lean_ctor_set(v___x_527_, 1, v___x_524_);
v___x_528_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__9));
v___x_529_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__10, &l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__10_once, _init_l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__10);
if (lean_obj_tag(v___y_520_) == 1)
{
lean_object* v_val_530_; lean_object* v___x_531_; 
v_val_530_ = lean_ctor_get(v___y_520_, 0);
lean_inc(v_val_530_);
lean_dec_ref_known(v___y_520_, 1);
v___x_531_ = l_Array_mkArray1___redArg(v_val_530_);
v___y_483_ = v_ref_521_;
v___y_484_ = v___x_522_;
v___y_485_ = v___x_527_;
v___y_486_ = v___y_511_;
v___y_487_ = v___y_513_;
v___y_488_ = v___x_529_;
v___y_489_ = v___y_516_;
v___y_490_ = v___x_525_;
v___y_491_ = v___y_510_;
v___y_492_ = v___x_523_;
v___y_493_ = v___y_512_;
v___y_494_ = v___y_514_;
v___y_495_ = v___x_528_;
v___y_496_ = v___y_515_;
v___y_497_ = v___y_517_;
v___y_498_ = v___y_519_;
v___y_499_ = v___y_518_;
v___y_500_ = v___x_531_;
goto v___jp_482_;
}
else
{
lean_object* v___x_532_; 
lean_dec(v___y_520_);
v___x_532_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__6));
v___y_483_ = v_ref_521_;
v___y_484_ = v___x_522_;
v___y_485_ = v___x_527_;
v___y_486_ = v___y_511_;
v___y_487_ = v___y_513_;
v___y_488_ = v___x_529_;
v___y_489_ = v___y_516_;
v___y_490_ = v___x_525_;
v___y_491_ = v___y_510_;
v___y_492_ = v___x_523_;
v___y_493_ = v___y_512_;
v___y_494_ = v___y_514_;
v___y_495_ = v___x_528_;
v___y_496_ = v___y_515_;
v___y_497_ = v___y_517_;
v___y_498_ = v___y_519_;
v___y_499_ = v___y_518_;
v___y_500_ = v___x_532_;
goto v___jp_482_;
}
}
v___jp_535_:
{
lean_object* v___x_546_; 
v___x_546_ = l_Lean_Syntax_getOptional_x3f(v___x_534_);
lean_dec(v___x_534_);
if (lean_obj_tag(v___x_546_) == 0)
{
lean_object* v___x_547_; 
v___x_547_ = lean_box(0);
v___y_510_ = v___y_536_;
v___y_511_ = v___y_538_;
v___y_512_ = v___y_542_;
v___y_513_ = v___y_540_;
v___y_514_ = v___y_545_;
v___y_515_ = v_args_537_;
v___y_516_ = v___y_539_;
v___y_517_ = v___y_544_;
v___y_518_ = v___y_541_;
v___y_519_ = v___y_543_;
v___y_520_ = v___x_547_;
goto v___jp_509_;
}
else
{
lean_object* v_val_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_555_; 
v_val_548_ = lean_ctor_get(v___x_546_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_555_ == 0)
{
v___x_550_ = v___x_546_;
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_val_548_);
lean_dec(v___x_546_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_553_; 
if (v_isShared_551_ == 0)
{
v___x_553_ = v___x_550_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_val_548_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
v___y_510_ = v___y_536_;
v___y_511_ = v___y_538_;
v___y_512_ = v___y_542_;
v___y_513_ = v___y_540_;
v___y_514_ = v___y_545_;
v___y_515_ = v_args_537_;
v___y_516_ = v___y_539_;
v___y_517_ = v___y_544_;
v___y_518_ = v___y_541_;
v___y_519_ = v___y_543_;
v___y_520_ = v___x_553_;
goto v___jp_509_;
}
}
}
}
v___jp_556_:
{
lean_object* v___x_566_; lean_object* v___x_567_; uint8_t v___x_568_; 
v___x_566_ = lean_unsigned_to_nat(4u);
v___x_567_ = l_Lean_Syntax_getArg(v_stx_330_, v___x_566_);
v___x_568_ = l_Lean_Syntax_isNone(v___x_567_);
if (v___x_568_ == 0)
{
uint8_t v___x_569_; 
lean_inc(v___x_567_);
v___x_569_ = l_Lean_Syntax_matchesNull(v___x_567_, v___x_345_);
if (v___x_569_ == 0)
{
lean_object* v___x_570_; 
lean_dec(v___x_567_);
lean_dec(v_o_557_);
lean_dec(v___x_534_);
lean_dec(v_tk_352_);
lean_dec(v___x_346_);
lean_dec_ref(v___x_333_);
lean_dec_ref(v___x_332_);
lean_dec_ref(v___x_331_);
v___x_570_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
return v___x_570_;
}
else
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; uint8_t v___x_574_; 
v___x_571_ = l_Lean_Syntax_getArg(v___x_567_, v___x_351_);
lean_dec(v___x_567_);
v___x_572_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__11));
lean_inc_ref(v___x_333_);
lean_inc_ref(v___x_332_);
lean_inc_ref(v___x_331_);
v___x_573_ = l_Lean_Name_mkStr4(v___x_331_, v___x_332_, v___x_333_, v___x_572_);
lean_inc(v___x_571_);
v___x_574_ = l_Lean_Syntax_isOfKind(v___x_571_, v___x_573_);
lean_dec(v___x_573_);
if (v___x_574_ == 0)
{
lean_object* v___x_575_; 
lean_dec(v___x_571_);
lean_dec(v_o_557_);
lean_dec(v___x_534_);
lean_dec(v_tk_352_);
lean_dec(v___x_346_);
lean_dec_ref(v___x_333_);
lean_dec_ref(v___x_332_);
lean_dec_ref(v___x_331_);
v___x_575_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
return v___x_575_;
}
else
{
lean_object* v___x_576_; lean_object* v_args_577_; lean_object* v___x_578_; 
v___x_576_ = l_Lean_Syntax_getArg(v___x_571_, v___x_345_);
lean_dec(v___x_571_);
v_args_577_ = l_Lean_Syntax_getArgs(v___x_576_);
lean_dec(v___x_576_);
v___x_578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_578_, 0, v_args_577_);
v___y_536_ = v_o_557_;
v_args_537_ = v___x_578_;
v___y_538_ = v___y_558_;
v___y_539_ = v___y_559_;
v___y_540_ = v___y_560_;
v___y_541_ = v___y_561_;
v___y_542_ = v___y_562_;
v___y_543_ = v___y_563_;
v___y_544_ = v___y_564_;
v___y_545_ = v___y_565_;
goto v___jp_535_;
}
}
}
else
{
lean_object* v___x_579_; 
lean_dec(v___x_567_);
v___x_579_ = lean_box(0);
v___y_536_ = v_o_557_;
v_args_537_ = v___x_579_;
v___y_538_ = v___y_558_;
v___y_539_ = v___y_559_;
v___y_540_ = v___y_560_;
v___y_541_ = v___y_561_;
v___y_542_ = v___y_562_;
v___y_543_ = v___y_563_;
v___y_544_ = v___y_564_;
v___y_545_ = v___y_565_;
goto v___jp_535_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___boxed(lean_object* v___x_588_, lean_object* v_stx_589_, lean_object* v___x_590_, lean_object* v___x_591_, lean_object* v___x_592_, lean_object* v___x_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_){
_start:
{
uint8_t v___x_5505__boxed_603_; uint8_t v___x_5509__boxed_604_; lean_object* v_res_605_; 
v___x_5505__boxed_603_ = lean_unbox(v___x_588_);
v___x_5509__boxed_604_ = lean_unbox(v___x_593_);
v_res_605_ = l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1(v___x_5505__boxed_603_, v_stx_589_, v___x_590_, v___x_591_, v___x_592_, v___x_5509__boxed_604_, v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace(lean_object* v_stx_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_){
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpTrace___boxed(lean_object* v_stx_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_Lean_Elab_Tactic_Conv_evalSimpTrace(v_stx_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_);
lean_dec(v_a_641_);
lean_dec_ref(v_a_640_);
lean_dec(v_a_639_);
lean_dec_ref(v_a_638_);
lean_dec(v_a_637_);
lean_dec_ref(v_a_636_);
lean_dec(v_a_635_);
lean_dec_ref(v_a_634_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1(){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_652_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_653_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__1));
v___x_654_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__1));
v___x_655_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___boxed), 10, 0);
v___x_656_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_652_, v___x_653_, v___x_654_, v___x_655_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___boxed(lean_object* v_a_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1();
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg___lam__0(lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_){
_start:
{
lean_object* v___x_668_; 
v___x_668_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_660_, v___y_663_, v___y_664_, v___y_665_, v___y_666_);
if (lean_obj_tag(v___x_668_) == 0)
{
lean_object* v_a_669_; lean_object* v___x_670_; 
v_a_669_ = lean_ctor_get(v___x_668_, 0);
lean_inc(v_a_669_);
lean_dec_ref_known(v___x_668_, 1);
v___x_670_ = l_Lean_Meta_Split_simpMatch(v_a_669_, v___y_663_, v___y_664_, v___y_665_, v___y_666_);
if (lean_obj_tag(v___x_670_) == 0)
{
lean_object* v_a_671_; lean_object* v___x_672_; 
v_a_671_ = lean_ctor_get(v___x_670_, 0);
lean_inc(v_a_671_);
lean_dec_ref_known(v___x_670_, 1);
v___x_672_ = l_Lean_Elab_Tactic_Conv_applySimpResult(v_a_671_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_);
return v___x_672_;
}
else
{
lean_object* v_a_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_680_; 
v_a_673_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_680_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_680_ == 0)
{
v___x_675_ = v___x_670_;
v_isShared_676_ = v_isSharedCheck_680_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_a_673_);
lean_dec(v___x_670_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_680_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_678_; 
if (v_isShared_676_ == 0)
{
v___x_678_ = v___x_675_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_a_673_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
}
}
else
{
lean_object* v_a_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_688_; 
v_a_681_ = lean_ctor_get(v___x_668_, 0);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_688_ == 0)
{
v___x_683_ = v___x_668_;
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_a_681_);
lean_dec(v___x_668_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___x_686_; 
if (v_isShared_684_ == 0)
{
v___x_686_ = v___x_683_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_a_681_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg___lam__0___boxed(lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_){
_start:
{
lean_object* v_res_698_; 
v_res_698_ = l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg___lam__0(v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_);
lean_dec(v___y_696_);
lean_dec_ref(v___y_695_);
lean_dec(v___y_694_);
lean_dec_ref(v___y_693_);
lean_dec(v___y_692_);
lean_dec_ref(v___y_691_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
return v_res_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg(lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_){
_start:
{
lean_object* v___f_709_; lean_object* v___x_710_; 
v___f_709_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg___closed__0));
v___x_710_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_709_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg___boxed(lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg(v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
lean_dec(v_a_718_);
lean_dec_ref(v_a_717_);
lean_dec(v_a_716_);
lean_dec_ref(v_a_715_);
lean_dec(v_a_714_);
lean_dec_ref(v_a_713_);
lean_dec(v_a_712_);
lean_dec_ref(v_a_711_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch(lean_object* v_x_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg(v_a_722_, v_a_723_, v_a_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSimpMatch___boxed(lean_object* v_x_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l_Lean_Elab_Tactic_Conv_evalSimpMatch(v_x_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_, v_a_739_, v_a_740_);
lean_dec(v_a_740_);
lean_dec_ref(v_a_739_);
lean_dec(v_a_738_);
lean_dec_ref(v_a_737_);
lean_dec(v_a_736_);
lean_dec_ref(v_a_735_);
lean_dec(v_a_734_);
lean_dec_ref(v_a_733_);
lean_dec(v_x_732_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1(){
_start:
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_758_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_759_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__1));
v___x_760_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__3));
v___x_761_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalSimpMatch___boxed), 10, 0);
v___x_762_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_758_, v___x_759_, v___x_760_, v___x_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___boxed(lean_object* v_a_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1();
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3(){
_start:
{
lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_791_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__3));
v___x_792_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__6));
v___x_793_ = l_Lean_addBuiltinDeclarationRanges(v___x_791_, v___x_792_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___boxed(lean_object* v_a_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3();
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimp___lam__0(lean_object* v_stx_798_, uint8_t v___x_799_, uint8_t v___x_800_, lean_object* v___x_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_){
_start:
{
lean_object* v___x_811_; 
v___x_811_ = l_Lean_Elab_Tactic_mkSimpContext(v_stx_798_, v___x_799_, v___x_800_, v___x_799_, v___x_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_);
if (lean_obj_tag(v___x_811_) == 0)
{
lean_object* v_a_812_; lean_object* v_ctx_813_; lean_object* v___x_814_; 
v_a_812_ = lean_ctor_get(v___x_811_, 0);
lean_inc(v_a_812_);
lean_dec_ref_known(v___x_811_, 1);
v_ctx_813_ = lean_ctor_get(v_a_812_, 0);
lean_inc_ref(v_ctx_813_);
lean_dec(v_a_812_);
v___x_814_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_803_, v___y_806_, v___y_807_, v___y_808_, v___y_809_);
if (lean_obj_tag(v___x_814_) == 0)
{
lean_object* v_a_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
v_a_815_ = lean_ctor_get(v___x_814_, 0);
lean_inc(v_a_815_);
lean_dec_ref_known(v___x_814_, 1);
v___x_816_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalDSimp___lam__0___closed__0));
v___x_817_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6, &l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6);
v___x_818_ = l_Lean_Meta_dsimp(v_a_815_, v_ctx_813_, v___x_816_, v___x_817_, v___y_806_, v___y_807_, v___y_808_, v___y_809_);
if (lean_obj_tag(v___x_818_) == 0)
{
lean_object* v_a_819_; lean_object* v_fst_820_; lean_object* v___x_821_; 
v_a_819_ = lean_ctor_get(v___x_818_, 0);
lean_inc(v_a_819_);
lean_dec_ref_known(v___x_818_, 1);
v_fst_820_ = lean_ctor_get(v_a_819_, 0);
lean_inc(v_fst_820_);
lean_dec(v_a_819_);
v___x_821_ = l_Lean_Elab_Tactic_Conv_changeLhs(v_fst_820_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_);
return v___x_821_;
}
else
{
lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_829_; 
v_a_822_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_829_ == 0)
{
v___x_824_ = v___x_818_;
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v___x_818_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_827_; 
if (v_isShared_825_ == 0)
{
v___x_827_ = v___x_824_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_a_822_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
}
}
else
{
lean_object* v_a_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_837_; 
lean_dec_ref(v_ctx_813_);
v_a_830_ = lean_ctor_get(v___x_814_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_814_);
if (v_isSharedCheck_837_ == 0)
{
v___x_832_ = v___x_814_;
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_a_830_);
lean_dec(v___x_814_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_835_; 
if (v_isShared_833_ == 0)
{
v___x_835_ = v___x_832_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_a_830_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
}
else
{
lean_object* v_a_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_845_; 
v_a_838_ = lean_ctor_get(v___x_811_, 0);
v_isSharedCheck_845_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_845_ == 0)
{
v___x_840_ = v___x_811_;
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_a_838_);
lean_dec(v___x_811_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_843_; 
if (v_isShared_841_ == 0)
{
v___x_843_ = v___x_840_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v_a_838_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimp___lam__0___boxed(lean_object* v_stx_846_, lean_object* v___x_847_, lean_object* v___x_848_, lean_object* v___x_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_){
_start:
{
uint8_t v___x_590__boxed_859_; uint8_t v___x_591__boxed_860_; lean_object* v_res_861_; 
v___x_590__boxed_859_ = lean_unbox(v___x_847_);
v___x_591__boxed_860_ = lean_unbox(v___x_848_);
v_res_861_ = l_Lean_Elab_Tactic_Conv_evalDSimp___lam__0(v_stx_846_, v___x_590__boxed_859_, v___x_591__boxed_860_, v___x_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_);
lean_dec(v___y_857_);
lean_dec_ref(v___y_856_);
lean_dec(v___y_855_);
lean_dec_ref(v___y_854_);
lean_dec(v___y_853_);
lean_dec_ref(v___y_852_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec(v_stx_846_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimp(lean_object* v_stx_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_){
_start:
{
uint8_t v___x_872_; uint8_t v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___f_877_; lean_object* v___x_878_; 
v___x_872_ = 0;
v___x_873_ = 2;
v___x_874_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimp___closed__0));
v___x_875_ = lean_box(v___x_872_);
v___x_876_ = lean_box(v___x_873_);
v___f_877_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalDSimp___lam__0___boxed), 13, 4);
lean_closure_set(v___f_877_, 0, v_stx_862_);
lean_closure_set(v___f_877_, 1, v___x_875_);
lean_closure_set(v___f_877_, 2, v___x_876_);
lean_closure_set(v___f_877_, 3, v___x_874_);
v___x_878_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_877_, v_a_863_, v_a_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimp___boxed(lean_object* v_stx_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_Lean_Elab_Tactic_Conv_evalDSimp(v_stx_879_, v_a_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_);
lean_dec(v_a_887_);
lean_dec_ref(v_a_886_);
lean_dec(v_a_885_);
lean_dec_ref(v_a_884_);
lean_dec(v_a_883_);
lean_dec_ref(v_a_882_);
lean_dec(v_a_881_);
lean_dec_ref(v_a_880_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1(){
_start:
{
lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_905_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_906_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__1));
v___x_907_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__3));
v___x_908_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalDSimp___boxed), 10, 0);
v___x_909_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_905_, v___x_906_, v___x_907_, v___x_908_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___boxed(lean_object* v_a_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1();
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3(){
_start:
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_937_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__3));
v___x_938_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__6));
v___x_939_ = l_Lean_addBuiltinDeclarationRanges(v___x_937_, v___x_938_);
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___boxed(lean_object* v_a_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3();
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimpTrace___lam__0(uint8_t v___x_943_, lean_object* v_stx_944_, lean_object* v___x_945_, lean_object* v___x_946_, lean_object* v___x_947_, uint8_t v___x_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_){
_start:
{
if (v___x_943_ == 0)
{
lean_object* v___x_958_; 
lean_dec_ref(v___x_947_);
lean_dec_ref(v___x_946_);
lean_dec_ref(v___x_945_);
v___x_958_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
return v___x_958_;
}
else
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; uint8_t v___x_963_; 
v___x_959_ = lean_unsigned_to_nat(1u);
v___x_960_ = l_Lean_Syntax_getArg(v_stx_944_, v___x_959_);
v___x_961_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__0));
lean_inc_ref(v___x_947_);
lean_inc_ref(v___x_946_);
lean_inc_ref(v___x_945_);
v___x_962_ = l_Lean_Name_mkStr4(v___x_945_, v___x_946_, v___x_947_, v___x_961_);
lean_inc(v___x_960_);
v___x_963_ = l_Lean_Syntax_isOfKind(v___x_960_, v___x_962_);
lean_dec(v___x_962_);
if (v___x_963_ == 0)
{
lean_object* v___x_964_; 
lean_dec(v___x_960_);
lean_dec_ref(v___x_947_);
lean_dec_ref(v___x_946_);
lean_dec_ref(v___x_945_);
v___x_964_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
return v___x_964_;
}
else
{
lean_object* v___x_965_; lean_object* v_tk_966_; lean_object* v___y_968_; uint8_t v___y_969_; lean_object* v___y_970_; lean_object* v___y_971_; lean_object* v___y_972_; lean_object* v___y_973_; lean_object* v___y_974_; lean_object* v___y_975_; lean_object* v___y_976_; lean_object* v___y_977_; lean_object* v___y_978_; lean_object* v___y_979_; lean_object* v___y_980_; lean_object* v___y_981_; lean_object* v___y_982_; lean_object* v___y_983_; lean_object* v___y_984_; lean_object* v___y_985_; lean_object* v___y_1062_; uint8_t v___y_1063_; lean_object* v___y_1064_; lean_object* v___y_1065_; lean_object* v___y_1066_; lean_object* v___y_1067_; lean_object* v___y_1068_; lean_object* v___y_1069_; lean_object* v___y_1070_; lean_object* v___y_1071_; lean_object* v___y_1072_; lean_object* v___y_1073_; lean_object* v___y_1074_; lean_object* v___y_1075_; lean_object* v___y_1076_; lean_object* v___y_1077_; lean_object* v___y_1078_; lean_object* v___y_1079_; lean_object* v___y_1092_; lean_object* v_args_1093_; lean_object* v___y_1094_; lean_object* v___y_1095_; lean_object* v___y_1096_; lean_object* v___y_1097_; lean_object* v___y_1098_; lean_object* v___y_1099_; lean_object* v___y_1100_; lean_object* v___y_1101_; lean_object* v_o_1119_; lean_object* v___y_1120_; lean_object* v___y_1121_; lean_object* v___y_1122_; lean_object* v___y_1123_; lean_object* v___y_1124_; lean_object* v___y_1125_; lean_object* v___y_1126_; lean_object* v___y_1127_; lean_object* v___x_1142_; lean_object* v___x_1143_; uint8_t v___x_1144_; 
v___x_965_ = lean_unsigned_to_nat(0u);
v_tk_966_ = l_Lean_Syntax_getArg(v_stx_944_, v___x_965_);
v___x_1142_ = lean_unsigned_to_nat(2u);
v___x_1143_ = l_Lean_Syntax_getArg(v_stx_944_, v___x_1142_);
v___x_1144_ = l_Lean_Syntax_isNone(v___x_1143_);
if (v___x_1144_ == 0)
{
uint8_t v___x_1145_; 
lean_inc(v___x_1143_);
v___x_1145_ = l_Lean_Syntax_matchesNull(v___x_1143_, v___x_959_);
if (v___x_1145_ == 0)
{
lean_object* v___x_1146_; 
lean_dec(v___x_1143_);
lean_dec(v_tk_966_);
lean_dec(v___x_960_);
lean_dec_ref(v___x_947_);
lean_dec_ref(v___x_946_);
lean_dec_ref(v___x_945_);
v___x_1146_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
return v___x_1146_;
}
else
{
lean_object* v_o_1147_; lean_object* v___x_1148_; 
v_o_1147_ = l_Lean_Syntax_getArg(v___x_1143_, v___x_965_);
lean_dec(v___x_1143_);
v___x_1148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1148_, 0, v_o_1147_);
v_o_1119_ = v___x_1148_;
v___y_1120_ = v___y_949_;
v___y_1121_ = v___y_950_;
v___y_1122_ = v___y_951_;
v___y_1123_ = v___y_952_;
v___y_1124_ = v___y_953_;
v___y_1125_ = v___y_954_;
v___y_1126_ = v___y_955_;
v___y_1127_ = v___y_956_;
goto v___jp_1118_;
}
}
else
{
lean_object* v___x_1149_; 
lean_dec(v___x_1143_);
v___x_1149_ = lean_box(0);
v_o_1119_ = v___x_1149_;
v___y_1120_ = v___y_949_;
v___y_1121_ = v___y_950_;
v___y_1122_ = v___y_951_;
v___y_1123_ = v___y_952_;
v___y_1124_ = v___y_953_;
v___y_1125_ = v___y_954_;
v___y_1126_ = v___y_955_;
v___y_1127_ = v___y_956_;
goto v___jp_1118_;
}
v___jp_967_:
{
lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; uint8_t v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
lean_inc_ref(v___y_976_);
v___x_986_ = l_Array_append___redArg(v___y_976_, v___y_985_);
lean_dec_ref(v___y_985_);
lean_inc(v___y_973_);
lean_inc(v___y_972_);
v___x_987_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_987_, 0, v___y_972_);
lean_ctor_set(v___x_987_, 1, v___y_973_);
lean_ctor_set(v___x_987_, 2, v___x_986_);
lean_inc(v___y_977_);
v___x_988_ = l_Lean_Syntax_node6(v___y_972_, v___y_968_, v___y_978_, v___x_960_, v___y_977_, v___y_975_, v___x_987_, v___y_977_);
v___x_989_ = 2;
v___x_990_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimp___closed__0));
v___x_991_ = l_Lean_Elab_Tactic_mkSimpContext(v___x_988_, v___y_969_, v___x_989_, v___y_969_, v___x_990_, v___y_970_, v___y_981_, v___y_982_, v___y_974_, v___y_980_, v___y_971_, v___y_979_, v___y_983_);
if (lean_obj_tag(v___x_991_) == 0)
{
lean_object* v_a_992_; lean_object* v_ctx_993_; lean_object* v___x_994_; 
v_a_992_ = lean_ctor_get(v___x_991_, 0);
lean_inc(v_a_992_);
lean_dec_ref_known(v___x_991_, 1);
v_ctx_993_ = lean_ctor_get(v_a_992_, 0);
lean_inc_ref(v_ctx_993_);
lean_dec(v_a_992_);
v___x_994_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_981_, v___y_980_, v___y_971_, v___y_979_, v___y_983_);
if (lean_obj_tag(v___x_994_) == 0)
{
lean_object* v_a_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
v_a_995_ = lean_ctor_get(v___x_994_, 0);
lean_inc(v_a_995_);
lean_dec_ref_known(v___x_994_, 1);
v___x_996_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalDSimp___lam__0___closed__0));
v___x_997_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6, &l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6);
v___x_998_ = l_Lean_Meta_dsimp(v_a_995_, v_ctx_993_, v___x_996_, v___x_997_, v___y_980_, v___y_971_, v___y_979_, v___y_983_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_object* v_a_999_; lean_object* v_fst_1000_; lean_object* v_snd_1001_; lean_object* v___x_1002_; 
v_a_999_ = lean_ctor_get(v___x_998_, 0);
lean_inc(v_a_999_);
lean_dec_ref_known(v___x_998_, 1);
v_fst_1000_ = lean_ctor_get(v_a_999_, 0);
lean_inc(v_fst_1000_);
v_snd_1001_ = lean_ctor_get(v_a_999_, 1);
lean_inc(v_snd_1001_);
lean_dec(v_a_999_);
v___x_1002_ = l_Lean_Elab_Tactic_Conv_changeLhs(v_fst_1000_, v___y_970_, v___y_981_, v___y_982_, v___y_974_, v___y_980_, v___y_971_, v___y_979_, v___y_983_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1035_; 
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1035_ == 0)
{
lean_object* v_unused_1036_; 
v_unused_1036_ = lean_ctor_get(v___x_1002_, 0);
lean_dec(v_unused_1036_);
v___x_1004_ = v___x_1002_;
v_isShared_1005_ = v_isSharedCheck_1035_;
goto v_resetjp_1003_;
}
else
{
lean_dec(v___x_1002_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1035_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v_usedTheorems_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1033_; 
v_usedTheorems_1006_ = lean_ctor_get(v_snd_1001_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v_snd_1001_);
if (v_isSharedCheck_1033_ == 0)
{
lean_object* v_unused_1034_; 
v_unused_1034_ = lean_ctor_get(v_snd_1001_, 1);
lean_dec(v_unused_1034_);
v___x_1008_ = v_snd_1001_;
v_isShared_1009_ = v_isSharedCheck_1033_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_usedTheorems_1006_);
lean_dec(v_snd_1001_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1033_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1010_; 
v___x_1010_ = l_Lean_Elab_Tactic_mkSimpCallStx(v___x_988_, v_usedTheorems_1006_, v___y_980_, v___y_971_, v___y_979_, v___y_983_);
lean_dec_ref(v_usedTheorems_1006_);
if (lean_obj_tag(v___x_1010_) == 0)
{
lean_object* v_a_1011_; lean_object* v___x_1012_; lean_object* v___x_1014_; 
v_a_1011_ = lean_ctor_get(v___x_1010_, 0);
lean_inc(v_a_1011_);
lean_dec_ref_known(v___x_1010_, 1);
v___x_1012_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__2));
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 1, v_a_1011_);
lean_ctor_set(v___x_1008_, 0, v___x_1012_);
v___x_1014_ = v___x_1008_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v___x_1012_);
lean_ctor_set(v_reuseFailAlloc_1024_, 1, v_a_1011_);
v___x_1014_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1018_; 
v___x_1015_ = lean_box(0);
v___x_1016_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1014_);
lean_ctor_set(v___x_1016_, 1, v___x_1015_);
lean_ctor_set(v___x_1016_, 2, v___x_1015_);
lean_ctor_set(v___x_1016_, 3, v___x_1015_);
lean_ctor_set(v___x_1016_, 4, v___x_1015_);
lean_ctor_set(v___x_1016_, 5, v___x_1015_);
lean_inc(v___y_984_);
if (v_isShared_1005_ == 0)
{
lean_ctor_set_tag(v___x_1004_, 1);
lean_ctor_set(v___x_1004_, 0, v___y_984_);
v___x_1018_ = v___x_1004_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v___y_984_);
v___x_1018_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
lean_object* v___x_1019_; uint8_t v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1019_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__3));
v___x_1020_ = 4;
v___x_1021_ = l_Lean_MessageData_nil;
v___x_1022_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_966_, v___x_1016_, v___x_1018_, v___x_1019_, v___x_1015_, v___x_1020_, v___x_1021_, v___y_979_, v___y_983_);
return v___x_1022_;
}
}
}
else
{
lean_object* v_a_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1032_; 
lean_del_object(v___x_1008_);
lean_del_object(v___x_1004_);
lean_dec(v_tk_966_);
v_a_1025_ = lean_ctor_get(v___x_1010_, 0);
v_isSharedCheck_1032_ = !lean_is_exclusive(v___x_1010_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_1027_ = v___x_1010_;
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_a_1025_);
lean_dec(v___x_1010_);
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
}
}
else
{
lean_dec(v_snd_1001_);
lean_dec(v___x_988_);
lean_dec(v_tk_966_);
return v___x_1002_;
}
}
else
{
lean_object* v_a_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1044_; 
lean_dec(v___x_988_);
lean_dec(v_tk_966_);
v_a_1037_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1039_ = v___x_998_;
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_a_1037_);
lean_dec(v___x_998_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1042_; 
if (v_isShared_1040_ == 0)
{
v___x_1042_ = v___x_1039_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_a_1037_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
}
else
{
lean_object* v_a_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1052_; 
lean_dec_ref(v_ctx_993_);
lean_dec(v___x_988_);
lean_dec(v_tk_966_);
v_a_1045_ = lean_ctor_get(v___x_994_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1047_ = v___x_994_;
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_a_1045_);
lean_dec(v___x_994_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1050_; 
if (v_isShared_1048_ == 0)
{
v___x_1050_ = v___x_1047_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_a_1045_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
}
else
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1060_; 
lean_dec(v___x_988_);
lean_dec(v_tk_966_);
v_a_1053_ = lean_ctor_get(v___x_991_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1055_ = v___x_991_;
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v___x_991_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1058_; 
if (v_isShared_1056_ == 0)
{
v___x_1058_ = v___x_1055_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_a_1053_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
}
}
v___jp_1061_:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; 
lean_inc_ref(v___y_1069_);
v___x_1080_ = l_Array_append___redArg(v___y_1069_, v___y_1079_);
lean_dec_ref(v___y_1079_);
lean_inc(v___y_1067_);
lean_inc(v___y_1066_);
v___x_1081_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1081_, 0, v___y_1066_);
lean_ctor_set(v___x_1081_, 1, v___y_1067_);
lean_ctor_set(v___x_1081_, 2, v___x_1080_);
if (lean_obj_tag(v___y_1074_) == 1)
{
lean_object* v_val_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; 
v_val_1082_ = lean_ctor_get(v___y_1074_, 0);
lean_inc(v_val_1082_);
lean_dec_ref_known(v___y_1074_, 1);
v___x_1083_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__4));
lean_inc_n(v___y_1066_, 3);
v___x_1084_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___y_1066_);
lean_ctor_set(v___x_1084_, 1, v___x_1083_);
lean_inc_ref(v___y_1069_);
v___x_1085_ = l_Array_append___redArg(v___y_1069_, v_val_1082_);
lean_dec(v_val_1082_);
lean_inc(v___y_1067_);
v___x_1086_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1086_, 0, v___y_1066_);
lean_ctor_set(v___x_1086_, 1, v___y_1067_);
lean_ctor_set(v___x_1086_, 2, v___x_1085_);
v___x_1087_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__5));
v___x_1088_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1088_, 0, v___y_1066_);
lean_ctor_set(v___x_1088_, 1, v___x_1087_);
v___x_1089_ = l_Array_mkArray3___redArg(v___x_1084_, v___x_1086_, v___x_1088_);
v___y_968_ = v___y_1062_;
v___y_969_ = v___y_1063_;
v___y_970_ = v___y_1064_;
v___y_971_ = v___y_1065_;
v___y_972_ = v___y_1066_;
v___y_973_ = v___y_1067_;
v___y_974_ = v___y_1068_;
v___y_975_ = v___x_1081_;
v___y_976_ = v___y_1069_;
v___y_977_ = v___y_1070_;
v___y_978_ = v___y_1071_;
v___y_979_ = v___y_1072_;
v___y_980_ = v___y_1073_;
v___y_981_ = v___y_1075_;
v___y_982_ = v___y_1076_;
v___y_983_ = v___y_1077_;
v___y_984_ = v___y_1078_;
v___y_985_ = v___x_1089_;
goto v___jp_967_;
}
else
{
lean_object* v___x_1090_; 
lean_dec(v___y_1074_);
v___x_1090_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__6));
v___y_968_ = v___y_1062_;
v___y_969_ = v___y_1063_;
v___y_970_ = v___y_1064_;
v___y_971_ = v___y_1065_;
v___y_972_ = v___y_1066_;
v___y_973_ = v___y_1067_;
v___y_974_ = v___y_1068_;
v___y_975_ = v___x_1081_;
v___y_976_ = v___y_1069_;
v___y_977_ = v___y_1070_;
v___y_978_ = v___y_1071_;
v___y_979_ = v___y_1072_;
v___y_980_ = v___y_1073_;
v___y_981_ = v___y_1075_;
v___y_982_ = v___y_1076_;
v___y_983_ = v___y_1077_;
v___y_984_ = v___y_1078_;
v___y_985_ = v___x_1090_;
goto v___jp_967_;
}
}
v___jp_1091_:
{
lean_object* v_ref_1102_; uint8_t v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
v_ref_1102_ = lean_ctor_get(v___y_1100_, 2);
v___x_1103_ = 0;
v___x_1104_ = l_Lean_SourceInfo_fromRef(v_ref_1102_, v___x_1103_);
v___x_1105_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__0));
v___x_1106_ = l_Lean_Name_mkStr4(v___x_945_, v___x_946_, v___x_947_, v___x_1105_);
v___x_1107_ = l_Lean_SourceInfo_fromRef(v_tk_966_, v___x_948_);
v___x_1108_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1107_);
lean_ctor_set(v___x_1108_, 1, v___x_1105_);
v___x_1109_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__9));
v___x_1110_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__10, &l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__10_once, _init_l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__10);
lean_inc(v___x_1104_);
v___x_1111_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1104_);
lean_ctor_set(v___x_1111_, 1, v___x_1109_);
lean_ctor_set(v___x_1111_, 2, v___x_1110_);
if (lean_obj_tag(v___y_1092_) == 1)
{
lean_object* v_val_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
v_val_1112_ = lean_ctor_get(v___y_1092_, 0);
lean_inc(v_val_1112_);
lean_dec_ref_known(v___y_1092_, 1);
v___x_1113_ = l_Lean_SourceInfo_fromRef(v_val_1112_, v___x_948_);
lean_dec(v_val_1112_);
v___x_1114_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__7));
v___x_1115_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1113_);
lean_ctor_set(v___x_1115_, 1, v___x_1114_);
v___x_1116_ = l_Array_mkArray1___redArg(v___x_1115_);
v___y_1062_ = v___x_1106_;
v___y_1063_ = v___x_1103_;
v___y_1064_ = v___y_1094_;
v___y_1065_ = v___y_1099_;
v___y_1066_ = v___x_1104_;
v___y_1067_ = v___x_1109_;
v___y_1068_ = v___y_1097_;
v___y_1069_ = v___x_1110_;
v___y_1070_ = v___x_1111_;
v___y_1071_ = v___x_1108_;
v___y_1072_ = v___y_1100_;
v___y_1073_ = v___y_1098_;
v___y_1074_ = v_args_1093_;
v___y_1075_ = v___y_1095_;
v___y_1076_ = v___y_1096_;
v___y_1077_ = v___y_1101_;
v___y_1078_ = v_ref_1102_;
v___y_1079_ = v___x_1116_;
goto v___jp_1061_;
}
else
{
lean_object* v___x_1117_; 
lean_dec(v___y_1092_);
v___x_1117_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__6));
v___y_1062_ = v___x_1106_;
v___y_1063_ = v___x_1103_;
v___y_1064_ = v___y_1094_;
v___y_1065_ = v___y_1099_;
v___y_1066_ = v___x_1104_;
v___y_1067_ = v___x_1109_;
v___y_1068_ = v___y_1097_;
v___y_1069_ = v___x_1110_;
v___y_1070_ = v___x_1111_;
v___y_1071_ = v___x_1108_;
v___y_1072_ = v___y_1100_;
v___y_1073_ = v___y_1098_;
v___y_1074_ = v_args_1093_;
v___y_1075_ = v___y_1095_;
v___y_1076_ = v___y_1096_;
v___y_1077_ = v___y_1101_;
v___y_1078_ = v_ref_1102_;
v___y_1079_ = v___x_1117_;
goto v___jp_1061_;
}
}
v___jp_1118_:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; uint8_t v___x_1130_; 
v___x_1128_ = lean_unsigned_to_nat(3u);
v___x_1129_ = l_Lean_Syntax_getArg(v_stx_944_, v___x_1128_);
v___x_1130_ = l_Lean_Syntax_isNone(v___x_1129_);
if (v___x_1130_ == 0)
{
uint8_t v___x_1131_; 
lean_inc(v___x_1129_);
v___x_1131_ = l_Lean_Syntax_matchesNull(v___x_1129_, v___x_959_);
if (v___x_1131_ == 0)
{
lean_object* v___x_1132_; 
lean_dec(v___x_1129_);
lean_dec(v_o_1119_);
lean_dec(v_tk_966_);
lean_dec(v___x_960_);
lean_dec_ref(v___x_947_);
lean_dec_ref(v___x_946_);
lean_dec_ref(v___x_945_);
v___x_1132_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
return v___x_1132_;
}
else
{
lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; uint8_t v___x_1136_; 
v___x_1133_ = l_Lean_Syntax_getArg(v___x_1129_, v___x_965_);
lean_dec(v___x_1129_);
v___x_1134_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalDSimpTrace___lam__0___closed__0));
lean_inc_ref(v___x_947_);
lean_inc_ref(v___x_946_);
lean_inc_ref(v___x_945_);
v___x_1135_ = l_Lean_Name_mkStr4(v___x_945_, v___x_946_, v___x_947_, v___x_1134_);
lean_inc(v___x_1133_);
v___x_1136_ = l_Lean_Syntax_isOfKind(v___x_1133_, v___x_1135_);
lean_dec(v___x_1135_);
if (v___x_1136_ == 0)
{
lean_object* v___x_1137_; 
lean_dec(v___x_1133_);
lean_dec(v_o_1119_);
lean_dec(v_tk_966_);
lean_dec(v___x_960_);
lean_dec_ref(v___x_947_);
lean_dec_ref(v___x_946_);
lean_dec_ref(v___x_945_);
v___x_1137_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
return v___x_1137_;
}
else
{
lean_object* v___x_1138_; lean_object* v_args_1139_; lean_object* v___x_1140_; 
v___x_1138_ = l_Lean_Syntax_getArg(v___x_1133_, v___x_959_);
lean_dec(v___x_1133_);
v_args_1139_ = l_Lean_Syntax_getArgs(v___x_1138_);
lean_dec(v___x_1138_);
v___x_1140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1140_, 0, v_args_1139_);
v___y_1092_ = v_o_1119_;
v_args_1093_ = v___x_1140_;
v___y_1094_ = v___y_1120_;
v___y_1095_ = v___y_1121_;
v___y_1096_ = v___y_1122_;
v___y_1097_ = v___y_1123_;
v___y_1098_ = v___y_1124_;
v___y_1099_ = v___y_1125_;
v___y_1100_ = v___y_1126_;
v___y_1101_ = v___y_1127_;
goto v___jp_1091_;
}
}
}
else
{
lean_object* v___x_1141_; 
lean_dec(v___x_1129_);
v___x_1141_ = lean_box(0);
v___y_1092_ = v_o_1119_;
v_args_1093_ = v___x_1141_;
v___y_1094_ = v___y_1120_;
v___y_1095_ = v___y_1121_;
v___y_1096_ = v___y_1122_;
v___y_1097_ = v___y_1123_;
v___y_1098_ = v___y_1124_;
v___y_1099_ = v___y_1125_;
v___y_1100_ = v___y_1126_;
v___y_1101_ = v___y_1127_;
goto v___jp_1091_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimpTrace___lam__0___boxed(lean_object* v___x_1150_, lean_object* v_stx_1151_, lean_object* v___x_1152_, lean_object* v___x_1153_, lean_object* v___x_1154_, lean_object* v___x_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_){
_start:
{
uint8_t v___x_4825__boxed_1165_; uint8_t v___x_4829__boxed_1166_; lean_object* v_res_1167_; 
v___x_4825__boxed_1165_ = lean_unbox(v___x_1150_);
v___x_4829__boxed_1166_ = lean_unbox(v___x_1155_);
v_res_1167_ = l_Lean_Elab_Tactic_Conv_evalDSimpTrace___lam__0(v___x_4825__boxed_1165_, v_stx_1151_, v___x_1152_, v___x_1153_, v___x_1154_, v___x_4829__boxed_1166_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_);
lean_dec(v___y_1163_);
lean_dec_ref(v___y_1162_);
lean_dec(v___y_1161_);
lean_dec_ref(v___y_1160_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec(v_stx_1151_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimpTrace(lean_object* v_stx_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_){
_start:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; uint8_t v___x_1189_; uint8_t v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___y_1193_; lean_object* v___x_1194_; 
v___x_1185_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__0));
v___x_1186_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__1));
v___x_1187_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__2));
v___x_1188_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__1));
lean_inc(v_stx_1175_);
v___x_1189_ = l_Lean_Syntax_isOfKind(v_stx_1175_, v___x_1188_);
v___x_1190_ = 1;
v___x_1191_ = lean_box(v___x_1189_);
v___x_1192_ = lean_box(v___x_1190_);
v___y_1193_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalDSimpTrace___lam__0___boxed), 15, 6);
lean_closure_set(v___y_1193_, 0, v___x_1191_);
lean_closure_set(v___y_1193_, 1, v_stx_1175_);
lean_closure_set(v___y_1193_, 2, v___x_1185_);
lean_closure_set(v___y_1193_, 3, v___x_1186_);
lean_closure_set(v___y_1193_, 4, v___x_1187_);
lean_closure_set(v___y_1193_, 5, v___x_1192_);
v___x_1194_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___y_1193_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDSimpTrace___boxed(lean_object* v_stx_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_){
_start:
{
lean_object* v_res_1205_; 
v_res_1205_ = l_Lean_Elab_Tactic_Conv_evalDSimpTrace(v_stx_1195_, v_a_1196_, v_a_1197_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_);
lean_dec(v_a_1203_);
lean_dec_ref(v_a_1202_);
lean_dec(v_a_1201_);
lean_dec_ref(v_a_1200_);
lean_dec(v_a_1199_);
lean_dec_ref(v_a_1198_);
lean_dec(v_a_1197_);
lean_dec_ref(v_a_1196_);
return v_res_1205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1(){
_start:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1214_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1215_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__1));
v___x_1216_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__1));
v___x_1217_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalDSimpTrace___boxed), 10, 0);
v___x_1218_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1214_, v___x_1215_, v___x_1216_, v___x_1217_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___boxed(lean_object* v_a_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1();
return v_res_1220_;
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
