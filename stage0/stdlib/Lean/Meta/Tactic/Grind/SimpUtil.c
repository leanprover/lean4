// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.SimpUtil
// Imports: public import Lean.Meta.Tactic.Simp.Simproc import Lean.Meta.Tactic.Grind.MatchDiscrOnly import Lean.Meta.Tactic.Grind.ForallProp import Lean.Meta.Tactic.Grind.Arith.Simproc import Lean.Meta.Tactic.Simp.BuiltinSimprocs.List import Lean.Meta.Tactic.Simp.BuiltinSimprocs.Core import Lean.Meta.Tactic.Grind.Util import Lean.Meta.Sym.Util import Init.Grind.Norm public import Init.Grind.Config import Init.ByCases import Lean.Meta.Tactic.Simp.Main
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_unfoldReducibleStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isConstructorApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkNoConfusion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_Meta_mkEqFalse_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_mkOr(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinSimproc(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_getSEvalSimprocs___redArg(lean_object*);
lean_object* l_Lean_Meta_Simp_Simprocs_erase(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Simprocs_add(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_addSimpMatchDiscrsOnly(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_addPreMatchCondSimproc(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_addSimproc(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_addForallSimproc(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_PersistentHashMap_Node_isEmpty___redArg(lean_object*);
extern lean_object* l_Lean_Meta_Grind_normExt;
lean_object* l_Lean_Meta_SimpExtension_getTheorems___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_SimpTheorems_addDeclToUnfold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAnd(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_mkIntLit(lean_object*);
lean_object* l_Lean_mkIntAdd(lean_object*, lean_object*);
lean_object* l_Lean_mkIntLE(lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_mkNatAdd(lean_object*, lean_object*);
lean_object* l_Lean_mkNatLE(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isProp(lean_object*);
lean_object* l_Lean_mkBVar(lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSimpCongrTheorems___redArg(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Meta_Simp_mkContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinDSimproc(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_Grind_addNormTheorem(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_normSymExt;
lean_object* l_Lean_Meta_Grind_addNormSymDeclToUnfold(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_registerNormTheorems_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_registerNormTheorems_spec__3___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_registerNormTheorems_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_registerNormTheorems_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2_spec__2_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2_spec__2_spec__4___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2_spec__2_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2_spec__2_spec__4___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2_spec__2_spec__4___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2_spec__2_spec__4___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__2;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__3;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__4;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_registerNormTheorems_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_registerNormTheorems_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_registerNormTheorems_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_registerNormTheorems_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_registerNormTheorems___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Meta_Grind_registerNormTheorems___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_registerNormTheorems___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_registerNormTheorems___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "not_le_eq"};
static const lean_object* l_Lean_Meta_Grind_registerNormTheorems___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_registerNormTheorems___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_registerNormTheorems___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_registerNormTheorems___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_Grind_registerNormTheorems___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_registerNormTheorems___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_registerNormTheorems___closed__1_value),LEAN_SCALAR_PTR_LITERAL(235, 23, 140, 144, 182, 73, 3, 60)}};
static const lean_object* l_Lean_Meta_Grind_registerNormTheorems___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_registerNormTheorems___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_registerNormTheorems___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l_Lean_Meta_Grind_registerNormTheorems___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_registerNormTheorems___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_registerNormTheorems___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_registerNormTheorems___closed__3_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_registerNormTheorems___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_registerNormTheorems___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_registerNormTheorems___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 74, 162, 108, 148, 71, 165, 71)}};
static const lean_object* l_Lean_Meta_Grind_registerNormTheorems___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_registerNormTheorems___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_registerNormTheorems___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "GE"};
static const lean_object* l_Lean_Meta_Grind_registerNormTheorems___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_registerNormTheorems___closed__5_value;
static const lean_string_object l_Lean_Meta_Grind_registerNormTheorems___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ge"};
static const lean_object* l_Lean_Meta_Grind_registerNormTheorems___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_registerNormTheorems___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_registerNormTheorems___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_registerNormTheorems___closed__5_value),LEAN_SCALAR_PTR_LITERAL(74, 169, 4, 72, 62, 21, 91, 24)}};
static const lean_ctor_object l_Lean_Meta_Grind_registerNormTheorems___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_registerNormTheorems___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_registerNormTheorems___closed__6_value),LEAN_SCALAR_PTR_LITERAL(71, 88, 92, 156, 129, 215, 23, 77)}};
static const lean_object* l_Lean_Meta_Grind_registerNormTheorems___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_registerNormTheorems___closed__7_value;
static const lean_string_object l_Lean_Meta_Grind_registerNormTheorems___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "GT"};
static const lean_object* l_Lean_Meta_Grind_registerNormTheorems___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_registerNormTheorems___closed__8_value;
static const lean_string_object l_Lean_Meta_Grind_registerNormTheorems___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "gt"};
static const lean_object* l_Lean_Meta_Grind_registerNormTheorems___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_registerNormTheorems___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Grind_registerNormTheorems___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_registerNormTheorems___closed__8_value),LEAN_SCALAR_PTR_LITERAL(240, 16, 15, 58, 66, 186, 138, 31)}};
static const lean_ctor_object l_Lean_Meta_Grind_registerNormTheorems___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_registerNormTheorems___closed__10_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_registerNormTheorems___closed__9_value),LEAN_SCALAR_PTR_LITERAL(239, 75, 137, 103, 59, 22, 209, 130)}};
static const lean_object* l_Lean_Meta_Grind_registerNormTheorems___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_registerNormTheorems___closed__10_value;
static const lean_string_object l_Lean_Meta_Grind_registerNormTheorems___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cast"};
static const lean_object* l_Lean_Meta_Grind_registerNormTheorems___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_registerNormTheorems___closed__11_value;
static const lean_ctor_object l_Lean_Meta_Grind_registerNormTheorems___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_registerNormTheorems___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_Grind_registerNormTheorems___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_registerNormTheorems___closed__12_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_registerNormTheorems___closed__11_value),LEAN_SCALAR_PTR_LITERAL(19, 237, 167, 212, 100, 179, 19, 112)}};
static const lean_object* l_Lean_Meta_Grind_registerNormTheorems___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_registerNormTheorems___closed__12_value;
static const lean_string_object l_Lean_Meta_Grind_registerNormTheorems___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lean_Meta_Grind_registerNormTheorems___closed__13 = (const lean_object*)&l_Lean_Meta_Grind_registerNormTheorems___closed__13_value;
static const lean_string_object l_Lean_Meta_Grind_registerNormTheorems___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "xor"};
static const lean_object* l_Lean_Meta_Grind_registerNormTheorems___closed__14 = (const lean_object*)&l_Lean_Meta_Grind_registerNormTheorems___closed__14_value;
static const lean_ctor_object l_Lean_Meta_Grind_registerNormTheorems___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_registerNormTheorems___closed__13_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Meta_Grind_registerNormTheorems___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_registerNormTheorems___closed__15_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_registerNormTheorems___closed__14_value),LEAN_SCALAR_PTR_LITERAL(159, 35, 146, 118, 24, 65, 174, 144)}};
static const lean_object* l_Lean_Meta_Grind_registerNormTheorems___closed__15 = (const lean_object*)&l_Lean_Meta_Grind_registerNormTheorems___closed__15_value;
static const lean_string_object l_Lean_Meta_Grind_registerNormTheorems___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Ne"};
static const lean_object* l_Lean_Meta_Grind_registerNormTheorems___closed__16 = (const lean_object*)&l_Lean_Meta_Grind_registerNormTheorems___closed__16_value;
static const lean_ctor_object l_Lean_Meta_Grind_registerNormTheorems___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_registerNormTheorems___closed__16_value),LEAN_SCALAR_PTR_LITERAL(161, 247, 70, 70, 118, 145, 235, 92)}};
static const lean_object* l_Lean_Meta_Grind_registerNormTheorems___closed__17 = (const lean_object*)&l_Lean_Meta_Grind_registerNormTheorems___closed__17_value;
static const lean_string_object l_Lean_Meta_Grind_registerNormTheorems___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "`grind` normalization theorems have already been initialized"};
static const lean_object* l_Lean_Meta_Grind_registerNormTheorems___closed__18 = (const lean_object*)&l_Lean_Meta_Grind_registerNormTheorems___closed__18_value;
static lean_once_cell_t l_Lean_Meta_Grind_registerNormTheorems___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_registerNormTheorems___closed__19;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerNormTheorems(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerNormTheorems___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2_spec__2_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2_spec__2___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2_spec__2(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "and"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_registerNormTheorems___closed__13_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0_value),LEAN_SCALAR_PTR_LITERAL(160, 26, 8, 228, 104, 32, 82, 85)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "or"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_registerNormTheorems___closed__13_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__2_value),LEAN_SCALAR_PTR_LITERAL(90, 191, 239, 225, 113, 224, 109, 182)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "not"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_registerNormTheorems___closed__13_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__4_value),LEAN_SCALAR_PTR_LITERAL(208, 215, 171, 150, 192, 180, 249, 22)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "BEq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "beq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__6_value),LEAN_SCALAR_PTR_LITERAL(195, 188, 39, 55, 57, 152, 88, 223)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__7_value),LEAN_SCALAR_PTR_LITERAL(82, 52, 243, 194, 7, 226, 90, 135)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Decidable"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "decide"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__9_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__10_value),LEAN_SCALAR_PTR_LITERAL(16, 96, 65, 173, 152, 155, 4, 222)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__11_value;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___boxed(lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_simpEq___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_simpEq___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpEq___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpEq___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_registerNormTheorems___closed__13_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_simpEq___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_simpEq___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__5_value;
static const lean_string_object l_Lean_Meta_Grind_simpEq___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "flip_bool_eq"};
static const lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpEq___redArg___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpEq___redArg___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpEq___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__7_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(19, 65, 30, 112, 127, 84, 12, 55)}};
static const lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Grind_simpEq___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__8;
static const lean_string_object l_Lean_Meta_Grind_simpEq___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpEq___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__9_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__10_value;
static lean_once_cell_t l_Lean_Meta_Grind_simpEq___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__11;
static const lean_string_object l_Lean_Meta_Grind_simpEq___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__12_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpEq___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__12_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__13 = (const lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__13_value;
static lean_once_cell_t l_Lean_Meta_Grind_simpEq___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__14;
static const lean_string_object l_Lean_Meta_Grind_simpEq___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "eq_false_eq"};
static const lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__15 = (const lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__15_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpEq___redArg___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpEq___redArg___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__16_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpEq___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__16_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__15_value),LEAN_SCALAR_PTR_LITERAL(79, 24, 241, 157, 245, 218, 196, 160)}};
static const lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__16 = (const lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__16_value;
static lean_once_cell_t l_Lean_Meta_Grind_simpEq___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__17;
static const lean_string_object l_Lean_Meta_Grind_simpEq___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "eq_true_eq"};
static const lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__18 = (const lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__18_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpEq___redArg___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpEq___redArg___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__19_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpEq___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__19_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__18_value),LEAN_SCALAR_PTR_LITERAL(100, 12, 190, 92, 208, 172, 117, 90)}};
static const lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__19 = (const lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__19_value;
static lean_once_cell_t l_Lean_Meta_Grind_simpEq___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__20;
static const lean_string_object l_Lean_Meta_Grind_simpEq___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "eq_self"};
static const lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__21 = (const lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__21_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpEq___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__21_value),LEAN_SCALAR_PTR_LITERAL(224, 148, 98, 216, 254, 239, 13, 169)}};
static const lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__22 = (const lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__22_value;
static const lean_string_object l_Lean_Meta_Grind_simpEq___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__23 = (const lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__23_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpEq___redArg___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_registerNormTheorems___closed__13_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpEq___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__24_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__23_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__24 = (const lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__24_value;
static lean_once_cell_t l_Lean_Meta_Grind_simpEq___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__25;
static const lean_string_object l_Lean_Meta_Grind_simpEq___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "bool_eq_to_prop"};
static const lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__26 = (const lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__26_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpEq___redArg___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpEq___redArg___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__27_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpEq___redArg___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__27_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__26_value),LEAN_SCALAR_PTR_LITERAL(79, 89, 141, 151, 119, 96, 24, 167)}};
static const lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__27 = (const lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__27_value;
static lean_once_cell_t l_Lean_Meta_Grind_simpEq___redArg___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__28;
static const lean_string_object l_Lean_Meta_Grind_simpEq___redArg___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__29 = (const lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__29_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpEq___redArg___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_registerNormTheorems___closed__13_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpEq___redArg___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__30_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__29_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__30 = (const lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__30_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpEq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simpEq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13__value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(219, 117, 235, 93, 32, 23, 150, 114)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__2_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__4_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__4_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__4_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13____boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_simpDIte___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "dite"};
static const lean_object* l_Lean_Meta_Grind_simpDIte___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_simpDIte___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpDIte___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpDIte___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(137, 166, 197, 161, 68, 218, 116, 116)}};
static const lean_object* l_Lean_Meta_Grind_simpDIte___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_simpDIte___redArg___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_simpDIte___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ite"};
static const lean_object* l_Lean_Meta_Grind_simpDIte___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_simpDIte___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpDIte___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpDIte___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(15, 2, 151, 246, 61, 29, 192, 254)}};
static const lean_object* l_Lean_Meta_Grind_simpDIte___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_simpDIte___redArg___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_simpDIte___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "dite_eq_ite"};
static const lean_object* l_Lean_Meta_Grind_simpDIte___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_simpDIte___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpDIte___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpDIte___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(58, 201, 242, 159, 222, 42, 9, 203)}};
static const lean_object* l_Lean_Meta_Grind_simpDIte___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_simpDIte___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpDIte___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpDIte___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpDIte(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpDIte___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "simpDIte"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_14__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_14__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_14__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_14__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_14__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_14__value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_14__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(207, 95, 197, 147, 158, 94, 39, 166)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_14__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpDIte___redArg___closed__1_value),((lean_object*)(((size_t)(5) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_14__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*6, .m_other = 0, .m_tag = 246}, .m_size = 6, .m_capacity = 6, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_14__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_14__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_14_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_14____boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_pushNot___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Not"};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(185, 11, 203, 55, 27, 192, 137, 230)}};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_pushNot___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Exists"};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(65, 29, 48, 135, 199, 176, 149, 70)}};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_pushNot___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "not_forall"};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(133, 192, 91, 90, 91, 211, 131, 26)}};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__5_value;
static const lean_string_object l_Lean_Meta_Grind_pushNot___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "not_implies"};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__7_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(142, 189, 44, 77, 86, 197, 178, 67)}};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Grind_pushNot___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__8;
static const lean_string_object l_Lean_Meta_Grind_pushNot___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Or"};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__9_value),LEAN_SCALAR_PTR_LITERAL(34, 237, 162, 225, 217, 98, 205, 196)}};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__10_value;
static const lean_string_object l_Lean_Meta_Grind_pushNot___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "And"};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__11_value;
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__12_value;
static const lean_string_object l_Lean_Meta_Grind_pushNot___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LE"};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__13 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__13_value;
static const lean_string_object l_Lean_Meta_Grind_pushNot___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "le"};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__14 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__14_value;
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__13_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__15_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__14_value),LEAN_SCALAR_PTR_LITERAL(109, 14, 90, 172, 72, 170, 136, 101)}};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__15 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__15_value;
static const lean_string_object l_Lean_Meta_Grind_pushNot___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "not_ite"};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__16 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__16_value;
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__17_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__17_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__16_value),LEAN_SCALAR_PTR_LITERAL(132, 165, 120, 219, 71, 87, 242, 138)}};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__17 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__17_value;
static lean_once_cell_t l_Lean_Meta_Grind_pushNot___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__18;
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_registerNormTheorems___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__19 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__19_value;
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_registerNormTheorems___closed__3_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__20 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__20_value;
static lean_once_cell_t l_Lean_Meta_Grind_pushNot___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__21;
static lean_once_cell_t l_Lean_Meta_Grind_pushNot___redArg___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__22;
static lean_once_cell_t l_Lean_Meta_Grind_pushNot___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__23;
static lean_once_cell_t l_Lean_Meta_Grind_pushNot___redArg___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__24;
static lean_once_cell_t l_Lean_Meta_Grind_pushNot___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__25;
static lean_once_cell_t l_Lean_Meta_Grind_pushNot___redArg___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__26;
static const lean_string_object l_Lean_Meta_Grind_pushNot___redArg___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "not_eq_true"};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__27 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__27_value;
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_registerNormTheorems___closed__13_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__28_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__27_value),LEAN_SCALAR_PTR_LITERAL(225, 244, 63, 40, 164, 6, 8, 162)}};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__28 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__28_value;
static lean_once_cell_t l_Lean_Meta_Grind_pushNot___redArg___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__29;
static const lean_string_object l_Lean_Meta_Grind_pushNot___redArg___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "not_eq_false"};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__30 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__30_value;
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_registerNormTheorems___closed__13_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__31_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__30_value),LEAN_SCALAR_PTR_LITERAL(83, 226, 87, 91, 103, 177, 77, 30)}};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__31 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__31_value;
static lean_once_cell_t l_Lean_Meta_Grind_pushNot___redArg___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__32;
static const lean_string_object l_Lean_Meta_Grind_pushNot___redArg___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "not_eq_prop"};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__33 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__33_value;
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__34_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__34_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__34_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__34_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__33_value),LEAN_SCALAR_PTR_LITERAL(93, 9, 240, 16, 38, 110, 5, 203)}};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__34 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__34_value;
static lean_once_cell_t l_Lean_Meta_Grind_pushNot___redArg___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__35;
static lean_once_cell_t l_Lean_Meta_Grind_pushNot___redArg___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__36;
static const lean_string_object l_Lean_Meta_Grind_pushNot___redArg___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "not_and"};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__37 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__37_value;
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__38_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__38_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__38_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__38_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__37_value),LEAN_SCALAR_PTR_LITERAL(239, 225, 24, 71, 205, 142, 249, 26)}};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__38 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__38_value;
static lean_once_cell_t l_Lean_Meta_Grind_pushNot___redArg___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__39;
static lean_once_cell_t l_Lean_Meta_Grind_pushNot___redArg___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__40;
static const lean_string_object l_Lean_Meta_Grind_pushNot___redArg___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "not_or"};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__41 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__41_value;
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__42_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__42_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__42_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__42_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__41_value),LEAN_SCALAR_PTR_LITERAL(235, 74, 178, 162, 31, 3, 143, 38)}};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__42 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__42_value;
static lean_once_cell_t l_Lean_Meta_Grind_pushNot___redArg___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__43;
static const lean_string_object l_Lean_Meta_Grind_pushNot___redArg___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "a"};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__44 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__44_value;
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__44_value),LEAN_SCALAR_PTR_LITERAL(247, 80, 99, 121, 74, 33, 203, 108)}};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__45 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__45_value;
static lean_once_cell_t l_Lean_Meta_Grind_pushNot___redArg___closed__46_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__46;
static const lean_string_object l_Lean_Meta_Grind_pushNot___redArg___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "not_exists"};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__47 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__47_value;
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__48_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__48_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__48_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__48_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__47_value),LEAN_SCALAR_PTR_LITERAL(122, 84, 103, 56, 9, 28, 88, 199)}};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__48 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__48_value;
static const lean_string_object l_Lean_Meta_Grind_pushNot___redArg___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "not_not"};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__49 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__49_value;
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__50_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__50_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__50_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__50_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__49_value),LEAN_SCALAR_PTR_LITERAL(37, 13, 167, 116, 75, 172, 227, 19)}};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__50 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__50_value;
static lean_once_cell_t l_Lean_Meta_Grind_pushNot___redArg___closed__51_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__51;
static const lean_string_object l_Lean_Meta_Grind_pushNot___redArg___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "not_true"};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__52 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__52_value;
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__53_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__53_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__53_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__53_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__52_value),LEAN_SCALAR_PTR_LITERAL(189, 233, 184, 33, 201, 88, 141, 182)}};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__53 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__53_value;
static lean_once_cell_t l_Lean_Meta_Grind_pushNot___redArg___closed__54_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__54;
static lean_once_cell_t l_Lean_Meta_Grind_pushNot___redArg___closed__55_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__55;
static const lean_string_object l_Lean_Meta_Grind_pushNot___redArg___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "not_false"};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__56 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__56_value;
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__57_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__57_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__57_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__57_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__56_value),LEAN_SCALAR_PTR_LITERAL(32, 161, 26, 17, 134, 82, 22, 22)}};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__57 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__57_value;
static lean_once_cell_t l_Lean_Meta_Grind_pushNot___redArg___closed__58_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__58;
static lean_once_cell_t l_Lean_Meta_Grind_pushNot___redArg___closed__59_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__59;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNot___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNot___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNot(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNot___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2942474041____hygCtx___hyg_11__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "pushNot"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2942474041____hygCtx___hyg_11_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2942474041____hygCtx___hyg_11__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2942474041____hygCtx___hyg_11__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2942474041____hygCtx___hyg_11__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2942474041____hygCtx___hyg_11__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2942474041____hygCtx___hyg_11__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2942474041____hygCtx___hyg_11__value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2942474041____hygCtx___hyg_11__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2942474041____hygCtx___hyg_11__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2942474041____hygCtx___hyg_11__value),LEAN_SCALAR_PTR_LITERAL(189, 165, 185, 106, 181, 96, 32, 196)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2942474041____hygCtx___hyg_11_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2942474041____hygCtx___hyg_11__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2942474041____hygCtx___hyg_11__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2942474041____hygCtx___hyg_11_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2942474041____hygCtx___hyg_11__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2942474041____hygCtx___hyg_11__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2942474041____hygCtx___hyg_11__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2942474041____hygCtx___hyg_11_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2942474041____hygCtx___hyg_11__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2942474041____hygCtx___hyg_11_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2942474041____hygCtx___hyg_11____boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_simpOr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "or_swap13"};
static const lean_object* l_Lean_Meta_Grind_simpOr___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_simpOr___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpOr___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpOr___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpOr___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpOr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpOr___redArg___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpOr___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(240, 5, 180, 71, 127, 106, 169, 101)}};
static const lean_object* l_Lean_Meta_Grind_simpOr___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_simpOr___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Grind_simpOr___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpOr___redArg___closed__2;
static const lean_string_object l_Lean_Meta_Grind_simpOr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "or_swap12"};
static const lean_object* l_Lean_Meta_Grind_simpOr___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_simpOr___redArg___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpOr___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpOr___redArg___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpOr___redArg___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpOr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpOr___redArg___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpOr___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(122, 217, 194, 116, 8, 17, 212, 54)}};
static const lean_object* l_Lean_Meta_Grind_simpOr___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_simpOr___redArg___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Grind_simpOr___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpOr___redArg___closed__5;
static const lean_string_object l_Lean_Meta_Grind_simpOr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "or_true"};
static const lean_object* l_Lean_Meta_Grind_simpOr___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_simpOr___redArg___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpOr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpOr___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(42, 114, 114, 128, 39, 158, 116, 220)}};
static const lean_object* l_Lean_Meta_Grind_simpOr___redArg___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_simpOr___redArg___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Grind_simpOr___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpOr___redArg___closed__8;
static const lean_string_object l_Lean_Meta_Grind_simpOr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "or_false"};
static const lean_object* l_Lean_Meta_Grind_simpOr___redArg___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_simpOr___redArg___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpOr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpOr___redArg___closed__9_value),LEAN_SCALAR_PTR_LITERAL(153, 216, 196, 245, 126, 96, 113, 194)}};
static const lean_object* l_Lean_Meta_Grind_simpOr___redArg___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_simpOr___redArg___closed__10_value;
static lean_once_cell_t l_Lean_Meta_Grind_simpOr___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpOr___redArg___closed__11;
static const lean_string_object l_Lean_Meta_Grind_simpOr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "or_assoc"};
static const lean_object* l_Lean_Meta_Grind_simpOr___redArg___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_simpOr___redArg___closed__12_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpOr___redArg___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpOr___redArg___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpOr___redArg___closed__13_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpOr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpOr___redArg___closed__13_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpOr___redArg___closed__12_value),LEAN_SCALAR_PTR_LITERAL(177, 212, 104, 129, 180, 187, 236, 119)}};
static const lean_object* l_Lean_Meta_Grind_simpOr___redArg___closed__13 = (const lean_object*)&l_Lean_Meta_Grind_simpOr___redArg___closed__13_value;
static lean_once_cell_t l_Lean_Meta_Grind_simpOr___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpOr___redArg___closed__14;
static const lean_string_object l_Lean_Meta_Grind_simpOr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "true_or"};
static const lean_object* l_Lean_Meta_Grind_simpOr___redArg___closed__15 = (const lean_object*)&l_Lean_Meta_Grind_simpOr___redArg___closed__15_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpOr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpOr___redArg___closed__15_value),LEAN_SCALAR_PTR_LITERAL(151, 252, 187, 232, 224, 57, 40, 42)}};
static const lean_object* l_Lean_Meta_Grind_simpOr___redArg___closed__16 = (const lean_object*)&l_Lean_Meta_Grind_simpOr___redArg___closed__16_value;
static lean_once_cell_t l_Lean_Meta_Grind_simpOr___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpOr___redArg___closed__17;
static const lean_string_object l_Lean_Meta_Grind_simpOr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "false_or"};
static const lean_object* l_Lean_Meta_Grind_simpOr___redArg___closed__18 = (const lean_object*)&l_Lean_Meta_Grind_simpOr___redArg___closed__18_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpOr___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpOr___redArg___closed__18_value),LEAN_SCALAR_PTR_LITERAL(30, 122, 222, 214, 97, 236, 146, 97)}};
static const lean_object* l_Lean_Meta_Grind_simpOr___redArg___closed__19 = (const lean_object*)&l_Lean_Meta_Grind_simpOr___redArg___closed__19_value;
static lean_once_cell_t l_Lean_Meta_Grind_simpOr___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpOr___redArg___closed__20;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpOr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpOr___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpOr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpOr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_12__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simpOr"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_12_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_12__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_12__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_12__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_12__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_12__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_12__value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_12__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_12__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_12__value),LEAN_SCALAR_PTR_LITERAL(228, 202, 179, 118, 39, 223, 137, 162)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_12_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_12__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_12__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__10_value),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_12_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_12__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_12__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_12__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_12_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_12__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_12_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_12____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reduceCtorEqCheap___lam__0(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reduceCtorEqCheap___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_reduceCtorEqCheap___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l_Lean_Meta_Grind_reduceCtorEqCheap___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_reduceCtorEqCheap___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_reduceCtorEqCheap___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_reduceCtorEqCheap___closed__0_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l_Lean_Meta_Grind_reduceCtorEqCheap___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_reduceCtorEqCheap___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reduceCtorEqCheap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reduceCtorEqCheap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "reduceCtorEqCheap"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_14__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_14__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_14__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_14__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_14__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_14__value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_14__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(34, 125, 108, 13, 73, 108, 9, 106)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_14__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_14_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_14____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_unfoldReducibleSimproc___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_unfoldReducibleSimproc___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_unfoldReducibleSimproc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_unfoldReducibleSimproc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___lam__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_10_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___lam__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_10____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_10__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___lam__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_10____boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_10_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_10__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_10__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "unfoldReducibleSimproc"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_10_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_10__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_10__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_10__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_10__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_10__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_10__value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_10__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_10__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_10__value),LEAN_SCALAR_PTR_LITERAL(51, 93, 112, 81, 25, 192, 216, 250)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_10_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_10__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_10__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_10_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_10__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_10_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_10____boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_getSimprocs___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "List"};
static const lean_object* l_Lean_Meta_Grind_getSimprocs___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_getSimprocs___redArg___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_getSimprocs___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "reduceReplicate"};
static const lean_object* l_Lean_Meta_Grind_getSimprocs___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_getSimprocs___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_getSimprocs___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_getSimprocs___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Lean_Meta_Grind_getSimprocs___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getSimprocs___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getSimprocs___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 105, 104, 187, 83, 144, 177, 61)}};
static const lean_object* l_Lean_Meta_Grind_getSimprocs___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_getSimprocs___redArg___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_getSimprocs___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "reduceCtorEq"};
static const lean_object* l_Lean_Meta_Grind_getSimprocs___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_getSimprocs___redArg___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_getSimprocs___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_getSimprocs___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(241, 230, 128, 19, 70, 224, 61, 3)}};
static const lean_object* l_Lean_Meta_Grind_getSimprocs___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_getSimprocs___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimprocs___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimprocs___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimprocs(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimprocs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_addDeclToUnfold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_addDeclToUnfold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNormTheorems(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNormTheorems___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimpContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimpContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_registerNormTheorems_spec__3___redArg(lean_object* v_x_1_){
_start:
{
uint8_t v___x_2_; 
v___x_2_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_registerNormTheorems_spec__3___redArg___boxed(lean_object* v_x_3_){
_start:
{
uint8_t v_res_4_; lean_object* v_r_5_; 
v_res_4_ = l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_registerNormTheorems_spec__3___redArg(v_x_3_);
lean_dec_ref(v_x_3_);
v_r_5_ = lean_box(v_res_4_);
return v_r_5_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_registerNormTheorems_spec__3(lean_object* v_00_u03b2_6_, lean_object* v_x_7_){
_start:
{
uint8_t v___x_8_; 
v___x_8_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_registerNormTheorems_spec__3___boxed(lean_object* v_00_u03b2_9_, lean_object* v_x_10_){
_start:
{
uint8_t v_res_11_; lean_object* v_r_12_; 
v_res_11_ = l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_registerNormTheorems_spec__3(v_00_u03b2_9_, v_x_10_);
lean_dec_ref(v_x_10_);
v_r_12_ = lean_box(v_res_11_);
return v_r_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__4_spec__5(lean_object* v_msgData_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_){
_start:
{
lean_object* v___x_19_; lean_object* v_env_20_; uint8_t v___x_21_; lean_object* v_env_22_; lean_object* v___x_23_; lean_object* v_toCold_24_; lean_object* v_mctx_25_; lean_object* v_lctx_26_; lean_object* v_options_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_19_ = lean_st_ref_get(v___y_17_);
v_env_20_ = lean_ctor_get(v___x_19_, 0);
lean_inc_ref(v_env_20_);
lean_dec(v___x_19_);
v___x_21_ = 0;
v_env_22_ = l_Lean_Environment_setRecordingDeps(v_env_20_, v___x_21_);
v___x_23_ = lean_st_ref_get(v___y_15_);
v_toCold_24_ = lean_ctor_get(v___y_16_, 0);
v_mctx_25_ = lean_ctor_get(v___x_23_, 0);
lean_inc_ref(v_mctx_25_);
lean_dec(v___x_23_);
v_lctx_26_ = lean_ctor_get(v___y_14_, 2);
v_options_27_ = lean_ctor_get(v_toCold_24_, 2);
lean_inc_ref(v_options_27_);
lean_inc_ref(v_lctx_26_);
v___x_28_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_28_, 0, v_env_22_);
lean_ctor_set(v___x_28_, 1, v_mctx_25_);
lean_ctor_set(v___x_28_, 2, v_lctx_26_);
lean_ctor_set(v___x_28_, 3, v_options_27_);
v___x_29_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_29_, 0, v___x_28_);
lean_ctor_set(v___x_29_, 1, v_msgData_13_);
v___x_30_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_30_, 0, v___x_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__4_spec__5___boxed(lean_object* v_msgData_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__4_spec__5(v_msgData_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_);
lean_dec(v___y_35_);
lean_dec_ref(v___y_34_);
lean_dec(v___y_33_);
lean_dec_ref(v___y_32_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__4___redArg(lean_object* v_msg_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_){
_start:
{
lean_object* v_ref_44_; lean_object* v___x_45_; lean_object* v_a_46_; lean_object* v___x_48_; uint8_t v_isShared_49_; uint8_t v_isSharedCheck_54_; 
v_ref_44_ = lean_ctor_get(v___y_41_, 2);
v___x_45_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__4_spec__5(v_msg_38_, v___y_39_, v___y_40_, v___y_41_, v___y_42_);
v_a_46_ = lean_ctor_get(v___x_45_, 0);
v_isSharedCheck_54_ = !lean_is_exclusive(v___x_45_);
if (v_isSharedCheck_54_ == 0)
{
v___x_48_ = v___x_45_;
v_isShared_49_ = v_isSharedCheck_54_;
goto v_resetjp_47_;
}
else
{
lean_inc(v_a_46_);
lean_dec(v___x_45_);
v___x_48_ = lean_box(0);
v_isShared_49_ = v_isSharedCheck_54_;
goto v_resetjp_47_;
}
v_resetjp_47_:
{
lean_object* v___x_50_; lean_object* v___x_52_; 
lean_inc(v_ref_44_);
v___x_50_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_50_, 0, v_ref_44_);
lean_ctor_set(v___x_50_, 1, v_a_46_);
if (v_isShared_49_ == 0)
{
lean_ctor_set_tag(v___x_48_, 1);
lean_ctor_set(v___x_48_, 0, v___x_50_);
v___x_52_ = v___x_48_;
goto v_reusejp_51_;
}
else
{
lean_object* v_reuseFailAlloc_53_; 
v_reuseFailAlloc_53_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_53_, 0, v___x_50_);
v___x_52_ = v_reuseFailAlloc_53_;
goto v_reusejp_51_;
}
v_reusejp_51_:
{
return v___x_52_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__4___redArg___boxed(lean_object* v_msg_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l_Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__4___redArg(v_msg_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
lean_dec(v___y_59_);
lean_dec_ref(v___y_58_);
lean_dec(v___y_57_);
lean_dec_ref(v___y_56_);
return v_res_61_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2_spec__2_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_62_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2_spec__2_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_63_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2_spec__2_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2_spec__2_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2_spec__2_spec__4___redArg___closed__0);
v___x_64_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_64_, 0, v___x_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2_spec__2_spec__4___redArg(){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2_spec__2_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2_spec__2_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2_spec__2_spec__4___redArg___closed__1);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2_spec__2_spec__4___redArg___boxed(lean_object* v___dummy_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2_spec__2_spec__4___redArg();
return v_res_68_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_69_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2_spec__2_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2_spec__2_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2_spec__2_spec__4___redArg___closed__0);
v___x_70_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_70_, 0, v___x_69_);
return v___x_70_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_71_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__0);
v___x_72_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_72_, 0, v___x_71_);
lean_ctor_set(v___x_72_, 1, v___x_71_);
return v___x_72_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2_spec__2_spec__4___redArg();
return v___x_73_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_74_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__0);
v___x_75_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_75_, 0, v___x_74_);
lean_ctor_set(v___x_75_, 1, v___x_74_);
return v___x_75_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_76_ = lean_unsigned_to_nat(0u);
v___x_77_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__0);
v___x_78_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_78_, 0, v___x_77_);
lean_ctor_set(v___x_78_, 1, v___x_77_);
lean_ctor_set(v___x_78_, 2, v___x_76_);
return v___x_78_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_79_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__4, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__4_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__4);
v___x_80_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__3);
v___x_81_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__0);
v___x_82_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__2);
v___x_83_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_83_, 0, v___x_82_);
lean_ctor_set(v___x_83_, 1, v___x_81_);
lean_ctor_set(v___x_83_, 2, v___x_80_);
lean_ctor_set(v___x_83_, 3, v___x_81_);
lean_ctor_set(v___x_83_, 4, v___x_81_);
lean_ctor_set(v___x_83_, 5, v___x_81_);
lean_ctor_set(v___x_83_, 6, v___x_81_);
lean_ctor_set(v___x_83_, 7, v___x_79_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg(lean_object* v_ext_84_, lean_object* v_b_85_, uint8_t v_kind_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_){
_start:
{
lean_object* v_toCold_91_; lean_object* v_currNamespace_92_; lean_object* v___x_93_; lean_object* v_env_94_; lean_object* v_nextMacroScope_95_; lean_object* v_ngen_96_; lean_object* v_auxDeclNGen_97_; lean_object* v_traceState_98_; lean_object* v_recordedDeps_99_; lean_object* v_messages_100_; lean_object* v_infoState_101_; lean_object* v_snapshotTasks_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_129_; 
v_toCold_91_ = lean_ctor_get(v___y_88_, 0);
v_currNamespace_92_ = lean_ctor_get(v_toCold_91_, 4);
v___x_93_ = lean_st_ref_take(v___y_89_);
v_env_94_ = lean_ctor_get(v___x_93_, 0);
v_nextMacroScope_95_ = lean_ctor_get(v___x_93_, 1);
v_ngen_96_ = lean_ctor_get(v___x_93_, 2);
v_auxDeclNGen_97_ = lean_ctor_get(v___x_93_, 3);
v_traceState_98_ = lean_ctor_get(v___x_93_, 4);
v_recordedDeps_99_ = lean_ctor_get(v___x_93_, 6);
v_messages_100_ = lean_ctor_get(v___x_93_, 7);
v_infoState_101_ = lean_ctor_get(v___x_93_, 8);
v_snapshotTasks_102_ = lean_ctor_get(v___x_93_, 9);
v_isSharedCheck_129_ = !lean_is_exclusive(v___x_93_);
if (v_isSharedCheck_129_ == 0)
{
lean_object* v_unused_130_; 
v_unused_130_ = lean_ctor_get(v___x_93_, 5);
lean_dec(v_unused_130_);
v___x_104_ = v___x_93_;
v_isShared_105_ = v_isSharedCheck_129_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_snapshotTasks_102_);
lean_inc(v_infoState_101_);
lean_inc(v_messages_100_);
lean_inc(v_recordedDeps_99_);
lean_inc(v_traceState_98_);
lean_inc(v_auxDeclNGen_97_);
lean_inc(v_ngen_96_);
lean_inc(v_nextMacroScope_95_);
lean_inc(v_env_94_);
lean_dec(v___x_93_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_129_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_109_; 
lean_inc(v_currNamespace_92_);
v___x_106_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_94_, v_ext_84_, v_b_85_, v_kind_86_, v_currNamespace_92_);
v___x_107_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__1);
if (v_isShared_105_ == 0)
{
lean_ctor_set(v___x_104_, 5, v___x_107_);
lean_ctor_set(v___x_104_, 0, v___x_106_);
v___x_109_ = v___x_104_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v___x_106_);
lean_ctor_set(v_reuseFailAlloc_128_, 1, v_nextMacroScope_95_);
lean_ctor_set(v_reuseFailAlloc_128_, 2, v_ngen_96_);
lean_ctor_set(v_reuseFailAlloc_128_, 3, v_auxDeclNGen_97_);
lean_ctor_set(v_reuseFailAlloc_128_, 4, v_traceState_98_);
lean_ctor_set(v_reuseFailAlloc_128_, 5, v___x_107_);
lean_ctor_set(v_reuseFailAlloc_128_, 6, v_recordedDeps_99_);
lean_ctor_set(v_reuseFailAlloc_128_, 7, v_messages_100_);
lean_ctor_set(v_reuseFailAlloc_128_, 8, v_infoState_101_);
lean_ctor_set(v_reuseFailAlloc_128_, 9, v_snapshotTasks_102_);
v___x_109_ = v_reuseFailAlloc_128_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v_mctx_112_; lean_object* v_zetaDeltaFVarIds_113_; lean_object* v_postponed_114_; lean_object* v_diag_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_126_; 
v___x_110_ = lean_st_ref_put(v___y_89_, v___x_109_);
v___x_111_ = lean_st_ref_take(v___y_87_);
v_mctx_112_ = lean_ctor_get(v___x_111_, 0);
v_zetaDeltaFVarIds_113_ = lean_ctor_get(v___x_111_, 2);
v_postponed_114_ = lean_ctor_get(v___x_111_, 3);
v_diag_115_ = lean_ctor_get(v___x_111_, 4);
v_isSharedCheck_126_ = !lean_is_exclusive(v___x_111_);
if (v_isSharedCheck_126_ == 0)
{
lean_object* v_unused_127_; 
v_unused_127_ = lean_ctor_get(v___x_111_, 1);
lean_dec(v_unused_127_);
v___x_117_ = v___x_111_;
v_isShared_118_ = v_isSharedCheck_126_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_diag_115_);
lean_inc(v_postponed_114_);
lean_inc(v_zetaDeltaFVarIds_113_);
lean_inc(v_mctx_112_);
lean_dec(v___x_111_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_126_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_122_; 
v___x_119_ = lean_box(0);
v___x_120_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__5, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__5_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__5);
if (v_isShared_118_ == 0)
{
lean_ctor_set(v___x_117_, 1, v___x_120_);
v___x_122_ = v___x_117_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v_mctx_112_);
lean_ctor_set(v_reuseFailAlloc_125_, 1, v___x_120_);
lean_ctor_set(v_reuseFailAlloc_125_, 2, v_zetaDeltaFVarIds_113_);
lean_ctor_set(v_reuseFailAlloc_125_, 3, v_postponed_114_);
lean_ctor_set(v_reuseFailAlloc_125_, 4, v_diag_115_);
v___x_122_ = v_reuseFailAlloc_125_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_123_ = lean_st_ref_put(v___y_87_, v___x_122_);
v___x_124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_124_, 0, v___x_119_);
return v___x_124_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___boxed(lean_object* v_ext_131_, lean_object* v_b_132_, lean_object* v_kind_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_){
_start:
{
uint8_t v_kind_boxed_138_; lean_object* v_res_139_; 
v_kind_boxed_138_ = lean_unbox(v_kind_133_);
v_res_139_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg(v_ext_131_, v_b_132_, v_kind_boxed_138_, v___y_134_, v___y_135_, v___y_136_);
lean_dec(v___y_136_);
lean_dec_ref(v___y_135_);
lean_dec(v___y_134_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_registerNormTheorems_spec__1(lean_object* v_as_140_, size_t v_sz_141_, size_t v_i_142_, lean_object* v_b_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_){
_start:
{
uint8_t v___x_149_; 
v___x_149_ = lean_usize_dec_lt(v_i_142_, v_sz_141_);
if (v___x_149_ == 0)
{
lean_object* v___x_150_; 
v___x_150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_150_, 0, v_b_143_);
return v___x_150_;
}
else
{
lean_object* v___x_151_; lean_object* v_a_152_; uint8_t v___x_153_; uint8_t v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_151_ = lean_box(0);
v_a_152_ = lean_array_uget_borrowed(v_as_140_, v_i_142_);
v___x_153_ = 0;
v___x_154_ = 0;
v___x_155_ = lean_unsigned_to_nat(1000u);
lean_inc(v_a_152_);
v___x_156_ = l_Lean_Meta_Grind_addNormTheorem(v_a_152_, v___x_149_, v___x_153_, v___x_154_, v___x_155_, v___y_144_, v___y_145_, v___y_146_, v___y_147_);
if (lean_obj_tag(v___x_156_) == 0)
{
size_t v___x_157_; size_t v___x_158_; 
lean_dec_ref_known(v___x_156_, 1);
v___x_157_ = ((size_t)1ULL);
v___x_158_ = lean_usize_add(v_i_142_, v___x_157_);
v_i_142_ = v___x_158_;
v_b_143_ = v___x_151_;
goto _start;
}
else
{
return v___x_156_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_registerNormTheorems_spec__1___boxed(lean_object* v_as_160_, lean_object* v_sz_161_, lean_object* v_i_162_, lean_object* v_b_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_){
_start:
{
size_t v_sz_boxed_169_; size_t v_i_boxed_170_; lean_object* v_res_171_; 
v_sz_boxed_169_ = lean_unbox_usize(v_sz_161_);
lean_dec(v_sz_161_);
v_i_boxed_170_ = lean_unbox_usize(v_i_162_);
lean_dec(v_i_162_);
v_res_171_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_registerNormTheorems_spec__1(v_as_160_, v_sz_boxed_169_, v_i_boxed_170_, v_b_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_);
lean_dec(v___y_167_);
lean_dec_ref(v___y_166_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
lean_dec_ref(v_as_160_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_registerNormTheorems_spec__0(lean_object* v_as_172_, size_t v_sz_173_, size_t v_i_174_, lean_object* v_b_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_){
_start:
{
uint8_t v___x_181_; 
v___x_181_ = lean_usize_dec_lt(v_i_174_, v_sz_173_);
if (v___x_181_ == 0)
{
lean_object* v___x_182_; 
v___x_182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_182_, 0, v_b_175_);
return v___x_182_;
}
else
{
lean_object* v___x_183_; lean_object* v_a_184_; uint8_t v___x_185_; uint8_t v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_183_ = lean_box(0);
v_a_184_ = lean_array_uget_borrowed(v_as_172_, v_i_174_);
v___x_185_ = 0;
v___x_186_ = 0;
v___x_187_ = lean_unsigned_to_nat(1000u);
lean_inc(v_a_184_);
v___x_188_ = l_Lean_Meta_Grind_addNormTheorem(v_a_184_, v___x_185_, v___x_185_, v___x_186_, v___x_187_, v___y_176_, v___y_177_, v___y_178_, v___y_179_);
if (lean_obj_tag(v___x_188_) == 0)
{
size_t v___x_189_; size_t v___x_190_; 
lean_dec_ref_known(v___x_188_, 1);
v___x_189_ = ((size_t)1ULL);
v___x_190_ = lean_usize_add(v_i_174_, v___x_189_);
v_i_174_ = v___x_190_;
v_b_175_ = v___x_183_;
goto _start;
}
else
{
return v___x_188_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_registerNormTheorems_spec__0___boxed(lean_object* v_as_192_, lean_object* v_sz_193_, lean_object* v_i_194_, lean_object* v_b_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_){
_start:
{
size_t v_sz_boxed_201_; size_t v_i_boxed_202_; lean_object* v_res_203_; 
v_sz_boxed_201_ = lean_unbox_usize(v_sz_193_);
lean_dec(v_sz_193_);
v_i_boxed_202_ = lean_unbox_usize(v_i_194_);
lean_dec(v_i_194_);
v_res_203_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_registerNormTheorems_spec__0(v_as_192_, v_sz_boxed_201_, v_i_boxed_202_, v_b_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_);
lean_dec(v___y_199_);
lean_dec_ref(v___y_198_);
lean_dec(v___y_197_);
lean_dec_ref(v___y_196_);
lean_dec_ref(v_as_192_);
return v_res_203_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_registerNormTheorems___closed__19(void){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_236_ = ((lean_object*)(l_Lean_Meta_Grind_registerNormTheorems___closed__18));
v___x_237_ = l_Lean_stringToMessageData(v___x_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerNormTheorems(lean_object* v_preDeclNames_238_, lean_object* v_postDeclNames_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_){
_start:
{
lean_object* v___y_246_; lean_object* v___y_247_; lean_object* v___y_248_; lean_object* v___y_249_; lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_308_ = l_Lean_Meta_Grind_normExt;
v___x_309_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v___x_308_, v_a_243_);
if (lean_obj_tag(v___x_309_) == 0)
{
lean_object* v_a_310_; lean_object* v_lemmaNames_311_; uint8_t v___x_312_; 
v_a_310_ = lean_ctor_get(v___x_309_, 0);
lean_inc(v_a_310_);
lean_dec_ref_known(v___x_309_, 1);
v_lemmaNames_311_ = lean_ctor_get(v_a_310_, 2);
lean_inc_ref(v_lemmaNames_311_);
lean_dec(v_a_310_);
v___x_312_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_lemmaNames_311_);
lean_dec_ref(v_lemmaNames_311_);
if (v___x_312_ == 0)
{
lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_313_ = lean_obj_once(&l_Lean_Meta_Grind_registerNormTheorems___closed__19, &l_Lean_Meta_Grind_registerNormTheorems___closed__19_once, _init_l_Lean_Meta_Grind_registerNormTheorems___closed__19);
v___x_314_ = l_Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__4___redArg(v___x_313_, v_a_240_, v_a_241_, v_a_242_, v_a_243_);
return v___x_314_;
}
else
{
v___y_246_ = v_a_240_;
v___y_247_ = v_a_241_;
v___y_248_ = v_a_242_;
v___y_249_ = v_a_243_;
goto v___jp_245_;
}
}
else
{
lean_object* v_a_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_322_; 
v_a_315_ = lean_ctor_get(v___x_309_, 0);
v_isSharedCheck_322_ = !lean_is_exclusive(v___x_309_);
if (v_isSharedCheck_322_ == 0)
{
v___x_317_ = v___x_309_;
v_isShared_318_ = v_isSharedCheck_322_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_a_315_);
lean_dec(v___x_309_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_322_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v___x_320_; 
if (v_isShared_318_ == 0)
{
v___x_320_ = v___x_317_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v_a_315_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
return v___x_320_;
}
}
}
v___jp_245_:
{
lean_object* v___x_250_; size_t v_sz_251_; size_t v___x_252_; lean_object* v___x_253_; 
v___x_250_ = lean_box(0);
v_sz_251_ = lean_array_size(v_preDeclNames_238_);
v___x_252_ = ((size_t)0ULL);
v___x_253_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_registerNormTheorems_spec__0(v_preDeclNames_238_, v_sz_251_, v___x_252_, v___x_250_, v___y_246_, v___y_247_, v___y_248_, v___y_249_);
if (lean_obj_tag(v___x_253_) == 0)
{
size_t v_sz_254_; lean_object* v___x_255_; 
lean_dec_ref_known(v___x_253_, 1);
v_sz_254_ = lean_array_size(v_postDeclNames_239_);
v___x_255_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_registerNormTheorems_spec__1(v_postDeclNames_239_, v_sz_254_, v___x_252_, v___x_250_, v___y_246_, v___y_247_, v___y_248_, v___y_249_);
if (lean_obj_tag(v___x_255_) == 0)
{
lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_306_; 
v_isSharedCheck_306_ = !lean_is_exclusive(v___x_255_);
if (v_isSharedCheck_306_ == 0)
{
lean_object* v_unused_307_; 
v_unused_307_ = lean_ctor_get(v___x_255_, 0);
lean_dec(v_unused_307_);
v___x_257_ = v___x_255_;
v_isShared_258_ = v_isSharedCheck_306_;
goto v_resetjp_256_;
}
else
{
lean_dec(v___x_255_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_306_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_259_ = ((lean_object*)(l_Lean_Meta_Grind_registerNormTheorems___closed__2));
v___x_260_ = l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(v___x_259_, v___y_246_, v___y_247_, v___y_248_, v___y_249_);
if (lean_obj_tag(v___x_260_) == 0)
{
lean_object* v_a_261_; lean_object* v___x_262_; lean_object* v___x_264_; 
v_a_261_ = lean_ctor_get(v___x_260_, 0);
lean_inc(v_a_261_);
lean_dec_ref_known(v___x_260_, 1);
v___x_262_ = l_Lean_Meta_Grind_normSymExt;
if (v_isShared_258_ == 0)
{
lean_ctor_set(v___x_257_, 0, v_a_261_);
v___x_264_ = v___x_257_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_a_261_);
v___x_264_ = v_reuseFailAlloc_297_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
uint8_t v___x_265_; lean_object* v___x_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_295_; 
v___x_265_ = 0;
v___x_266_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg(v___x_262_, v___x_264_, v___x_265_, v___y_247_, v___y_248_, v___y_249_);
v_isSharedCheck_295_ = !lean_is_exclusive(v___x_266_);
if (v_isSharedCheck_295_ == 0)
{
lean_object* v_unused_296_; 
v_unused_296_ = lean_ctor_get(v___x_266_, 0);
lean_dec(v_unused_296_);
v___x_268_ = v___x_266_;
v_isShared_269_ = v_isSharedCheck_295_;
goto v_resetjp_267_;
}
else
{
lean_dec(v___x_266_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_295_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_270_ = ((lean_object*)(l_Lean_Meta_Grind_registerNormTheorems___closed__4));
v___x_271_ = l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(v___x_270_, v___y_246_, v___y_247_, v___y_248_, v___y_249_);
if (lean_obj_tag(v___x_271_) == 0)
{
lean_object* v_a_272_; lean_object* v___x_274_; 
v_a_272_ = lean_ctor_get(v___x_271_, 0);
lean_inc(v_a_272_);
lean_dec_ref_known(v___x_271_, 1);
if (v_isShared_269_ == 0)
{
lean_ctor_set(v___x_268_, 0, v_a_272_);
v___x_274_ = v___x_268_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v_a_272_);
v___x_274_ = v_reuseFailAlloc_286_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_275_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg(v___x_262_, v___x_274_, v___x_265_, v___y_247_, v___y_248_, v___y_249_);
lean_dec_ref(v___x_275_);
v___x_276_ = ((lean_object*)(l_Lean_Meta_Grind_registerNormTheorems___closed__7));
v___x_277_ = l_Lean_Meta_Grind_addNormSymDeclToUnfold(v___x_276_, v___x_265_, v___y_246_, v___y_247_, v___y_248_, v___y_249_);
if (lean_obj_tag(v___x_277_) == 0)
{
lean_object* v___x_278_; lean_object* v___x_279_; 
lean_dec_ref_known(v___x_277_, 1);
v___x_278_ = ((lean_object*)(l_Lean_Meta_Grind_registerNormTheorems___closed__10));
v___x_279_ = l_Lean_Meta_Grind_addNormSymDeclToUnfold(v___x_278_, v___x_265_, v___y_246_, v___y_247_, v___y_248_, v___y_249_);
if (lean_obj_tag(v___x_279_) == 0)
{
lean_object* v___x_280_; lean_object* v___x_281_; 
lean_dec_ref_known(v___x_279_, 1);
v___x_280_ = ((lean_object*)(l_Lean_Meta_Grind_registerNormTheorems___closed__12));
v___x_281_ = l_Lean_Meta_Grind_addNormSymDeclToUnfold(v___x_280_, v___x_265_, v___y_246_, v___y_247_, v___y_248_, v___y_249_);
if (lean_obj_tag(v___x_281_) == 0)
{
lean_object* v___x_282_; lean_object* v___x_283_; 
lean_dec_ref_known(v___x_281_, 1);
v___x_282_ = ((lean_object*)(l_Lean_Meta_Grind_registerNormTheorems___closed__15));
v___x_283_ = l_Lean_Meta_Grind_addNormSymDeclToUnfold(v___x_282_, v___x_265_, v___y_246_, v___y_247_, v___y_248_, v___y_249_);
if (lean_obj_tag(v___x_283_) == 0)
{
lean_object* v___x_284_; lean_object* v___x_285_; 
lean_dec_ref_known(v___x_283_, 1);
v___x_284_ = ((lean_object*)(l_Lean_Meta_Grind_registerNormTheorems___closed__17));
v___x_285_ = l_Lean_Meta_Grind_addNormSymDeclToUnfold(v___x_284_, v___x_265_, v___y_246_, v___y_247_, v___y_248_, v___y_249_);
return v___x_285_;
}
else
{
return v___x_283_;
}
}
else
{
return v___x_281_;
}
}
else
{
return v___x_279_;
}
}
else
{
return v___x_277_;
}
}
}
else
{
lean_object* v_a_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_294_; 
lean_del_object(v___x_268_);
v_a_287_ = lean_ctor_get(v___x_271_, 0);
v_isSharedCheck_294_ = !lean_is_exclusive(v___x_271_);
if (v_isSharedCheck_294_ == 0)
{
v___x_289_ = v___x_271_;
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_a_287_);
lean_dec(v___x_271_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_292_; 
if (v_isShared_290_ == 0)
{
v___x_292_ = v___x_289_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_a_287_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
}
}
}
else
{
lean_object* v_a_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_305_; 
lean_del_object(v___x_257_);
v_a_298_ = lean_ctor_get(v___x_260_, 0);
v_isSharedCheck_305_ = !lean_is_exclusive(v___x_260_);
if (v_isSharedCheck_305_ == 0)
{
v___x_300_ = v___x_260_;
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_a_298_);
lean_dec(v___x_260_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_303_; 
if (v_isShared_301_ == 0)
{
v___x_303_ = v___x_300_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_a_298_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
return v___x_303_;
}
}
}
}
}
else
{
return v___x_255_;
}
}
else
{
return v___x_253_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerNormTheorems___boxed(lean_object* v_preDeclNames_323_, lean_object* v_postDeclNames_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Lean_Meta_Grind_registerNormTheorems(v_preDeclNames_323_, v_postDeclNames_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_);
lean_dec(v_a_328_);
lean_dec_ref(v_a_327_);
lean_dec(v_a_326_);
lean_dec_ref(v_a_325_);
lean_dec_ref(v_postDeclNames_324_);
lean_dec_ref(v_preDeclNames_323_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2(lean_object* v_00_u03b1_331_, lean_object* v_00_u03b2_332_, lean_object* v_00_u03c3_333_, lean_object* v_ext_334_, lean_object* v_b_335_, uint8_t v_kind_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
lean_object* v___x_342_; 
v___x_342_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg(v_ext_334_, v_b_335_, v_kind_336_, v___y_338_, v___y_339_, v___y_340_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___boxed(lean_object* v_00_u03b1_343_, lean_object* v_00_u03b2_344_, lean_object* v_00_u03c3_345_, lean_object* v_ext_346_, lean_object* v_b_347_, lean_object* v_kind_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_){
_start:
{
uint8_t v_kind_boxed_354_; lean_object* v_res_355_; 
v_kind_boxed_354_ = lean_unbox(v_kind_348_);
v_res_355_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2(v_00_u03b1_343_, v_00_u03b2_344_, v_00_u03c3_345_, v_ext_346_, v_b_347_, v_kind_boxed_354_, v___y_349_, v___y_350_, v___y_351_, v___y_352_);
lean_dec(v___y_352_);
lean_dec_ref(v___y_351_);
lean_dec(v___y_350_);
lean_dec_ref(v___y_349_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__4(lean_object* v_00_u03b1_356_, lean_object* v_msg_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = l_Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__4___redArg(v_msg_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__4___boxed(lean_object* v_00_u03b1_364_, lean_object* v_msg_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__4(v_00_u03b1_364_, v_msg_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_);
lean_dec(v___y_369_);
lean_dec_ref(v___y_368_);
lean_dec(v___y_367_);
lean_dec_ref(v___y_366_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2_spec__2_spec__4(lean_object* v_00_u03b2_372_){
_start:
{
lean_object* v___x_373_; 
v___x_373_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__2);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2_spec__2___redArg(){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__2);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2_spec__2___redArg___boxed(lean_object* v___dummy_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l_Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2_spec__2___redArg();
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2_spec__2(lean_object* v_00_u03b2_378_){
_start:
{
lean_object* v___x_379_; 
v___x_379_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__2);
return v___x_379_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget(lean_object* v_declName_402_){
_start:
{
lean_object* v___x_403_; uint8_t v___x_404_; 
v___x_403_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__1));
v___x_404_ = lean_name_eq(v_declName_402_, v___x_403_);
if (v___x_404_ == 0)
{
lean_object* v___x_405_; uint8_t v___x_406_; 
v___x_405_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__3));
v___x_406_ = lean_name_eq(v_declName_402_, v___x_405_);
if (v___x_406_ == 0)
{
lean_object* v___x_407_; uint8_t v___x_408_; 
v___x_407_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__5));
v___x_408_ = lean_name_eq(v_declName_402_, v___x_407_);
if (v___x_408_ == 0)
{
lean_object* v___x_409_; uint8_t v___x_410_; 
v___x_409_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__8));
v___x_410_ = lean_name_eq(v_declName_402_, v___x_409_);
if (v___x_410_ == 0)
{
lean_object* v___x_411_; uint8_t v___x_412_; 
v___x_411_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__11));
v___x_412_ = lean_name_eq(v_declName_402_, v___x_411_);
return v___x_412_;
}
else
{
return v___x_410_;
}
}
else
{
return v___x_408_;
}
}
else
{
return v___x_406_;
}
}
else
{
return v___x_404_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___boxed(lean_object* v_declName_413_){
_start:
{
uint8_t v_res_414_; lean_object* v_r_415_; 
v_res_414_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget(v_declName_413_);
lean_dec(v_declName_413_);
v_r_415_ = lean_box(v_res_414_);
return v_r_415_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpEq___redArg___closed__8(void){
_start:
{
lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_430_ = lean_box(0);
v___x_431_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__7));
v___x_432_ = l_Lean_mkConst(v___x_431_, v___x_430_);
return v___x_432_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpEq___redArg___closed__11(void){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_436_ = lean_box(0);
v___x_437_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__10));
v___x_438_ = l_Lean_mkConst(v___x_437_, v___x_436_);
return v___x_438_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpEq___redArg___closed__14(void){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_442_ = lean_box(0);
v___x_443_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__13));
v___x_444_ = l_Lean_mkConst(v___x_443_, v___x_442_);
return v___x_444_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpEq___redArg___closed__17(void){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_450_ = lean_box(0);
v___x_451_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__16));
v___x_452_ = l_Lean_mkConst(v___x_451_, v___x_450_);
return v___x_452_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpEq___redArg___closed__20(void){
_start:
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_458_ = lean_box(0);
v___x_459_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__19));
v___x_460_ = l_Lean_mkConst(v___x_459_, v___x_458_);
return v___x_460_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpEq___redArg___closed__25(void){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_468_ = lean_box(0);
v___x_469_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__24));
v___x_470_ = l_Lean_mkConst(v___x_469_, v___x_468_);
return v___x_470_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpEq___redArg___closed__28(void){
_start:
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_476_ = lean_box(0);
v___x_477_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__27));
v___x_478_ = l_Lean_mkConst(v___x_477_, v___x_476_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpEq___redArg(lean_object* v_e_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_){
_start:
{
lean_object* v___x_492_; 
v___x_492_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_483_, v_a_485_);
if (lean_obj_tag(v___x_492_) == 0)
{
lean_object* v_a_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_614_; 
v_a_493_ = lean_ctor_get(v___x_492_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_614_ == 0)
{
v___x_495_ = v___x_492_;
v_isShared_496_ = v_isSharedCheck_614_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_a_493_);
lean_dec(v___x_492_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_614_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_497_; uint8_t v___x_498_; 
v___x_497_ = l_Lean_Expr_cleanupAnnotations(v_a_493_);
lean_dec(v_a_493_);
v___x_498_ = l_Lean_Expr_isApp(v___x_497_);
if (v___x_498_ == 0)
{
lean_dec_ref(v___x_497_);
lean_del_object(v___x_495_);
goto v___jp_489_;
}
else
{
lean_object* v___x_499_; uint8_t v___x_500_; 
v___x_499_ = l_Lean_Expr_appFnCleanup___redArg(v___x_497_);
v___x_500_ = l_Lean_Expr_isApp(v___x_499_);
if (v___x_500_ == 0)
{
lean_dec_ref(v___x_499_);
lean_dec_ref(v___x_497_);
lean_del_object(v___x_495_);
goto v___jp_489_;
}
else
{
lean_object* v___x_501_; uint8_t v___x_502_; 
v___x_501_ = l_Lean_Expr_appFnCleanup___redArg(v___x_499_);
v___x_502_ = l_Lean_Expr_isApp(v___x_501_);
if (v___x_502_ == 0)
{
lean_dec_ref(v___x_501_);
lean_dec_ref(v___x_499_);
lean_dec_ref(v___x_497_);
lean_del_object(v___x_495_);
goto v___jp_489_;
}
else
{
lean_object* v___x_503_; lean_object* v___x_504_; uint8_t v___x_505_; 
v___x_503_ = l_Lean_Expr_appFnCleanup___redArg(v___x_501_);
v___x_504_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__2));
v___x_505_ = l_Lean_Expr_isConstOf(v___x_503_, v___x_504_);
if (v___x_505_ == 0)
{
lean_dec_ref(v___x_503_);
lean_dec_ref(v___x_501_);
lean_dec_ref(v___x_499_);
lean_dec_ref(v___x_497_);
lean_del_object(v___x_495_);
goto v___jp_489_;
}
else
{
lean_object* v_arg_506_; lean_object* v_arg_507_; lean_object* v_arg_508_; lean_object* v___x_509_; 
v_arg_506_ = lean_ctor_get(v___x_497_, 1);
lean_inc_ref(v_arg_506_);
lean_dec_ref(v___x_497_);
v_arg_507_ = lean_ctor_get(v___x_499_, 1);
lean_inc_ref(v_arg_507_);
lean_dec_ref(v___x_499_);
v_arg_508_ = lean_ctor_get(v___x_501_, 1);
lean_inc_ref_n(v_arg_508_, 2);
lean_dec_ref(v___x_501_);
v___x_509_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_508_, v_a_485_);
if (lean_obj_tag(v___x_509_) == 0)
{
lean_object* v_a_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_605_; 
v_a_510_ = lean_ctor_get(v___x_509_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_509_);
if (v_isSharedCheck_605_ == 0)
{
v___x_512_ = v___x_509_;
v_isShared_513_ = v_isSharedCheck_605_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_a_510_);
lean_dec(v___x_509_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_605_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_519_; lean_object* v___x_520_; uint8_t v___x_521_; 
v___x_519_ = l_Lean_Expr_cleanupAnnotations(v_a_510_);
lean_dec(v_a_510_);
v___x_520_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__3));
v___x_521_ = l_Lean_Expr_isConstOf(v___x_519_, v___x_520_);
lean_dec_ref(v___x_519_);
if (v___x_521_ == 0)
{
uint8_t v___x_532_; 
lean_del_object(v___x_512_);
lean_del_object(v___x_495_);
v___x_532_ = lean_expr_eqv(v_arg_507_, v_arg_506_);
if (v___x_532_ == 0)
{
lean_object* v___x_533_; uint8_t v___x_534_; 
lean_dec_ref(v_arg_508_);
lean_dec_ref(v___x_503_);
v___x_533_ = lean_obj_once(&l_Lean_Meta_Grind_simpEq___redArg___closed__11, &l_Lean_Meta_Grind_simpEq___redArg___closed__11_once, _init_l_Lean_Meta_Grind_simpEq___redArg___closed__11);
v___x_534_ = lean_expr_eqv(v_arg_506_, v___x_533_);
if (v___x_534_ == 0)
{
lean_object* v___x_535_; uint8_t v___x_536_; 
v___x_535_ = lean_obj_once(&l_Lean_Meta_Grind_simpEq___redArg___closed__14, &l_Lean_Meta_Grind_simpEq___redArg___closed__14_once, _init_l_Lean_Meta_Grind_simpEq___redArg___closed__14);
v___x_536_ = lean_expr_eqv(v_arg_506_, v___x_535_);
lean_dec_ref(v_arg_506_);
if (v___x_536_ == 0)
{
lean_object* v___x_537_; lean_object* v___x_538_; 
lean_dec_ref(v_arg_507_);
v___x_537_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
v___x_538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_538_, 0, v___x_537_);
return v___x_538_;
}
else
{
lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
lean_inc_ref(v_arg_507_);
v___x_539_ = l_Lean_mkNot(v_arg_507_);
v___x_540_ = lean_obj_once(&l_Lean_Meta_Grind_simpEq___redArg___closed__17, &l_Lean_Meta_Grind_simpEq___redArg___closed__17_once, _init_l_Lean_Meta_Grind_simpEq___redArg___closed__17);
v___x_541_ = l_Lean_Expr_app___override(v___x_540_, v_arg_507_);
v___x_542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
v___x_543_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_543_, 0, v___x_539_);
lean_ctor_set(v___x_543_, 1, v___x_542_);
lean_ctor_set_uint8(v___x_543_, sizeof(void*)*2, v___x_505_);
v___x_544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
v___x_545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_545_, 0, v___x_544_);
return v___x_545_;
}
}
else
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
lean_dec_ref(v_arg_506_);
v___x_546_ = lean_obj_once(&l_Lean_Meta_Grind_simpEq___redArg___closed__20, &l_Lean_Meta_Grind_simpEq___redArg___closed__20_once, _init_l_Lean_Meta_Grind_simpEq___redArg___closed__20);
lean_inc_ref(v_arg_507_);
v___x_547_ = l_Lean_Expr_app___override(v___x_546_, v_arg_507_);
v___x_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
v___x_549_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_549_, 0, v_arg_507_);
lean_ctor_set(v___x_549_, 1, v___x_548_);
lean_ctor_set_uint8(v___x_549_, sizeof(void*)*2, v___x_505_);
v___x_550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_550_, 0, v___x_549_);
v___x_551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_551_, 0, v___x_550_);
return v___x_551_;
}
}
else
{
lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
lean_dec_ref(v_arg_506_);
v___x_552_ = l_Lean_Expr_constLevels_x21(v___x_503_);
lean_dec_ref(v___x_503_);
v___x_553_ = lean_obj_once(&l_Lean_Meta_Grind_simpEq___redArg___closed__11, &l_Lean_Meta_Grind_simpEq___redArg___closed__11_once, _init_l_Lean_Meta_Grind_simpEq___redArg___closed__11);
v___x_554_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__22));
v___x_555_ = l_Lean_mkConst(v___x_554_, v___x_552_);
v___x_556_ = l_Lean_mkAppB(v___x_555_, v_arg_508_, v_arg_507_);
v___x_557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_557_, 0, v___x_556_);
v___x_558_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_558_, 0, v___x_553_);
lean_ctor_set(v___x_558_, 1, v___x_557_);
lean_ctor_set_uint8(v___x_558_, sizeof(void*)*2, v___x_505_);
v___x_559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_559_, 0, v___x_558_);
v___x_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_560_, 0, v___x_559_);
return v___x_560_;
}
}
else
{
lean_object* v___x_561_; 
v___x_561_ = l_Lean_Expr_getAppFn(v_arg_506_);
if (lean_obj_tag(v___x_561_) == 4)
{
lean_object* v_declName_562_; lean_object* v___x_563_; uint8_t v___x_590_; 
v_declName_562_ = lean_ctor_get(v___x_561_, 0);
lean_inc(v_declName_562_);
lean_dec_ref_known(v___x_561_, 2);
v___x_563_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__24));
v___x_590_ = lean_name_eq(v_declName_562_, v___x_563_);
if (v___x_590_ == 0)
{
lean_object* v___x_591_; uint8_t v___x_592_; 
v___x_591_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__30));
v___x_592_ = lean_name_eq(v_declName_562_, v___x_591_);
if (v___x_592_ == 0)
{
lean_object* v___x_593_; 
lean_del_object(v___x_512_);
v___x_593_ = l_Lean_Expr_getAppFn(v_arg_507_);
if (lean_obj_tag(v___x_593_) == 4)
{
lean_object* v_declName_594_; uint8_t v___x_595_; 
v_declName_594_ = lean_ctor_get(v___x_593_, 0);
lean_inc(v_declName_594_);
lean_dec_ref_known(v___x_593_, 2);
v___x_595_ = lean_name_eq(v_declName_594_, v___x_563_);
if (v___x_595_ == 0)
{
uint8_t v___x_596_; 
v___x_596_ = lean_name_eq(v_declName_594_, v___x_591_);
if (v___x_596_ == 0)
{
uint8_t v___x_597_; 
lean_del_object(v___x_495_);
v___x_597_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget(v_declName_594_);
lean_dec(v_declName_594_);
if (v___x_597_ == 0)
{
uint8_t v___x_598_; 
v___x_598_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget(v_declName_562_);
lean_dec(v_declName_562_);
if (v___x_598_ == 0)
{
lean_object* v___x_599_; lean_object* v___x_600_; 
lean_dec_ref(v_arg_508_);
lean_dec_ref(v_arg_507_);
lean_dec_ref(v_arg_506_);
lean_dec_ref(v___x_503_);
v___x_599_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
v___x_600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_600_, 0, v___x_599_);
return v___x_600_;
}
else
{
goto v___jp_564_;
}
}
else
{
lean_dec(v_declName_562_);
goto v___jp_564_;
}
}
else
{
lean_dec(v_declName_594_);
lean_dec(v_declName_562_);
goto v___jp_522_;
}
}
else
{
lean_dec(v_declName_594_);
lean_dec(v_declName_562_);
goto v___jp_522_;
}
}
else
{
lean_object* v___x_601_; lean_object* v___x_602_; 
lean_dec_ref(v___x_593_);
lean_dec(v_declName_562_);
lean_dec_ref(v_arg_508_);
lean_dec_ref(v_arg_507_);
lean_dec_ref(v_arg_506_);
lean_dec_ref(v___x_503_);
lean_del_object(v___x_495_);
v___x_601_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
v___x_602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_602_, 0, v___x_601_);
return v___x_602_;
}
}
else
{
lean_dec(v_declName_562_);
lean_dec_ref(v_arg_508_);
lean_dec_ref(v_arg_507_);
lean_dec_ref(v_arg_506_);
lean_dec_ref(v___x_503_);
lean_del_object(v___x_495_);
goto v___jp_514_;
}
}
else
{
lean_dec(v_declName_562_);
lean_dec_ref(v_arg_508_);
lean_dec_ref(v_arg_507_);
lean_dec_ref(v_arg_506_);
lean_dec_ref(v___x_503_);
lean_del_object(v___x_495_);
goto v___jp_514_;
}
v___jp_564_:
{
lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_565_ = lean_obj_once(&l_Lean_Meta_Grind_simpEq___redArg___closed__25, &l_Lean_Meta_Grind_simpEq___redArg___closed__25_once, _init_l_Lean_Meta_Grind_simpEq___redArg___closed__25);
lean_inc_ref(v_arg_507_);
lean_inc_ref(v_arg_508_);
lean_inc_ref(v___x_503_);
v___x_566_ = l_Lean_mkApp3(v___x_503_, v_arg_508_, v_arg_507_, v___x_565_);
lean_inc_ref(v_arg_506_);
v___x_567_ = l_Lean_mkApp3(v___x_503_, v_arg_508_, v_arg_506_, v___x_565_);
v___x_568_ = l_Lean_Meta_mkEq(v___x_566_, v___x_567_, v_a_484_, v_a_485_, v_a_486_, v_a_487_);
if (lean_obj_tag(v___x_568_) == 0)
{
lean_object* v_a_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_581_; 
v_a_569_ = lean_ctor_get(v___x_568_, 0);
v_isSharedCheck_581_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_581_ == 0)
{
v___x_571_ = v___x_568_;
v_isShared_572_ = v_isSharedCheck_581_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_a_569_);
lean_dec(v___x_568_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_581_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_579_; 
v___x_573_ = lean_obj_once(&l_Lean_Meta_Grind_simpEq___redArg___closed__28, &l_Lean_Meta_Grind_simpEq___redArg___closed__28_once, _init_l_Lean_Meta_Grind_simpEq___redArg___closed__28);
v___x_574_ = l_Lean_mkAppB(v___x_573_, v_arg_507_, v_arg_506_);
v___x_575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_575_, 0, v___x_574_);
v___x_576_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_576_, 0, v_a_569_);
lean_ctor_set(v___x_576_, 1, v___x_575_);
lean_ctor_set_uint8(v___x_576_, sizeof(void*)*2, v___x_521_);
v___x_577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
if (v_isShared_572_ == 0)
{
lean_ctor_set(v___x_571_, 0, v___x_577_);
v___x_579_ = v___x_571_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v___x_577_);
v___x_579_ = v_reuseFailAlloc_580_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
return v___x_579_;
}
}
}
else
{
lean_object* v_a_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_589_; 
lean_dec_ref(v_arg_507_);
lean_dec_ref(v_arg_506_);
v_a_582_ = lean_ctor_get(v___x_568_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_589_ == 0)
{
v___x_584_ = v___x_568_;
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_a_582_);
lean_dec(v___x_568_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_587_; 
if (v_isShared_585_ == 0)
{
v___x_587_ = v___x_584_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_a_582_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
}
}
}
else
{
lean_object* v___x_603_; lean_object* v___x_604_; 
lean_dec_ref(v___x_561_);
lean_del_object(v___x_512_);
lean_dec_ref(v_arg_508_);
lean_dec_ref(v_arg_507_);
lean_dec_ref(v_arg_506_);
lean_dec_ref(v___x_503_);
lean_del_object(v___x_495_);
v___x_603_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
v___x_604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_604_, 0, v___x_603_);
return v___x_604_;
}
}
v___jp_514_:
{
lean_object* v___x_515_; lean_object* v___x_517_; 
v___x_515_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 0, v___x_515_);
v___x_517_ = v___x_512_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v___x_515_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
v___jp_522_:
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_530_; 
lean_inc_ref(v_arg_507_);
lean_inc_ref(v_arg_506_);
v___x_523_ = l_Lean_mkApp3(v___x_503_, v_arg_508_, v_arg_506_, v_arg_507_);
v___x_524_ = lean_obj_once(&l_Lean_Meta_Grind_simpEq___redArg___closed__8, &l_Lean_Meta_Grind_simpEq___redArg___closed__8_once, _init_l_Lean_Meta_Grind_simpEq___redArg___closed__8);
v___x_525_ = l_Lean_mkAppB(v___x_524_, v_arg_507_, v_arg_506_);
v___x_526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_526_, 0, v___x_525_);
v___x_527_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_527_, 0, v___x_523_);
lean_ctor_set(v___x_527_, 1, v___x_526_);
lean_ctor_set_uint8(v___x_527_, sizeof(void*)*2, v___x_521_);
v___x_528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_528_, 0, v___x_527_);
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 0, v___x_528_);
v___x_530_ = v___x_495_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v___x_528_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
}
else
{
lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_613_; 
lean_dec_ref(v_arg_508_);
lean_dec_ref(v_arg_507_);
lean_dec_ref(v_arg_506_);
lean_dec_ref(v___x_503_);
lean_del_object(v___x_495_);
v_a_606_ = lean_ctor_get(v___x_509_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_509_);
if (v_isSharedCheck_613_ == 0)
{
v___x_608_ = v___x_509_;
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_dec(v___x_509_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_611_; 
if (v_isShared_609_ == 0)
{
v___x_611_ = v___x_608_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_a_606_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_622_; 
v_a_615_ = lean_ctor_get(v___x_492_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_622_ == 0)
{
v___x_617_ = v___x_492_;
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_a_615_);
lean_dec(v___x_492_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_620_; 
if (v_isShared_618_ == 0)
{
v___x_620_ = v___x_617_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_a_615_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
v___jp_489_:
{
lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_490_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
v___x_491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_491_, 0, v___x_490_);
return v___x_491_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpEq___redArg___boxed(lean_object* v_e_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_Lean_Meta_Grind_simpEq___redArg(v_e_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_);
lean_dec(v_a_627_);
lean_dec_ref(v_a_626_);
lean_dec(v_a_625_);
lean_dec_ref(v_a_624_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpEq(lean_object* v_e_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_){
_start:
{
lean_object* v___x_639_; 
v___x_639_ = l_Lean_Meta_Grind_simpEq___redArg(v_e_630_, v_a_634_, v_a_635_, v_a_636_, v_a_637_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpEq___boxed(lean_object* v_e_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l_Lean_Meta_Grind_simpEq(v_e_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_);
lean_dec(v_a_647_);
lean_dec_ref(v_a_646_);
lean_dec(v_a_645_);
lean_dec_ref(v_a_644_);
lean_dec(v_a_643_);
lean_dec_ref(v_a_642_);
lean_dec(v_a_641_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13_(){
_start:
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_669_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13_));
v___x_670_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__4_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13_));
v___x_671_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpEq___boxed), 9, 0);
v___x_672_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_669_, v___x_670_, v___x_671_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13____boxed(lean_object* v_a_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13_();
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpDIte___redArg(lean_object* v_e_684_, lean_object* v_a_685_){
_start:
{
lean_object* v___x_690_; 
v___x_690_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_684_, v_a_685_);
if (lean_obj_tag(v___x_690_) == 0)
{
lean_object* v_a_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_746_; 
v_a_691_ = lean_ctor_get(v___x_690_, 0);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_746_ == 0)
{
v___x_693_ = v___x_690_;
v_isShared_694_ = v_isSharedCheck_746_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_dec(v___x_690_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_746_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_695_; uint8_t v___x_696_; 
v___x_695_ = l_Lean_Expr_cleanupAnnotations(v_a_691_);
lean_dec(v_a_691_);
v___x_696_ = l_Lean_Expr_isApp(v___x_695_);
if (v___x_696_ == 0)
{
lean_dec_ref(v___x_695_);
lean_del_object(v___x_693_);
goto v___jp_687_;
}
else
{
lean_object* v___x_697_; uint8_t v___x_698_; 
v___x_697_ = l_Lean_Expr_appFnCleanup___redArg(v___x_695_);
v___x_698_ = l_Lean_Expr_isApp(v___x_697_);
if (v___x_698_ == 0)
{
lean_dec_ref(v___x_697_);
lean_dec_ref(v___x_695_);
lean_del_object(v___x_693_);
goto v___jp_687_;
}
else
{
lean_object* v___x_699_; uint8_t v___x_700_; 
v___x_699_ = l_Lean_Expr_appFnCleanup___redArg(v___x_697_);
v___x_700_ = l_Lean_Expr_isApp(v___x_699_);
if (v___x_700_ == 0)
{
lean_dec_ref(v___x_699_);
lean_dec_ref(v___x_697_);
lean_dec_ref(v___x_695_);
lean_del_object(v___x_693_);
goto v___jp_687_;
}
else
{
lean_object* v___x_701_; uint8_t v___x_702_; 
v___x_701_ = l_Lean_Expr_appFnCleanup___redArg(v___x_699_);
v___x_702_ = l_Lean_Expr_isApp(v___x_701_);
if (v___x_702_ == 0)
{
lean_dec_ref(v___x_701_);
lean_dec_ref(v___x_699_);
lean_dec_ref(v___x_697_);
lean_dec_ref(v___x_695_);
lean_del_object(v___x_693_);
goto v___jp_687_;
}
else
{
lean_object* v___x_703_; uint8_t v___x_704_; 
v___x_703_ = l_Lean_Expr_appFnCleanup___redArg(v___x_701_);
v___x_704_ = l_Lean_Expr_isApp(v___x_703_);
if (v___x_704_ == 0)
{
lean_dec_ref(v___x_703_);
lean_dec_ref(v___x_701_);
lean_dec_ref(v___x_699_);
lean_dec_ref(v___x_697_);
lean_dec_ref(v___x_695_);
lean_del_object(v___x_693_);
goto v___jp_687_;
}
else
{
lean_object* v___x_705_; lean_object* v___x_706_; uint8_t v___x_707_; 
v___x_705_ = l_Lean_Expr_appFnCleanup___redArg(v___x_703_);
v___x_706_ = ((lean_object*)(l_Lean_Meta_Grind_simpDIte___redArg___closed__1));
v___x_707_ = l_Lean_Expr_isConstOf(v___x_705_, v___x_706_);
if (v___x_707_ == 0)
{
lean_dec_ref(v___x_705_);
lean_dec_ref(v___x_703_);
lean_dec_ref(v___x_701_);
lean_dec_ref(v___x_699_);
lean_dec_ref(v___x_697_);
lean_dec_ref(v___x_695_);
lean_del_object(v___x_693_);
goto v___jp_687_;
}
else
{
lean_object* v_arg_708_; 
v_arg_708_ = lean_ctor_get(v___x_697_, 1);
lean_inc_ref(v_arg_708_);
lean_dec_ref(v___x_697_);
if (lean_obj_tag(v_arg_708_) == 6)
{
lean_object* v_body_709_; uint8_t v___x_710_; 
v_body_709_ = lean_ctor_get(v_arg_708_, 2);
lean_inc_ref(v_body_709_);
lean_dec_ref_known(v_arg_708_, 3);
v___x_710_ = l_Lean_Expr_hasLooseBVars(v_body_709_);
if (v___x_710_ == 0)
{
lean_object* v_arg_711_; 
v_arg_711_ = lean_ctor_get(v___x_695_, 1);
lean_inc_ref(v_arg_711_);
lean_dec_ref(v___x_695_);
if (lean_obj_tag(v_arg_711_) == 6)
{
lean_object* v_body_712_; uint8_t v___x_713_; 
v_body_712_ = lean_ctor_get(v_arg_711_, 2);
lean_inc_ref(v_body_712_);
lean_dec_ref_known(v_arg_711_, 3);
v___x_713_ = l_Lean_Expr_hasLooseBVars(v_body_712_);
if (v___x_713_ == 0)
{
lean_object* v_arg_714_; lean_object* v_arg_715_; lean_object* v_arg_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_728_; 
v_arg_714_ = lean_ctor_get(v___x_699_, 1);
lean_inc_ref_n(v_arg_714_, 2);
lean_dec_ref(v___x_699_);
v_arg_715_ = lean_ctor_get(v___x_701_, 1);
lean_inc_ref_n(v_arg_715_, 2);
lean_dec_ref(v___x_701_);
v_arg_716_ = lean_ctor_get(v___x_703_, 1);
lean_inc_ref_n(v_arg_716_, 2);
lean_dec_ref(v___x_703_);
v___x_717_ = l_Lean_Expr_constLevels_x21(v___x_705_);
lean_dec_ref(v___x_705_);
v___x_718_ = ((lean_object*)(l_Lean_Meta_Grind_simpDIte___redArg___closed__3));
lean_inc(v___x_717_);
v___x_719_ = l_Lean_mkConst(v___x_718_, v___x_717_);
lean_inc_ref(v_body_712_);
lean_inc_ref(v_body_709_);
v___x_720_ = l_Lean_mkApp5(v___x_719_, v_arg_716_, v_arg_715_, v_arg_714_, v_body_709_, v_body_712_);
v___x_721_ = ((lean_object*)(l_Lean_Meta_Grind_simpDIte___redArg___closed__5));
v___x_722_ = l_Lean_mkConst(v___x_721_, v___x_717_);
v___x_723_ = l_Lean_mkApp5(v___x_722_, v_arg_715_, v_arg_716_, v_body_709_, v_body_712_, v_arg_714_);
v___x_724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_724_, 0, v___x_723_);
v___x_725_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_725_, 0, v___x_720_);
lean_ctor_set(v___x_725_, 1, v___x_724_);
lean_ctor_set_uint8(v___x_725_, sizeof(void*)*2, v___x_707_);
v___x_726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_726_, 0, v___x_725_);
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 0, v___x_726_);
v___x_728_ = v___x_693_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v___x_726_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
else
{
lean_object* v___x_730_; lean_object* v___x_732_; 
lean_dec_ref(v_body_712_);
lean_dec_ref(v_body_709_);
lean_dec_ref(v___x_705_);
lean_dec_ref(v___x_703_);
lean_dec_ref(v___x_701_);
lean_dec_ref(v___x_699_);
v___x_730_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 0, v___x_730_);
v___x_732_ = v___x_693_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v___x_730_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
else
{
lean_object* v___x_734_; lean_object* v___x_736_; 
lean_dec_ref(v_arg_711_);
lean_dec_ref(v_body_709_);
lean_dec_ref(v___x_705_);
lean_dec_ref(v___x_703_);
lean_dec_ref(v___x_701_);
lean_dec_ref(v___x_699_);
v___x_734_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 0, v___x_734_);
v___x_736_ = v___x_693_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v___x_734_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
else
{
lean_object* v___x_738_; lean_object* v___x_740_; 
lean_dec_ref(v_body_709_);
lean_dec_ref(v___x_705_);
lean_dec_ref(v___x_703_);
lean_dec_ref(v___x_701_);
lean_dec_ref(v___x_699_);
lean_dec_ref(v___x_695_);
v___x_738_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 0, v___x_738_);
v___x_740_ = v___x_693_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v___x_738_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
}
else
{
lean_object* v___x_742_; lean_object* v___x_744_; 
lean_dec_ref(v_arg_708_);
lean_dec_ref(v___x_705_);
lean_dec_ref(v___x_703_);
lean_dec_ref(v___x_701_);
lean_dec_ref(v___x_699_);
lean_dec_ref(v___x_695_);
v___x_742_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 0, v___x_742_);
v___x_744_ = v___x_693_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v___x_742_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_754_; 
v_a_747_ = lean_ctor_get(v___x_690_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_754_ == 0)
{
v___x_749_ = v___x_690_;
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_a_747_);
lean_dec(v___x_690_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_752_; 
if (v_isShared_750_ == 0)
{
v___x_752_ = v___x_749_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_a_747_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
v___jp_687_:
{
lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_688_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
v___x_689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_689_, 0, v___x_688_);
return v___x_689_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpDIte___redArg___boxed(lean_object* v_e_755_, lean_object* v_a_756_, lean_object* v_a_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_Lean_Meta_Grind_simpDIte___redArg(v_e_755_, v_a_756_);
lean_dec(v_a_756_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpDIte(lean_object* v_e_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_){
_start:
{
lean_object* v___x_768_; 
v___x_768_ = l_Lean_Meta_Grind_simpDIte___redArg(v_e_759_, v_a_764_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpDIte___boxed(lean_object* v_e_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_Lean_Meta_Grind_simpDIte(v_e_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_);
lean_dec(v_a_776_);
lean_dec_ref(v_a_775_);
lean_dec(v_a_774_);
lean_dec_ref(v_a_773_);
lean_dec(v_a_772_);
lean_dec_ref(v_a_771_);
lean_dec(v_a_770_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_14_(){
_start:
{
lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_799_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_14_));
v___x_800_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_14_));
v___x_801_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpDIte___boxed), 9, 0);
v___x_802_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_799_, v___x_800_, v___x_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_14____boxed(lean_object* v_a_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_14_();
return v_res_804_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__8(void){
_start:
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_821_ = lean_box(0);
v___x_822_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__7));
v___x_823_ = l_Lean_mkConst(v___x_822_, v___x_821_);
return v___x_823_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__18(void){
_start:
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_840_ = lean_box(0);
v___x_841_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__17));
v___x_842_ = l_Lean_mkConst(v___x_841_, v___x_840_);
return v___x_842_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__21(void){
_start:
{
lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_847_ = lean_unsigned_to_nat(1u);
v___x_848_ = lean_nat_to_int(v___x_847_);
return v___x_848_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__22(void){
_start:
{
lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_849_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__21, &l_Lean_Meta_Grind_pushNot___redArg___closed__21_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__21);
v___x_850_ = l_Lean_mkIntLit(v___x_849_);
return v___x_850_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__23(void){
_start:
{
lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_851_ = lean_box(0);
v___x_852_ = ((lean_object*)(l_Lean_Meta_Grind_registerNormTheorems___closed__4));
v___x_853_ = l_Lean_mkConst(v___x_852_, v___x_851_);
return v___x_853_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__24(void){
_start:
{
lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_854_ = lean_unsigned_to_nat(1u);
v___x_855_ = l_Lean_mkNatLit(v___x_854_);
return v___x_855_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__25(void){
_start:
{
lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_856_ = lean_box(0);
v___x_857_ = ((lean_object*)(l_Lean_Meta_Grind_registerNormTheorems___closed__2));
v___x_858_ = l_Lean_mkConst(v___x_857_, v___x_856_);
return v___x_858_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__26(void){
_start:
{
lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_859_ = lean_box(0);
v___x_860_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__30));
v___x_861_ = l_Lean_mkConst(v___x_860_, v___x_859_);
return v___x_861_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__29(void){
_start:
{
lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_866_ = lean_box(0);
v___x_867_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__28));
v___x_868_ = l_Lean_mkConst(v___x_867_, v___x_866_);
return v___x_868_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__32(void){
_start:
{
lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_873_ = lean_box(0);
v___x_874_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__31));
v___x_875_ = l_Lean_mkConst(v___x_874_, v___x_873_);
return v___x_875_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__35(void){
_start:
{
lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_881_ = lean_box(0);
v___x_882_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__34));
v___x_883_ = l_Lean_mkConst(v___x_882_, v___x_881_);
return v___x_883_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__36(void){
_start:
{
lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_884_ = lean_box(0);
v___x_885_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__10));
v___x_886_ = l_Lean_mkConst(v___x_885_, v___x_884_);
return v___x_886_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__39(void){
_start:
{
lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_892_ = lean_box(0);
v___x_893_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__38));
v___x_894_ = l_Lean_mkConst(v___x_893_, v___x_892_);
return v___x_894_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__40(void){
_start:
{
lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_895_ = lean_box(0);
v___x_896_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__12));
v___x_897_ = l_Lean_mkConst(v___x_896_, v___x_895_);
return v___x_897_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__43(void){
_start:
{
lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_903_ = lean_box(0);
v___x_904_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__42));
v___x_905_ = l_Lean_mkConst(v___x_904_, v___x_903_);
return v___x_905_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__46(void){
_start:
{
lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_909_ = lean_unsigned_to_nat(0u);
v___x_910_ = l_Lean_mkBVar(v___x_909_);
return v___x_910_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__51(void){
_start:
{
lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_921_ = lean_box(0);
v___x_922_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__50));
v___x_923_ = l_Lean_mkConst(v___x_922_, v___x_921_);
return v___x_923_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__54(void){
_start:
{
lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_929_ = lean_box(0);
v___x_930_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__53));
v___x_931_ = l_Lean_mkConst(v___x_930_, v___x_929_);
return v___x_931_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__55(void){
_start:
{
lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_932_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__54, &l_Lean_Meta_Grind_pushNot___redArg___closed__54_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__54);
v___x_933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_933_, 0, v___x_932_);
return v___x_933_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__58(void){
_start:
{
lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_939_ = lean_box(0);
v___x_940_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__57));
v___x_941_ = l_Lean_mkConst(v___x_940_, v___x_939_);
return v___x_941_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__59(void){
_start:
{
lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_942_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__58, &l_Lean_Meta_Grind_pushNot___redArg___closed__58_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__58);
v___x_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_943_, 0, v___x_942_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNot___redArg(lean_object* v_e_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_){
_start:
{
lean_object* v___x_953_; 
v___x_953_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_944_, v_a_946_);
if (lean_obj_tag(v___x_953_) == 0)
{
lean_object* v_a_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_1277_; 
v_a_954_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_956_ = v___x_953_;
v_isShared_957_ = v_isSharedCheck_1277_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_a_954_);
lean_dec(v___x_953_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_1277_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_958_; uint8_t v___x_959_; 
v___x_958_ = l_Lean_Expr_cleanupAnnotations(v_a_954_);
lean_dec(v_a_954_);
v___x_959_ = l_Lean_Expr_isApp(v___x_958_);
if (v___x_959_ == 0)
{
lean_dec_ref(v___x_958_);
lean_del_object(v___x_956_);
goto v___jp_950_;
}
else
{
lean_object* v___x_960_; lean_object* v___x_961_; uint8_t v___x_962_; lean_object* v___y_964_; lean_object* v___y_965_; lean_object* v___y_966_; uint8_t v___y_967_; lean_object* v___y_968_; lean_object* v___y_969_; lean_object* v___y_970_; lean_object* v___y_971_; 
v___x_960_ = l_Lean_Expr_appFnCleanup___redArg(v___x_958_);
v___x_961_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__1));
v___x_962_ = l_Lean_Expr_isConstOf(v___x_960_, v___x_961_);
lean_dec_ref(v___x_960_);
if (v___x_962_ == 0)
{
lean_dec_ref(v___x_958_);
lean_del_object(v___x_956_);
goto v___jp_950_;
}
else
{
lean_object* v_arg_1003_; lean_object* v___y_1005_; lean_object* v___y_1006_; lean_object* v___y_1007_; lean_object* v___y_1008_; lean_object* v___x_1043_; 
v_arg_1003_ = lean_ctor_get(v___x_958_, 1);
lean_inc_ref_n(v_arg_1003_, 2);
lean_dec_ref(v___x_958_);
v___x_1043_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1003_, v_a_946_);
if (lean_obj_tag(v___x_1043_) == 0)
{
lean_object* v_a_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1268_; 
v_a_1044_ = lean_ctor_get(v___x_1043_, 0);
v_isSharedCheck_1268_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1046_ = v___x_1043_;
v_isShared_1047_ = v_isSharedCheck_1268_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_a_1044_);
lean_dec(v___x_1043_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1268_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; uint8_t v___x_1050_; 
v___x_1048_ = l_Lean_Expr_cleanupAnnotations(v_a_1044_);
lean_dec(v_a_1044_);
v___x_1049_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__13));
v___x_1050_ = l_Lean_Expr_isConstOf(v___x_1048_, v___x_1049_);
if (v___x_1050_ == 0)
{
lean_object* v___x_1051_; uint8_t v___x_1052_; 
v___x_1051_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__10));
v___x_1052_ = l_Lean_Expr_isConstOf(v___x_1048_, v___x_1051_);
if (v___x_1052_ == 0)
{
uint8_t v___x_1053_; 
v___x_1053_ = l_Lean_Expr_isApp(v___x_1048_);
if (v___x_1053_ == 0)
{
lean_dec_ref(v___x_1048_);
lean_del_object(v___x_1046_);
v___y_1005_ = v_a_945_;
v___y_1006_ = v_a_946_;
v___y_1007_ = v_a_947_;
v___y_1008_ = v_a_948_;
goto v___jp_1004_;
}
else
{
lean_object* v_arg_1054_; lean_object* v___x_1055_; uint8_t v___x_1056_; 
v_arg_1054_ = lean_ctor_get(v___x_1048_, 1);
lean_inc_ref(v_arg_1054_);
v___x_1055_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1048_);
lean_dec_ref(v___x_1048_);
v___x_1056_ = l_Lean_Expr_isConstOf(v___x_1055_, v___x_961_);
if (v___x_1056_ == 0)
{
uint8_t v___x_1057_; 
v___x_1057_ = l_Lean_Expr_isApp(v___x_1055_);
if (v___x_1057_ == 0)
{
lean_dec_ref(v___x_1055_);
lean_dec_ref(v_arg_1054_);
lean_del_object(v___x_1046_);
v___y_1005_ = v_a_945_;
v___y_1006_ = v_a_946_;
v___y_1007_ = v_a_947_;
v___y_1008_ = v_a_948_;
goto v___jp_1004_;
}
else
{
lean_object* v_arg_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; uint8_t v___x_1061_; 
v_arg_1058_ = lean_ctor_get(v___x_1055_, 1);
lean_inc_ref(v_arg_1058_);
v___x_1059_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1055_);
lean_dec_ref(v___x_1055_);
v___x_1060_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__3));
v___x_1061_ = l_Lean_Expr_isConstOf(v___x_1059_, v___x_1060_);
if (v___x_1061_ == 0)
{
lean_object* v___x_1062_; uint8_t v___x_1063_; 
v___x_1062_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__10));
v___x_1063_ = l_Lean_Expr_isConstOf(v___x_1059_, v___x_1062_);
if (v___x_1063_ == 0)
{
lean_object* v___x_1064_; uint8_t v___x_1065_; 
v___x_1064_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__12));
v___x_1065_ = l_Lean_Expr_isConstOf(v___x_1059_, v___x_1064_);
if (v___x_1065_ == 0)
{
uint8_t v___x_1066_; 
v___x_1066_ = l_Lean_Expr_isApp(v___x_1059_);
if (v___x_1066_ == 0)
{
lean_dec_ref(v___x_1059_);
lean_dec_ref(v_arg_1058_);
lean_dec_ref(v_arg_1054_);
lean_del_object(v___x_1046_);
v___y_1005_ = v_a_945_;
v___y_1006_ = v_a_946_;
v___y_1007_ = v_a_947_;
v___y_1008_ = v_a_948_;
goto v___jp_1004_;
}
else
{
lean_object* v_arg_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; uint8_t v___x_1070_; 
v_arg_1067_ = lean_ctor_get(v___x_1059_, 1);
lean_inc_ref(v_arg_1067_);
v___x_1068_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1059_);
lean_dec_ref(v___x_1059_);
v___x_1069_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__2));
v___x_1070_ = l_Lean_Expr_isConstOf(v___x_1068_, v___x_1069_);
if (v___x_1070_ == 0)
{
uint8_t v___x_1071_; 
v___x_1071_ = l_Lean_Expr_isApp(v___x_1068_);
if (v___x_1071_ == 0)
{
lean_dec_ref(v___x_1068_);
lean_dec_ref(v_arg_1067_);
lean_dec_ref(v_arg_1058_);
lean_dec_ref(v_arg_1054_);
lean_del_object(v___x_1046_);
v___y_1005_ = v_a_945_;
v___y_1006_ = v_a_946_;
v___y_1007_ = v_a_947_;
v___y_1008_ = v_a_948_;
goto v___jp_1004_;
}
else
{
lean_object* v_arg_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; uint8_t v___x_1075_; 
v_arg_1072_ = lean_ctor_get(v___x_1068_, 1);
lean_inc_ref(v_arg_1072_);
v___x_1073_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1068_);
lean_dec_ref(v___x_1068_);
v___x_1074_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__15));
v___x_1075_ = l_Lean_Expr_isConstOf(v___x_1073_, v___x_1074_);
if (v___x_1075_ == 0)
{
uint8_t v___x_1076_; 
v___x_1076_ = l_Lean_Expr_isApp(v___x_1073_);
if (v___x_1076_ == 0)
{
lean_dec_ref(v___x_1073_);
lean_dec_ref(v_arg_1072_);
lean_dec_ref(v_arg_1067_);
lean_dec_ref(v_arg_1058_);
lean_dec_ref(v_arg_1054_);
lean_del_object(v___x_1046_);
v___y_1005_ = v_a_945_;
v___y_1006_ = v_a_946_;
v___y_1007_ = v_a_947_;
v___y_1008_ = v_a_948_;
goto v___jp_1004_;
}
else
{
lean_object* v___x_1077_; lean_object* v___x_1078_; uint8_t v___x_1079_; 
v___x_1077_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1073_);
v___x_1078_ = ((lean_object*)(l_Lean_Meta_Grind_simpDIte___redArg___closed__3));
v___x_1079_ = l_Lean_Expr_isConstOf(v___x_1077_, v___x_1078_);
if (v___x_1079_ == 0)
{
lean_dec_ref(v___x_1077_);
lean_dec_ref(v___x_1073_);
lean_dec_ref(v_arg_1072_);
lean_dec_ref(v_arg_1067_);
lean_dec_ref(v_arg_1058_);
lean_dec_ref(v_arg_1054_);
lean_del_object(v___x_1046_);
v___y_1005_ = v_a_945_;
v___y_1006_ = v_a_946_;
v___y_1007_ = v_a_947_;
v___y_1008_ = v_a_948_;
goto v___jp_1004_;
}
else
{
lean_object* v_arg_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1090_; 
lean_dec_ref(v_arg_1003_);
lean_del_object(v___x_956_);
v_arg_1080_ = lean_ctor_get(v___x_1073_, 1);
lean_inc_ref(v_arg_1080_);
lean_dec_ref(v___x_1073_);
lean_inc_ref(v_arg_1058_);
v___x_1081_ = l_Lean_mkNot(v_arg_1058_);
lean_inc_ref(v_arg_1054_);
v___x_1082_ = l_Lean_mkNot(v_arg_1054_);
lean_inc_ref(v_arg_1067_);
lean_inc_ref(v_arg_1072_);
v___x_1083_ = l_Lean_mkApp5(v___x_1077_, v_arg_1080_, v_arg_1072_, v_arg_1067_, v___x_1081_, v___x_1082_);
v___x_1084_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__18, &l_Lean_Meta_Grind_pushNot___redArg___closed__18_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__18);
v___x_1085_ = l_Lean_mkApp4(v___x_1084_, v_arg_1072_, v_arg_1067_, v_arg_1058_, v_arg_1054_);
v___x_1086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1085_);
v___x_1087_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1087_, 0, v___x_1083_);
lean_ctor_set(v___x_1087_, 1, v___x_1086_);
lean_ctor_set_uint8(v___x_1087_, sizeof(void*)*2, v___x_1079_);
v___x_1088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1087_);
if (v_isShared_1047_ == 0)
{
lean_ctor_set(v___x_1046_, 0, v___x_1088_);
v___x_1090_ = v___x_1046_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v___x_1088_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
}
}
else
{
lean_object* v___x_1092_; 
lean_dec_ref(v___x_1073_);
lean_dec_ref(v_arg_1067_);
lean_del_object(v___x_1046_);
lean_dec_ref(v_arg_1003_);
lean_del_object(v___x_956_);
v___x_1092_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1072_, v_a_946_);
if (lean_obj_tag(v___x_1092_) == 0)
{
lean_object* v_a_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1128_; 
v_a_1093_ = lean_ctor_get(v___x_1092_, 0);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1095_ = v___x_1092_;
v_isShared_1096_ = v_isSharedCheck_1128_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_a_1093_);
lean_dec(v___x_1092_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1128_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; uint8_t v___x_1099_; 
v___x_1097_ = l_Lean_Expr_cleanupAnnotations(v_a_1093_);
lean_dec(v_a_1093_);
v___x_1098_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__19));
v___x_1099_ = l_Lean_Expr_isConstOf(v___x_1097_, v___x_1098_);
if (v___x_1099_ == 0)
{
lean_object* v___x_1100_; uint8_t v___x_1101_; 
v___x_1100_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__20));
v___x_1101_ = l_Lean_Expr_isConstOf(v___x_1097_, v___x_1100_);
lean_dec_ref(v___x_1097_);
if (v___x_1101_ == 0)
{
lean_object* v___x_1102_; lean_object* v___x_1104_; 
lean_dec_ref(v_arg_1058_);
lean_dec_ref(v_arg_1054_);
v___x_1102_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
if (v_isShared_1096_ == 0)
{
lean_ctor_set(v___x_1095_, 0, v___x_1102_);
v___x_1104_ = v___x_1095_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v___x_1102_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
else
{
lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1115_; 
v___x_1106_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__22, &l_Lean_Meta_Grind_pushNot___redArg___closed__22_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__22);
lean_inc_ref(v_arg_1054_);
v___x_1107_ = l_Lean_mkIntAdd(v_arg_1054_, v___x_1106_);
lean_inc_ref(v_arg_1058_);
v___x_1108_ = l_Lean_mkIntLE(v___x_1107_, v_arg_1058_);
v___x_1109_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__23, &l_Lean_Meta_Grind_pushNot___redArg___closed__23_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__23);
v___x_1110_ = l_Lean_mkAppB(v___x_1109_, v_arg_1058_, v_arg_1054_);
v___x_1111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1110_);
v___x_1112_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1112_, 0, v___x_1108_);
lean_ctor_set(v___x_1112_, 1, v___x_1111_);
lean_ctor_set_uint8(v___x_1112_, sizeof(void*)*2, v___x_1101_);
v___x_1113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1113_, 0, v___x_1112_);
if (v_isShared_1096_ == 0)
{
lean_ctor_set(v___x_1095_, 0, v___x_1113_);
v___x_1115_ = v___x_1095_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v___x_1113_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
else
{
lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1126_; 
lean_dec_ref(v___x_1097_);
v___x_1117_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__24, &l_Lean_Meta_Grind_pushNot___redArg___closed__24_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__24);
lean_inc_ref(v_arg_1054_);
v___x_1118_ = l_Lean_mkNatAdd(v_arg_1054_, v___x_1117_);
lean_inc_ref(v_arg_1058_);
v___x_1119_ = l_Lean_mkNatLE(v___x_1118_, v_arg_1058_);
v___x_1120_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__25, &l_Lean_Meta_Grind_pushNot___redArg___closed__25_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__25);
v___x_1121_ = l_Lean_mkAppB(v___x_1120_, v_arg_1058_, v_arg_1054_);
v___x_1122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1121_);
v___x_1123_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1123_, 0, v___x_1119_);
lean_ctor_set(v___x_1123_, 1, v___x_1122_);
lean_ctor_set_uint8(v___x_1123_, sizeof(void*)*2, v___x_1099_);
v___x_1124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1123_);
if (v_isShared_1096_ == 0)
{
lean_ctor_set(v___x_1095_, 0, v___x_1124_);
v___x_1126_ = v___x_1095_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v___x_1124_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
}
else
{
lean_object* v_a_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1136_; 
lean_dec_ref(v_arg_1058_);
lean_dec_ref(v_arg_1054_);
v_a_1129_ = lean_ctor_get(v___x_1092_, 0);
v_isSharedCheck_1136_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1131_ = v___x_1092_;
v_isShared_1132_ = v_isSharedCheck_1136_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_a_1129_);
lean_dec(v___x_1092_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1136_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___x_1134_; 
if (v_isShared_1132_ == 0)
{
v___x_1134_ = v___x_1131_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_a_1129_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
return v___x_1134_;
}
}
}
}
}
}
else
{
uint8_t v___x_1137_; 
lean_dec_ref(v_arg_1003_);
lean_del_object(v___x_956_);
v___x_1137_ = l_Lean_Expr_isProp(v_arg_1067_);
if (v___x_1137_ == 0)
{
lean_object* v___x_1138_; 
lean_del_object(v___x_1046_);
v___x_1138_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1054_, v_a_946_);
if (lean_obj_tag(v___x_1138_) == 0)
{
lean_object* v_a_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1172_; 
v_a_1139_ = lean_ctor_get(v___x_1138_, 0);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1138_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1141_ = v___x_1138_;
v_isShared_1142_ = v_isSharedCheck_1172_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_a_1139_);
lean_dec(v___x_1138_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1172_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; uint8_t v___x_1145_; 
v___x_1143_ = l_Lean_Expr_cleanupAnnotations(v_a_1139_);
lean_dec(v_a_1139_);
v___x_1144_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__30));
v___x_1145_ = l_Lean_Expr_isConstOf(v___x_1143_, v___x_1144_);
if (v___x_1145_ == 0)
{
lean_object* v___x_1146_; uint8_t v___x_1147_; 
v___x_1146_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__24));
v___x_1147_ = l_Lean_Expr_isConstOf(v___x_1143_, v___x_1146_);
lean_dec_ref(v___x_1143_);
if (v___x_1147_ == 0)
{
lean_object* v___x_1148_; lean_object* v___x_1150_; 
lean_dec_ref(v___x_1068_);
lean_dec_ref(v_arg_1067_);
lean_dec_ref(v_arg_1058_);
v___x_1148_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
if (v_isShared_1142_ == 0)
{
lean_ctor_set(v___x_1141_, 0, v___x_1148_);
v___x_1150_ = v___x_1141_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v___x_1148_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
else
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1160_; 
v___x_1152_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__26, &l_Lean_Meta_Grind_pushNot___redArg___closed__26_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__26);
lean_inc_ref(v_arg_1058_);
v___x_1153_ = l_Lean_mkApp3(v___x_1068_, v_arg_1067_, v_arg_1058_, v___x_1152_);
v___x_1154_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__29, &l_Lean_Meta_Grind_pushNot___redArg___closed__29_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__29);
v___x_1155_ = l_Lean_Expr_app___override(v___x_1154_, v_arg_1058_);
v___x_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1155_);
v___x_1157_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1157_, 0, v___x_1153_);
lean_ctor_set(v___x_1157_, 1, v___x_1156_);
lean_ctor_set_uint8(v___x_1157_, sizeof(void*)*2, v___x_1070_);
v___x_1158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1157_);
if (v_isShared_1142_ == 0)
{
lean_ctor_set(v___x_1141_, 0, v___x_1158_);
v___x_1160_ = v___x_1141_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v___x_1158_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
}
else
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1170_; 
lean_dec_ref(v___x_1143_);
v___x_1162_ = lean_obj_once(&l_Lean_Meta_Grind_simpEq___redArg___closed__25, &l_Lean_Meta_Grind_simpEq___redArg___closed__25_once, _init_l_Lean_Meta_Grind_simpEq___redArg___closed__25);
lean_inc_ref(v_arg_1058_);
v___x_1163_ = l_Lean_mkApp3(v___x_1068_, v_arg_1067_, v_arg_1058_, v___x_1162_);
v___x_1164_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__32, &l_Lean_Meta_Grind_pushNot___redArg___closed__32_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__32);
v___x_1165_ = l_Lean_Expr_app___override(v___x_1164_, v_arg_1058_);
v___x_1166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1165_);
v___x_1167_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1167_, 0, v___x_1163_);
lean_ctor_set(v___x_1167_, 1, v___x_1166_);
lean_ctor_set_uint8(v___x_1167_, sizeof(void*)*2, v___x_1070_);
v___x_1168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1167_);
if (v_isShared_1142_ == 0)
{
lean_ctor_set(v___x_1141_, 0, v___x_1168_);
v___x_1170_ = v___x_1141_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v___x_1168_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
}
else
{
lean_object* v_a_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1180_; 
lean_dec_ref(v___x_1068_);
lean_dec_ref(v_arg_1067_);
lean_dec_ref(v_arg_1058_);
v_a_1173_ = lean_ctor_get(v___x_1138_, 0);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_1138_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1175_ = v___x_1138_;
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_a_1173_);
lean_dec(v___x_1138_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1178_; 
if (v_isShared_1176_ == 0)
{
v___x_1178_ = v___x_1175_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_a_1173_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
}
else
{
lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1189_; 
lean_inc_ref(v_arg_1054_);
v___x_1181_ = l_Lean_mkNot(v_arg_1054_);
lean_inc_ref(v_arg_1058_);
v___x_1182_ = l_Lean_mkApp3(v___x_1068_, v_arg_1067_, v_arg_1058_, v___x_1181_);
v___x_1183_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__35, &l_Lean_Meta_Grind_pushNot___redArg___closed__35_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__35);
v___x_1184_ = l_Lean_mkAppB(v___x_1183_, v_arg_1058_, v_arg_1054_);
v___x_1185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1184_);
v___x_1186_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1186_, 0, v___x_1182_);
lean_ctor_set(v___x_1186_, 1, v___x_1185_);
lean_ctor_set_uint8(v___x_1186_, sizeof(void*)*2, v___x_1070_);
v___x_1187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1186_);
if (v_isShared_1047_ == 0)
{
lean_ctor_set(v___x_1046_, 0, v___x_1187_);
v___x_1189_ = v___x_1046_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v___x_1187_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
}
}
else
{
lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1201_; 
lean_dec_ref(v___x_1059_);
lean_dec_ref(v_arg_1003_);
lean_del_object(v___x_956_);
v___x_1191_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__36, &l_Lean_Meta_Grind_pushNot___redArg___closed__36_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__36);
lean_inc_ref(v_arg_1058_);
v___x_1192_ = l_Lean_mkNot(v_arg_1058_);
lean_inc_ref(v_arg_1054_);
v___x_1193_ = l_Lean_mkNot(v_arg_1054_);
v___x_1194_ = l_Lean_mkAppB(v___x_1191_, v___x_1192_, v___x_1193_);
v___x_1195_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__39, &l_Lean_Meta_Grind_pushNot___redArg___closed__39_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__39);
v___x_1196_ = l_Lean_mkAppB(v___x_1195_, v_arg_1058_, v_arg_1054_);
v___x_1197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1196_);
v___x_1198_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1198_, 0, v___x_1194_);
lean_ctor_set(v___x_1198_, 1, v___x_1197_);
lean_ctor_set_uint8(v___x_1198_, sizeof(void*)*2, v___x_1065_);
v___x_1199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1198_);
if (v_isShared_1047_ == 0)
{
lean_ctor_set(v___x_1046_, 0, v___x_1199_);
v___x_1201_ = v___x_1046_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v___x_1199_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
}
else
{
lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1213_; 
lean_dec_ref(v___x_1059_);
lean_dec_ref(v_arg_1003_);
lean_del_object(v___x_956_);
v___x_1203_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__40, &l_Lean_Meta_Grind_pushNot___redArg___closed__40_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__40);
lean_inc_ref(v_arg_1058_);
v___x_1204_ = l_Lean_mkNot(v_arg_1058_);
lean_inc_ref(v_arg_1054_);
v___x_1205_ = l_Lean_mkNot(v_arg_1054_);
v___x_1206_ = l_Lean_mkAppB(v___x_1203_, v___x_1204_, v___x_1205_);
v___x_1207_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__43, &l_Lean_Meta_Grind_pushNot___redArg___closed__43_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__43);
v___x_1208_ = l_Lean_mkAppB(v___x_1207_, v_arg_1058_, v_arg_1054_);
v___x_1209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1208_);
v___x_1210_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1210_, 0, v___x_1206_);
lean_ctor_set(v___x_1210_, 1, v___x_1209_);
lean_ctor_set_uint8(v___x_1210_, sizeof(void*)*2, v___x_1063_);
v___x_1211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1210_);
if (v_isShared_1047_ == 0)
{
lean_ctor_set(v___x_1046_, 0, v___x_1211_);
v___x_1213_ = v___x_1046_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v___x_1211_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
}
else
{
lean_object* v___x_1215_; uint8_t v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
lean_dec_ref(v___x_1059_);
lean_del_object(v___x_1046_);
lean_dec_ref(v_arg_1003_);
lean_del_object(v___x_956_);
v___x_1215_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__45));
v___x_1216_ = 0;
v___x_1217_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__46, &l_Lean_Meta_Grind_pushNot___redArg___closed__46_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__46);
lean_inc_ref(v_arg_1054_);
v___x_1218_ = l_Lean_Expr_app___override(v_arg_1054_, v___x_1217_);
v___x_1219_ = l_Lean_mkNot(v___x_1218_);
lean_inc_ref_n(v_arg_1058_, 2);
v___x_1220_ = l_Lean_mkForall(v___x_1215_, v___x_1216_, v_arg_1058_, v___x_1219_);
v___x_1221_ = l_Lean_Meta_getLevel(v_arg_1058_, v_a_945_, v_a_946_, v_a_947_, v_a_948_);
if (lean_obj_tag(v___x_1221_) == 0)
{
lean_object* v_a_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1237_; 
v_a_1222_ = lean_ctor_get(v___x_1221_, 0);
v_isSharedCheck_1237_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1224_ = v___x_1221_;
v_isShared_1225_ = v_isSharedCheck_1237_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_a_1222_);
lean_dec(v___x_1221_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1237_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1235_; 
v___x_1226_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__48));
v___x_1227_ = lean_box(0);
v___x_1228_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1228_, 0, v_a_1222_);
lean_ctor_set(v___x_1228_, 1, v___x_1227_);
v___x_1229_ = l_Lean_mkConst(v___x_1226_, v___x_1228_);
v___x_1230_ = l_Lean_mkAppB(v___x_1229_, v_arg_1058_, v_arg_1054_);
v___x_1231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1231_, 0, v___x_1230_);
v___x_1232_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1232_, 0, v___x_1220_);
lean_ctor_set(v___x_1232_, 1, v___x_1231_);
lean_ctor_set_uint8(v___x_1232_, sizeof(void*)*2, v___x_1061_);
v___x_1233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1232_);
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 0, v___x_1233_);
v___x_1235_ = v___x_1224_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v___x_1233_);
v___x_1235_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
return v___x_1235_;
}
}
}
else
{
lean_object* v_a_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1245_; 
lean_dec_ref(v___x_1220_);
lean_dec_ref(v_arg_1058_);
lean_dec_ref(v_arg_1054_);
v_a_1238_ = lean_ctor_get(v___x_1221_, 0);
v_isSharedCheck_1245_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1240_ = v___x_1221_;
v_isShared_1241_ = v_isSharedCheck_1245_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_a_1238_);
lean_dec(v___x_1221_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1245_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v___x_1243_; 
if (v_isShared_1241_ == 0)
{
v___x_1243_ = v___x_1240_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v_a_1238_);
v___x_1243_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
return v___x_1243_;
}
}
}
}
}
}
else
{
lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1252_; 
lean_dec_ref(v___x_1055_);
lean_dec_ref(v_arg_1003_);
lean_del_object(v___x_956_);
v___x_1246_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__51, &l_Lean_Meta_Grind_pushNot___redArg___closed__51_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__51);
lean_inc_ref(v_arg_1054_);
v___x_1247_ = l_Lean_Expr_app___override(v___x_1246_, v_arg_1054_);
v___x_1248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1248_, 0, v___x_1247_);
v___x_1249_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1249_, 0, v_arg_1054_);
lean_ctor_set(v___x_1249_, 1, v___x_1248_);
lean_ctor_set_uint8(v___x_1249_, sizeof(void*)*2, v___x_1056_);
v___x_1250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1249_);
if (v_isShared_1047_ == 0)
{
lean_ctor_set(v___x_1046_, 0, v___x_1250_);
v___x_1252_ = v___x_1046_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v___x_1250_);
v___x_1252_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
return v___x_1252_;
}
}
}
}
else
{
lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1259_; 
lean_dec_ref(v___x_1048_);
lean_dec_ref(v_arg_1003_);
lean_del_object(v___x_956_);
v___x_1254_ = lean_obj_once(&l_Lean_Meta_Grind_simpEq___redArg___closed__14, &l_Lean_Meta_Grind_simpEq___redArg___closed__14_once, _init_l_Lean_Meta_Grind_simpEq___redArg___closed__14);
v___x_1255_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__55, &l_Lean_Meta_Grind_pushNot___redArg___closed__55_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__55);
v___x_1256_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1256_, 0, v___x_1254_);
lean_ctor_set(v___x_1256_, 1, v___x_1255_);
lean_ctor_set_uint8(v___x_1256_, sizeof(void*)*2, v___x_1052_);
v___x_1257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1256_);
if (v_isShared_1047_ == 0)
{
lean_ctor_set(v___x_1046_, 0, v___x_1257_);
v___x_1259_ = v___x_1046_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v___x_1257_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
else
{
lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1266_; 
lean_dec_ref(v___x_1048_);
lean_dec_ref(v_arg_1003_);
lean_del_object(v___x_956_);
v___x_1261_ = lean_obj_once(&l_Lean_Meta_Grind_simpEq___redArg___closed__11, &l_Lean_Meta_Grind_simpEq___redArg___closed__11_once, _init_l_Lean_Meta_Grind_simpEq___redArg___closed__11);
v___x_1262_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__59, &l_Lean_Meta_Grind_pushNot___redArg___closed__59_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__59);
v___x_1263_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1263_, 0, v___x_1261_);
lean_ctor_set(v___x_1263_, 1, v___x_1262_);
lean_ctor_set_uint8(v___x_1263_, sizeof(void*)*2, v___x_1050_);
v___x_1264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1263_);
if (v_isShared_1047_ == 0)
{
lean_ctor_set(v___x_1046_, 0, v___x_1264_);
v___x_1266_ = v___x_1046_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v___x_1264_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
return v___x_1266_;
}
}
}
}
else
{
lean_object* v_a_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1276_; 
lean_dec_ref(v_arg_1003_);
lean_del_object(v___x_956_);
v_a_1269_ = lean_ctor_get(v___x_1043_, 0);
v_isSharedCheck_1276_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1271_ = v___x_1043_;
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_a_1269_);
lean_dec(v___x_1043_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1274_; 
if (v_isShared_1272_ == 0)
{
v___x_1274_ = v___x_1271_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v_a_1269_);
v___x_1274_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
return v___x_1274_;
}
}
}
v___jp_1004_:
{
if (lean_obj_tag(v_arg_1003_) == 7)
{
lean_object* v_binderName_1009_; lean_object* v_binderType_1010_; lean_object* v_body_1011_; uint8_t v_binderInfo_1012_; lean_object* v___x_1013_; 
lean_del_object(v___x_956_);
v_binderName_1009_ = lean_ctor_get(v_arg_1003_, 0);
lean_inc(v_binderName_1009_);
v_binderType_1010_ = lean_ctor_get(v_arg_1003_, 1);
lean_inc_ref_n(v_binderType_1010_, 2);
v_body_1011_ = lean_ctor_get(v_arg_1003_, 2);
lean_inc_ref(v_body_1011_);
v_binderInfo_1012_ = lean_ctor_get_uint8(v_arg_1003_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_arg_1003_, 3);
v___x_1013_ = l_Lean_Meta_isProp(v_binderType_1010_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_);
if (lean_obj_tag(v___x_1013_) == 0)
{
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1030_; 
v_a_1014_ = lean_ctor_get(v___x_1013_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1016_ = v___x_1013_;
v_isShared_1017_ = v_isSharedCheck_1030_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_1013_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1030_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
uint8_t v___x_1018_; 
v___x_1018_ = l_Lean_Expr_hasLooseBVars(v_body_1011_);
if (v___x_1018_ == 0)
{
uint8_t v___x_1019_; 
v___x_1019_ = lean_unbox(v_a_1014_);
lean_dec(v_a_1014_);
if (v___x_1019_ == 0)
{
lean_del_object(v___x_1016_);
v___y_964_ = v_binderType_1010_;
v___y_965_ = v___y_1007_;
v___y_966_ = v___y_1006_;
v___y_967_ = v_binderInfo_1012_;
v___y_968_ = v_binderName_1009_;
v___y_969_ = v___y_1008_;
v___y_970_ = v___y_1005_;
v___y_971_ = v_body_1011_;
goto v___jp_963_;
}
else
{
lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1028_; 
lean_dec(v_binderName_1009_);
lean_inc_ref(v_body_1011_);
v___x_1020_ = l_Lean_mkNot(v_body_1011_);
lean_inc_ref(v_binderType_1010_);
v___x_1021_ = l_Lean_mkAnd(v_binderType_1010_, v___x_1020_);
v___x_1022_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__8, &l_Lean_Meta_Grind_pushNot___redArg___closed__8_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__8);
v___x_1023_ = l_Lean_mkAppB(v___x_1022_, v_binderType_1010_, v_body_1011_);
v___x_1024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1023_);
v___x_1025_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1025_, 0, v___x_1021_);
lean_ctor_set(v___x_1025_, 1, v___x_1024_);
lean_ctor_set_uint8(v___x_1025_, sizeof(void*)*2, v___x_962_);
v___x_1026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1025_);
if (v_isShared_1017_ == 0)
{
lean_ctor_set(v___x_1016_, 0, v___x_1026_);
v___x_1028_ = v___x_1016_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v___x_1026_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
else
{
lean_del_object(v___x_1016_);
lean_dec(v_a_1014_);
v___y_964_ = v_binderType_1010_;
v___y_965_ = v___y_1007_;
v___y_966_ = v___y_1006_;
v___y_967_ = v_binderInfo_1012_;
v___y_968_ = v_binderName_1009_;
v___y_969_ = v___y_1008_;
v___y_970_ = v___y_1005_;
v___y_971_ = v_body_1011_;
goto v___jp_963_;
}
}
}
else
{
lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1038_; 
lean_dec_ref(v_body_1011_);
lean_dec_ref(v_binderType_1010_);
lean_dec(v_binderName_1009_);
v_a_1031_ = lean_ctor_get(v___x_1013_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1033_ = v___x_1013_;
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_1013_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1036_; 
if (v_isShared_1034_ == 0)
{
v___x_1036_ = v___x_1033_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_a_1031_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
}
else
{
lean_object* v___x_1039_; lean_object* v___x_1041_; 
lean_dec_ref(v_arg_1003_);
v___x_1039_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
if (v_isShared_957_ == 0)
{
lean_ctor_set(v___x_956_, 0, v___x_1039_);
v___x_1041_ = v___x_956_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_1039_);
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
v___jp_963_:
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
lean_inc_ref(v___y_971_);
lean_inc_ref_n(v___y_964_, 3);
lean_inc(v___y_968_);
v___x_972_ = l_Lean_mkLambda(v___y_968_, v___y_967_, v___y_964_, v___y_971_);
v___x_973_ = l_Lean_mkNot(v___y_971_);
v___x_974_ = l_Lean_mkLambda(v___y_968_, v___y_967_, v___y_964_, v___x_973_);
v___x_975_ = l_Lean_Meta_getLevel(v___y_964_, v___y_970_, v___y_966_, v___y_965_, v___y_969_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v_a_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_994_; 
v_a_976_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_994_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_994_ == 0)
{
v___x_978_ = v___x_975_;
v_isShared_979_ = v_isSharedCheck_994_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_a_976_);
lean_dec(v___x_975_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_994_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_992_; 
v___x_980_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__3));
v___x_981_ = lean_box(0);
v___x_982_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_982_, 0, v_a_976_);
lean_ctor_set(v___x_982_, 1, v___x_981_);
lean_inc_ref(v___x_982_);
v___x_983_ = l_Lean_mkConst(v___x_980_, v___x_982_);
lean_inc_ref(v___y_964_);
v___x_984_ = l_Lean_mkAppB(v___x_983_, v___y_964_, v___x_974_);
v___x_985_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__5));
v___x_986_ = l_Lean_mkConst(v___x_985_, v___x_982_);
v___x_987_ = l_Lean_mkAppB(v___x_986_, v___y_964_, v___x_972_);
v___x_988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_988_, 0, v___x_987_);
v___x_989_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_989_, 0, v___x_984_);
lean_ctor_set(v___x_989_, 1, v___x_988_);
lean_ctor_set_uint8(v___x_989_, sizeof(void*)*2, v___x_962_);
v___x_990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_990_, 0, v___x_989_);
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 0, v___x_990_);
v___x_992_ = v___x_978_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v___x_990_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
}
else
{
lean_object* v_a_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1002_; 
lean_dec_ref(v___x_974_);
lean_dec_ref(v___x_972_);
lean_dec_ref(v___y_964_);
v_a_995_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_997_ = v___x_975_;
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_a_995_);
lean_dec(v___x_975_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_1000_; 
if (v_isShared_998_ == 0)
{
v___x_1000_ = v___x_997_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_a_995_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1285_; 
v_a_1278_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1280_ = v___x_953_;
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_a_1278_);
lean_dec(v___x_953_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1283_; 
if (v_isShared_1281_ == 0)
{
v___x_1283_ = v___x_1280_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_a_1278_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
}
v___jp_950_:
{
lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_951_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
v___x_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_952_, 0, v___x_951_);
return v___x_952_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNot___redArg___boxed(lean_object* v_e_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_){
_start:
{
lean_object* v_res_1292_; 
v_res_1292_ = l_Lean_Meta_Grind_pushNot___redArg(v_e_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
lean_dec(v_a_1290_);
lean_dec_ref(v_a_1289_);
lean_dec(v_a_1288_);
lean_dec_ref(v_a_1287_);
return v_res_1292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNot(lean_object* v_e_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_){
_start:
{
lean_object* v___x_1302_; 
v___x_1302_ = l_Lean_Meta_Grind_pushNot___redArg(v_e_1293_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_);
return v___x_1302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNot___boxed(lean_object* v_e_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_){
_start:
{
lean_object* v_res_1312_; 
v_res_1312_ = l_Lean_Meta_Grind_pushNot(v_e_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_);
lean_dec(v_a_1310_);
lean_dec_ref(v_a_1309_);
lean_dec(v_a_1308_);
lean_dec_ref(v_a_1307_);
lean_dec(v_a_1306_);
lean_dec_ref(v_a_1305_);
lean_dec(v_a_1304_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2942474041____hygCtx___hyg_11_(){
_start:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1329_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2942474041____hygCtx___hyg_11_));
v___x_1330_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2942474041____hygCtx___hyg_11_));
v___x_1331_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_pushNot___boxed), 9, 0);
v___x_1332_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_1329_, v___x_1330_, v___x_1331_);
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2942474041____hygCtx___hyg_11____boxed(lean_object* v_a_1333_){
_start:
{
lean_object* v_res_1334_; 
v_res_1334_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2942474041____hygCtx___hyg_11_();
return v_res_1334_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpOr___redArg___closed__2(void){
_start:
{
lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; 
v___x_1340_ = lean_box(0);
v___x_1341_ = ((lean_object*)(l_Lean_Meta_Grind_simpOr___redArg___closed__1));
v___x_1342_ = l_Lean_mkConst(v___x_1341_, v___x_1340_);
return v___x_1342_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpOr___redArg___closed__5(void){
_start:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; 
v___x_1348_ = lean_box(0);
v___x_1349_ = ((lean_object*)(l_Lean_Meta_Grind_simpOr___redArg___closed__4));
v___x_1350_ = l_Lean_mkConst(v___x_1349_, v___x_1348_);
return v___x_1350_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpOr___redArg___closed__8(void){
_start:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1354_ = lean_box(0);
v___x_1355_ = ((lean_object*)(l_Lean_Meta_Grind_simpOr___redArg___closed__7));
v___x_1356_ = l_Lean_mkConst(v___x_1355_, v___x_1354_);
return v___x_1356_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpOr___redArg___closed__11(void){
_start:
{
lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1360_ = lean_box(0);
v___x_1361_ = ((lean_object*)(l_Lean_Meta_Grind_simpOr___redArg___closed__10));
v___x_1362_ = l_Lean_mkConst(v___x_1361_, v___x_1360_);
return v___x_1362_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpOr___redArg___closed__14(void){
_start:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; 
v___x_1368_ = lean_box(0);
v___x_1369_ = ((lean_object*)(l_Lean_Meta_Grind_simpOr___redArg___closed__13));
v___x_1370_ = l_Lean_mkConst(v___x_1369_, v___x_1368_);
return v___x_1370_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpOr___redArg___closed__17(void){
_start:
{
lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; 
v___x_1374_ = lean_box(0);
v___x_1375_ = ((lean_object*)(l_Lean_Meta_Grind_simpOr___redArg___closed__16));
v___x_1376_ = l_Lean_mkConst(v___x_1375_, v___x_1374_);
return v___x_1376_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpOr___redArg___closed__20(void){
_start:
{
lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1380_ = lean_box(0);
v___x_1381_ = ((lean_object*)(l_Lean_Meta_Grind_simpOr___redArg___closed__19));
v___x_1382_ = l_Lean_mkConst(v___x_1381_, v___x_1380_);
return v___x_1382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpOr___redArg(lean_object* v_e_1383_, lean_object* v_a_1384_){
_start:
{
lean_object* v___x_1392_; 
v___x_1392_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1383_, v_a_1384_);
if (lean_obj_tag(v___x_1392_) == 0)
{
lean_object* v_a_1393_; lean_object* v___x_1394_; uint8_t v___x_1395_; 
v_a_1393_ = lean_ctor_get(v___x_1392_, 0);
lean_inc(v_a_1393_);
lean_dec_ref_known(v___x_1392_, 1);
v___x_1394_ = l_Lean_Expr_cleanupAnnotations(v_a_1393_);
lean_dec(v_a_1393_);
v___x_1395_ = l_Lean_Expr_isApp(v___x_1394_);
if (v___x_1395_ == 0)
{
lean_dec_ref(v___x_1394_);
goto v___jp_1389_;
}
else
{
lean_object* v___x_1396_; uint8_t v___x_1397_; 
v___x_1396_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1394_);
v___x_1397_ = l_Lean_Expr_isApp(v___x_1396_);
if (v___x_1397_ == 0)
{
lean_dec_ref(v___x_1396_);
lean_dec_ref(v___x_1394_);
goto v___jp_1389_;
}
else
{
lean_object* v___x_1398_; lean_object* v___x_1399_; uint8_t v___x_1400_; 
v___x_1398_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1396_);
v___x_1399_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__10));
v___x_1400_ = l_Lean_Expr_isConstOf(v___x_1398_, v___x_1399_);
lean_dec_ref(v___x_1398_);
if (v___x_1400_ == 0)
{
lean_dec_ref(v___x_1396_);
lean_dec_ref(v___x_1394_);
goto v___jp_1389_;
}
else
{
lean_object* v_arg_1401_; lean_object* v_arg_1402_; lean_object* v___y_1404_; lean_object* v___x_1478_; 
v_arg_1401_ = lean_ctor_get(v___x_1394_, 1);
lean_inc_ref(v_arg_1401_);
lean_dec_ref(v___x_1394_);
v_arg_1402_ = lean_ctor_get(v___x_1396_, 1);
lean_inc_ref_n(v_arg_1402_, 2);
lean_dec_ref(v___x_1396_);
v___x_1478_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1402_, v_a_1384_);
if (lean_obj_tag(v___x_1478_) == 0)
{
lean_object* v_a_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1521_; 
v_a_1479_ = lean_ctor_get(v___x_1478_, 0);
v_isSharedCheck_1521_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1481_ = v___x_1478_;
v_isShared_1482_ = v_isSharedCheck_1521_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_a_1479_);
lean_dec(v___x_1478_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1521_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; uint8_t v___x_1485_; 
v___x_1483_ = l_Lean_Expr_cleanupAnnotations(v_a_1479_);
lean_dec(v_a_1479_);
v___x_1484_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__13));
v___x_1485_ = l_Lean_Expr_isConstOf(v___x_1483_, v___x_1484_);
if (v___x_1485_ == 0)
{
lean_object* v___x_1486_; uint8_t v___x_1487_; 
v___x_1486_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__10));
v___x_1487_ = l_Lean_Expr_isConstOf(v___x_1483_, v___x_1486_);
if (v___x_1487_ == 0)
{
uint8_t v___x_1488_; 
v___x_1488_ = l_Lean_Expr_isApp(v___x_1483_);
if (v___x_1488_ == 0)
{
lean_dec_ref(v___x_1483_);
lean_del_object(v___x_1481_);
v___y_1404_ = v_a_1384_;
goto v___jp_1403_;
}
else
{
lean_object* v___x_1489_; uint8_t v___x_1490_; 
v___x_1489_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1483_);
v___x_1490_ = l_Lean_Expr_isApp(v___x_1489_);
if (v___x_1490_ == 0)
{
lean_dec_ref(v___x_1489_);
lean_dec_ref(v___x_1483_);
lean_del_object(v___x_1481_);
v___y_1404_ = v_a_1384_;
goto v___jp_1403_;
}
else
{
lean_object* v___x_1491_; uint8_t v___x_1492_; 
v___x_1491_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1489_);
v___x_1492_ = l_Lean_Expr_isConstOf(v___x_1491_, v___x_1399_);
lean_dec_ref(v___x_1491_);
if (v___x_1492_ == 0)
{
lean_dec_ref(v___x_1489_);
lean_dec_ref(v___x_1483_);
lean_del_object(v___x_1481_);
v___y_1404_ = v_a_1384_;
goto v___jp_1403_;
}
else
{
lean_object* v_arg_1493_; lean_object* v_arg_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1503_; 
lean_dec_ref(v_arg_1402_);
v_arg_1493_ = lean_ctor_get(v___x_1483_, 1);
lean_inc_ref_n(v_arg_1493_, 2);
lean_dec_ref(v___x_1483_);
v_arg_1494_ = lean_ctor_get(v___x_1489_, 1);
lean_inc_ref_n(v_arg_1494_, 2);
lean_dec_ref(v___x_1489_);
lean_inc_ref(v_arg_1401_);
v___x_1495_ = l_Lean_mkOr(v_arg_1493_, v_arg_1401_);
v___x_1496_ = l_Lean_mkOr(v_arg_1494_, v___x_1495_);
v___x_1497_ = lean_obj_once(&l_Lean_Meta_Grind_simpOr___redArg___closed__14, &l_Lean_Meta_Grind_simpOr___redArg___closed__14_once, _init_l_Lean_Meta_Grind_simpOr___redArg___closed__14);
v___x_1498_ = l_Lean_mkApp3(v___x_1497_, v_arg_1494_, v_arg_1493_, v_arg_1401_);
v___x_1499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1499_, 0, v___x_1498_);
v___x_1500_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1500_, 0, v___x_1496_);
lean_ctor_set(v___x_1500_, 1, v___x_1499_);
lean_ctor_set_uint8(v___x_1500_, sizeof(void*)*2, v___x_1492_);
v___x_1501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1501_, 0, v___x_1500_);
if (v_isShared_1482_ == 0)
{
lean_ctor_set(v___x_1481_, 0, v___x_1501_);
v___x_1503_ = v___x_1481_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v___x_1501_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
return v___x_1503_;
}
}
}
}
}
else
{
lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1511_; 
lean_dec_ref(v___x_1483_);
v___x_1505_ = lean_obj_once(&l_Lean_Meta_Grind_simpOr___redArg___closed__17, &l_Lean_Meta_Grind_simpOr___redArg___closed__17_once, _init_l_Lean_Meta_Grind_simpOr___redArg___closed__17);
v___x_1506_ = l_Lean_Expr_app___override(v___x_1505_, v_arg_1401_);
v___x_1507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1507_, 0, v___x_1506_);
v___x_1508_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1508_, 0, v_arg_1402_);
lean_ctor_set(v___x_1508_, 1, v___x_1507_);
lean_ctor_set_uint8(v___x_1508_, sizeof(void*)*2, v___x_1487_);
v___x_1509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1508_);
if (v_isShared_1482_ == 0)
{
lean_ctor_set(v___x_1481_, 0, v___x_1509_);
v___x_1511_ = v___x_1481_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v___x_1509_);
v___x_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
return v___x_1511_;
}
}
}
else
{
lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1519_; 
lean_dec_ref(v___x_1483_);
lean_dec_ref(v_arg_1402_);
v___x_1513_ = lean_obj_once(&l_Lean_Meta_Grind_simpOr___redArg___closed__20, &l_Lean_Meta_Grind_simpOr___redArg___closed__20_once, _init_l_Lean_Meta_Grind_simpOr___redArg___closed__20);
lean_inc_ref(v_arg_1401_);
v___x_1514_ = l_Lean_Expr_app___override(v___x_1513_, v_arg_1401_);
v___x_1515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1515_, 0, v___x_1514_);
v___x_1516_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1516_, 0, v_arg_1401_);
lean_ctor_set(v___x_1516_, 1, v___x_1515_);
lean_ctor_set_uint8(v___x_1516_, sizeof(void*)*2, v___x_1485_);
v___x_1517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1517_, 0, v___x_1516_);
if (v_isShared_1482_ == 0)
{
lean_ctor_set(v___x_1481_, 0, v___x_1517_);
v___x_1519_ = v___x_1481_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v___x_1517_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
return v___x_1519_;
}
}
}
}
else
{
lean_object* v_a_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1529_; 
lean_dec_ref(v_arg_1402_);
lean_dec_ref(v_arg_1401_);
v_a_1522_ = lean_ctor_get(v___x_1478_, 0);
v_isSharedCheck_1529_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1529_ == 0)
{
v___x_1524_ = v___x_1478_;
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_a_1522_);
lean_dec(v___x_1478_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v___x_1527_; 
if (v_isShared_1525_ == 0)
{
v___x_1527_ = v___x_1524_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_a_1522_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
return v___x_1527_;
}
}
}
v___jp_1403_:
{
lean_object* v___x_1405_; 
lean_inc_ref(v_arg_1401_);
v___x_1405_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1401_, v___y_1404_);
if (lean_obj_tag(v___x_1405_) == 0)
{
lean_object* v_a_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1469_; 
v_a_1406_ = lean_ctor_get(v___x_1405_, 0);
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1408_ = v___x_1405_;
v_isShared_1409_ = v_isSharedCheck_1469_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_a_1406_);
lean_dec(v___x_1405_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1469_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; uint8_t v___x_1412_; 
v___x_1410_ = l_Lean_Expr_cleanupAnnotations(v_a_1406_);
lean_dec(v_a_1406_);
v___x_1411_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__13));
v___x_1412_ = l_Lean_Expr_isConstOf(v___x_1410_, v___x_1411_);
if (v___x_1412_ == 0)
{
lean_object* v___x_1413_; uint8_t v___x_1414_; 
v___x_1413_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__10));
v___x_1414_ = l_Lean_Expr_isConstOf(v___x_1410_, v___x_1413_);
if (v___x_1414_ == 0)
{
uint8_t v___x_1415_; 
lean_dec_ref(v_arg_1401_);
v___x_1415_ = l_Lean_Expr_isApp(v___x_1410_);
if (v___x_1415_ == 0)
{
lean_dec_ref(v___x_1410_);
lean_del_object(v___x_1408_);
lean_dec_ref(v_arg_1402_);
goto v___jp_1386_;
}
else
{
lean_object* v___x_1416_; uint8_t v___x_1417_; 
v___x_1416_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1410_);
v___x_1417_ = l_Lean_Expr_isApp(v___x_1416_);
if (v___x_1417_ == 0)
{
lean_dec_ref(v___x_1416_);
lean_dec_ref(v___x_1410_);
lean_del_object(v___x_1408_);
lean_dec_ref(v_arg_1402_);
goto v___jp_1386_;
}
else
{
lean_object* v___x_1418_; uint8_t v___x_1419_; 
v___x_1418_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1416_);
v___x_1419_ = l_Lean_Expr_isConstOf(v___x_1418_, v___x_1399_);
lean_dec_ref(v___x_1418_);
if (v___x_1419_ == 0)
{
lean_dec_ref(v___x_1416_);
lean_dec_ref(v___x_1410_);
lean_del_object(v___x_1408_);
lean_dec_ref(v_arg_1402_);
goto v___jp_1386_;
}
else
{
uint8_t v___x_1420_; 
v___x_1420_ = l_Lean_Expr_isForall(v_arg_1402_);
if (v___x_1420_ == 0)
{
lean_object* v_arg_1421_; lean_object* v_arg_1422_; uint8_t v___x_1423_; 
v_arg_1421_ = lean_ctor_get(v___x_1410_, 1);
lean_inc_ref(v_arg_1421_);
lean_dec_ref(v___x_1410_);
v_arg_1422_ = lean_ctor_get(v___x_1416_, 1);
lean_inc_ref(v_arg_1422_);
lean_dec_ref(v___x_1416_);
v___x_1423_ = l_Lean_Expr_isForall(v_arg_1422_);
if (v___x_1423_ == 0)
{
uint8_t v___x_1424_; 
v___x_1424_ = l_Lean_Expr_isForall(v_arg_1421_);
if (v___x_1424_ == 0)
{
lean_object* v___x_1425_; lean_object* v___x_1427_; 
lean_dec_ref(v_arg_1422_);
lean_dec_ref(v_arg_1421_);
lean_dec_ref(v_arg_1402_);
v___x_1425_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 0, v___x_1425_);
v___x_1427_ = v___x_1408_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v___x_1425_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
else
{
lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1437_; 
lean_inc_ref(v_arg_1402_);
lean_inc_ref(v_arg_1422_);
v___x_1429_ = l_Lean_mkOr(v_arg_1422_, v_arg_1402_);
lean_inc_ref(v_arg_1421_);
v___x_1430_ = l_Lean_mkOr(v_arg_1421_, v___x_1429_);
v___x_1431_ = lean_obj_once(&l_Lean_Meta_Grind_simpOr___redArg___closed__2, &l_Lean_Meta_Grind_simpOr___redArg___closed__2_once, _init_l_Lean_Meta_Grind_simpOr___redArg___closed__2);
v___x_1432_ = l_Lean_mkApp3(v___x_1431_, v_arg_1402_, v_arg_1422_, v_arg_1421_);
v___x_1433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1432_);
v___x_1434_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1434_, 0, v___x_1430_);
lean_ctor_set(v___x_1434_, 1, v___x_1433_);
lean_ctor_set_uint8(v___x_1434_, sizeof(void*)*2, v___x_1419_);
v___x_1435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1435_, 0, v___x_1434_);
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 0, v___x_1435_);
v___x_1437_ = v___x_1408_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v___x_1435_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
}
else
{
lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1447_; 
lean_inc_ref(v_arg_1421_);
lean_inc_ref(v_arg_1402_);
v___x_1439_ = l_Lean_mkOr(v_arg_1402_, v_arg_1421_);
lean_inc_ref(v_arg_1422_);
v___x_1440_ = l_Lean_mkOr(v_arg_1422_, v___x_1439_);
v___x_1441_ = lean_obj_once(&l_Lean_Meta_Grind_simpOr___redArg___closed__5, &l_Lean_Meta_Grind_simpOr___redArg___closed__5_once, _init_l_Lean_Meta_Grind_simpOr___redArg___closed__5);
v___x_1442_ = l_Lean_mkApp3(v___x_1441_, v_arg_1402_, v_arg_1422_, v_arg_1421_);
v___x_1443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1442_);
v___x_1444_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1444_, 0, v___x_1440_);
lean_ctor_set(v___x_1444_, 1, v___x_1443_);
lean_ctor_set_uint8(v___x_1444_, sizeof(void*)*2, v___x_1419_);
v___x_1445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1445_, 0, v___x_1444_);
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 0, v___x_1445_);
v___x_1447_ = v___x_1408_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v___x_1445_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
return v___x_1447_;
}
}
}
else
{
lean_object* v___x_1449_; lean_object* v___x_1451_; 
lean_dec_ref(v___x_1416_);
lean_dec_ref(v___x_1410_);
lean_dec_ref(v_arg_1402_);
v___x_1449_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 0, v___x_1449_);
v___x_1451_ = v___x_1408_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v___x_1449_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
}
}
}
}
else
{
lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1459_; 
lean_dec_ref(v___x_1410_);
v___x_1453_ = lean_obj_once(&l_Lean_Meta_Grind_simpOr___redArg___closed__8, &l_Lean_Meta_Grind_simpOr___redArg___closed__8_once, _init_l_Lean_Meta_Grind_simpOr___redArg___closed__8);
v___x_1454_ = l_Lean_Expr_app___override(v___x_1453_, v_arg_1402_);
v___x_1455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1455_, 0, v___x_1454_);
v___x_1456_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1456_, 0, v_arg_1401_);
lean_ctor_set(v___x_1456_, 1, v___x_1455_);
lean_ctor_set_uint8(v___x_1456_, sizeof(void*)*2, v___x_1414_);
v___x_1457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1457_, 0, v___x_1456_);
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 0, v___x_1457_);
v___x_1459_ = v___x_1408_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v___x_1457_);
v___x_1459_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
return v___x_1459_;
}
}
}
else
{
lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1467_; 
lean_dec_ref(v___x_1410_);
lean_dec_ref(v_arg_1401_);
v___x_1461_ = lean_obj_once(&l_Lean_Meta_Grind_simpOr___redArg___closed__11, &l_Lean_Meta_Grind_simpOr___redArg___closed__11_once, _init_l_Lean_Meta_Grind_simpOr___redArg___closed__11);
lean_inc_ref(v_arg_1402_);
v___x_1462_ = l_Lean_Expr_app___override(v___x_1461_, v_arg_1402_);
v___x_1463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1463_, 0, v___x_1462_);
v___x_1464_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1464_, 0, v_arg_1402_);
lean_ctor_set(v___x_1464_, 1, v___x_1463_);
lean_ctor_set_uint8(v___x_1464_, sizeof(void*)*2, v___x_1412_);
v___x_1465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1465_, 0, v___x_1464_);
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 0, v___x_1465_);
v___x_1467_ = v___x_1408_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v___x_1465_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
}
}
else
{
lean_object* v_a_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1477_; 
lean_dec_ref(v_arg_1402_);
lean_dec_ref(v_arg_1401_);
v_a_1470_ = lean_ctor_get(v___x_1405_, 0);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1472_ = v___x_1405_;
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_a_1470_);
lean_dec(v___x_1405_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1475_; 
if (v_isShared_1473_ == 0)
{
v___x_1475_ = v___x_1472_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_a_1470_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
return v___x_1475_;
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1537_; 
v_a_1530_ = lean_ctor_get(v___x_1392_, 0);
v_isSharedCheck_1537_ = !lean_is_exclusive(v___x_1392_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1532_ = v___x_1392_;
v_isShared_1533_ = v_isSharedCheck_1537_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_a_1530_);
lean_dec(v___x_1392_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1537_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v___x_1535_; 
if (v_isShared_1533_ == 0)
{
v___x_1535_ = v___x_1532_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_a_1530_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
}
v___jp_1386_:
{
lean_object* v___x_1387_; lean_object* v___x_1388_; 
v___x_1387_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
v___x_1388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1388_, 0, v___x_1387_);
return v___x_1388_;
}
v___jp_1389_:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; 
v___x_1390_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
v___x_1391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1391_, 0, v___x_1390_);
return v___x_1391_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpOr___redArg___boxed(lean_object* v_e_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_){
_start:
{
lean_object* v_res_1541_; 
v_res_1541_ = l_Lean_Meta_Grind_simpOr___redArg(v_e_1538_, v_a_1539_);
lean_dec(v_a_1539_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpOr(lean_object* v_e_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_){
_start:
{
lean_object* v___x_1551_; 
v___x_1551_ = l_Lean_Meta_Grind_simpOr___redArg(v_e_1542_, v_a_1547_);
return v___x_1551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpOr___boxed(lean_object* v_e_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_){
_start:
{
lean_object* v_res_1561_; 
v_res_1561_ = l_Lean_Meta_Grind_simpOr(v_e_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_);
lean_dec(v_a_1559_);
lean_dec_ref(v_a_1558_);
lean_dec(v_a_1557_);
lean_dec_ref(v_a_1556_);
lean_dec(v_a_1555_);
lean_dec_ref(v_a_1554_);
lean_dec(v_a_1553_);
return v_res_1561_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_12_(){
_start:
{
lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1579_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_12_));
v___x_1580_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_12_));
v___x_1581_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpOr___boxed), 9, 0);
v___x_1582_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_1579_, v___x_1580_, v___x_1581_);
return v___x_1582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_12____boxed(lean_object* v_a_1583_){
_start:
{
lean_object* v_res_1584_; 
v_res_1584_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_12_();
return v_res_1584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reduceCtorEqCheap___lam__0(uint8_t v___x_1585_, uint8_t v___x_1586_, lean_object* v_h_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_){
_start:
{
lean_object* v___x_1596_; lean_object* v___y_1598_; lean_object* v___x_1618_; 
v___x_1596_ = lean_obj_once(&l_Lean_Meta_Grind_simpEq___redArg___closed__14, &l_Lean_Meta_Grind_simpEq___redArg___closed__14_once, _init_l_Lean_Meta_Grind_simpEq___redArg___closed__14);
lean_inc_ref(v_h_1587_);
v___x_1618_ = l_Lean_Meta_mkNoConfusion(v___x_1596_, v_h_1587_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_);
if (lean_obj_tag(v___x_1618_) == 0)
{
lean_object* v_a_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; uint8_t v___x_1623_; lean_object* v___x_1624_; 
v_a_1619_ = lean_ctor_get(v___x_1618_, 0);
lean_inc(v_a_1619_);
lean_dec_ref_known(v___x_1618_, 1);
v___x_1620_ = lean_unsigned_to_nat(1u);
v___x_1621_ = lean_mk_empty_array_with_capacity(v___x_1620_);
v___x_1622_ = lean_array_push(v___x_1621_, v_h_1587_);
v___x_1623_ = 1;
v___x_1624_ = l_Lean_Meta_mkLambdaFVars(v___x_1622_, v_a_1619_, v___x_1586_, v___x_1585_, v___x_1586_, v___x_1585_, v___x_1623_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_);
lean_dec_ref(v___x_1622_);
if (lean_obj_tag(v___x_1624_) == 0)
{
lean_object* v_a_1625_; lean_object* v___x_1626_; uint8_t v_transparency_1627_; uint8_t v___x_1628_; uint8_t v___x_1629_; 
v_a_1625_ = lean_ctor_get(v___x_1624_, 0);
lean_inc(v_a_1625_);
lean_dec_ref_known(v___x_1624_, 1);
v___x_1626_ = l_Lean_Meta_Context_config(v___y_1591_);
v_transparency_1627_ = lean_ctor_get_uint8(v___x_1626_, 9);
lean_dec_ref(v___x_1626_);
v___x_1628_ = 1;
v___x_1629_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_1627_, v___x_1628_);
if (v___x_1629_ == 0)
{
lean_object* v_keyedConfig_1630_; uint8_t v_trackZetaDelta_1631_; lean_object* v_zetaDeltaSet_1632_; lean_object* v_lctx_1633_; lean_object* v_localInstances_1634_; lean_object* v_defEqCtx_x3f_1635_; lean_object* v_synthPendingDepth_1636_; lean_object* v_customCanUnfoldPredicate_x3f_1637_; uint8_t v_univApprox_1638_; uint8_t v_inTypeClassResolution_1639_; uint8_t v_cacheInferType_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; 
v_keyedConfig_1630_ = lean_ctor_get(v___y_1591_, 0);
v_trackZetaDelta_1631_ = lean_ctor_get_uint8(v___y_1591_, sizeof(void*)*7);
v_zetaDeltaSet_1632_ = lean_ctor_get(v___y_1591_, 1);
v_lctx_1633_ = lean_ctor_get(v___y_1591_, 2);
v_localInstances_1634_ = lean_ctor_get(v___y_1591_, 3);
v_defEqCtx_x3f_1635_ = lean_ctor_get(v___y_1591_, 4);
v_synthPendingDepth_1636_ = lean_ctor_get(v___y_1591_, 5);
v_customCanUnfoldPredicate_x3f_1637_ = lean_ctor_get(v___y_1591_, 6);
v_univApprox_1638_ = lean_ctor_get_uint8(v___y_1591_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1639_ = lean_ctor_get_uint8(v___y_1591_, sizeof(void*)*7 + 2);
v_cacheInferType_1640_ = lean_ctor_get_uint8(v___y_1591_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_1630_);
v___x_1641_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_1628_, v_keyedConfig_1630_);
lean_inc(v_customCanUnfoldPredicate_x3f_1637_);
lean_inc(v_synthPendingDepth_1636_);
lean_inc(v_defEqCtx_x3f_1635_);
lean_inc_ref(v_localInstances_1634_);
lean_inc_ref(v_lctx_1633_);
lean_inc(v_zetaDeltaSet_1632_);
v___x_1642_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1642_, 0, v___x_1641_);
lean_ctor_set(v___x_1642_, 1, v_zetaDeltaSet_1632_);
lean_ctor_set(v___x_1642_, 2, v_lctx_1633_);
lean_ctor_set(v___x_1642_, 3, v_localInstances_1634_);
lean_ctor_set(v___x_1642_, 4, v_defEqCtx_x3f_1635_);
lean_ctor_set(v___x_1642_, 5, v_synthPendingDepth_1636_);
lean_ctor_set(v___x_1642_, 6, v_customCanUnfoldPredicate_x3f_1637_);
lean_ctor_set_uint8(v___x_1642_, sizeof(void*)*7, v_trackZetaDelta_1631_);
lean_ctor_set_uint8(v___x_1642_, sizeof(void*)*7 + 1, v_univApprox_1638_);
lean_ctor_set_uint8(v___x_1642_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1639_);
lean_ctor_set_uint8(v___x_1642_, sizeof(void*)*7 + 3, v_cacheInferType_1640_);
v___x_1643_ = l_Lean_Meta_mkEqFalse_x27(v_a_1625_, v___x_1642_, v___y_1592_, v___y_1593_, v___y_1594_);
lean_dec_ref_known(v___x_1642_, 7);
v___y_1598_ = v___x_1643_;
goto v___jp_1597_;
}
else
{
lean_object* v___x_1644_; 
v___x_1644_ = l_Lean_Meta_mkEqFalse_x27(v_a_1625_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_);
v___y_1598_ = v___x_1644_;
goto v___jp_1597_;
}
}
else
{
lean_object* v_a_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1652_; 
v_a_1645_ = lean_ctor_get(v___x_1624_, 0);
v_isSharedCheck_1652_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1647_ = v___x_1624_;
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_a_1645_);
lean_dec(v___x_1624_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
lean_object* v___x_1650_; 
if (v_isShared_1648_ == 0)
{
v___x_1650_ = v___x_1647_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v_a_1645_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
}
}
else
{
lean_object* v_a_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1660_; 
lean_dec_ref(v_h_1587_);
v_a_1653_ = lean_ctor_get(v___x_1618_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1655_ = v___x_1618_;
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_a_1653_);
lean_dec(v___x_1618_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1658_; 
if (v_isShared_1656_ == 0)
{
v___x_1658_ = v___x_1655_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_a_1653_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
return v___x_1658_;
}
}
}
v___jp_1597_:
{
if (lean_obj_tag(v___y_1598_) == 0)
{
lean_object* v_a_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1609_; 
v_a_1599_ = lean_ctor_get(v___y_1598_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___y_1598_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1601_ = v___y_1598_;
v_isShared_1602_ = v_isSharedCheck_1609_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_a_1599_);
lean_dec(v___y_1598_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1609_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1607_; 
v___x_1603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1603_, 0, v_a_1599_);
v___x_1604_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1604_, 0, v___x_1596_);
lean_ctor_set(v___x_1604_, 1, v___x_1603_);
lean_ctor_set_uint8(v___x_1604_, sizeof(void*)*2, v___x_1585_);
v___x_1605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1605_, 0, v___x_1604_);
if (v_isShared_1602_ == 0)
{
lean_ctor_set(v___x_1601_, 0, v___x_1605_);
v___x_1607_ = v___x_1601_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v___x_1605_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
else
{
lean_object* v_a_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1617_; 
v_a_1610_ = lean_ctor_get(v___y_1598_, 0);
v_isSharedCheck_1617_ = !lean_is_exclusive(v___y_1598_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1612_ = v___y_1598_;
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_a_1610_);
lean_dec(v___y_1598_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v___x_1615_; 
if (v_isShared_1613_ == 0)
{
v___x_1615_ = v___x_1612_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v_a_1610_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
return v___x_1615_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reduceCtorEqCheap___lam__0___boxed(lean_object* v___x_1661_, lean_object* v___x_1662_, lean_object* v_h_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_){
_start:
{
uint8_t v___x_12418__boxed_1672_; uint8_t v___x_12419__boxed_1673_; lean_object* v_res_1674_; 
v___x_12418__boxed_1672_ = lean_unbox(v___x_1661_);
v___x_12419__boxed_1673_ = lean_unbox(v___x_1662_);
v_res_1674_ = l_Lean_Meta_Grind_reduceCtorEqCheap___lam__0(v___x_12418__boxed_1672_, v___x_12419__boxed_1673_, v_h_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_);
lean_dec(v___y_1670_);
lean_dec_ref(v___y_1669_);
lean_dec(v___y_1668_);
lean_dec_ref(v___y_1667_);
lean_dec(v___y_1666_);
lean_dec_ref(v___y_1665_);
lean_dec(v___y_1664_);
return v_res_1674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___redArg___lam__0(lean_object* v_k_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v_b_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_){
_start:
{
lean_object* v___x_1685_; 
lean_inc(v___y_1683_);
lean_inc_ref(v___y_1682_);
lean_inc(v___y_1681_);
lean_inc_ref(v___y_1680_);
lean_inc(v___y_1678_);
lean_inc_ref(v___y_1677_);
lean_inc(v___y_1676_);
v___x_1685_ = lean_apply_9(v_k_1675_, v_b_1679_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, lean_box(0));
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v_b_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___redArg___lam__0(v_k_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v_b_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
lean_dec(v___y_1694_);
lean_dec_ref(v___y_1693_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
lean_dec(v___y_1689_);
lean_dec_ref(v___y_1688_);
lean_dec(v___y_1687_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___redArg(lean_object* v_name_1697_, uint8_t v_bi_1698_, lean_object* v_type_1699_, lean_object* v_k_1700_, uint8_t v_kind_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_){
_start:
{
lean_object* v___f_1710_; lean_object* v___x_1711_; 
lean_inc(v___y_1704_);
lean_inc_ref(v___y_1703_);
lean_inc(v___y_1702_);
v___f_1710_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1710_, 0, v_k_1700_);
lean_closure_set(v___f_1710_, 1, v___y_1702_);
lean_closure_set(v___f_1710_, 2, v___y_1703_);
lean_closure_set(v___f_1710_, 3, v___y_1704_);
v___x_1711_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1697_, v_bi_1698_, v_type_1699_, v___f_1710_, v_kind_1701_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_);
if (lean_obj_tag(v___x_1711_) == 0)
{
return v___x_1711_;
}
else
{
lean_object* v_a_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1719_; 
v_a_1712_ = lean_ctor_get(v___x_1711_, 0);
v_isSharedCheck_1719_ = !lean_is_exclusive(v___x_1711_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1714_ = v___x_1711_;
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_a_1712_);
lean_dec(v___x_1711_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1717_; 
if (v_isShared_1715_ == 0)
{
v___x_1717_ = v___x_1714_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_a_1712_);
v___x_1717_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
return v___x_1717_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___redArg___boxed(lean_object* v_name_1720_, lean_object* v_bi_1721_, lean_object* v_type_1722_, lean_object* v_k_1723_, lean_object* v_kind_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_){
_start:
{
uint8_t v_bi_boxed_1733_; uint8_t v_kind_boxed_1734_; lean_object* v_res_1735_; 
v_bi_boxed_1733_ = lean_unbox(v_bi_1721_);
v_kind_boxed_1734_ = lean_unbox(v_kind_1724_);
v_res_1735_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___redArg(v_name_1720_, v_bi_boxed_1733_, v_type_1722_, v_k_1723_, v_kind_boxed_1734_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_);
lean_dec(v___y_1731_);
lean_dec_ref(v___y_1730_);
lean_dec(v___y_1729_);
lean_dec_ref(v___y_1728_);
lean_dec(v___y_1727_);
lean_dec_ref(v___y_1726_);
lean_dec(v___y_1725_);
return v_res_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0___redArg(lean_object* v_name_1736_, lean_object* v_type_1737_, lean_object* v_k_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_){
_start:
{
uint8_t v___x_1747_; uint8_t v___x_1748_; lean_object* v___x_1749_; 
v___x_1747_ = 0;
v___x_1748_ = 0;
v___x_1749_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___redArg(v_name_1736_, v___x_1747_, v_type_1737_, v_k_1738_, v___x_1748_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_);
return v___x_1749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0___redArg___boxed(lean_object* v_name_1750_, lean_object* v_type_1751_, lean_object* v_k_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_){
_start:
{
lean_object* v_res_1761_; 
v_res_1761_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0___redArg(v_name_1750_, v_type_1751_, v_k_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_);
lean_dec(v___y_1759_);
lean_dec_ref(v___y_1758_);
lean_dec(v___y_1757_);
lean_dec_ref(v___y_1756_);
lean_dec(v___y_1755_);
lean_dec_ref(v___y_1754_);
lean_dec(v___y_1753_);
return v_res_1761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reduceCtorEqCheap(lean_object* v_e_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_){
_start:
{
lean_object* v___x_1777_; 
lean_inc_ref(v_e_1765_);
v___x_1777_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1765_, v_a_1770_);
if (lean_obj_tag(v___x_1777_) == 0)
{
lean_object* v_a_1778_; lean_object* v___x_1779_; uint8_t v___x_1780_; 
v_a_1778_ = lean_ctor_get(v___x_1777_, 0);
lean_inc(v_a_1778_);
lean_dec_ref_known(v___x_1777_, 1);
v___x_1779_ = l_Lean_Expr_cleanupAnnotations(v_a_1778_);
lean_dec(v_a_1778_);
v___x_1780_ = l_Lean_Expr_isApp(v___x_1779_);
if (v___x_1780_ == 0)
{
lean_dec_ref(v___x_1779_);
lean_dec_ref(v_e_1765_);
goto v___jp_1774_;
}
else
{
lean_object* v___x_1781_; uint8_t v___x_1782_; 
v___x_1781_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1779_);
v___x_1782_ = l_Lean_Expr_isApp(v___x_1781_);
if (v___x_1782_ == 0)
{
lean_dec_ref(v___x_1781_);
lean_dec_ref(v___x_1779_);
lean_dec_ref(v_e_1765_);
goto v___jp_1774_;
}
else
{
lean_object* v___x_1783_; uint8_t v___x_1784_; 
v___x_1783_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1781_);
v___x_1784_ = l_Lean_Expr_isApp(v___x_1783_);
if (v___x_1784_ == 0)
{
lean_dec_ref(v___x_1783_);
lean_dec_ref(v___x_1781_);
lean_dec_ref(v___x_1779_);
lean_dec_ref(v_e_1765_);
goto v___jp_1774_;
}
else
{
lean_object* v___x_1785_; lean_object* v___x_1786_; uint8_t v___x_1787_; 
v___x_1785_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1783_);
lean_dec_ref(v___x_1783_);
v___x_1786_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__2));
v___x_1787_ = l_Lean_Expr_isConstOf(v___x_1785_, v___x_1786_);
lean_dec_ref(v___x_1785_);
if (v___x_1787_ == 0)
{
lean_dec_ref(v___x_1781_);
lean_dec_ref(v___x_1779_);
lean_dec_ref(v_e_1765_);
goto v___jp_1774_;
}
else
{
lean_object* v_arg_1788_; lean_object* v_arg_1789_; lean_object* v___x_1790_; 
v_arg_1788_ = lean_ctor_get(v___x_1779_, 1);
lean_inc_ref(v_arg_1788_);
lean_dec_ref(v___x_1779_);
v_arg_1789_ = lean_ctor_get(v___x_1781_, 1);
lean_inc_ref(v_arg_1789_);
lean_dec_ref(v___x_1781_);
v___x_1790_ = l_Lean_Meta_isConstructorApp_x3f(v_arg_1789_, v_a_1769_, v_a_1770_, v_a_1771_, v_a_1772_);
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_object* v_a_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1833_; 
v_a_1791_ = lean_ctor_get(v___x_1790_, 0);
v_isSharedCheck_1833_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1793_ = v___x_1790_;
v_isShared_1794_ = v_isSharedCheck_1833_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_a_1791_);
lean_dec(v___x_1790_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1833_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
if (lean_obj_tag(v_a_1791_) == 1)
{
lean_object* v_val_1795_; lean_object* v___x_1796_; 
lean_del_object(v___x_1793_);
v_val_1795_ = lean_ctor_get(v_a_1791_, 0);
lean_inc(v_val_1795_);
lean_dec_ref_known(v_a_1791_, 1);
v___x_1796_ = l_Lean_Meta_isConstructorApp_x3f(v_arg_1788_, v_a_1769_, v_a_1770_, v_a_1771_, v_a_1772_);
if (lean_obj_tag(v___x_1796_) == 0)
{
lean_object* v_a_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1820_; 
v_a_1797_ = lean_ctor_get(v___x_1796_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1799_ = v___x_1796_;
v_isShared_1800_ = v_isSharedCheck_1820_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_a_1797_);
lean_dec(v___x_1796_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1820_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
if (lean_obj_tag(v_a_1797_) == 1)
{
lean_object* v_toConstantVal_1801_; lean_object* v_val_1802_; lean_object* v_toConstantVal_1803_; lean_object* v_name_1804_; lean_object* v_name_1805_; uint8_t v___x_1806_; 
v_toConstantVal_1801_ = lean_ctor_get(v_val_1795_, 0);
lean_inc_ref(v_toConstantVal_1801_);
lean_dec(v_val_1795_);
v_val_1802_ = lean_ctor_get(v_a_1797_, 0);
lean_inc(v_val_1802_);
lean_dec_ref_known(v_a_1797_, 1);
v_toConstantVal_1803_ = lean_ctor_get(v_val_1802_, 0);
lean_inc_ref(v_toConstantVal_1803_);
lean_dec(v_val_1802_);
v_name_1804_ = lean_ctor_get(v_toConstantVal_1801_, 0);
lean_inc(v_name_1804_);
lean_dec_ref(v_toConstantVal_1801_);
v_name_1805_ = lean_ctor_get(v_toConstantVal_1803_, 0);
lean_inc(v_name_1805_);
lean_dec_ref(v_toConstantVal_1803_);
v___x_1806_ = lean_name_eq(v_name_1804_, v_name_1805_);
lean_dec(v_name_1805_);
lean_dec(v_name_1804_);
if (v___x_1806_ == 0)
{
lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___f_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; 
lean_del_object(v___x_1799_);
v___x_1807_ = lean_box(v___x_1787_);
v___x_1808_ = lean_box(v___x_1806_);
v___f_1809_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_reduceCtorEqCheap___lam__0___boxed), 11, 2);
lean_closure_set(v___f_1809_, 0, v___x_1807_);
lean_closure_set(v___f_1809_, 1, v___x_1808_);
v___x_1810_ = ((lean_object*)(l_Lean_Meta_Grind_reduceCtorEqCheap___closed__1));
v___x_1811_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0___redArg(v___x_1810_, v_e_1765_, v___f_1809_, v_a_1766_, v_a_1767_, v_a_1768_, v_a_1769_, v_a_1770_, v_a_1771_, v_a_1772_);
return v___x_1811_;
}
else
{
lean_object* v___x_1812_; lean_object* v___x_1814_; 
lean_dec_ref(v_e_1765_);
v___x_1812_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
if (v_isShared_1800_ == 0)
{
lean_ctor_set(v___x_1799_, 0, v___x_1812_);
v___x_1814_ = v___x_1799_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v___x_1812_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
}
else
{
lean_object* v___x_1816_; lean_object* v___x_1818_; 
lean_dec(v_a_1797_);
lean_dec(v_val_1795_);
lean_dec_ref(v_e_1765_);
v___x_1816_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
if (v_isShared_1800_ == 0)
{
lean_ctor_set(v___x_1799_, 0, v___x_1816_);
v___x_1818_ = v___x_1799_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v___x_1816_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
return v___x_1818_;
}
}
}
}
else
{
lean_object* v_a_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1828_; 
lean_dec(v_val_1795_);
lean_dec_ref(v_e_1765_);
v_a_1821_ = lean_ctor_get(v___x_1796_, 0);
v_isSharedCheck_1828_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1823_ = v___x_1796_;
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_a_1821_);
lean_dec(v___x_1796_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v___x_1826_; 
if (v_isShared_1824_ == 0)
{
v___x_1826_ = v___x_1823_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_a_1821_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
return v___x_1826_;
}
}
}
}
else
{
lean_object* v___x_1829_; lean_object* v___x_1831_; 
lean_dec(v_a_1791_);
lean_dec_ref(v_arg_1788_);
lean_dec_ref(v_e_1765_);
v___x_1829_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
if (v_isShared_1794_ == 0)
{
lean_ctor_set(v___x_1793_, 0, v___x_1829_);
v___x_1831_ = v___x_1793_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v___x_1829_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
return v___x_1831_;
}
}
}
}
else
{
lean_object* v_a_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1841_; 
lean_dec_ref(v_arg_1788_);
lean_dec_ref(v_e_1765_);
v_a_1834_ = lean_ctor_get(v___x_1790_, 0);
v_isSharedCheck_1841_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1836_ = v___x_1790_;
v_isShared_1837_ = v_isSharedCheck_1841_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_a_1834_);
lean_dec(v___x_1790_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1841_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v___x_1839_; 
if (v_isShared_1837_ == 0)
{
v___x_1839_ = v___x_1836_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v_a_1834_);
v___x_1839_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
return v___x_1839_;
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1849_; 
lean_dec_ref(v_e_1765_);
v_a_1842_ = lean_ctor_get(v___x_1777_, 0);
v_isSharedCheck_1849_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1844_ = v___x_1777_;
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_a_1842_);
lean_dec(v___x_1777_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1847_; 
if (v_isShared_1845_ == 0)
{
v___x_1847_ = v___x_1844_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_a_1842_);
v___x_1847_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
return v___x_1847_;
}
}
}
v___jp_1774_:
{
lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1775_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
v___x_1776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1776_, 0, v___x_1775_);
return v___x_1776_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reduceCtorEqCheap___boxed(lean_object* v_e_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_){
_start:
{
lean_object* v_res_1859_; 
v_res_1859_ = l_Lean_Meta_Grind_reduceCtorEqCheap(v_e_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_);
lean_dec(v_a_1857_);
lean_dec_ref(v_a_1856_);
lean_dec(v_a_1855_);
lean_dec_ref(v_a_1854_);
lean_dec(v_a_1853_);
lean_dec_ref(v_a_1852_);
lean_dec(v_a_1851_);
return v_res_1859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0(lean_object* v_00_u03b1_1860_, lean_object* v_name_1861_, uint8_t v_bi_1862_, lean_object* v_type_1863_, lean_object* v_k_1864_, uint8_t v_kind_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_){
_start:
{
lean_object* v___x_1874_; 
v___x_1874_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___redArg(v_name_1861_, v_bi_1862_, v_type_1863_, v_k_1864_, v_kind_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_);
return v___x_1874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1875_, lean_object* v_name_1876_, lean_object* v_bi_1877_, lean_object* v_type_1878_, lean_object* v_k_1879_, lean_object* v_kind_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_){
_start:
{
uint8_t v_bi_boxed_1889_; uint8_t v_kind_boxed_1890_; lean_object* v_res_1891_; 
v_bi_boxed_1889_ = lean_unbox(v_bi_1877_);
v_kind_boxed_1890_ = lean_unbox(v_kind_1880_);
v_res_1891_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0(v_00_u03b1_1875_, v_name_1876_, v_bi_boxed_1889_, v_type_1878_, v_k_1879_, v_kind_boxed_1890_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_);
lean_dec(v___y_1887_);
lean_dec_ref(v___y_1886_);
lean_dec(v___y_1885_);
lean_dec_ref(v___y_1884_);
lean_dec(v___y_1883_);
lean_dec_ref(v___y_1882_);
lean_dec(v___y_1881_);
return v_res_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0(lean_object* v_00_u03b1_1892_, lean_object* v_name_1893_, lean_object* v_type_1894_, lean_object* v_k_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_){
_start:
{
lean_object* v___x_1904_; 
v___x_1904_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0___redArg(v_name_1893_, v_type_1894_, v_k_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0___boxed(lean_object* v_00_u03b1_1905_, lean_object* v_name_1906_, lean_object* v_type_1907_, lean_object* v_k_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_){
_start:
{
lean_object* v_res_1917_; 
v_res_1917_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0(v_00_u03b1_1905_, v_name_1906_, v_type_1907_, v_k_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_);
lean_dec(v___y_1915_);
lean_dec_ref(v___y_1914_);
lean_dec(v___y_1913_);
lean_dec_ref(v___y_1912_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
lean_dec(v___y_1909_);
return v_res_1917_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_14_(){
_start:
{
lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
v___x_1925_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_14_));
v___x_1926_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__4_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13_));
v___x_1927_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_reduceCtorEqCheap___boxed), 9, 0);
v___x_1928_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_1925_, v___x_1926_, v___x_1927_);
return v___x_1928_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_14____boxed(lean_object* v_a_1929_){
_start:
{
lean_object* v_res_1930_; 
v_res_1930_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_14_();
return v_res_1930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_unfoldReducibleSimproc___redArg(lean_object* v_e_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_){
_start:
{
lean_object* v___x_1937_; 
v___x_1937_ = l_Lean_Meta_Sym_unfoldReducibleStep(v_e_1931_, v_a_1932_, v_a_1933_, v_a_1934_, v_a_1935_);
return v___x_1937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_unfoldReducibleSimproc___redArg___boxed(lean_object* v_e_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_){
_start:
{
lean_object* v_res_1944_; 
v_res_1944_ = l_Lean_Meta_Grind_unfoldReducibleSimproc___redArg(v_e_1938_, v_a_1939_, v_a_1940_, v_a_1941_, v_a_1942_);
lean_dec(v_a_1942_);
lean_dec_ref(v_a_1941_);
lean_dec(v_a_1940_);
lean_dec_ref(v_a_1939_);
return v_res_1944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_unfoldReducibleSimproc(lean_object* v_e_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_){
_start:
{
lean_object* v___x_1954_; 
v___x_1954_ = l_Lean_Meta_Sym_unfoldReducibleStep(v_e_1945_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_);
return v___x_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_unfoldReducibleSimproc___boxed(lean_object* v_e_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_){
_start:
{
lean_object* v_res_1964_; 
v_res_1964_ = l_Lean_Meta_Grind_unfoldReducibleSimproc(v_e_1955_, v_a_1956_, v_a_1957_, v_a_1958_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_);
lean_dec(v_a_1962_);
lean_dec_ref(v_a_1961_);
lean_dec(v_a_1960_);
lean_dec_ref(v_a_1959_);
lean_dec(v_a_1958_);
lean_dec_ref(v_a_1957_);
lean_dec(v_a_1956_);
return v_res_1964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___lam__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_10_(lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_){
_start:
{
lean_object* v___x_1974_; 
v___x_1974_ = l_Lean_Meta_Sym_unfoldReducibleStep(v___y_1965_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_);
return v___x_1974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___lam__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_10____boxed(lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_){
_start:
{
lean_object* v_res_1984_; 
v_res_1984_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___lam__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_10_(v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_);
lean_dec(v___y_1982_);
lean_dec_ref(v___y_1981_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
lean_dec(v___y_1978_);
lean_dec_ref(v___y_1977_);
lean_dec(v___y_1976_);
return v_res_1984_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_10_(){
_start:
{
lean_object* v___f_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___f_1997_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_10_));
v___x_1998_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_10_));
v___x_1999_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_10_));
v___x_2000_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1998_, v___x_1999_, v___f_1997_);
return v___x_2000_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_10____boxed(lean_object* v_a_2001_){
_start:
{
lean_object* v_res_2002_; 
v_res_2002_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_10_();
return v_res_2002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimprocs___redArg(lean_object* v_a_2011_, lean_object* v_a_2012_){
_start:
{
lean_object* v___x_2014_; 
v___x_2014_ = l_Lean_Meta_Simp_getSEvalSimprocs___redArg(v_a_2012_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v_a_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; uint8_t v___x_2021_; lean_object* v___x_2022_; 
v_a_2015_ = lean_ctor_get(v___x_2014_, 0);
lean_inc(v_a_2015_);
lean_dec_ref_known(v___x_2014_, 1);
v___x_2016_ = ((lean_object*)(l_Lean_Meta_Grind_getSimprocs___redArg___closed__2));
v___x_2017_ = l_Lean_Meta_Simp_Simprocs_erase(v_a_2015_, v___x_2016_);
v___x_2018_ = ((lean_object*)(l_Lean_Meta_Grind_getSimprocs___redArg___closed__4));
v___x_2019_ = l_Lean_Meta_Simp_Simprocs_erase(v___x_2017_, v___x_2018_);
v___x_2020_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_14_));
v___x_2021_ = 1;
v___x_2022_ = l_Lean_Meta_Simp_Simprocs_add(v___x_2019_, v___x_2020_, v___x_2021_, v_a_2011_, v_a_2012_);
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_object* v_a_2023_; lean_object* v___x_2024_; 
v_a_2023_ = lean_ctor_get(v___x_2022_, 0);
lean_inc(v_a_2023_);
lean_dec_ref_known(v___x_2022_, 1);
v___x_2024_ = l_Lean_Meta_Grind_addSimpMatchDiscrsOnly(v_a_2023_, v_a_2011_, v_a_2012_);
if (lean_obj_tag(v___x_2024_) == 0)
{
lean_object* v_a_2025_; lean_object* v___x_2026_; 
v_a_2025_ = lean_ctor_get(v___x_2024_, 0);
lean_inc(v_a_2025_);
lean_dec_ref_known(v___x_2024_, 1);
v___x_2026_ = l_Lean_Meta_Grind_addPreMatchCondSimproc(v_a_2025_, v_a_2011_, v_a_2012_);
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_object* v_a_2027_; lean_object* v___x_2028_; 
v_a_2027_ = lean_ctor_get(v___x_2026_, 0);
lean_inc(v_a_2027_);
lean_dec_ref_known(v___x_2026_, 1);
v___x_2028_ = l_Lean_Meta_Grind_Arith_addSimproc(v_a_2027_, v_a_2011_, v_a_2012_);
if (lean_obj_tag(v___x_2028_) == 0)
{
lean_object* v_a_2029_; lean_object* v___x_2030_; 
v_a_2029_ = lean_ctor_get(v___x_2028_, 0);
lean_inc(v_a_2029_);
lean_dec_ref_known(v___x_2028_, 1);
v___x_2030_ = l_Lean_Meta_Grind_addForallSimproc(v_a_2029_, v_a_2011_, v_a_2012_);
if (lean_obj_tag(v___x_2030_) == 0)
{
lean_object* v_a_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; 
v_a_2031_ = lean_ctor_get(v___x_2030_, 0);
lean_inc(v_a_2031_);
lean_dec_ref_known(v___x_2030_, 1);
v___x_2032_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13_));
v___x_2033_ = l_Lean_Meta_Simp_Simprocs_add(v_a_2031_, v___x_2032_, v___x_2021_, v_a_2011_, v_a_2012_);
if (lean_obj_tag(v___x_2033_) == 0)
{
lean_object* v_a_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; 
v_a_2034_ = lean_ctor_get(v___x_2033_, 0);
lean_inc(v_a_2034_);
lean_dec_ref_known(v___x_2033_, 1);
v___x_2035_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_12_));
v___x_2036_ = l_Lean_Meta_Simp_Simprocs_add(v_a_2034_, v___x_2035_, v___x_2021_, v_a_2011_, v_a_2012_);
if (lean_obj_tag(v___x_2036_) == 0)
{
lean_object* v_a_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; 
v_a_2037_ = lean_ctor_get(v___x_2036_, 0);
lean_inc(v_a_2037_);
lean_dec_ref_known(v___x_2036_, 1);
v___x_2038_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_14_));
v___x_2039_ = l_Lean_Meta_Simp_Simprocs_add(v_a_2037_, v___x_2038_, v___x_2021_, v_a_2011_, v_a_2012_);
if (lean_obj_tag(v___x_2039_) == 0)
{
lean_object* v_a_2040_; lean_object* v___x_2041_; uint8_t v___x_2042_; lean_object* v___x_2043_; 
v_a_2040_ = lean_ctor_get(v___x_2039_, 0);
lean_inc(v_a_2040_);
lean_dec_ref_known(v___x_2039_, 1);
v___x_2041_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2942474041____hygCtx___hyg_11_));
v___x_2042_ = 0;
v___x_2043_ = l_Lean_Meta_Simp_Simprocs_add(v_a_2040_, v___x_2041_, v___x_2042_, v_a_2011_, v_a_2012_);
if (lean_obj_tag(v___x_2043_) == 0)
{
lean_object* v_a_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; 
v_a_2044_ = lean_ctor_get(v___x_2043_, 0);
lean_inc(v_a_2044_);
lean_dec_ref_known(v___x_2043_, 1);
v___x_2045_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_10_));
v___x_2046_ = l_Lean_Meta_Simp_Simprocs_add(v_a_2044_, v___x_2045_, v___x_2042_, v_a_2011_, v_a_2012_);
if (lean_obj_tag(v___x_2046_) == 0)
{
lean_object* v_a_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2057_; 
v_a_2047_ = lean_ctor_get(v___x_2046_, 0);
v_isSharedCheck_2057_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_2049_ = v___x_2046_;
v_isShared_2050_ = v_isSharedCheck_2057_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_a_2047_);
lean_dec(v___x_2046_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2057_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2055_; 
v___x_2051_ = lean_unsigned_to_nat(1u);
v___x_2052_ = lean_mk_empty_array_with_capacity(v___x_2051_);
v___x_2053_ = lean_array_push(v___x_2052_, v_a_2047_);
if (v_isShared_2050_ == 0)
{
lean_ctor_set(v___x_2049_, 0, v___x_2053_);
v___x_2055_ = v___x_2049_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v___x_2053_);
v___x_2055_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
return v___x_2055_;
}
}
}
else
{
lean_object* v_a_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2065_; 
v_a_2058_ = lean_ctor_get(v___x_2046_, 0);
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2060_ = v___x_2046_;
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_a_2058_);
lean_dec(v___x_2046_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2063_; 
if (v_isShared_2061_ == 0)
{
v___x_2063_ = v___x_2060_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v_a_2058_);
v___x_2063_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
return v___x_2063_;
}
}
}
}
else
{
lean_object* v_a_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2073_; 
v_a_2066_ = lean_ctor_get(v___x_2043_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2043_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2068_ = v___x_2043_;
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_a_2066_);
lean_dec(v___x_2043_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2071_; 
if (v_isShared_2069_ == 0)
{
v___x_2071_ = v___x_2068_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_a_2066_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
}
else
{
lean_object* v_a_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2081_; 
v_a_2074_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2076_ = v___x_2039_;
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_a_2074_);
lean_dec(v___x_2039_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2079_; 
if (v_isShared_2077_ == 0)
{
v___x_2079_ = v___x_2076_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_a_2074_);
v___x_2079_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
return v___x_2079_;
}
}
}
}
else
{
lean_object* v_a_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2089_; 
v_a_2082_ = lean_ctor_get(v___x_2036_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2084_ = v___x_2036_;
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_a_2082_);
lean_dec(v___x_2036_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2087_; 
if (v_isShared_2085_ == 0)
{
v___x_2087_ = v___x_2084_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_a_2082_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
return v___x_2087_;
}
}
}
}
else
{
lean_object* v_a_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2097_; 
v_a_2090_ = lean_ctor_get(v___x_2033_, 0);
v_isSharedCheck_2097_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_2092_ = v___x_2033_;
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_a_2090_);
lean_dec(v___x_2033_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2095_; 
if (v_isShared_2093_ == 0)
{
v___x_2095_ = v___x_2092_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v_a_2090_);
v___x_2095_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
return v___x_2095_;
}
}
}
}
else
{
lean_object* v_a_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2105_; 
v_a_2098_ = lean_ctor_get(v___x_2030_, 0);
v_isSharedCheck_2105_ = !lean_is_exclusive(v___x_2030_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2100_ = v___x_2030_;
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_a_2098_);
lean_dec(v___x_2030_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
lean_object* v___x_2103_; 
if (v_isShared_2101_ == 0)
{
v___x_2103_ = v___x_2100_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_a_2098_);
v___x_2103_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
return v___x_2103_;
}
}
}
}
else
{
lean_object* v_a_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2113_; 
v_a_2106_ = lean_ctor_get(v___x_2028_, 0);
v_isSharedCheck_2113_ = !lean_is_exclusive(v___x_2028_);
if (v_isSharedCheck_2113_ == 0)
{
v___x_2108_ = v___x_2028_;
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_a_2106_);
lean_dec(v___x_2028_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v___x_2111_; 
if (v_isShared_2109_ == 0)
{
v___x_2111_ = v___x_2108_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v_a_2106_);
v___x_2111_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
return v___x_2111_;
}
}
}
}
else
{
lean_object* v_a_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2121_; 
v_a_2114_ = lean_ctor_get(v___x_2026_, 0);
v_isSharedCheck_2121_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2121_ == 0)
{
v___x_2116_ = v___x_2026_;
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_a_2114_);
lean_dec(v___x_2026_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v___x_2119_; 
if (v_isShared_2117_ == 0)
{
v___x_2119_ = v___x_2116_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v_a_2114_);
v___x_2119_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
return v___x_2119_;
}
}
}
}
else
{
lean_object* v_a_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2129_; 
v_a_2122_ = lean_ctor_get(v___x_2024_, 0);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2124_ = v___x_2024_;
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_a_2122_);
lean_dec(v___x_2024_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2127_; 
if (v_isShared_2125_ == 0)
{
v___x_2127_ = v___x_2124_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_a_2122_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
}
}
else
{
lean_object* v_a_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2137_; 
v_a_2130_ = lean_ctor_get(v___x_2022_, 0);
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2132_ = v___x_2022_;
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_a_2130_);
lean_dec(v___x_2022_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v___x_2135_; 
if (v_isShared_2133_ == 0)
{
v___x_2135_ = v___x_2132_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_a_2130_);
v___x_2135_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
return v___x_2135_;
}
}
}
}
else
{
lean_object* v_a_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2145_; 
v_a_2138_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2140_ = v___x_2014_;
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_a_2138_);
lean_dec(v___x_2014_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2143_; 
if (v_isShared_2141_ == 0)
{
v___x_2143_ = v___x_2140_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v_a_2138_);
v___x_2143_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
return v___x_2143_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimprocs___redArg___boxed(lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_){
_start:
{
lean_object* v_res_2149_; 
v_res_2149_ = l_Lean_Meta_Grind_getSimprocs___redArg(v_a_2146_, v_a_2147_);
lean_dec(v_a_2147_);
lean_dec_ref(v_a_2146_);
return v_res_2149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimprocs(lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_){
_start:
{
lean_object* v___x_2155_; 
v___x_2155_ = l_Lean_Meta_Grind_getSimprocs___redArg(v_a_2152_, v_a_2153_);
return v___x_2155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimprocs___boxed(lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_){
_start:
{
lean_object* v_res_2161_; 
v_res_2161_ = l_Lean_Meta_Grind_getSimprocs(v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_);
lean_dec(v_a_2159_);
lean_dec_ref(v_a_2158_);
lean_dec(v_a_2157_);
lean_dec_ref(v_a_2156_);
return v_res_2161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_addDeclToUnfold(lean_object* v_s_2162_, lean_object* v_declName_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_){
_start:
{
lean_object* v___x_2169_; lean_object* v_env_2170_; uint8_t v___x_2171_; uint8_t v___x_2172_; 
v___x_2169_ = lean_st_ref_get(v_a_2167_);
v_env_2170_ = lean_ctor_get(v___x_2169_, 0);
lean_inc_ref(v_env_2170_);
lean_dec(v___x_2169_);
v___x_2171_ = 1;
lean_inc(v_declName_2163_);
v___x_2172_ = l_Lean_Environment_contains(v_env_2170_, v_declName_2163_, v___x_2171_);
if (v___x_2172_ == 0)
{
lean_object* v___x_2173_; 
lean_dec(v_declName_2163_);
v___x_2173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2173_, 0, v_s_2162_);
return v___x_2173_;
}
else
{
lean_object* v___x_2174_; 
v___x_2174_ = l_Lean_Meta_SimpTheorems_addDeclToUnfold(v_s_2162_, v_declName_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_);
return v___x_2174_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_addDeclToUnfold___boxed(lean_object* v_s_2175_, lean_object* v_declName_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_){
_start:
{
lean_object* v_res_2182_; 
v_res_2182_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_addDeclToUnfold(v_s_2175_, v_declName_2176_, v_a_2177_, v_a_2178_, v_a_2179_, v_a_2180_);
lean_dec(v_a_2180_);
lean_dec_ref(v_a_2179_);
lean_dec(v_a_2178_);
lean_dec_ref(v_a_2177_);
return v_res_2182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNormTheorems(lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_){
_start:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; 
v___x_2188_ = l_Lean_Meta_Grind_normExt;
v___x_2189_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v___x_2188_, v_a_2186_);
if (lean_obj_tag(v___x_2189_) == 0)
{
lean_object* v_a_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; 
v_a_2190_ = lean_ctor_get(v___x_2189_, 0);
lean_inc(v_a_2190_);
lean_dec_ref_known(v___x_2189_, 1);
v___x_2191_ = ((lean_object*)(l_Lean_Meta_Grind_registerNormTheorems___closed__7));
v___x_2192_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_addDeclToUnfold(v_a_2190_, v___x_2191_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_);
if (lean_obj_tag(v___x_2192_) == 0)
{
lean_object* v_a_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; 
v_a_2193_ = lean_ctor_get(v___x_2192_, 0);
lean_inc(v_a_2193_);
lean_dec_ref_known(v___x_2192_, 1);
v___x_2194_ = ((lean_object*)(l_Lean_Meta_Grind_registerNormTheorems___closed__10));
v___x_2195_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_addDeclToUnfold(v_a_2193_, v___x_2194_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_);
if (lean_obj_tag(v___x_2195_) == 0)
{
lean_object* v_a_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; 
v_a_2196_ = lean_ctor_get(v___x_2195_, 0);
lean_inc(v_a_2196_);
lean_dec_ref_known(v___x_2195_, 1);
v___x_2197_ = ((lean_object*)(l_Lean_Meta_Grind_registerNormTheorems___closed__12));
v___x_2198_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_addDeclToUnfold(v_a_2196_, v___x_2197_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_);
if (lean_obj_tag(v___x_2198_) == 0)
{
lean_object* v_a_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; 
v_a_2199_ = lean_ctor_get(v___x_2198_, 0);
lean_inc(v_a_2199_);
lean_dec_ref_known(v___x_2198_, 1);
v___x_2200_ = ((lean_object*)(l_Lean_Meta_Grind_registerNormTheorems___closed__15));
v___x_2201_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_addDeclToUnfold(v_a_2199_, v___x_2200_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_);
if (lean_obj_tag(v___x_2201_) == 0)
{
lean_object* v_a_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
v_a_2202_ = lean_ctor_get(v___x_2201_, 0);
lean_inc(v_a_2202_);
lean_dec_ref_known(v___x_2201_, 1);
v___x_2203_ = ((lean_object*)(l_Lean_Meta_Grind_registerNormTheorems___closed__17));
v___x_2204_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_addDeclToUnfold(v_a_2202_, v___x_2203_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_);
return v___x_2204_;
}
else
{
return v___x_2201_;
}
}
else
{
return v___x_2198_;
}
}
else
{
return v___x_2195_;
}
}
else
{
return v___x_2192_;
}
}
else
{
return v___x_2189_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNormTheorems___boxed(lean_object* v_a_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_){
_start:
{
lean_object* v_res_2210_; 
v_res_2210_ = l_Lean_Meta_Grind_getNormTheorems(v_a_2205_, v_a_2206_, v_a_2207_, v_a_2208_);
lean_dec(v_a_2208_);
lean_dec_ref(v_a_2207_);
lean_dec(v_a_2206_);
lean_dec_ref(v_a_2205_);
return v_res_2210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimpContext(lean_object* v_config_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_){
_start:
{
lean_object* v___x_2217_; 
v___x_2217_ = l_Lean_Meta_Grind_getNormTheorems(v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_);
if (lean_obj_tag(v___x_2217_) == 0)
{
lean_object* v_a_2218_; lean_object* v___x_2219_; 
v_a_2218_ = lean_ctor_get(v___x_2217_, 0);
lean_inc(v_a_2218_);
lean_dec_ref_known(v___x_2217_, 1);
v___x_2219_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_2215_);
if (lean_obj_tag(v___x_2219_) == 0)
{
lean_object* v_a_2220_; uint8_t v_zetaDelta_2221_; uint8_t v_zeta_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; uint8_t v___x_2225_; uint8_t v___x_2226_; uint8_t v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; 
v_a_2220_ = lean_ctor_get(v___x_2219_, 0);
lean_inc(v_a_2220_);
lean_dec_ref_known(v___x_2219_, 1);
v_zetaDelta_2221_ = lean_ctor_get_uint8(v_config_2211_, sizeof(void*)*18 + 19);
v_zeta_2222_ = lean_ctor_get_uint8(v_config_2211_, sizeof(void*)*18 + 20);
v___x_2223_ = lean_unsigned_to_nat(100000u);
v___x_2224_ = lean_unsigned_to_nat(2u);
v___x_2225_ = 0;
v___x_2226_ = 1;
v___x_2227_ = 0;
v___x_2228_ = lean_box(0);
v___x_2229_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_2229_, 0, v___x_2223_);
lean_ctor_set(v___x_2229_, 1, v___x_2224_);
lean_ctor_set(v___x_2229_, 2, v___x_2228_);
lean_ctor_set_uint8(v___x_2229_, sizeof(void*)*3, v___x_2225_);
lean_ctor_set_uint8(v___x_2229_, sizeof(void*)*3 + 1, v___x_2226_);
lean_ctor_set_uint8(v___x_2229_, sizeof(void*)*3 + 2, v___x_2225_);
lean_ctor_set_uint8(v___x_2229_, sizeof(void*)*3 + 3, v_zeta_2222_);
lean_ctor_set_uint8(v___x_2229_, sizeof(void*)*3 + 4, v___x_2226_);
lean_ctor_set_uint8(v___x_2229_, sizeof(void*)*3 + 5, v___x_2226_);
lean_ctor_set_uint8(v___x_2229_, sizeof(void*)*3 + 6, v___x_2227_);
lean_ctor_set_uint8(v___x_2229_, sizeof(void*)*3 + 7, v___x_2226_);
lean_ctor_set_uint8(v___x_2229_, sizeof(void*)*3 + 8, v___x_2226_);
lean_ctor_set_uint8(v___x_2229_, sizeof(void*)*3 + 9, v___x_2225_);
lean_ctor_set_uint8(v___x_2229_, sizeof(void*)*3 + 10, v___x_2226_);
lean_ctor_set_uint8(v___x_2229_, sizeof(void*)*3 + 11, v___x_2225_);
lean_ctor_set_uint8(v___x_2229_, sizeof(void*)*3 + 12, v___x_2226_);
lean_ctor_set_uint8(v___x_2229_, sizeof(void*)*3 + 13, v___x_2226_);
lean_ctor_set_uint8(v___x_2229_, sizeof(void*)*3 + 14, v___x_2225_);
lean_ctor_set_uint8(v___x_2229_, sizeof(void*)*3 + 15, v___x_2225_);
lean_ctor_set_uint8(v___x_2229_, sizeof(void*)*3 + 16, v_zetaDelta_2221_);
lean_ctor_set_uint8(v___x_2229_, sizeof(void*)*3 + 17, v___x_2226_);
lean_ctor_set_uint8(v___x_2229_, sizeof(void*)*3 + 18, v___x_2225_);
lean_ctor_set_uint8(v___x_2229_, sizeof(void*)*3 + 19, v___x_2226_);
lean_ctor_set_uint8(v___x_2229_, sizeof(void*)*3 + 20, v___x_2225_);
lean_ctor_set_uint8(v___x_2229_, sizeof(void*)*3 + 21, v___x_2226_);
lean_ctor_set_uint8(v___x_2229_, sizeof(void*)*3 + 22, v___x_2226_);
lean_ctor_set_uint8(v___x_2229_, sizeof(void*)*3 + 23, v___x_2226_);
lean_ctor_set_uint8(v___x_2229_, sizeof(void*)*3 + 24, v___x_2225_);
lean_ctor_set_uint8(v___x_2229_, sizeof(void*)*3 + 25, v___x_2225_);
lean_ctor_set_uint8(v___x_2229_, sizeof(void*)*3 + 26, v___x_2225_);
lean_ctor_set_uint8(v___x_2229_, sizeof(void*)*3 + 27, v___x_2225_);
lean_ctor_set_uint8(v___x_2229_, sizeof(void*)*3 + 28, v___x_2225_);
v___x_2230_ = lean_unsigned_to_nat(1u);
v___x_2231_ = lean_mk_empty_array_with_capacity(v___x_2230_);
v___x_2232_ = lean_array_push(v___x_2231_, v_a_2218_);
v___x_2233_ = l_Lean_Options_empty;
v___x_2234_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_2229_, v___x_2232_, v_a_2220_, v___x_2233_, v_a_2212_, v_a_2214_, v_a_2215_);
return v___x_2234_;
}
else
{
lean_object* v_a_2235_; lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2242_; 
lean_dec(v_a_2218_);
v_a_2235_ = lean_ctor_get(v___x_2219_, 0);
v_isSharedCheck_2242_ = !lean_is_exclusive(v___x_2219_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2237_ = v___x_2219_;
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
else
{
lean_inc(v_a_2235_);
lean_dec(v___x_2219_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
lean_object* v___x_2240_; 
if (v_isShared_2238_ == 0)
{
v___x_2240_ = v___x_2237_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_a_2235_);
v___x_2240_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
return v___x_2240_;
}
}
}
}
else
{
lean_object* v_a_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2250_; 
v_a_2243_ = lean_ctor_get(v___x_2217_, 0);
v_isSharedCheck_2250_ = !lean_is_exclusive(v___x_2217_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2245_ = v___x_2217_;
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_a_2243_);
lean_dec(v___x_2217_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
lean_object* v___x_2248_; 
if (v_isShared_2246_ == 0)
{
v___x_2248_ = v___x_2245_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v_a_2243_);
v___x_2248_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
return v___x_2248_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimpContext___boxed(lean_object* v_config_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_){
_start:
{
lean_object* v_res_2257_; 
v_res_2257_ = l_Lean_Meta_Grind_getSimpContext(v_config_2251_, v_a_2252_, v_a_2253_, v_a_2254_, v_a_2255_);
lean_dec(v_a_2255_);
lean_dec_ref(v_a_2254_);
lean_dec(v_a_2253_);
lean_dec_ref(v_a_2252_);
lean_dec_ref(v_config_2251_);
return v_res_2257_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_MatchDiscrOnly(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_ForallProp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Util(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Norm(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Config(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Main(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_SimpUtil(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_MatchDiscrOnly(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_ForallProp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Norm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_14_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2942474041____hygCtx___hyg_11_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_12_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_14_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_10_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_SimpUtil(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Simp_Simproc(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_MatchDiscrOnly(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_ForallProp(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Simproc(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Util(uint8_t builtin);
lean_object* initialize_Init_Grind_Norm(uint8_t builtin);
lean_object* initialize_Init_Grind_Config(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_Main(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_SimpUtil(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_MatchDiscrOnly(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_ForallProp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Norm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_SimpUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_SimpUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_SimpUtil(builtin);
}
#ifdef __cplusplus
}
#endif
