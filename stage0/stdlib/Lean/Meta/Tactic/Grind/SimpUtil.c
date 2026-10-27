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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__2;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_registerNormTheorems_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_registerNormTheorems_spec__3___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_registerNormTheorems_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_registerNormTheorems_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__0);
v___x_3_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
return v___x_3_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__1);
v___x_5_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5_, 0, v___x_4_);
lean_ctor_set(v___x_5_, 1, v___x_4_);
return v___x_5_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_6_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__1);
v___x_7_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_7_, 0, v___x_6_);
lean_ctor_set(v___x_7_, 1, v___x_6_);
lean_ctor_set(v___x_7_, 2, v___x_6_);
lean_ctor_set(v___x_7_, 3, v___x_6_);
lean_ctor_set(v___x_7_, 4, v___x_6_);
lean_ctor_set(v___x_7_, 5, v___x_6_);
lean_ctor_set(v___x_7_, 6, v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg(lean_object* v_ext_8_, lean_object* v_b_9_, uint8_t v_kind_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_){
_start:
{
lean_object* v_toCold_15_; lean_object* v_currNamespace_16_; lean_object* v___x_17_; lean_object* v_env_18_; lean_object* v_nextMacroScope_19_; lean_object* v_ngen_20_; lean_object* v_auxDeclNGen_21_; lean_object* v_traceState_22_; lean_object* v_recordedDeps_23_; lean_object* v_messages_24_; lean_object* v_infoState_25_; lean_object* v_snapshotTasks_26_; lean_object* v___x_28_; uint8_t v_isShared_29_; uint8_t v_isSharedCheck_53_; 
v_toCold_15_ = lean_ctor_get(v___y_12_, 0);
v_currNamespace_16_ = lean_ctor_get(v_toCold_15_, 4);
v___x_17_ = lean_st_ref_take(v___y_13_);
v_env_18_ = lean_ctor_get(v___x_17_, 0);
v_nextMacroScope_19_ = lean_ctor_get(v___x_17_, 1);
v_ngen_20_ = lean_ctor_get(v___x_17_, 2);
v_auxDeclNGen_21_ = lean_ctor_get(v___x_17_, 3);
v_traceState_22_ = lean_ctor_get(v___x_17_, 4);
v_recordedDeps_23_ = lean_ctor_get(v___x_17_, 6);
v_messages_24_ = lean_ctor_get(v___x_17_, 7);
v_infoState_25_ = lean_ctor_get(v___x_17_, 8);
v_snapshotTasks_26_ = lean_ctor_get(v___x_17_, 9);
v_isSharedCheck_53_ = !lean_is_exclusive(v___x_17_);
if (v_isSharedCheck_53_ == 0)
{
lean_object* v_unused_54_; 
v_unused_54_ = lean_ctor_get(v___x_17_, 5);
lean_dec(v_unused_54_);
v___x_28_ = v___x_17_;
v_isShared_29_ = v_isSharedCheck_53_;
goto v_resetjp_27_;
}
else
{
lean_inc(v_snapshotTasks_26_);
lean_inc(v_infoState_25_);
lean_inc(v_messages_24_);
lean_inc(v_recordedDeps_23_);
lean_inc(v_traceState_22_);
lean_inc(v_auxDeclNGen_21_);
lean_inc(v_ngen_20_);
lean_inc(v_nextMacroScope_19_);
lean_inc(v_env_18_);
lean_dec(v___x_17_);
v___x_28_ = lean_box(0);
v_isShared_29_ = v_isSharedCheck_53_;
goto v_resetjp_27_;
}
v_resetjp_27_:
{
lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_33_; 
lean_inc(v_currNamespace_16_);
v___x_30_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_18_, v_ext_8_, v_b_9_, v_kind_10_, v_currNamespace_16_);
v___x_31_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__2);
if (v_isShared_29_ == 0)
{
lean_ctor_set(v___x_28_, 5, v___x_31_);
lean_ctor_set(v___x_28_, 0, v___x_30_);
v___x_33_ = v___x_28_;
goto v_reusejp_32_;
}
else
{
lean_object* v_reuseFailAlloc_52_; 
v_reuseFailAlloc_52_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_52_, 0, v___x_30_);
lean_ctor_set(v_reuseFailAlloc_52_, 1, v_nextMacroScope_19_);
lean_ctor_set(v_reuseFailAlloc_52_, 2, v_ngen_20_);
lean_ctor_set(v_reuseFailAlloc_52_, 3, v_auxDeclNGen_21_);
lean_ctor_set(v_reuseFailAlloc_52_, 4, v_traceState_22_);
lean_ctor_set(v_reuseFailAlloc_52_, 5, v___x_31_);
lean_ctor_set(v_reuseFailAlloc_52_, 6, v_recordedDeps_23_);
lean_ctor_set(v_reuseFailAlloc_52_, 7, v_messages_24_);
lean_ctor_set(v_reuseFailAlloc_52_, 8, v_infoState_25_);
lean_ctor_set(v_reuseFailAlloc_52_, 9, v_snapshotTasks_26_);
v___x_33_ = v_reuseFailAlloc_52_;
goto v_reusejp_32_;
}
v_reusejp_32_:
{
lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v_mctx_36_; lean_object* v_zetaDeltaFVarIds_37_; lean_object* v_postponed_38_; lean_object* v_diag_39_; lean_object* v___x_41_; uint8_t v_isShared_42_; uint8_t v_isSharedCheck_50_; 
v___x_34_ = lean_st_ref_put(v___y_13_, v___x_33_);
v___x_35_ = lean_st_ref_take(v___y_11_);
v_mctx_36_ = lean_ctor_get(v___x_35_, 0);
v_zetaDeltaFVarIds_37_ = lean_ctor_get(v___x_35_, 2);
v_postponed_38_ = lean_ctor_get(v___x_35_, 3);
v_diag_39_ = lean_ctor_get(v___x_35_, 4);
v_isSharedCheck_50_ = !lean_is_exclusive(v___x_35_);
if (v_isSharedCheck_50_ == 0)
{
lean_object* v_unused_51_; 
v_unused_51_ = lean_ctor_get(v___x_35_, 1);
lean_dec(v_unused_51_);
v___x_41_ = v___x_35_;
v_isShared_42_ = v_isSharedCheck_50_;
goto v_resetjp_40_;
}
else
{
lean_inc(v_diag_39_);
lean_inc(v_postponed_38_);
lean_inc(v_zetaDeltaFVarIds_37_);
lean_inc(v_mctx_36_);
lean_dec(v___x_35_);
v___x_41_ = lean_box(0);
v_isShared_42_ = v_isSharedCheck_50_;
goto v_resetjp_40_;
}
v_resetjp_40_:
{
lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_46_; 
v___x_43_ = lean_box(0);
v___x_44_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___closed__3);
if (v_isShared_42_ == 0)
{
lean_ctor_set(v___x_41_, 1, v___x_44_);
v___x_46_ = v___x_41_;
goto v_reusejp_45_;
}
else
{
lean_object* v_reuseFailAlloc_49_; 
v_reuseFailAlloc_49_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_49_, 0, v_mctx_36_);
lean_ctor_set(v_reuseFailAlloc_49_, 1, v___x_44_);
lean_ctor_set(v_reuseFailAlloc_49_, 2, v_zetaDeltaFVarIds_37_);
lean_ctor_set(v_reuseFailAlloc_49_, 3, v_postponed_38_);
lean_ctor_set(v_reuseFailAlloc_49_, 4, v_diag_39_);
v___x_46_ = v_reuseFailAlloc_49_;
goto v_reusejp_45_;
}
v_reusejp_45_:
{
lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_47_ = lean_st_ref_put(v___y_11_, v___x_46_);
v___x_48_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_48_, 0, v___x_43_);
return v___x_48_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___boxed(lean_object* v_ext_55_, lean_object* v_b_56_, lean_object* v_kind_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_){
_start:
{
uint8_t v_kind_boxed_62_; lean_object* v_res_63_; 
v_kind_boxed_62_ = lean_unbox(v_kind_57_);
v_res_63_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg(v_ext_55_, v_b_56_, v_kind_boxed_62_, v___y_58_, v___y_59_, v___y_60_);
lean_dec(v___y_60_);
lean_dec_ref(v___y_59_);
lean_dec(v___y_58_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2(lean_object* v_00_u03b1_64_, lean_object* v_00_u03b2_65_, lean_object* v_00_u03c3_66_, lean_object* v_ext_67_, lean_object* v_b_68_, uint8_t v_kind_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg(v_ext_67_, v_b_68_, v_kind_69_, v___y_71_, v___y_72_, v___y_73_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___boxed(lean_object* v_00_u03b1_76_, lean_object* v_00_u03b2_77_, lean_object* v_00_u03c3_78_, lean_object* v_ext_79_, lean_object* v_b_80_, lean_object* v_kind_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_){
_start:
{
uint8_t v_kind_boxed_87_; lean_object* v_res_88_; 
v_kind_boxed_87_ = lean_unbox(v_kind_81_);
v_res_88_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2(v_00_u03b1_76_, v_00_u03b2_77_, v_00_u03c3_78_, v_ext_79_, v_b_80_, v_kind_boxed_87_, v___y_82_, v___y_83_, v___y_84_, v___y_85_);
lean_dec(v___y_85_);
lean_dec_ref(v___y_84_);
lean_dec(v___y_83_);
lean_dec_ref(v___y_82_);
return v_res_88_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_registerNormTheorems_spec__3___redArg(lean_object* v_x_89_){
_start:
{
uint8_t v___x_90_; 
v___x_90_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_registerNormTheorems_spec__3___redArg___boxed(lean_object* v_x_91_){
_start:
{
uint8_t v_res_92_; lean_object* v_r_93_; 
v_res_92_ = l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_registerNormTheorems_spec__3___redArg(v_x_91_);
lean_dec_ref(v_x_91_);
v_r_93_ = lean_box(v_res_92_);
return v_r_93_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_registerNormTheorems_spec__3(lean_object* v_00_u03b2_94_, lean_object* v_x_95_){
_start:
{
uint8_t v___x_96_; 
v___x_96_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_registerNormTheorems_spec__3___boxed(lean_object* v_00_u03b2_97_, lean_object* v_x_98_){
_start:
{
uint8_t v_res_99_; lean_object* v_r_100_; 
v_res_99_ = l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_registerNormTheorems_spec__3(v_00_u03b2_97_, v_x_98_);
lean_dec_ref(v_x_98_);
v_r_100_ = lean_box(v_res_99_);
return v_r_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__4_spec__4(lean_object* v_msgData_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_){
_start:
{
lean_object* v___x_107_; lean_object* v_env_108_; uint8_t v___x_109_; lean_object* v_env_110_; lean_object* v___x_111_; lean_object* v_toCold_112_; lean_object* v_mctx_113_; lean_object* v_lctx_114_; lean_object* v_options_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_107_ = lean_st_ref_get(v___y_105_);
v_env_108_ = lean_ctor_get(v___x_107_, 0);
lean_inc_ref(v_env_108_);
lean_dec(v___x_107_);
v___x_109_ = 0;
v_env_110_ = l_Lean_Environment_setRecordingDeps(v_env_108_, v___x_109_);
v___x_111_ = lean_st_ref_get(v___y_103_);
v_toCold_112_ = lean_ctor_get(v___y_104_, 0);
v_mctx_113_ = lean_ctor_get(v___x_111_, 0);
lean_inc_ref(v_mctx_113_);
lean_dec(v___x_111_);
v_lctx_114_ = lean_ctor_get(v___y_102_, 2);
v_options_115_ = lean_ctor_get(v_toCold_112_, 2);
lean_inc_ref(v_options_115_);
lean_inc_ref(v_lctx_114_);
v___x_116_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_116_, 0, v_env_110_);
lean_ctor_set(v___x_116_, 1, v_mctx_113_);
lean_ctor_set(v___x_116_, 2, v_lctx_114_);
lean_ctor_set(v___x_116_, 3, v_options_115_);
v___x_117_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_117_, 0, v___x_116_);
lean_ctor_set(v___x_117_, 1, v_msgData_101_);
v___x_118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_118_, 0, v___x_117_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__4_spec__4___boxed(lean_object* v_msgData_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__4_spec__4(v_msgData_119_, v___y_120_, v___y_121_, v___y_122_, v___y_123_);
lean_dec(v___y_123_);
lean_dec_ref(v___y_122_);
lean_dec(v___y_121_);
lean_dec_ref(v___y_120_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__4___redArg(lean_object* v_msg_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_){
_start:
{
lean_object* v_ref_132_; lean_object* v___x_133_; lean_object* v_a_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_142_; 
v_ref_132_ = lean_ctor_get(v___y_129_, 2);
v___x_133_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__4_spec__4(v_msg_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_);
v_a_134_ = lean_ctor_get(v___x_133_, 0);
v_isSharedCheck_142_ = !lean_is_exclusive(v___x_133_);
if (v_isSharedCheck_142_ == 0)
{
v___x_136_ = v___x_133_;
v_isShared_137_ = v_isSharedCheck_142_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_a_134_);
lean_dec(v___x_133_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_142_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v___x_138_; lean_object* v___x_140_; 
lean_inc(v_ref_132_);
v___x_138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_138_, 0, v_ref_132_);
lean_ctor_set(v___x_138_, 1, v_a_134_);
if (v_isShared_137_ == 0)
{
lean_ctor_set_tag(v___x_136_, 1);
lean_ctor_set(v___x_136_, 0, v___x_138_);
v___x_140_ = v___x_136_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v___x_138_);
v___x_140_ = v_reuseFailAlloc_141_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
return v___x_140_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__4___redArg___boxed(lean_object* v_msg_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__4___redArg(v_msg_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_);
lean_dec(v___y_147_);
lean_dec_ref(v___y_146_);
lean_dec(v___y_145_);
lean_dec_ref(v___y_144_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_registerNormTheorems_spec__1(lean_object* v_as_150_, size_t v_sz_151_, size_t v_i_152_, lean_object* v_b_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_){
_start:
{
uint8_t v___x_159_; 
v___x_159_ = lean_usize_dec_lt(v_i_152_, v_sz_151_);
if (v___x_159_ == 0)
{
lean_object* v___x_160_; 
v___x_160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_160_, 0, v_b_153_);
return v___x_160_;
}
else
{
lean_object* v___x_161_; lean_object* v_a_162_; uint8_t v___x_163_; uint8_t v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_161_ = lean_box(0);
v_a_162_ = lean_array_uget_borrowed(v_as_150_, v_i_152_);
v___x_163_ = 0;
v___x_164_ = 0;
v___x_165_ = lean_unsigned_to_nat(1000u);
lean_inc(v_a_162_);
v___x_166_ = l_Lean_Meta_Grind_addNormTheorem(v_a_162_, v___x_159_, v___x_163_, v___x_164_, v___x_165_, v___y_154_, v___y_155_, v___y_156_, v___y_157_);
if (lean_obj_tag(v___x_166_) == 0)
{
size_t v___x_167_; size_t v___x_168_; 
lean_dec_ref_known(v___x_166_, 1);
v___x_167_ = ((size_t)1ULL);
v___x_168_ = lean_usize_add(v_i_152_, v___x_167_);
v_i_152_ = v___x_168_;
v_b_153_ = v___x_161_;
goto _start;
}
else
{
return v___x_166_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_registerNormTheorems_spec__1___boxed(lean_object* v_as_170_, lean_object* v_sz_171_, lean_object* v_i_172_, lean_object* v_b_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_){
_start:
{
size_t v_sz_boxed_179_; size_t v_i_boxed_180_; lean_object* v_res_181_; 
v_sz_boxed_179_ = lean_unbox_usize(v_sz_171_);
lean_dec(v_sz_171_);
v_i_boxed_180_ = lean_unbox_usize(v_i_172_);
lean_dec(v_i_172_);
v_res_181_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_registerNormTheorems_spec__1(v_as_170_, v_sz_boxed_179_, v_i_boxed_180_, v_b_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_);
lean_dec(v___y_177_);
lean_dec_ref(v___y_176_);
lean_dec(v___y_175_);
lean_dec_ref(v___y_174_);
lean_dec_ref(v_as_170_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_registerNormTheorems_spec__0(lean_object* v_as_182_, size_t v_sz_183_, size_t v_i_184_, lean_object* v_b_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_){
_start:
{
uint8_t v___x_191_; 
v___x_191_ = lean_usize_dec_lt(v_i_184_, v_sz_183_);
if (v___x_191_ == 0)
{
lean_object* v___x_192_; 
v___x_192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_192_, 0, v_b_185_);
return v___x_192_;
}
else
{
lean_object* v___x_193_; lean_object* v_a_194_; uint8_t v___x_195_; uint8_t v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_193_ = lean_box(0);
v_a_194_ = lean_array_uget_borrowed(v_as_182_, v_i_184_);
v___x_195_ = 0;
v___x_196_ = 0;
v___x_197_ = lean_unsigned_to_nat(1000u);
lean_inc(v_a_194_);
v___x_198_ = l_Lean_Meta_Grind_addNormTheorem(v_a_194_, v___x_195_, v___x_195_, v___x_196_, v___x_197_, v___y_186_, v___y_187_, v___y_188_, v___y_189_);
if (lean_obj_tag(v___x_198_) == 0)
{
size_t v___x_199_; size_t v___x_200_; 
lean_dec_ref_known(v___x_198_, 1);
v___x_199_ = ((size_t)1ULL);
v___x_200_ = lean_usize_add(v_i_184_, v___x_199_);
v_i_184_ = v___x_200_;
v_b_185_ = v___x_193_;
goto _start;
}
else
{
return v___x_198_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_registerNormTheorems_spec__0___boxed(lean_object* v_as_202_, lean_object* v_sz_203_, lean_object* v_i_204_, lean_object* v_b_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_){
_start:
{
size_t v_sz_boxed_211_; size_t v_i_boxed_212_; lean_object* v_res_213_; 
v_sz_boxed_211_ = lean_unbox_usize(v_sz_203_);
lean_dec(v_sz_203_);
v_i_boxed_212_ = lean_unbox_usize(v_i_204_);
lean_dec(v_i_204_);
v_res_213_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_registerNormTheorems_spec__0(v_as_202_, v_sz_boxed_211_, v_i_boxed_212_, v_b_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_);
lean_dec(v___y_209_);
lean_dec_ref(v___y_208_);
lean_dec(v___y_207_);
lean_dec_ref(v___y_206_);
lean_dec_ref(v_as_202_);
return v_res_213_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_registerNormTheorems___closed__19(void){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_246_ = ((lean_object*)(l_Lean_Meta_Grind_registerNormTheorems___closed__18));
v___x_247_ = l_Lean_stringToMessageData(v___x_246_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerNormTheorems(lean_object* v_preDeclNames_248_, lean_object* v_postDeclNames_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_){
_start:
{
lean_object* v___y_256_; lean_object* v___y_257_; lean_object* v___y_258_; lean_object* v___y_259_; lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_318_ = l_Lean_Meta_Grind_normExt;
v___x_319_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v___x_318_, v_a_253_);
if (lean_obj_tag(v___x_319_) == 0)
{
lean_object* v_a_320_; lean_object* v_lemmaNames_321_; uint8_t v___x_322_; 
v_a_320_ = lean_ctor_get(v___x_319_, 0);
lean_inc(v_a_320_);
lean_dec_ref_known(v___x_319_, 1);
v_lemmaNames_321_ = lean_ctor_get(v_a_320_, 2);
lean_inc_ref(v_lemmaNames_321_);
lean_dec(v_a_320_);
v___x_322_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_lemmaNames_321_);
lean_dec_ref(v_lemmaNames_321_);
if (v___x_322_ == 0)
{
lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_323_ = lean_obj_once(&l_Lean_Meta_Grind_registerNormTheorems___closed__19, &l_Lean_Meta_Grind_registerNormTheorems___closed__19_once, _init_l_Lean_Meta_Grind_registerNormTheorems___closed__19);
v___x_324_ = l_Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__4___redArg(v___x_323_, v_a_250_, v_a_251_, v_a_252_, v_a_253_);
return v___x_324_;
}
else
{
v___y_256_ = v_a_250_;
v___y_257_ = v_a_251_;
v___y_258_ = v_a_252_;
v___y_259_ = v_a_253_;
goto v___jp_255_;
}
}
else
{
lean_object* v_a_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_332_; 
v_a_325_ = lean_ctor_get(v___x_319_, 0);
v_isSharedCheck_332_ = !lean_is_exclusive(v___x_319_);
if (v_isSharedCheck_332_ == 0)
{
v___x_327_ = v___x_319_;
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_a_325_);
lean_dec(v___x_319_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_330_; 
if (v_isShared_328_ == 0)
{
v___x_330_ = v___x_327_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_a_325_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
}
v___jp_255_:
{
lean_object* v___x_260_; size_t v_sz_261_; size_t v___x_262_; lean_object* v___x_263_; 
v___x_260_ = lean_box(0);
v_sz_261_ = lean_array_size(v_preDeclNames_248_);
v___x_262_ = ((size_t)0ULL);
v___x_263_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_registerNormTheorems_spec__0(v_preDeclNames_248_, v_sz_261_, v___x_262_, v___x_260_, v___y_256_, v___y_257_, v___y_258_, v___y_259_);
if (lean_obj_tag(v___x_263_) == 0)
{
size_t v_sz_264_; lean_object* v___x_265_; 
lean_dec_ref_known(v___x_263_, 1);
v_sz_264_ = lean_array_size(v_postDeclNames_249_);
v___x_265_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_registerNormTheorems_spec__1(v_postDeclNames_249_, v_sz_264_, v___x_262_, v___x_260_, v___y_256_, v___y_257_, v___y_258_, v___y_259_);
if (lean_obj_tag(v___x_265_) == 0)
{
lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_316_; 
v_isSharedCheck_316_ = !lean_is_exclusive(v___x_265_);
if (v_isSharedCheck_316_ == 0)
{
lean_object* v_unused_317_; 
v_unused_317_ = lean_ctor_get(v___x_265_, 0);
lean_dec(v_unused_317_);
v___x_267_ = v___x_265_;
v_isShared_268_ = v_isSharedCheck_316_;
goto v_resetjp_266_;
}
else
{
lean_dec(v___x_265_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_316_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_269_ = ((lean_object*)(l_Lean_Meta_Grind_registerNormTheorems___closed__2));
v___x_270_ = l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(v___x_269_, v___y_256_, v___y_257_, v___y_258_, v___y_259_);
if (lean_obj_tag(v___x_270_) == 0)
{
lean_object* v_a_271_; lean_object* v___x_272_; lean_object* v___x_274_; 
v_a_271_ = lean_ctor_get(v___x_270_, 0);
lean_inc(v_a_271_);
lean_dec_ref_known(v___x_270_, 1);
v___x_272_ = l_Lean_Meta_Grind_normSymExt;
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 0, v_a_271_);
v___x_274_ = v___x_267_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v_a_271_);
v___x_274_ = v_reuseFailAlloc_307_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
uint8_t v___x_275_; lean_object* v___x_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_305_; 
v___x_275_ = 0;
v___x_276_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg(v___x_272_, v___x_274_, v___x_275_, v___y_257_, v___y_258_, v___y_259_);
v_isSharedCheck_305_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_305_ == 0)
{
lean_object* v_unused_306_; 
v_unused_306_ = lean_ctor_get(v___x_276_, 0);
lean_dec(v_unused_306_);
v___x_278_ = v___x_276_;
v_isShared_279_ = v_isSharedCheck_305_;
goto v_resetjp_277_;
}
else
{
lean_dec(v___x_276_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_305_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_280_ = ((lean_object*)(l_Lean_Meta_Grind_registerNormTheorems___closed__4));
v___x_281_ = l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(v___x_280_, v___y_256_, v___y_257_, v___y_258_, v___y_259_);
if (lean_obj_tag(v___x_281_) == 0)
{
lean_object* v_a_282_; lean_object* v___x_284_; 
v_a_282_ = lean_ctor_get(v___x_281_, 0);
lean_inc(v_a_282_);
lean_dec_ref_known(v___x_281_, 1);
if (v_isShared_279_ == 0)
{
lean_ctor_set(v___x_278_, 0, v_a_282_);
v___x_284_ = v___x_278_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v_a_282_);
v___x_284_ = v_reuseFailAlloc_296_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_285_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg(v___x_272_, v___x_284_, v___x_275_, v___y_257_, v___y_258_, v___y_259_);
lean_dec_ref(v___x_285_);
v___x_286_ = ((lean_object*)(l_Lean_Meta_Grind_registerNormTheorems___closed__7));
v___x_287_ = l_Lean_Meta_Grind_addNormSymDeclToUnfold(v___x_286_, v___x_275_, v___y_256_, v___y_257_, v___y_258_, v___y_259_);
if (lean_obj_tag(v___x_287_) == 0)
{
lean_object* v___x_288_; lean_object* v___x_289_; 
lean_dec_ref_known(v___x_287_, 1);
v___x_288_ = ((lean_object*)(l_Lean_Meta_Grind_registerNormTheorems___closed__10));
v___x_289_ = l_Lean_Meta_Grind_addNormSymDeclToUnfold(v___x_288_, v___x_275_, v___y_256_, v___y_257_, v___y_258_, v___y_259_);
if (lean_obj_tag(v___x_289_) == 0)
{
lean_object* v___x_290_; lean_object* v___x_291_; 
lean_dec_ref_known(v___x_289_, 1);
v___x_290_ = ((lean_object*)(l_Lean_Meta_Grind_registerNormTheorems___closed__12));
v___x_291_ = l_Lean_Meta_Grind_addNormSymDeclToUnfold(v___x_290_, v___x_275_, v___y_256_, v___y_257_, v___y_258_, v___y_259_);
if (lean_obj_tag(v___x_291_) == 0)
{
lean_object* v___x_292_; lean_object* v___x_293_; 
lean_dec_ref_known(v___x_291_, 1);
v___x_292_ = ((lean_object*)(l_Lean_Meta_Grind_registerNormTheorems___closed__15));
v___x_293_ = l_Lean_Meta_Grind_addNormSymDeclToUnfold(v___x_292_, v___x_275_, v___y_256_, v___y_257_, v___y_258_, v___y_259_);
if (lean_obj_tag(v___x_293_) == 0)
{
lean_object* v___x_294_; lean_object* v___x_295_; 
lean_dec_ref_known(v___x_293_, 1);
v___x_294_ = ((lean_object*)(l_Lean_Meta_Grind_registerNormTheorems___closed__17));
v___x_295_ = l_Lean_Meta_Grind_addNormSymDeclToUnfold(v___x_294_, v___x_275_, v___y_256_, v___y_257_, v___y_258_, v___y_259_);
return v___x_295_;
}
else
{
return v___x_293_;
}
}
else
{
return v___x_291_;
}
}
else
{
return v___x_289_;
}
}
else
{
return v___x_287_;
}
}
}
else
{
lean_object* v_a_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_304_; 
lean_del_object(v___x_278_);
v_a_297_ = lean_ctor_get(v___x_281_, 0);
v_isSharedCheck_304_ = !lean_is_exclusive(v___x_281_);
if (v_isSharedCheck_304_ == 0)
{
v___x_299_ = v___x_281_;
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_a_297_);
lean_dec(v___x_281_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_302_; 
if (v_isShared_300_ == 0)
{
v___x_302_ = v___x_299_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_a_297_);
v___x_302_ = v_reuseFailAlloc_303_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
return v___x_302_;
}
}
}
}
}
}
else
{
lean_object* v_a_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_315_; 
lean_del_object(v___x_267_);
v_a_308_ = lean_ctor_get(v___x_270_, 0);
v_isSharedCheck_315_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_315_ == 0)
{
v___x_310_ = v___x_270_;
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_a_308_);
lean_dec(v___x_270_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_313_; 
if (v_isShared_311_ == 0)
{
v___x_313_ = v___x_310_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_a_308_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
}
}
else
{
return v___x_265_;
}
}
else
{
return v___x_263_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerNormTheorems___boxed(lean_object* v_preDeclNames_333_, lean_object* v_postDeclNames_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_Lean_Meta_Grind_registerNormTheorems(v_preDeclNames_333_, v_postDeclNames_334_, v_a_335_, v_a_336_, v_a_337_, v_a_338_);
lean_dec(v_a_338_);
lean_dec_ref(v_a_337_);
lean_dec(v_a_336_);
lean_dec_ref(v_a_335_);
lean_dec_ref(v_postDeclNames_334_);
lean_dec_ref(v_preDeclNames_333_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__4(lean_object* v_00_u03b1_341_, lean_object* v_msg_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = l_Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__4___redArg(v_msg_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__4___boxed(lean_object* v_00_u03b1_349_, lean_object* v_msg_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__4(v_00_u03b1_349_, v_msg_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
lean_dec(v___y_352_);
lean_dec_ref(v___y_351_);
return v_res_356_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget(lean_object* v_declName_379_){
_start:
{
lean_object* v___x_380_; uint8_t v___x_381_; 
v___x_380_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__1));
v___x_381_ = lean_name_eq(v_declName_379_, v___x_380_);
if (v___x_381_ == 0)
{
lean_object* v___x_382_; uint8_t v___x_383_; 
v___x_382_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__3));
v___x_383_ = lean_name_eq(v_declName_379_, v___x_382_);
if (v___x_383_ == 0)
{
lean_object* v___x_384_; uint8_t v___x_385_; 
v___x_384_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__5));
v___x_385_ = lean_name_eq(v_declName_379_, v___x_384_);
if (v___x_385_ == 0)
{
lean_object* v___x_386_; uint8_t v___x_387_; 
v___x_386_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__8));
v___x_387_ = lean_name_eq(v_declName_379_, v___x_386_);
if (v___x_387_ == 0)
{
lean_object* v___x_388_; uint8_t v___x_389_; 
v___x_388_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__11));
v___x_389_ = lean_name_eq(v_declName_379_, v___x_388_);
return v___x_389_;
}
else
{
return v___x_387_;
}
}
else
{
return v___x_385_;
}
}
else
{
return v___x_383_;
}
}
else
{
return v___x_381_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___boxed(lean_object* v_declName_390_){
_start:
{
uint8_t v_res_391_; lean_object* v_r_392_; 
v_res_391_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget(v_declName_390_);
lean_dec(v_declName_390_);
v_r_392_ = lean_box(v_res_391_);
return v_r_392_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpEq___redArg___closed__8(void){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_407_ = lean_box(0);
v___x_408_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__7));
v___x_409_ = l_Lean_mkConst(v___x_408_, v___x_407_);
return v___x_409_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpEq___redArg___closed__11(void){
_start:
{
lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_413_ = lean_box(0);
v___x_414_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__10));
v___x_415_ = l_Lean_mkConst(v___x_414_, v___x_413_);
return v___x_415_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpEq___redArg___closed__14(void){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_419_ = lean_box(0);
v___x_420_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__13));
v___x_421_ = l_Lean_mkConst(v___x_420_, v___x_419_);
return v___x_421_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpEq___redArg___closed__17(void){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_427_ = lean_box(0);
v___x_428_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__16));
v___x_429_ = l_Lean_mkConst(v___x_428_, v___x_427_);
return v___x_429_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpEq___redArg___closed__20(void){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_435_ = lean_box(0);
v___x_436_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__19));
v___x_437_ = l_Lean_mkConst(v___x_436_, v___x_435_);
return v___x_437_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpEq___redArg___closed__25(void){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_445_ = lean_box(0);
v___x_446_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__24));
v___x_447_ = l_Lean_mkConst(v___x_446_, v___x_445_);
return v___x_447_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpEq___redArg___closed__28(void){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_453_ = lean_box(0);
v___x_454_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__27));
v___x_455_ = l_Lean_mkConst(v___x_454_, v___x_453_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpEq___redArg(lean_object* v_e_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_){
_start:
{
lean_object* v___x_469_; 
v___x_469_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_460_, v_a_462_);
if (lean_obj_tag(v___x_469_) == 0)
{
lean_object* v_a_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_591_; 
v_a_470_ = lean_ctor_get(v___x_469_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_591_ == 0)
{
v___x_472_ = v___x_469_;
v_isShared_473_ = v_isSharedCheck_591_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_a_470_);
lean_dec(v___x_469_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_591_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_474_; uint8_t v___x_475_; 
v___x_474_ = l_Lean_Expr_cleanupAnnotations(v_a_470_);
lean_dec(v_a_470_);
v___x_475_ = l_Lean_Expr_isApp(v___x_474_);
if (v___x_475_ == 0)
{
lean_dec_ref(v___x_474_);
lean_del_object(v___x_472_);
goto v___jp_466_;
}
else
{
lean_object* v___x_476_; uint8_t v___x_477_; 
v___x_476_ = l_Lean_Expr_appFnCleanup___redArg(v___x_474_);
v___x_477_ = l_Lean_Expr_isApp(v___x_476_);
if (v___x_477_ == 0)
{
lean_dec_ref(v___x_476_);
lean_dec_ref(v___x_474_);
lean_del_object(v___x_472_);
goto v___jp_466_;
}
else
{
lean_object* v___x_478_; uint8_t v___x_479_; 
v___x_478_ = l_Lean_Expr_appFnCleanup___redArg(v___x_476_);
v___x_479_ = l_Lean_Expr_isApp(v___x_478_);
if (v___x_479_ == 0)
{
lean_dec_ref(v___x_478_);
lean_dec_ref(v___x_476_);
lean_dec_ref(v___x_474_);
lean_del_object(v___x_472_);
goto v___jp_466_;
}
else
{
lean_object* v___x_480_; lean_object* v___x_481_; uint8_t v___x_482_; 
v___x_480_ = l_Lean_Expr_appFnCleanup___redArg(v___x_478_);
v___x_481_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__2));
v___x_482_ = l_Lean_Expr_isConstOf(v___x_480_, v___x_481_);
if (v___x_482_ == 0)
{
lean_dec_ref(v___x_480_);
lean_dec_ref(v___x_478_);
lean_dec_ref(v___x_476_);
lean_dec_ref(v___x_474_);
lean_del_object(v___x_472_);
goto v___jp_466_;
}
else
{
lean_object* v_arg_483_; lean_object* v_arg_484_; lean_object* v_arg_485_; lean_object* v___x_486_; 
v_arg_483_ = lean_ctor_get(v___x_474_, 1);
lean_inc_ref(v_arg_483_);
lean_dec_ref(v___x_474_);
v_arg_484_ = lean_ctor_get(v___x_476_, 1);
lean_inc_ref(v_arg_484_);
lean_dec_ref(v___x_476_);
v_arg_485_ = lean_ctor_get(v___x_478_, 1);
lean_inc_ref_n(v_arg_485_, 2);
lean_dec_ref(v___x_478_);
v___x_486_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_485_, v_a_462_);
if (lean_obj_tag(v___x_486_) == 0)
{
lean_object* v_a_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_582_; 
v_a_487_ = lean_ctor_get(v___x_486_, 0);
v_isSharedCheck_582_ = !lean_is_exclusive(v___x_486_);
if (v_isSharedCheck_582_ == 0)
{
v___x_489_ = v___x_486_;
v_isShared_490_ = v_isSharedCheck_582_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_a_487_);
lean_dec(v___x_486_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_582_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_496_; lean_object* v___x_497_; uint8_t v___x_498_; 
v___x_496_ = l_Lean_Expr_cleanupAnnotations(v_a_487_);
lean_dec(v_a_487_);
v___x_497_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__3));
v___x_498_ = l_Lean_Expr_isConstOf(v___x_496_, v___x_497_);
lean_dec_ref(v___x_496_);
if (v___x_498_ == 0)
{
uint8_t v___x_509_; 
lean_del_object(v___x_489_);
lean_del_object(v___x_472_);
v___x_509_ = lean_expr_eqv(v_arg_484_, v_arg_483_);
if (v___x_509_ == 0)
{
lean_object* v___x_510_; uint8_t v___x_511_; 
lean_dec_ref(v_arg_485_);
lean_dec_ref(v___x_480_);
v___x_510_ = lean_obj_once(&l_Lean_Meta_Grind_simpEq___redArg___closed__11, &l_Lean_Meta_Grind_simpEq___redArg___closed__11_once, _init_l_Lean_Meta_Grind_simpEq___redArg___closed__11);
v___x_511_ = lean_expr_eqv(v_arg_483_, v___x_510_);
if (v___x_511_ == 0)
{
lean_object* v___x_512_; uint8_t v___x_513_; 
v___x_512_ = lean_obj_once(&l_Lean_Meta_Grind_simpEq___redArg___closed__14, &l_Lean_Meta_Grind_simpEq___redArg___closed__14_once, _init_l_Lean_Meta_Grind_simpEq___redArg___closed__14);
v___x_513_ = lean_expr_eqv(v_arg_483_, v___x_512_);
lean_dec_ref(v_arg_483_);
if (v___x_513_ == 0)
{
lean_object* v___x_514_; lean_object* v___x_515_; 
lean_dec_ref(v_arg_484_);
v___x_514_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
v___x_515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_515_, 0, v___x_514_);
return v___x_515_;
}
else
{
lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
lean_inc_ref(v_arg_484_);
v___x_516_ = l_Lean_mkNot(v_arg_484_);
v___x_517_ = lean_obj_once(&l_Lean_Meta_Grind_simpEq___redArg___closed__17, &l_Lean_Meta_Grind_simpEq___redArg___closed__17_once, _init_l_Lean_Meta_Grind_simpEq___redArg___closed__17);
v___x_518_ = l_Lean_Expr_app___override(v___x_517_, v_arg_484_);
v___x_519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_519_, 0, v___x_518_);
v___x_520_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_520_, 0, v___x_516_);
lean_ctor_set(v___x_520_, 1, v___x_519_);
lean_ctor_set_uint8(v___x_520_, sizeof(void*)*2, v___x_482_);
v___x_521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_521_, 0, v___x_520_);
v___x_522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_522_, 0, v___x_521_);
return v___x_522_;
}
}
else
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
lean_dec_ref(v_arg_483_);
v___x_523_ = lean_obj_once(&l_Lean_Meta_Grind_simpEq___redArg___closed__20, &l_Lean_Meta_Grind_simpEq___redArg___closed__20_once, _init_l_Lean_Meta_Grind_simpEq___redArg___closed__20);
lean_inc_ref(v_arg_484_);
v___x_524_ = l_Lean_Expr_app___override(v___x_523_, v_arg_484_);
v___x_525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_525_, 0, v___x_524_);
v___x_526_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_526_, 0, v_arg_484_);
lean_ctor_set(v___x_526_, 1, v___x_525_);
lean_ctor_set_uint8(v___x_526_, sizeof(void*)*2, v___x_482_);
v___x_527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_527_, 0, v___x_526_);
v___x_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_528_, 0, v___x_527_);
return v___x_528_;
}
}
else
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
lean_dec_ref(v_arg_483_);
v___x_529_ = l_Lean_Expr_constLevels_x21(v___x_480_);
lean_dec_ref(v___x_480_);
v___x_530_ = lean_obj_once(&l_Lean_Meta_Grind_simpEq___redArg___closed__11, &l_Lean_Meta_Grind_simpEq___redArg___closed__11_once, _init_l_Lean_Meta_Grind_simpEq___redArg___closed__11);
v___x_531_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__22));
v___x_532_ = l_Lean_mkConst(v___x_531_, v___x_529_);
v___x_533_ = l_Lean_mkAppB(v___x_532_, v_arg_485_, v_arg_484_);
v___x_534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_534_, 0, v___x_533_);
v___x_535_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_535_, 0, v___x_530_);
lean_ctor_set(v___x_535_, 1, v___x_534_);
lean_ctor_set_uint8(v___x_535_, sizeof(void*)*2, v___x_482_);
v___x_536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_536_, 0, v___x_535_);
v___x_537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_537_, 0, v___x_536_);
return v___x_537_;
}
}
else
{
lean_object* v___x_538_; 
v___x_538_ = l_Lean_Expr_getAppFn(v_arg_483_);
if (lean_obj_tag(v___x_538_) == 4)
{
lean_object* v_declName_539_; lean_object* v___x_540_; uint8_t v___x_567_; 
v_declName_539_ = lean_ctor_get(v___x_538_, 0);
lean_inc(v_declName_539_);
lean_dec_ref_known(v___x_538_, 2);
v___x_540_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__24));
v___x_567_ = lean_name_eq(v_declName_539_, v___x_540_);
if (v___x_567_ == 0)
{
lean_object* v___x_568_; uint8_t v___x_569_; 
v___x_568_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__30));
v___x_569_ = lean_name_eq(v_declName_539_, v___x_568_);
if (v___x_569_ == 0)
{
lean_object* v___x_570_; 
lean_del_object(v___x_489_);
v___x_570_ = l_Lean_Expr_getAppFn(v_arg_484_);
if (lean_obj_tag(v___x_570_) == 4)
{
lean_object* v_declName_571_; uint8_t v___x_572_; 
v_declName_571_ = lean_ctor_get(v___x_570_, 0);
lean_inc(v_declName_571_);
lean_dec_ref_known(v___x_570_, 2);
v___x_572_ = lean_name_eq(v_declName_571_, v___x_540_);
if (v___x_572_ == 0)
{
uint8_t v___x_573_; 
v___x_573_ = lean_name_eq(v_declName_571_, v___x_568_);
if (v___x_573_ == 0)
{
uint8_t v___x_574_; 
lean_del_object(v___x_472_);
v___x_574_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget(v_declName_571_);
lean_dec(v_declName_571_);
if (v___x_574_ == 0)
{
uint8_t v___x_575_; 
v___x_575_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget(v_declName_539_);
lean_dec(v_declName_539_);
if (v___x_575_ == 0)
{
lean_object* v___x_576_; lean_object* v___x_577_; 
lean_dec_ref(v_arg_485_);
lean_dec_ref(v_arg_484_);
lean_dec_ref(v_arg_483_);
lean_dec_ref(v___x_480_);
v___x_576_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
v___x_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
return v___x_577_;
}
else
{
goto v___jp_541_;
}
}
else
{
lean_dec(v_declName_539_);
goto v___jp_541_;
}
}
else
{
lean_dec(v_declName_571_);
lean_dec(v_declName_539_);
goto v___jp_499_;
}
}
else
{
lean_dec(v_declName_571_);
lean_dec(v_declName_539_);
goto v___jp_499_;
}
}
else
{
lean_object* v___x_578_; lean_object* v___x_579_; 
lean_dec_ref(v___x_570_);
lean_dec(v_declName_539_);
lean_dec_ref(v_arg_485_);
lean_dec_ref(v_arg_484_);
lean_dec_ref(v_arg_483_);
lean_dec_ref(v___x_480_);
lean_del_object(v___x_472_);
v___x_578_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
v___x_579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_579_, 0, v___x_578_);
return v___x_579_;
}
}
else
{
lean_dec(v_declName_539_);
lean_dec_ref(v_arg_485_);
lean_dec_ref(v_arg_484_);
lean_dec_ref(v_arg_483_);
lean_dec_ref(v___x_480_);
lean_del_object(v___x_472_);
goto v___jp_491_;
}
}
else
{
lean_dec(v_declName_539_);
lean_dec_ref(v_arg_485_);
lean_dec_ref(v_arg_484_);
lean_dec_ref(v_arg_483_);
lean_dec_ref(v___x_480_);
lean_del_object(v___x_472_);
goto v___jp_491_;
}
v___jp_541_:
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_542_ = lean_obj_once(&l_Lean_Meta_Grind_simpEq___redArg___closed__25, &l_Lean_Meta_Grind_simpEq___redArg___closed__25_once, _init_l_Lean_Meta_Grind_simpEq___redArg___closed__25);
lean_inc_ref(v_arg_484_);
lean_inc_ref(v_arg_485_);
lean_inc_ref(v___x_480_);
v___x_543_ = l_Lean_mkApp3(v___x_480_, v_arg_485_, v_arg_484_, v___x_542_);
lean_inc_ref(v_arg_483_);
v___x_544_ = l_Lean_mkApp3(v___x_480_, v_arg_485_, v_arg_483_, v___x_542_);
v___x_545_ = l_Lean_Meta_mkEq(v___x_543_, v___x_544_, v_a_461_, v_a_462_, v_a_463_, v_a_464_);
if (lean_obj_tag(v___x_545_) == 0)
{
lean_object* v_a_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_558_; 
v_a_546_ = lean_ctor_get(v___x_545_, 0);
v_isSharedCheck_558_ = !lean_is_exclusive(v___x_545_);
if (v_isSharedCheck_558_ == 0)
{
v___x_548_ = v___x_545_;
v_isShared_549_ = v_isSharedCheck_558_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_a_546_);
lean_dec(v___x_545_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_558_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_556_; 
v___x_550_ = lean_obj_once(&l_Lean_Meta_Grind_simpEq___redArg___closed__28, &l_Lean_Meta_Grind_simpEq___redArg___closed__28_once, _init_l_Lean_Meta_Grind_simpEq___redArg___closed__28);
v___x_551_ = l_Lean_mkAppB(v___x_550_, v_arg_484_, v_arg_483_);
v___x_552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_552_, 0, v___x_551_);
v___x_553_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_553_, 0, v_a_546_);
lean_ctor_set(v___x_553_, 1, v___x_552_);
lean_ctor_set_uint8(v___x_553_, sizeof(void*)*2, v___x_498_);
v___x_554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_554_, 0, v___x_553_);
if (v_isShared_549_ == 0)
{
lean_ctor_set(v___x_548_, 0, v___x_554_);
v___x_556_ = v___x_548_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v___x_554_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
}
else
{
lean_object* v_a_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_566_; 
lean_dec_ref(v_arg_484_);
lean_dec_ref(v_arg_483_);
v_a_559_ = lean_ctor_get(v___x_545_, 0);
v_isSharedCheck_566_ = !lean_is_exclusive(v___x_545_);
if (v_isSharedCheck_566_ == 0)
{
v___x_561_ = v___x_545_;
v_isShared_562_ = v_isSharedCheck_566_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_a_559_);
lean_dec(v___x_545_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_566_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_564_; 
if (v_isShared_562_ == 0)
{
v___x_564_ = v___x_561_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v_a_559_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
return v___x_564_;
}
}
}
}
}
else
{
lean_object* v___x_580_; lean_object* v___x_581_; 
lean_dec_ref(v___x_538_);
lean_del_object(v___x_489_);
lean_dec_ref(v_arg_485_);
lean_dec_ref(v_arg_484_);
lean_dec_ref(v_arg_483_);
lean_dec_ref(v___x_480_);
lean_del_object(v___x_472_);
v___x_580_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
v___x_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
return v___x_581_;
}
}
v___jp_491_:
{
lean_object* v___x_492_; lean_object* v___x_494_; 
v___x_492_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 0, v___x_492_);
v___x_494_ = v___x_489_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v___x_492_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
v___jp_499_:
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_507_; 
lean_inc_ref(v_arg_484_);
lean_inc_ref(v_arg_483_);
v___x_500_ = l_Lean_mkApp3(v___x_480_, v_arg_485_, v_arg_483_, v_arg_484_);
v___x_501_ = lean_obj_once(&l_Lean_Meta_Grind_simpEq___redArg___closed__8, &l_Lean_Meta_Grind_simpEq___redArg___closed__8_once, _init_l_Lean_Meta_Grind_simpEq___redArg___closed__8);
v___x_502_ = l_Lean_mkAppB(v___x_501_, v_arg_484_, v_arg_483_);
v___x_503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_503_, 0, v___x_502_);
v___x_504_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_504_, 0, v___x_500_);
lean_ctor_set(v___x_504_, 1, v___x_503_);
lean_ctor_set_uint8(v___x_504_, sizeof(void*)*2, v___x_498_);
v___x_505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_505_, 0, v___x_504_);
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 0, v___x_505_);
v___x_507_ = v___x_472_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v___x_505_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
}
}
else
{
lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_590_; 
lean_dec_ref(v_arg_485_);
lean_dec_ref(v_arg_484_);
lean_dec_ref(v_arg_483_);
lean_dec_ref(v___x_480_);
lean_del_object(v___x_472_);
v_a_583_ = lean_ctor_get(v___x_486_, 0);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_486_);
if (v_isSharedCheck_590_ == 0)
{
v___x_585_ = v___x_486_;
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_dec(v___x_486_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_588_; 
if (v_isShared_586_ == 0)
{
v___x_588_ = v___x_585_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_a_583_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
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
lean_object* v_a_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_599_; 
v_a_592_ = lean_ctor_get(v___x_469_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_599_ == 0)
{
v___x_594_ = v___x_469_;
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_a_592_);
lean_dec(v___x_469_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_597_; 
if (v_isShared_595_ == 0)
{
v___x_597_ = v___x_594_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_a_592_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
v___jp_466_:
{
lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_467_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
v___x_468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_468_, 0, v___x_467_);
return v___x_468_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpEq___redArg___boxed(lean_object* v_e_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_){
_start:
{
lean_object* v_res_606_; 
v_res_606_ = l_Lean_Meta_Grind_simpEq___redArg(v_e_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_);
lean_dec(v_a_604_);
lean_dec_ref(v_a_603_);
lean_dec(v_a_602_);
lean_dec_ref(v_a_601_);
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpEq(lean_object* v_e_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = l_Lean_Meta_Grind_simpEq___redArg(v_e_607_, v_a_611_, v_a_612_, v_a_613_, v_a_614_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpEq___boxed(lean_object* v_e_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Lean_Meta_Grind_simpEq(v_e_617_, v_a_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_);
lean_dec(v_a_624_);
lean_dec_ref(v_a_623_);
lean_dec(v_a_622_);
lean_dec_ref(v_a_621_);
lean_dec(v_a_620_);
lean_dec_ref(v_a_619_);
lean_dec(v_a_618_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13_(){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_646_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13_));
v___x_647_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__4_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13_));
v___x_648_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpEq___boxed), 9, 0);
v___x_649_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_646_, v___x_647_, v___x_648_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13____boxed(lean_object* v_a_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13_();
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpDIte___redArg(lean_object* v_e_661_, lean_object* v_a_662_){
_start:
{
lean_object* v___x_667_; 
v___x_667_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_661_, v_a_662_);
if (lean_obj_tag(v___x_667_) == 0)
{
lean_object* v_a_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_723_; 
v_a_668_ = lean_ctor_get(v___x_667_, 0);
v_isSharedCheck_723_ = !lean_is_exclusive(v___x_667_);
if (v_isSharedCheck_723_ == 0)
{
v___x_670_ = v___x_667_;
v_isShared_671_ = v_isSharedCheck_723_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_a_668_);
lean_dec(v___x_667_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_723_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v___x_672_; uint8_t v___x_673_; 
v___x_672_ = l_Lean_Expr_cleanupAnnotations(v_a_668_);
lean_dec(v_a_668_);
v___x_673_ = l_Lean_Expr_isApp(v___x_672_);
if (v___x_673_ == 0)
{
lean_dec_ref(v___x_672_);
lean_del_object(v___x_670_);
goto v___jp_664_;
}
else
{
lean_object* v___x_674_; uint8_t v___x_675_; 
v___x_674_ = l_Lean_Expr_appFnCleanup___redArg(v___x_672_);
v___x_675_ = l_Lean_Expr_isApp(v___x_674_);
if (v___x_675_ == 0)
{
lean_dec_ref(v___x_674_);
lean_dec_ref(v___x_672_);
lean_del_object(v___x_670_);
goto v___jp_664_;
}
else
{
lean_object* v___x_676_; uint8_t v___x_677_; 
v___x_676_ = l_Lean_Expr_appFnCleanup___redArg(v___x_674_);
v___x_677_ = l_Lean_Expr_isApp(v___x_676_);
if (v___x_677_ == 0)
{
lean_dec_ref(v___x_676_);
lean_dec_ref(v___x_674_);
lean_dec_ref(v___x_672_);
lean_del_object(v___x_670_);
goto v___jp_664_;
}
else
{
lean_object* v___x_678_; uint8_t v___x_679_; 
v___x_678_ = l_Lean_Expr_appFnCleanup___redArg(v___x_676_);
v___x_679_ = l_Lean_Expr_isApp(v___x_678_);
if (v___x_679_ == 0)
{
lean_dec_ref(v___x_678_);
lean_dec_ref(v___x_676_);
lean_dec_ref(v___x_674_);
lean_dec_ref(v___x_672_);
lean_del_object(v___x_670_);
goto v___jp_664_;
}
else
{
lean_object* v___x_680_; uint8_t v___x_681_; 
v___x_680_ = l_Lean_Expr_appFnCleanup___redArg(v___x_678_);
v___x_681_ = l_Lean_Expr_isApp(v___x_680_);
if (v___x_681_ == 0)
{
lean_dec_ref(v___x_680_);
lean_dec_ref(v___x_678_);
lean_dec_ref(v___x_676_);
lean_dec_ref(v___x_674_);
lean_dec_ref(v___x_672_);
lean_del_object(v___x_670_);
goto v___jp_664_;
}
else
{
lean_object* v___x_682_; lean_object* v___x_683_; uint8_t v___x_684_; 
v___x_682_ = l_Lean_Expr_appFnCleanup___redArg(v___x_680_);
v___x_683_ = ((lean_object*)(l_Lean_Meta_Grind_simpDIte___redArg___closed__1));
v___x_684_ = l_Lean_Expr_isConstOf(v___x_682_, v___x_683_);
if (v___x_684_ == 0)
{
lean_dec_ref(v___x_682_);
lean_dec_ref(v___x_680_);
lean_dec_ref(v___x_678_);
lean_dec_ref(v___x_676_);
lean_dec_ref(v___x_674_);
lean_dec_ref(v___x_672_);
lean_del_object(v___x_670_);
goto v___jp_664_;
}
else
{
lean_object* v_arg_685_; 
v_arg_685_ = lean_ctor_get(v___x_674_, 1);
lean_inc_ref(v_arg_685_);
lean_dec_ref(v___x_674_);
if (lean_obj_tag(v_arg_685_) == 6)
{
lean_object* v_body_686_; uint8_t v___x_687_; 
v_body_686_ = lean_ctor_get(v_arg_685_, 2);
lean_inc_ref(v_body_686_);
lean_dec_ref_known(v_arg_685_, 3);
v___x_687_ = l_Lean_Expr_hasLooseBVars(v_body_686_);
if (v___x_687_ == 0)
{
lean_object* v_arg_688_; 
v_arg_688_ = lean_ctor_get(v___x_672_, 1);
lean_inc_ref(v_arg_688_);
lean_dec_ref(v___x_672_);
if (lean_obj_tag(v_arg_688_) == 6)
{
lean_object* v_body_689_; uint8_t v___x_690_; 
v_body_689_ = lean_ctor_get(v_arg_688_, 2);
lean_inc_ref(v_body_689_);
lean_dec_ref_known(v_arg_688_, 3);
v___x_690_ = l_Lean_Expr_hasLooseBVars(v_body_689_);
if (v___x_690_ == 0)
{
lean_object* v_arg_691_; lean_object* v_arg_692_; lean_object* v_arg_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_705_; 
v_arg_691_ = lean_ctor_get(v___x_676_, 1);
lean_inc_ref_n(v_arg_691_, 2);
lean_dec_ref(v___x_676_);
v_arg_692_ = lean_ctor_get(v___x_678_, 1);
lean_inc_ref_n(v_arg_692_, 2);
lean_dec_ref(v___x_678_);
v_arg_693_ = lean_ctor_get(v___x_680_, 1);
lean_inc_ref_n(v_arg_693_, 2);
lean_dec_ref(v___x_680_);
v___x_694_ = l_Lean_Expr_constLevels_x21(v___x_682_);
lean_dec_ref(v___x_682_);
v___x_695_ = ((lean_object*)(l_Lean_Meta_Grind_simpDIte___redArg___closed__3));
lean_inc(v___x_694_);
v___x_696_ = l_Lean_mkConst(v___x_695_, v___x_694_);
lean_inc_ref(v_body_689_);
lean_inc_ref(v_body_686_);
v___x_697_ = l_Lean_mkApp5(v___x_696_, v_arg_693_, v_arg_692_, v_arg_691_, v_body_686_, v_body_689_);
v___x_698_ = ((lean_object*)(l_Lean_Meta_Grind_simpDIte___redArg___closed__5));
v___x_699_ = l_Lean_mkConst(v___x_698_, v___x_694_);
v___x_700_ = l_Lean_mkApp5(v___x_699_, v_arg_692_, v_arg_693_, v_body_686_, v_body_689_, v_arg_691_);
v___x_701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_701_, 0, v___x_700_);
v___x_702_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_702_, 0, v___x_697_);
lean_ctor_set(v___x_702_, 1, v___x_701_);
lean_ctor_set_uint8(v___x_702_, sizeof(void*)*2, v___x_684_);
v___x_703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_703_, 0, v___x_702_);
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 0, v___x_703_);
v___x_705_ = v___x_670_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v___x_703_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
else
{
lean_object* v___x_707_; lean_object* v___x_709_; 
lean_dec_ref(v_body_689_);
lean_dec_ref(v_body_686_);
lean_dec_ref(v___x_682_);
lean_dec_ref(v___x_680_);
lean_dec_ref(v___x_678_);
lean_dec_ref(v___x_676_);
v___x_707_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 0, v___x_707_);
v___x_709_ = v___x_670_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v___x_707_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
else
{
lean_object* v___x_711_; lean_object* v___x_713_; 
lean_dec_ref(v_arg_688_);
lean_dec_ref(v_body_686_);
lean_dec_ref(v___x_682_);
lean_dec_ref(v___x_680_);
lean_dec_ref(v___x_678_);
lean_dec_ref(v___x_676_);
v___x_711_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 0, v___x_711_);
v___x_713_ = v___x_670_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v___x_711_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
else
{
lean_object* v___x_715_; lean_object* v___x_717_; 
lean_dec_ref(v_body_686_);
lean_dec_ref(v___x_682_);
lean_dec_ref(v___x_680_);
lean_dec_ref(v___x_678_);
lean_dec_ref(v___x_676_);
lean_dec_ref(v___x_672_);
v___x_715_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 0, v___x_715_);
v___x_717_ = v___x_670_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v___x_715_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
else
{
lean_object* v___x_719_; lean_object* v___x_721_; 
lean_dec_ref(v_arg_685_);
lean_dec_ref(v___x_682_);
lean_dec_ref(v___x_680_);
lean_dec_ref(v___x_678_);
lean_dec_ref(v___x_676_);
lean_dec_ref(v___x_672_);
v___x_719_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 0, v___x_719_);
v___x_721_ = v___x_670_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_719_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
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
lean_object* v_a_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_731_; 
v_a_724_ = lean_ctor_get(v___x_667_, 0);
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_667_);
if (v_isSharedCheck_731_ == 0)
{
v___x_726_ = v___x_667_;
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_a_724_);
lean_dec(v___x_667_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_729_; 
if (v_isShared_727_ == 0)
{
v___x_729_ = v___x_726_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_a_724_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
v___jp_664_:
{
lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_665_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
v___x_666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_666_, 0, v___x_665_);
return v___x_666_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpDIte___redArg___boxed(lean_object* v_e_732_, lean_object* v_a_733_, lean_object* v_a_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Lean_Meta_Grind_simpDIte___redArg(v_e_732_, v_a_733_);
lean_dec(v_a_733_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpDIte(lean_object* v_e_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_){
_start:
{
lean_object* v___x_745_; 
v___x_745_ = l_Lean_Meta_Grind_simpDIte___redArg(v_e_736_, v_a_741_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpDIte___boxed(lean_object* v_e_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l_Lean_Meta_Grind_simpDIte(v_e_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_);
lean_dec(v_a_753_);
lean_dec_ref(v_a_752_);
lean_dec(v_a_751_);
lean_dec_ref(v_a_750_);
lean_dec(v_a_749_);
lean_dec_ref(v_a_748_);
lean_dec(v_a_747_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_14_(){
_start:
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_776_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_14_));
v___x_777_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_14_));
v___x_778_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpDIte___boxed), 9, 0);
v___x_779_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_776_, v___x_777_, v___x_778_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_14____boxed(lean_object* v_a_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_14_();
return v_res_781_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__8(void){
_start:
{
lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_798_ = lean_box(0);
v___x_799_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__7));
v___x_800_ = l_Lean_mkConst(v___x_799_, v___x_798_);
return v___x_800_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__18(void){
_start:
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_817_ = lean_box(0);
v___x_818_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__17));
v___x_819_ = l_Lean_mkConst(v___x_818_, v___x_817_);
return v___x_819_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__21(void){
_start:
{
lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_824_ = lean_unsigned_to_nat(1u);
v___x_825_ = lean_nat_to_int(v___x_824_);
return v___x_825_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__22(void){
_start:
{
lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_826_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__21, &l_Lean_Meta_Grind_pushNot___redArg___closed__21_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__21);
v___x_827_ = l_Lean_mkIntLit(v___x_826_);
return v___x_827_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__23(void){
_start:
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_828_ = lean_box(0);
v___x_829_ = ((lean_object*)(l_Lean_Meta_Grind_registerNormTheorems___closed__4));
v___x_830_ = l_Lean_mkConst(v___x_829_, v___x_828_);
return v___x_830_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__24(void){
_start:
{
lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_831_ = lean_unsigned_to_nat(1u);
v___x_832_ = l_Lean_mkNatLit(v___x_831_);
return v___x_832_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__25(void){
_start:
{
lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_833_ = lean_box(0);
v___x_834_ = ((lean_object*)(l_Lean_Meta_Grind_registerNormTheorems___closed__2));
v___x_835_ = l_Lean_mkConst(v___x_834_, v___x_833_);
return v___x_835_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__26(void){
_start:
{
lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_836_ = lean_box(0);
v___x_837_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__30));
v___x_838_ = l_Lean_mkConst(v___x_837_, v___x_836_);
return v___x_838_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__29(void){
_start:
{
lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_843_ = lean_box(0);
v___x_844_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__28));
v___x_845_ = l_Lean_mkConst(v___x_844_, v___x_843_);
return v___x_845_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__32(void){
_start:
{
lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_850_ = lean_box(0);
v___x_851_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__31));
v___x_852_ = l_Lean_mkConst(v___x_851_, v___x_850_);
return v___x_852_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__35(void){
_start:
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_858_ = lean_box(0);
v___x_859_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__34));
v___x_860_ = l_Lean_mkConst(v___x_859_, v___x_858_);
return v___x_860_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__36(void){
_start:
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_861_ = lean_box(0);
v___x_862_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__10));
v___x_863_ = l_Lean_mkConst(v___x_862_, v___x_861_);
return v___x_863_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__39(void){
_start:
{
lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_869_ = lean_box(0);
v___x_870_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__38));
v___x_871_ = l_Lean_mkConst(v___x_870_, v___x_869_);
return v___x_871_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__40(void){
_start:
{
lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_872_ = lean_box(0);
v___x_873_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__12));
v___x_874_ = l_Lean_mkConst(v___x_873_, v___x_872_);
return v___x_874_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__43(void){
_start:
{
lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_880_ = lean_box(0);
v___x_881_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__42));
v___x_882_ = l_Lean_mkConst(v___x_881_, v___x_880_);
return v___x_882_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__46(void){
_start:
{
lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_886_ = lean_unsigned_to_nat(0u);
v___x_887_ = l_Lean_mkBVar(v___x_886_);
return v___x_887_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__51(void){
_start:
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_898_ = lean_box(0);
v___x_899_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__50));
v___x_900_ = l_Lean_mkConst(v___x_899_, v___x_898_);
return v___x_900_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__54(void){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_906_ = lean_box(0);
v___x_907_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__53));
v___x_908_ = l_Lean_mkConst(v___x_907_, v___x_906_);
return v___x_908_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__55(void){
_start:
{
lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_909_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__54, &l_Lean_Meta_Grind_pushNot___redArg___closed__54_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__54);
v___x_910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_910_, 0, v___x_909_);
return v___x_910_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__58(void){
_start:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_916_ = lean_box(0);
v___x_917_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__57));
v___x_918_ = l_Lean_mkConst(v___x_917_, v___x_916_);
return v___x_918_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__59(void){
_start:
{
lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_919_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__58, &l_Lean_Meta_Grind_pushNot___redArg___closed__58_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__58);
v___x_920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_920_, 0, v___x_919_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNot___redArg(lean_object* v_e_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_){
_start:
{
lean_object* v___x_930_; 
v___x_930_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_921_, v_a_923_);
if (lean_obj_tag(v___x_930_) == 0)
{
lean_object* v_a_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_1254_; 
v_a_931_ = lean_ctor_get(v___x_930_, 0);
v_isSharedCheck_1254_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_1254_ == 0)
{
v___x_933_ = v___x_930_;
v_isShared_934_ = v_isSharedCheck_1254_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_a_931_);
lean_dec(v___x_930_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_1254_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_935_; uint8_t v___x_936_; 
v___x_935_ = l_Lean_Expr_cleanupAnnotations(v_a_931_);
lean_dec(v_a_931_);
v___x_936_ = l_Lean_Expr_isApp(v___x_935_);
if (v___x_936_ == 0)
{
lean_dec_ref(v___x_935_);
lean_del_object(v___x_933_);
goto v___jp_927_;
}
else
{
lean_object* v___x_937_; lean_object* v___x_938_; uint8_t v___x_939_; lean_object* v___y_941_; lean_object* v___y_942_; lean_object* v___y_943_; lean_object* v___y_944_; lean_object* v___y_945_; lean_object* v___y_946_; lean_object* v___y_947_; uint8_t v___y_948_; 
v___x_937_ = l_Lean_Expr_appFnCleanup___redArg(v___x_935_);
v___x_938_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__1));
v___x_939_ = l_Lean_Expr_isConstOf(v___x_937_, v___x_938_);
lean_dec_ref(v___x_937_);
if (v___x_939_ == 0)
{
lean_dec_ref(v___x_935_);
lean_del_object(v___x_933_);
goto v___jp_927_;
}
else
{
lean_object* v_arg_980_; lean_object* v___y_982_; lean_object* v___y_983_; lean_object* v___y_984_; lean_object* v___y_985_; lean_object* v___x_1020_; 
v_arg_980_ = lean_ctor_get(v___x_935_, 1);
lean_inc_ref_n(v_arg_980_, 2);
lean_dec_ref(v___x_935_);
v___x_1020_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_980_, v_a_923_);
if (lean_obj_tag(v___x_1020_) == 0)
{
lean_object* v_a_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1245_; 
v_a_1021_ = lean_ctor_get(v___x_1020_, 0);
v_isSharedCheck_1245_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1023_ = v___x_1020_;
v_isShared_1024_ = v_isSharedCheck_1245_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_a_1021_);
lean_dec(v___x_1020_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1245_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; uint8_t v___x_1027_; 
v___x_1025_ = l_Lean_Expr_cleanupAnnotations(v_a_1021_);
lean_dec(v_a_1021_);
v___x_1026_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__13));
v___x_1027_ = l_Lean_Expr_isConstOf(v___x_1025_, v___x_1026_);
if (v___x_1027_ == 0)
{
lean_object* v___x_1028_; uint8_t v___x_1029_; 
v___x_1028_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__10));
v___x_1029_ = l_Lean_Expr_isConstOf(v___x_1025_, v___x_1028_);
if (v___x_1029_ == 0)
{
uint8_t v___x_1030_; 
v___x_1030_ = l_Lean_Expr_isApp(v___x_1025_);
if (v___x_1030_ == 0)
{
lean_dec_ref(v___x_1025_);
lean_del_object(v___x_1023_);
v___y_982_ = v_a_922_;
v___y_983_ = v_a_923_;
v___y_984_ = v_a_924_;
v___y_985_ = v_a_925_;
goto v___jp_981_;
}
else
{
lean_object* v_arg_1031_; lean_object* v___x_1032_; uint8_t v___x_1033_; 
v_arg_1031_ = lean_ctor_get(v___x_1025_, 1);
lean_inc_ref(v_arg_1031_);
v___x_1032_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1025_);
lean_dec_ref(v___x_1025_);
v___x_1033_ = l_Lean_Expr_isConstOf(v___x_1032_, v___x_938_);
if (v___x_1033_ == 0)
{
uint8_t v___x_1034_; 
v___x_1034_ = l_Lean_Expr_isApp(v___x_1032_);
if (v___x_1034_ == 0)
{
lean_dec_ref(v___x_1032_);
lean_dec_ref(v_arg_1031_);
lean_del_object(v___x_1023_);
v___y_982_ = v_a_922_;
v___y_983_ = v_a_923_;
v___y_984_ = v_a_924_;
v___y_985_ = v_a_925_;
goto v___jp_981_;
}
else
{
lean_object* v_arg_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; uint8_t v___x_1038_; 
v_arg_1035_ = lean_ctor_get(v___x_1032_, 1);
lean_inc_ref(v_arg_1035_);
v___x_1036_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1032_);
lean_dec_ref(v___x_1032_);
v___x_1037_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__3));
v___x_1038_ = l_Lean_Expr_isConstOf(v___x_1036_, v___x_1037_);
if (v___x_1038_ == 0)
{
lean_object* v___x_1039_; uint8_t v___x_1040_; 
v___x_1039_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__10));
v___x_1040_ = l_Lean_Expr_isConstOf(v___x_1036_, v___x_1039_);
if (v___x_1040_ == 0)
{
lean_object* v___x_1041_; uint8_t v___x_1042_; 
v___x_1041_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__12));
v___x_1042_ = l_Lean_Expr_isConstOf(v___x_1036_, v___x_1041_);
if (v___x_1042_ == 0)
{
uint8_t v___x_1043_; 
v___x_1043_ = l_Lean_Expr_isApp(v___x_1036_);
if (v___x_1043_ == 0)
{
lean_dec_ref(v___x_1036_);
lean_dec_ref(v_arg_1035_);
lean_dec_ref(v_arg_1031_);
lean_del_object(v___x_1023_);
v___y_982_ = v_a_922_;
v___y_983_ = v_a_923_;
v___y_984_ = v_a_924_;
v___y_985_ = v_a_925_;
goto v___jp_981_;
}
else
{
lean_object* v_arg_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; uint8_t v___x_1047_; 
v_arg_1044_ = lean_ctor_get(v___x_1036_, 1);
lean_inc_ref(v_arg_1044_);
v___x_1045_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1036_);
lean_dec_ref(v___x_1036_);
v___x_1046_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__2));
v___x_1047_ = l_Lean_Expr_isConstOf(v___x_1045_, v___x_1046_);
if (v___x_1047_ == 0)
{
uint8_t v___x_1048_; 
v___x_1048_ = l_Lean_Expr_isApp(v___x_1045_);
if (v___x_1048_ == 0)
{
lean_dec_ref(v___x_1045_);
lean_dec_ref(v_arg_1044_);
lean_dec_ref(v_arg_1035_);
lean_dec_ref(v_arg_1031_);
lean_del_object(v___x_1023_);
v___y_982_ = v_a_922_;
v___y_983_ = v_a_923_;
v___y_984_ = v_a_924_;
v___y_985_ = v_a_925_;
goto v___jp_981_;
}
else
{
lean_object* v_arg_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; uint8_t v___x_1052_; 
v_arg_1049_ = lean_ctor_get(v___x_1045_, 1);
lean_inc_ref(v_arg_1049_);
v___x_1050_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1045_);
lean_dec_ref(v___x_1045_);
v___x_1051_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__15));
v___x_1052_ = l_Lean_Expr_isConstOf(v___x_1050_, v___x_1051_);
if (v___x_1052_ == 0)
{
uint8_t v___x_1053_; 
v___x_1053_ = l_Lean_Expr_isApp(v___x_1050_);
if (v___x_1053_ == 0)
{
lean_dec_ref(v___x_1050_);
lean_dec_ref(v_arg_1049_);
lean_dec_ref(v_arg_1044_);
lean_dec_ref(v_arg_1035_);
lean_dec_ref(v_arg_1031_);
lean_del_object(v___x_1023_);
v___y_982_ = v_a_922_;
v___y_983_ = v_a_923_;
v___y_984_ = v_a_924_;
v___y_985_ = v_a_925_;
goto v___jp_981_;
}
else
{
lean_object* v___x_1054_; lean_object* v___x_1055_; uint8_t v___x_1056_; 
v___x_1054_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1050_);
v___x_1055_ = ((lean_object*)(l_Lean_Meta_Grind_simpDIte___redArg___closed__3));
v___x_1056_ = l_Lean_Expr_isConstOf(v___x_1054_, v___x_1055_);
if (v___x_1056_ == 0)
{
lean_dec_ref(v___x_1054_);
lean_dec_ref(v___x_1050_);
lean_dec_ref(v_arg_1049_);
lean_dec_ref(v_arg_1044_);
lean_dec_ref(v_arg_1035_);
lean_dec_ref(v_arg_1031_);
lean_del_object(v___x_1023_);
v___y_982_ = v_a_922_;
v___y_983_ = v_a_923_;
v___y_984_ = v_a_924_;
v___y_985_ = v_a_925_;
goto v___jp_981_;
}
else
{
lean_object* v_arg_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1067_; 
lean_dec_ref(v_arg_980_);
lean_del_object(v___x_933_);
v_arg_1057_ = lean_ctor_get(v___x_1050_, 1);
lean_inc_ref(v_arg_1057_);
lean_dec_ref(v___x_1050_);
lean_inc_ref(v_arg_1035_);
v___x_1058_ = l_Lean_mkNot(v_arg_1035_);
lean_inc_ref(v_arg_1031_);
v___x_1059_ = l_Lean_mkNot(v_arg_1031_);
lean_inc_ref(v_arg_1044_);
lean_inc_ref(v_arg_1049_);
v___x_1060_ = l_Lean_mkApp5(v___x_1054_, v_arg_1057_, v_arg_1049_, v_arg_1044_, v___x_1058_, v___x_1059_);
v___x_1061_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__18, &l_Lean_Meta_Grind_pushNot___redArg___closed__18_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__18);
v___x_1062_ = l_Lean_mkApp4(v___x_1061_, v_arg_1049_, v_arg_1044_, v_arg_1035_, v_arg_1031_);
v___x_1063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1062_);
v___x_1064_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1064_, 0, v___x_1060_);
lean_ctor_set(v___x_1064_, 1, v___x_1063_);
lean_ctor_set_uint8(v___x_1064_, sizeof(void*)*2, v___x_1056_);
v___x_1065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1064_);
if (v_isShared_1024_ == 0)
{
lean_ctor_set(v___x_1023_, 0, v___x_1065_);
v___x_1067_ = v___x_1023_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v___x_1065_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
}
else
{
lean_object* v___x_1069_; 
lean_dec_ref(v___x_1050_);
lean_dec_ref(v_arg_1044_);
lean_del_object(v___x_1023_);
lean_dec_ref(v_arg_980_);
lean_del_object(v___x_933_);
v___x_1069_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1049_, v_a_923_);
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_object* v_a_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1105_; 
v_a_1070_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1072_ = v___x_1069_;
v_isShared_1073_ = v_isSharedCheck_1105_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_a_1070_);
lean_dec(v___x_1069_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1105_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; uint8_t v___x_1076_; 
v___x_1074_ = l_Lean_Expr_cleanupAnnotations(v_a_1070_);
lean_dec(v_a_1070_);
v___x_1075_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__19));
v___x_1076_ = l_Lean_Expr_isConstOf(v___x_1074_, v___x_1075_);
if (v___x_1076_ == 0)
{
lean_object* v___x_1077_; uint8_t v___x_1078_; 
v___x_1077_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__20));
v___x_1078_ = l_Lean_Expr_isConstOf(v___x_1074_, v___x_1077_);
lean_dec_ref(v___x_1074_);
if (v___x_1078_ == 0)
{
lean_object* v___x_1079_; lean_object* v___x_1081_; 
lean_dec_ref(v_arg_1035_);
lean_dec_ref(v_arg_1031_);
v___x_1079_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 0, v___x_1079_);
v___x_1081_ = v___x_1072_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v___x_1079_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
else
{
lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1092_; 
v___x_1083_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__22, &l_Lean_Meta_Grind_pushNot___redArg___closed__22_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__22);
lean_inc_ref(v_arg_1031_);
v___x_1084_ = l_Lean_mkIntAdd(v_arg_1031_, v___x_1083_);
lean_inc_ref(v_arg_1035_);
v___x_1085_ = l_Lean_mkIntLE(v___x_1084_, v_arg_1035_);
v___x_1086_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__23, &l_Lean_Meta_Grind_pushNot___redArg___closed__23_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__23);
v___x_1087_ = l_Lean_mkAppB(v___x_1086_, v_arg_1035_, v_arg_1031_);
v___x_1088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1087_);
v___x_1089_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1089_, 0, v___x_1085_);
lean_ctor_set(v___x_1089_, 1, v___x_1088_);
lean_ctor_set_uint8(v___x_1089_, sizeof(void*)*2, v___x_1078_);
v___x_1090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1089_);
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 0, v___x_1090_);
v___x_1092_ = v___x_1072_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v___x_1090_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
else
{
lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1103_; 
lean_dec_ref(v___x_1074_);
v___x_1094_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__24, &l_Lean_Meta_Grind_pushNot___redArg___closed__24_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__24);
lean_inc_ref(v_arg_1031_);
v___x_1095_ = l_Lean_mkNatAdd(v_arg_1031_, v___x_1094_);
lean_inc_ref(v_arg_1035_);
v___x_1096_ = l_Lean_mkNatLE(v___x_1095_, v_arg_1035_);
v___x_1097_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__25, &l_Lean_Meta_Grind_pushNot___redArg___closed__25_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__25);
v___x_1098_ = l_Lean_mkAppB(v___x_1097_, v_arg_1035_, v_arg_1031_);
v___x_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1098_);
v___x_1100_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1100_, 0, v___x_1096_);
lean_ctor_set(v___x_1100_, 1, v___x_1099_);
lean_ctor_set_uint8(v___x_1100_, sizeof(void*)*2, v___x_1076_);
v___x_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1100_);
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 0, v___x_1101_);
v___x_1103_ = v___x_1072_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v___x_1101_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
}
}
else
{
lean_object* v_a_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1113_; 
lean_dec_ref(v_arg_1035_);
lean_dec_ref(v_arg_1031_);
v_a_1106_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1108_ = v___x_1069_;
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_a_1106_);
lean_dec(v___x_1069_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1111_; 
if (v_isShared_1109_ == 0)
{
v___x_1111_ = v___x_1108_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_a_1106_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
}
}
}
else
{
uint8_t v___x_1114_; 
lean_dec_ref(v_arg_980_);
lean_del_object(v___x_933_);
v___x_1114_ = l_Lean_Expr_isProp(v_arg_1044_);
if (v___x_1114_ == 0)
{
lean_object* v___x_1115_; 
lean_del_object(v___x_1023_);
v___x_1115_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1031_, v_a_923_);
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_object* v_a_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1149_; 
v_a_1116_ = lean_ctor_get(v___x_1115_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1118_ = v___x_1115_;
v_isShared_1119_ = v_isSharedCheck_1149_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_a_1116_);
lean_dec(v___x_1115_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1149_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; uint8_t v___x_1122_; 
v___x_1120_ = l_Lean_Expr_cleanupAnnotations(v_a_1116_);
lean_dec(v_a_1116_);
v___x_1121_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__30));
v___x_1122_ = l_Lean_Expr_isConstOf(v___x_1120_, v___x_1121_);
if (v___x_1122_ == 0)
{
lean_object* v___x_1123_; uint8_t v___x_1124_; 
v___x_1123_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__24));
v___x_1124_ = l_Lean_Expr_isConstOf(v___x_1120_, v___x_1123_);
lean_dec_ref(v___x_1120_);
if (v___x_1124_ == 0)
{
lean_object* v___x_1125_; lean_object* v___x_1127_; 
lean_dec_ref(v___x_1045_);
lean_dec_ref(v_arg_1044_);
lean_dec_ref(v_arg_1035_);
v___x_1125_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
if (v_isShared_1119_ == 0)
{
lean_ctor_set(v___x_1118_, 0, v___x_1125_);
v___x_1127_ = v___x_1118_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v___x_1125_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
else
{
lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1137_; 
v___x_1129_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__26, &l_Lean_Meta_Grind_pushNot___redArg___closed__26_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__26);
lean_inc_ref(v_arg_1035_);
v___x_1130_ = l_Lean_mkApp3(v___x_1045_, v_arg_1044_, v_arg_1035_, v___x_1129_);
v___x_1131_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__29, &l_Lean_Meta_Grind_pushNot___redArg___closed__29_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__29);
v___x_1132_ = l_Lean_Expr_app___override(v___x_1131_, v_arg_1035_);
v___x_1133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1132_);
v___x_1134_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1134_, 0, v___x_1130_);
lean_ctor_set(v___x_1134_, 1, v___x_1133_);
lean_ctor_set_uint8(v___x_1134_, sizeof(void*)*2, v___x_1047_);
v___x_1135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1134_);
if (v_isShared_1119_ == 0)
{
lean_ctor_set(v___x_1118_, 0, v___x_1135_);
v___x_1137_ = v___x_1118_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v___x_1135_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
}
else
{
lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1147_; 
lean_dec_ref(v___x_1120_);
v___x_1139_ = lean_obj_once(&l_Lean_Meta_Grind_simpEq___redArg___closed__25, &l_Lean_Meta_Grind_simpEq___redArg___closed__25_once, _init_l_Lean_Meta_Grind_simpEq___redArg___closed__25);
lean_inc_ref(v_arg_1035_);
v___x_1140_ = l_Lean_mkApp3(v___x_1045_, v_arg_1044_, v_arg_1035_, v___x_1139_);
v___x_1141_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__32, &l_Lean_Meta_Grind_pushNot___redArg___closed__32_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__32);
v___x_1142_ = l_Lean_Expr_app___override(v___x_1141_, v_arg_1035_);
v___x_1143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1142_);
v___x_1144_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1144_, 0, v___x_1140_);
lean_ctor_set(v___x_1144_, 1, v___x_1143_);
lean_ctor_set_uint8(v___x_1144_, sizeof(void*)*2, v___x_1047_);
v___x_1145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1144_);
if (v_isShared_1119_ == 0)
{
lean_ctor_set(v___x_1118_, 0, v___x_1145_);
v___x_1147_ = v___x_1118_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v___x_1145_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
}
else
{
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1157_; 
lean_dec_ref(v___x_1045_);
lean_dec_ref(v_arg_1044_);
lean_dec_ref(v_arg_1035_);
v_a_1150_ = lean_ctor_get(v___x_1115_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1152_ = v___x_1115_;
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1115_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1155_; 
if (v_isShared_1153_ == 0)
{
v___x_1155_ = v___x_1152_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_a_1150_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
else
{
lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1166_; 
lean_inc_ref(v_arg_1031_);
v___x_1158_ = l_Lean_mkNot(v_arg_1031_);
lean_inc_ref(v_arg_1035_);
v___x_1159_ = l_Lean_mkApp3(v___x_1045_, v_arg_1044_, v_arg_1035_, v___x_1158_);
v___x_1160_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__35, &l_Lean_Meta_Grind_pushNot___redArg___closed__35_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__35);
v___x_1161_ = l_Lean_mkAppB(v___x_1160_, v_arg_1035_, v_arg_1031_);
v___x_1162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1161_);
v___x_1163_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1163_, 0, v___x_1159_);
lean_ctor_set(v___x_1163_, 1, v___x_1162_);
lean_ctor_set_uint8(v___x_1163_, sizeof(void*)*2, v___x_1047_);
v___x_1164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1163_);
if (v_isShared_1024_ == 0)
{
lean_ctor_set(v___x_1023_, 0, v___x_1164_);
v___x_1166_ = v___x_1023_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v___x_1164_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
}
}
}
else
{
lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1178_; 
lean_dec_ref(v___x_1036_);
lean_dec_ref(v_arg_980_);
lean_del_object(v___x_933_);
v___x_1168_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__36, &l_Lean_Meta_Grind_pushNot___redArg___closed__36_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__36);
lean_inc_ref(v_arg_1035_);
v___x_1169_ = l_Lean_mkNot(v_arg_1035_);
lean_inc_ref(v_arg_1031_);
v___x_1170_ = l_Lean_mkNot(v_arg_1031_);
v___x_1171_ = l_Lean_mkAppB(v___x_1168_, v___x_1169_, v___x_1170_);
v___x_1172_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__39, &l_Lean_Meta_Grind_pushNot___redArg___closed__39_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__39);
v___x_1173_ = l_Lean_mkAppB(v___x_1172_, v_arg_1035_, v_arg_1031_);
v___x_1174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1173_);
v___x_1175_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1175_, 0, v___x_1171_);
lean_ctor_set(v___x_1175_, 1, v___x_1174_);
lean_ctor_set_uint8(v___x_1175_, sizeof(void*)*2, v___x_1042_);
v___x_1176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1175_);
if (v_isShared_1024_ == 0)
{
lean_ctor_set(v___x_1023_, 0, v___x_1176_);
v___x_1178_ = v___x_1023_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v___x_1176_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
else
{
lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1190_; 
lean_dec_ref(v___x_1036_);
lean_dec_ref(v_arg_980_);
lean_del_object(v___x_933_);
v___x_1180_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__40, &l_Lean_Meta_Grind_pushNot___redArg___closed__40_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__40);
lean_inc_ref(v_arg_1035_);
v___x_1181_ = l_Lean_mkNot(v_arg_1035_);
lean_inc_ref(v_arg_1031_);
v___x_1182_ = l_Lean_mkNot(v_arg_1031_);
v___x_1183_ = l_Lean_mkAppB(v___x_1180_, v___x_1181_, v___x_1182_);
v___x_1184_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__43, &l_Lean_Meta_Grind_pushNot___redArg___closed__43_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__43);
v___x_1185_ = l_Lean_mkAppB(v___x_1184_, v_arg_1035_, v_arg_1031_);
v___x_1186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1186_, 0, v___x_1185_);
v___x_1187_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1187_, 0, v___x_1183_);
lean_ctor_set(v___x_1187_, 1, v___x_1186_);
lean_ctor_set_uint8(v___x_1187_, sizeof(void*)*2, v___x_1040_);
v___x_1188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1187_);
if (v_isShared_1024_ == 0)
{
lean_ctor_set(v___x_1023_, 0, v___x_1188_);
v___x_1190_ = v___x_1023_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v___x_1188_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
}
else
{
lean_object* v___x_1192_; uint8_t v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
lean_dec_ref(v___x_1036_);
lean_del_object(v___x_1023_);
lean_dec_ref(v_arg_980_);
lean_del_object(v___x_933_);
v___x_1192_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__45));
v___x_1193_ = 0;
v___x_1194_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__46, &l_Lean_Meta_Grind_pushNot___redArg___closed__46_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__46);
lean_inc_ref(v_arg_1031_);
v___x_1195_ = l_Lean_Expr_app___override(v_arg_1031_, v___x_1194_);
v___x_1196_ = l_Lean_mkNot(v___x_1195_);
lean_inc_ref_n(v_arg_1035_, 2);
v___x_1197_ = l_Lean_mkForall(v___x_1192_, v___x_1193_, v_arg_1035_, v___x_1196_);
v___x_1198_ = l_Lean_Meta_getLevel(v_arg_1035_, v_a_922_, v_a_923_, v_a_924_, v_a_925_);
if (lean_obj_tag(v___x_1198_) == 0)
{
lean_object* v_a_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1214_; 
v_a_1199_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1201_ = v___x_1198_;
v_isShared_1202_ = v_isSharedCheck_1214_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_a_1199_);
lean_dec(v___x_1198_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1214_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1212_; 
v___x_1203_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__48));
v___x_1204_ = lean_box(0);
v___x_1205_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1205_, 0, v_a_1199_);
lean_ctor_set(v___x_1205_, 1, v___x_1204_);
v___x_1206_ = l_Lean_mkConst(v___x_1203_, v___x_1205_);
v___x_1207_ = l_Lean_mkAppB(v___x_1206_, v_arg_1035_, v_arg_1031_);
v___x_1208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1207_);
v___x_1209_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1209_, 0, v___x_1197_);
lean_ctor_set(v___x_1209_, 1, v___x_1208_);
lean_ctor_set_uint8(v___x_1209_, sizeof(void*)*2, v___x_1038_);
v___x_1210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1210_, 0, v___x_1209_);
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 0, v___x_1210_);
v___x_1212_ = v___x_1201_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v___x_1210_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
else
{
lean_object* v_a_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1222_; 
lean_dec_ref(v___x_1197_);
lean_dec_ref(v_arg_1035_);
lean_dec_ref(v_arg_1031_);
v_a_1215_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1217_ = v___x_1198_;
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_a_1215_);
lean_dec(v___x_1198_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1220_; 
if (v_isShared_1218_ == 0)
{
v___x_1220_ = v___x_1217_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_a_1215_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
return v___x_1220_;
}
}
}
}
}
}
else
{
lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1229_; 
lean_dec_ref(v___x_1032_);
lean_dec_ref(v_arg_980_);
lean_del_object(v___x_933_);
v___x_1223_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__51, &l_Lean_Meta_Grind_pushNot___redArg___closed__51_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__51);
lean_inc_ref(v_arg_1031_);
v___x_1224_ = l_Lean_Expr_app___override(v___x_1223_, v_arg_1031_);
v___x_1225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1224_);
v___x_1226_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1226_, 0, v_arg_1031_);
lean_ctor_set(v___x_1226_, 1, v___x_1225_);
lean_ctor_set_uint8(v___x_1226_, sizeof(void*)*2, v___x_1033_);
v___x_1227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1226_);
if (v_isShared_1024_ == 0)
{
lean_ctor_set(v___x_1023_, 0, v___x_1227_);
v___x_1229_ = v___x_1023_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v___x_1227_);
v___x_1229_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
return v___x_1229_;
}
}
}
}
else
{
lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1236_; 
lean_dec_ref(v___x_1025_);
lean_dec_ref(v_arg_980_);
lean_del_object(v___x_933_);
v___x_1231_ = lean_obj_once(&l_Lean_Meta_Grind_simpEq___redArg___closed__14, &l_Lean_Meta_Grind_simpEq___redArg___closed__14_once, _init_l_Lean_Meta_Grind_simpEq___redArg___closed__14);
v___x_1232_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__55, &l_Lean_Meta_Grind_pushNot___redArg___closed__55_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__55);
v___x_1233_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1233_, 0, v___x_1231_);
lean_ctor_set(v___x_1233_, 1, v___x_1232_);
lean_ctor_set_uint8(v___x_1233_, sizeof(void*)*2, v___x_1029_);
v___x_1234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1234_, 0, v___x_1233_);
if (v_isShared_1024_ == 0)
{
lean_ctor_set(v___x_1023_, 0, v___x_1234_);
v___x_1236_ = v___x_1023_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v___x_1234_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
return v___x_1236_;
}
}
}
else
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1243_; 
lean_dec_ref(v___x_1025_);
lean_dec_ref(v_arg_980_);
lean_del_object(v___x_933_);
v___x_1238_ = lean_obj_once(&l_Lean_Meta_Grind_simpEq___redArg___closed__11, &l_Lean_Meta_Grind_simpEq___redArg___closed__11_once, _init_l_Lean_Meta_Grind_simpEq___redArg___closed__11);
v___x_1239_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__59, &l_Lean_Meta_Grind_pushNot___redArg___closed__59_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__59);
v___x_1240_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1240_, 0, v___x_1238_);
lean_ctor_set(v___x_1240_, 1, v___x_1239_);
lean_ctor_set_uint8(v___x_1240_, sizeof(void*)*2, v___x_1027_);
v___x_1241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1240_);
if (v_isShared_1024_ == 0)
{
lean_ctor_set(v___x_1023_, 0, v___x_1241_);
v___x_1243_ = v___x_1023_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v___x_1241_);
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
else
{
lean_object* v_a_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1253_; 
lean_dec_ref(v_arg_980_);
lean_del_object(v___x_933_);
v_a_1246_ = lean_ctor_get(v___x_1020_, 0);
v_isSharedCheck_1253_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1248_ = v___x_1020_;
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_a_1246_);
lean_dec(v___x_1020_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1251_; 
if (v_isShared_1249_ == 0)
{
v___x_1251_ = v___x_1248_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v_a_1246_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
return v___x_1251_;
}
}
}
v___jp_981_:
{
if (lean_obj_tag(v_arg_980_) == 7)
{
lean_object* v_binderName_986_; lean_object* v_binderType_987_; lean_object* v_body_988_; uint8_t v_binderInfo_989_; lean_object* v___x_990_; 
lean_del_object(v___x_933_);
v_binderName_986_ = lean_ctor_get(v_arg_980_, 0);
lean_inc(v_binderName_986_);
v_binderType_987_ = lean_ctor_get(v_arg_980_, 1);
lean_inc_ref_n(v_binderType_987_, 2);
v_body_988_ = lean_ctor_get(v_arg_980_, 2);
lean_inc_ref(v_body_988_);
v_binderInfo_989_ = lean_ctor_get_uint8(v_arg_980_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_arg_980_, 3);
v___x_990_ = l_Lean_Meta_isProp(v_binderType_987_, v___y_982_, v___y_983_, v___y_984_, v___y_985_);
if (lean_obj_tag(v___x_990_) == 0)
{
lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_1007_; 
v_a_991_ = lean_ctor_get(v___x_990_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_993_ = v___x_990_;
v_isShared_994_ = v_isSharedCheck_1007_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___x_990_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_1007_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
uint8_t v___x_995_; 
v___x_995_ = l_Lean_Expr_hasLooseBVars(v_body_988_);
if (v___x_995_ == 0)
{
uint8_t v___x_996_; 
v___x_996_ = lean_unbox(v_a_991_);
lean_dec(v_a_991_);
if (v___x_996_ == 0)
{
lean_del_object(v___x_993_);
v___y_941_ = v___y_982_;
v___y_942_ = v_body_988_;
v___y_943_ = v___y_985_;
v___y_944_ = v___y_983_;
v___y_945_ = v___y_984_;
v___y_946_ = v_binderType_987_;
v___y_947_ = v_binderName_986_;
v___y_948_ = v_binderInfo_989_;
goto v___jp_940_;
}
else
{
lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1005_; 
lean_dec(v_binderName_986_);
lean_inc_ref(v_body_988_);
v___x_997_ = l_Lean_mkNot(v_body_988_);
lean_inc_ref(v_binderType_987_);
v___x_998_ = l_Lean_mkAnd(v_binderType_987_, v___x_997_);
v___x_999_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__8, &l_Lean_Meta_Grind_pushNot___redArg___closed__8_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__8);
v___x_1000_ = l_Lean_mkAppB(v___x_999_, v_binderType_987_, v_body_988_);
v___x_1001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1001_, 0, v___x_1000_);
v___x_1002_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1002_, 0, v___x_998_);
lean_ctor_set(v___x_1002_, 1, v___x_1001_);
lean_ctor_set_uint8(v___x_1002_, sizeof(void*)*2, v___x_939_);
v___x_1003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1002_);
if (v_isShared_994_ == 0)
{
lean_ctor_set(v___x_993_, 0, v___x_1003_);
v___x_1005_ = v___x_993_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v___x_1003_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
else
{
lean_del_object(v___x_993_);
lean_dec(v_a_991_);
v___y_941_ = v___y_982_;
v___y_942_ = v_body_988_;
v___y_943_ = v___y_985_;
v___y_944_ = v___y_983_;
v___y_945_ = v___y_984_;
v___y_946_ = v_binderType_987_;
v___y_947_ = v_binderName_986_;
v___y_948_ = v_binderInfo_989_;
goto v___jp_940_;
}
}
}
else
{
lean_object* v_a_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1015_; 
lean_dec_ref(v_body_988_);
lean_dec_ref(v_binderType_987_);
lean_dec(v_binderName_986_);
v_a_1008_ = lean_ctor_get(v___x_990_, 0);
v_isSharedCheck_1015_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_1010_ = v___x_990_;
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_a_1008_);
lean_dec(v___x_990_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v___x_1013_; 
if (v_isShared_1011_ == 0)
{
v___x_1013_ = v___x_1010_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_a_1008_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
}
}
else
{
lean_object* v___x_1016_; lean_object* v___x_1018_; 
lean_dec_ref(v_arg_980_);
v___x_1016_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 0, v___x_1016_);
v___x_1018_ = v___x_933_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v___x_1016_);
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
v___jp_940_:
{
lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
lean_inc_ref(v___y_942_);
lean_inc_ref_n(v___y_946_, 3);
lean_inc(v___y_947_);
v___x_949_ = l_Lean_mkLambda(v___y_947_, v___y_948_, v___y_946_, v___y_942_);
v___x_950_ = l_Lean_mkNot(v___y_942_);
v___x_951_ = l_Lean_mkLambda(v___y_947_, v___y_948_, v___y_946_, v___x_950_);
v___x_952_ = l_Lean_Meta_getLevel(v___y_946_, v___y_941_, v___y_944_, v___y_945_, v___y_943_);
if (lean_obj_tag(v___x_952_) == 0)
{
lean_object* v_a_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_971_; 
v_a_953_ = lean_ctor_get(v___x_952_, 0);
v_isSharedCheck_971_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_971_ == 0)
{
v___x_955_ = v___x_952_;
v_isShared_956_ = v_isSharedCheck_971_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_a_953_);
lean_dec(v___x_952_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_971_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_969_; 
v___x_957_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__3));
v___x_958_ = lean_box(0);
v___x_959_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_959_, 0, v_a_953_);
lean_ctor_set(v___x_959_, 1, v___x_958_);
lean_inc_ref(v___x_959_);
v___x_960_ = l_Lean_mkConst(v___x_957_, v___x_959_);
lean_inc_ref(v___y_946_);
v___x_961_ = l_Lean_mkAppB(v___x_960_, v___y_946_, v___x_951_);
v___x_962_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__5));
v___x_963_ = l_Lean_mkConst(v___x_962_, v___x_959_);
v___x_964_ = l_Lean_mkAppB(v___x_963_, v___y_946_, v___x_949_);
v___x_965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_965_, 0, v___x_964_);
v___x_966_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_966_, 0, v___x_961_);
lean_ctor_set(v___x_966_, 1, v___x_965_);
lean_ctor_set_uint8(v___x_966_, sizeof(void*)*2, v___x_939_);
v___x_967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_967_, 0, v___x_966_);
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 0, v___x_967_);
v___x_969_ = v___x_955_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v___x_967_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
}
}
}
else
{
lean_object* v_a_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_979_; 
lean_dec_ref(v___x_951_);
lean_dec_ref(v___x_949_);
lean_dec_ref(v___y_946_);
v_a_972_ = lean_ctor_get(v___x_952_, 0);
v_isSharedCheck_979_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_979_ == 0)
{
v___x_974_ = v___x_952_;
v_isShared_975_ = v_isSharedCheck_979_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_a_972_);
lean_dec(v___x_952_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_979_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v___x_977_; 
if (v_isShared_975_ == 0)
{
v___x_977_ = v___x_974_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v_a_972_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1262_; 
v_a_1255_ = lean_ctor_get(v___x_930_, 0);
v_isSharedCheck_1262_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_1262_ == 0)
{
v___x_1257_ = v___x_930_;
v_isShared_1258_ = v_isSharedCheck_1262_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_a_1255_);
lean_dec(v___x_930_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1262_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1260_; 
if (v_isShared_1258_ == 0)
{
v___x_1260_ = v___x_1257_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v_a_1255_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
return v___x_1260_;
}
}
}
v___jp_927_:
{
lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_928_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
v___x_929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_929_, 0, v___x_928_);
return v___x_929_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNot___redArg___boxed(lean_object* v_e_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_){
_start:
{
lean_object* v_res_1269_; 
v_res_1269_ = l_Lean_Meta_Grind_pushNot___redArg(v_e_1263_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_);
lean_dec(v_a_1267_);
lean_dec_ref(v_a_1266_);
lean_dec(v_a_1265_);
lean_dec_ref(v_a_1264_);
return v_res_1269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNot(lean_object* v_e_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_){
_start:
{
lean_object* v___x_1279_; 
v___x_1279_ = l_Lean_Meta_Grind_pushNot___redArg(v_e_1270_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNot___boxed(lean_object* v_e_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_){
_start:
{
lean_object* v_res_1289_; 
v_res_1289_ = l_Lean_Meta_Grind_pushNot(v_e_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_);
lean_dec(v_a_1287_);
lean_dec_ref(v_a_1286_);
lean_dec(v_a_1285_);
lean_dec_ref(v_a_1284_);
lean_dec(v_a_1283_);
lean_dec_ref(v_a_1282_);
lean_dec(v_a_1281_);
return v_res_1289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2942474041____hygCtx___hyg_11_(){
_start:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1306_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2942474041____hygCtx___hyg_11_));
v___x_1307_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2942474041____hygCtx___hyg_11_));
v___x_1308_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_pushNot___boxed), 9, 0);
v___x_1309_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_1306_, v___x_1307_, v___x_1308_);
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2942474041____hygCtx___hyg_11____boxed(lean_object* v_a_1310_){
_start:
{
lean_object* v_res_1311_; 
v_res_1311_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2942474041____hygCtx___hyg_11_();
return v_res_1311_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpOr___redArg___closed__2(void){
_start:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1317_ = lean_box(0);
v___x_1318_ = ((lean_object*)(l_Lean_Meta_Grind_simpOr___redArg___closed__1));
v___x_1319_ = l_Lean_mkConst(v___x_1318_, v___x_1317_);
return v___x_1319_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpOr___redArg___closed__5(void){
_start:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; 
v___x_1325_ = lean_box(0);
v___x_1326_ = ((lean_object*)(l_Lean_Meta_Grind_simpOr___redArg___closed__4));
v___x_1327_ = l_Lean_mkConst(v___x_1326_, v___x_1325_);
return v___x_1327_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpOr___redArg___closed__8(void){
_start:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1331_ = lean_box(0);
v___x_1332_ = ((lean_object*)(l_Lean_Meta_Grind_simpOr___redArg___closed__7));
v___x_1333_ = l_Lean_mkConst(v___x_1332_, v___x_1331_);
return v___x_1333_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpOr___redArg___closed__11(void){
_start:
{
lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; 
v___x_1337_ = lean_box(0);
v___x_1338_ = ((lean_object*)(l_Lean_Meta_Grind_simpOr___redArg___closed__10));
v___x_1339_ = l_Lean_mkConst(v___x_1338_, v___x_1337_);
return v___x_1339_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpOr___redArg___closed__14(void){
_start:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; 
v___x_1345_ = lean_box(0);
v___x_1346_ = ((lean_object*)(l_Lean_Meta_Grind_simpOr___redArg___closed__13));
v___x_1347_ = l_Lean_mkConst(v___x_1346_, v___x_1345_);
return v___x_1347_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpOr___redArg___closed__17(void){
_start:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; 
v___x_1351_ = lean_box(0);
v___x_1352_ = ((lean_object*)(l_Lean_Meta_Grind_simpOr___redArg___closed__16));
v___x_1353_ = l_Lean_mkConst(v___x_1352_, v___x_1351_);
return v___x_1353_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpOr___redArg___closed__20(void){
_start:
{
lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1357_ = lean_box(0);
v___x_1358_ = ((lean_object*)(l_Lean_Meta_Grind_simpOr___redArg___closed__19));
v___x_1359_ = l_Lean_mkConst(v___x_1358_, v___x_1357_);
return v___x_1359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpOr___redArg(lean_object* v_e_1360_, lean_object* v_a_1361_){
_start:
{
lean_object* v___x_1369_; 
v___x_1369_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1360_, v_a_1361_);
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_object* v_a_1370_; lean_object* v___x_1371_; uint8_t v___x_1372_; 
v_a_1370_ = lean_ctor_get(v___x_1369_, 0);
lean_inc(v_a_1370_);
lean_dec_ref_known(v___x_1369_, 1);
v___x_1371_ = l_Lean_Expr_cleanupAnnotations(v_a_1370_);
lean_dec(v_a_1370_);
v___x_1372_ = l_Lean_Expr_isApp(v___x_1371_);
if (v___x_1372_ == 0)
{
lean_dec_ref(v___x_1371_);
goto v___jp_1366_;
}
else
{
lean_object* v___x_1373_; uint8_t v___x_1374_; 
v___x_1373_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1371_);
v___x_1374_ = l_Lean_Expr_isApp(v___x_1373_);
if (v___x_1374_ == 0)
{
lean_dec_ref(v___x_1373_);
lean_dec_ref(v___x_1371_);
goto v___jp_1366_;
}
else
{
lean_object* v___x_1375_; lean_object* v___x_1376_; uint8_t v___x_1377_; 
v___x_1375_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1373_);
v___x_1376_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__10));
v___x_1377_ = l_Lean_Expr_isConstOf(v___x_1375_, v___x_1376_);
lean_dec_ref(v___x_1375_);
if (v___x_1377_ == 0)
{
lean_dec_ref(v___x_1373_);
lean_dec_ref(v___x_1371_);
goto v___jp_1366_;
}
else
{
lean_object* v_arg_1378_; lean_object* v_arg_1379_; lean_object* v___y_1381_; lean_object* v___x_1455_; 
v_arg_1378_ = lean_ctor_get(v___x_1371_, 1);
lean_inc_ref(v_arg_1378_);
lean_dec_ref(v___x_1371_);
v_arg_1379_ = lean_ctor_get(v___x_1373_, 1);
lean_inc_ref_n(v_arg_1379_, 2);
lean_dec_ref(v___x_1373_);
v___x_1455_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1379_, v_a_1361_);
if (lean_obj_tag(v___x_1455_) == 0)
{
lean_object* v_a_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1498_; 
v_a_1456_ = lean_ctor_get(v___x_1455_, 0);
v_isSharedCheck_1498_ = !lean_is_exclusive(v___x_1455_);
if (v_isSharedCheck_1498_ == 0)
{
v___x_1458_ = v___x_1455_;
v_isShared_1459_ = v_isSharedCheck_1498_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_a_1456_);
lean_dec(v___x_1455_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1498_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v___x_1460_; lean_object* v___x_1461_; uint8_t v___x_1462_; 
v___x_1460_ = l_Lean_Expr_cleanupAnnotations(v_a_1456_);
lean_dec(v_a_1456_);
v___x_1461_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__13));
v___x_1462_ = l_Lean_Expr_isConstOf(v___x_1460_, v___x_1461_);
if (v___x_1462_ == 0)
{
lean_object* v___x_1463_; uint8_t v___x_1464_; 
v___x_1463_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__10));
v___x_1464_ = l_Lean_Expr_isConstOf(v___x_1460_, v___x_1463_);
if (v___x_1464_ == 0)
{
uint8_t v___x_1465_; 
v___x_1465_ = l_Lean_Expr_isApp(v___x_1460_);
if (v___x_1465_ == 0)
{
lean_dec_ref(v___x_1460_);
lean_del_object(v___x_1458_);
v___y_1381_ = v_a_1361_;
goto v___jp_1380_;
}
else
{
lean_object* v___x_1466_; uint8_t v___x_1467_; 
v___x_1466_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1460_);
v___x_1467_ = l_Lean_Expr_isApp(v___x_1466_);
if (v___x_1467_ == 0)
{
lean_dec_ref(v___x_1466_);
lean_dec_ref(v___x_1460_);
lean_del_object(v___x_1458_);
v___y_1381_ = v_a_1361_;
goto v___jp_1380_;
}
else
{
lean_object* v___x_1468_; uint8_t v___x_1469_; 
v___x_1468_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1466_);
v___x_1469_ = l_Lean_Expr_isConstOf(v___x_1468_, v___x_1376_);
lean_dec_ref(v___x_1468_);
if (v___x_1469_ == 0)
{
lean_dec_ref(v___x_1466_);
lean_dec_ref(v___x_1460_);
lean_del_object(v___x_1458_);
v___y_1381_ = v_a_1361_;
goto v___jp_1380_;
}
else
{
lean_object* v_arg_1470_; lean_object* v_arg_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1480_; 
lean_dec_ref(v_arg_1379_);
v_arg_1470_ = lean_ctor_get(v___x_1460_, 1);
lean_inc_ref_n(v_arg_1470_, 2);
lean_dec_ref(v___x_1460_);
v_arg_1471_ = lean_ctor_get(v___x_1466_, 1);
lean_inc_ref_n(v_arg_1471_, 2);
lean_dec_ref(v___x_1466_);
lean_inc_ref(v_arg_1378_);
v___x_1472_ = l_Lean_mkOr(v_arg_1470_, v_arg_1378_);
v___x_1473_ = l_Lean_mkOr(v_arg_1471_, v___x_1472_);
v___x_1474_ = lean_obj_once(&l_Lean_Meta_Grind_simpOr___redArg___closed__14, &l_Lean_Meta_Grind_simpOr___redArg___closed__14_once, _init_l_Lean_Meta_Grind_simpOr___redArg___closed__14);
v___x_1475_ = l_Lean_mkApp3(v___x_1474_, v_arg_1471_, v_arg_1470_, v_arg_1378_);
v___x_1476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1476_, 0, v___x_1475_);
v___x_1477_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1477_, 0, v___x_1473_);
lean_ctor_set(v___x_1477_, 1, v___x_1476_);
lean_ctor_set_uint8(v___x_1477_, sizeof(void*)*2, v___x_1469_);
v___x_1478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1478_, 0, v___x_1477_);
if (v_isShared_1459_ == 0)
{
lean_ctor_set(v___x_1458_, 0, v___x_1478_);
v___x_1480_ = v___x_1458_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v___x_1478_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
}
}
}
else
{
lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1488_; 
lean_dec_ref(v___x_1460_);
v___x_1482_ = lean_obj_once(&l_Lean_Meta_Grind_simpOr___redArg___closed__17, &l_Lean_Meta_Grind_simpOr___redArg___closed__17_once, _init_l_Lean_Meta_Grind_simpOr___redArg___closed__17);
v___x_1483_ = l_Lean_Expr_app___override(v___x_1482_, v_arg_1378_);
v___x_1484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1483_);
v___x_1485_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1485_, 0, v_arg_1379_);
lean_ctor_set(v___x_1485_, 1, v___x_1484_);
lean_ctor_set_uint8(v___x_1485_, sizeof(void*)*2, v___x_1464_);
v___x_1486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1485_);
if (v_isShared_1459_ == 0)
{
lean_ctor_set(v___x_1458_, 0, v___x_1486_);
v___x_1488_ = v___x_1458_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v___x_1486_);
v___x_1488_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
return v___x_1488_;
}
}
}
else
{
lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1496_; 
lean_dec_ref(v___x_1460_);
lean_dec_ref(v_arg_1379_);
v___x_1490_ = lean_obj_once(&l_Lean_Meta_Grind_simpOr___redArg___closed__20, &l_Lean_Meta_Grind_simpOr___redArg___closed__20_once, _init_l_Lean_Meta_Grind_simpOr___redArg___closed__20);
lean_inc_ref(v_arg_1378_);
v___x_1491_ = l_Lean_Expr_app___override(v___x_1490_, v_arg_1378_);
v___x_1492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1492_, 0, v___x_1491_);
v___x_1493_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1493_, 0, v_arg_1378_);
lean_ctor_set(v___x_1493_, 1, v___x_1492_);
lean_ctor_set_uint8(v___x_1493_, sizeof(void*)*2, v___x_1462_);
v___x_1494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1494_, 0, v___x_1493_);
if (v_isShared_1459_ == 0)
{
lean_ctor_set(v___x_1458_, 0, v___x_1494_);
v___x_1496_ = v___x_1458_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v___x_1494_);
v___x_1496_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
return v___x_1496_;
}
}
}
}
else
{
lean_object* v_a_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1506_; 
lean_dec_ref(v_arg_1379_);
lean_dec_ref(v_arg_1378_);
v_a_1499_ = lean_ctor_get(v___x_1455_, 0);
v_isSharedCheck_1506_ = !lean_is_exclusive(v___x_1455_);
if (v_isSharedCheck_1506_ == 0)
{
v___x_1501_ = v___x_1455_;
v_isShared_1502_ = v_isSharedCheck_1506_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_a_1499_);
lean_dec(v___x_1455_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1506_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v___x_1504_; 
if (v_isShared_1502_ == 0)
{
v___x_1504_ = v___x_1501_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v_a_1499_);
v___x_1504_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
return v___x_1504_;
}
}
}
v___jp_1380_:
{
lean_object* v___x_1382_; 
lean_inc_ref(v_arg_1378_);
v___x_1382_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1378_, v___y_1381_);
if (lean_obj_tag(v___x_1382_) == 0)
{
lean_object* v_a_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1446_; 
v_a_1383_ = lean_ctor_get(v___x_1382_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1385_ = v___x_1382_;
v_isShared_1386_ = v_isSharedCheck_1446_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_a_1383_);
lean_dec(v___x_1382_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1446_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v___x_1387_; lean_object* v___x_1388_; uint8_t v___x_1389_; 
v___x_1387_ = l_Lean_Expr_cleanupAnnotations(v_a_1383_);
lean_dec(v_a_1383_);
v___x_1388_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__13));
v___x_1389_ = l_Lean_Expr_isConstOf(v___x_1387_, v___x_1388_);
if (v___x_1389_ == 0)
{
lean_object* v___x_1390_; uint8_t v___x_1391_; 
v___x_1390_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__10));
v___x_1391_ = l_Lean_Expr_isConstOf(v___x_1387_, v___x_1390_);
if (v___x_1391_ == 0)
{
uint8_t v___x_1392_; 
lean_dec_ref(v_arg_1378_);
v___x_1392_ = l_Lean_Expr_isApp(v___x_1387_);
if (v___x_1392_ == 0)
{
lean_dec_ref(v___x_1387_);
lean_del_object(v___x_1385_);
lean_dec_ref(v_arg_1379_);
goto v___jp_1363_;
}
else
{
lean_object* v___x_1393_; uint8_t v___x_1394_; 
v___x_1393_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1387_);
v___x_1394_ = l_Lean_Expr_isApp(v___x_1393_);
if (v___x_1394_ == 0)
{
lean_dec_ref(v___x_1393_);
lean_dec_ref(v___x_1387_);
lean_del_object(v___x_1385_);
lean_dec_ref(v_arg_1379_);
goto v___jp_1363_;
}
else
{
lean_object* v___x_1395_; uint8_t v___x_1396_; 
v___x_1395_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1393_);
v___x_1396_ = l_Lean_Expr_isConstOf(v___x_1395_, v___x_1376_);
lean_dec_ref(v___x_1395_);
if (v___x_1396_ == 0)
{
lean_dec_ref(v___x_1393_);
lean_dec_ref(v___x_1387_);
lean_del_object(v___x_1385_);
lean_dec_ref(v_arg_1379_);
goto v___jp_1363_;
}
else
{
uint8_t v___x_1397_; 
v___x_1397_ = l_Lean_Expr_isForall(v_arg_1379_);
if (v___x_1397_ == 0)
{
lean_object* v_arg_1398_; lean_object* v_arg_1399_; uint8_t v___x_1400_; 
v_arg_1398_ = lean_ctor_get(v___x_1387_, 1);
lean_inc_ref(v_arg_1398_);
lean_dec_ref(v___x_1387_);
v_arg_1399_ = lean_ctor_get(v___x_1393_, 1);
lean_inc_ref(v_arg_1399_);
lean_dec_ref(v___x_1393_);
v___x_1400_ = l_Lean_Expr_isForall(v_arg_1399_);
if (v___x_1400_ == 0)
{
uint8_t v___x_1401_; 
v___x_1401_ = l_Lean_Expr_isForall(v_arg_1398_);
if (v___x_1401_ == 0)
{
lean_object* v___x_1402_; lean_object* v___x_1404_; 
lean_dec_ref(v_arg_1399_);
lean_dec_ref(v_arg_1398_);
lean_dec_ref(v_arg_1379_);
v___x_1402_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
if (v_isShared_1386_ == 0)
{
lean_ctor_set(v___x_1385_, 0, v___x_1402_);
v___x_1404_ = v___x_1385_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v___x_1402_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
else
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1414_; 
lean_inc_ref(v_arg_1379_);
lean_inc_ref(v_arg_1399_);
v___x_1406_ = l_Lean_mkOr(v_arg_1399_, v_arg_1379_);
lean_inc_ref(v_arg_1398_);
v___x_1407_ = l_Lean_mkOr(v_arg_1398_, v___x_1406_);
v___x_1408_ = lean_obj_once(&l_Lean_Meta_Grind_simpOr___redArg___closed__2, &l_Lean_Meta_Grind_simpOr___redArg___closed__2_once, _init_l_Lean_Meta_Grind_simpOr___redArg___closed__2);
v___x_1409_ = l_Lean_mkApp3(v___x_1408_, v_arg_1379_, v_arg_1399_, v_arg_1398_);
v___x_1410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1410_, 0, v___x_1409_);
v___x_1411_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1411_, 0, v___x_1407_);
lean_ctor_set(v___x_1411_, 1, v___x_1410_);
lean_ctor_set_uint8(v___x_1411_, sizeof(void*)*2, v___x_1396_);
v___x_1412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1412_, 0, v___x_1411_);
if (v_isShared_1386_ == 0)
{
lean_ctor_set(v___x_1385_, 0, v___x_1412_);
v___x_1414_ = v___x_1385_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v___x_1412_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
}
else
{
lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1424_; 
lean_inc_ref(v_arg_1398_);
lean_inc_ref(v_arg_1379_);
v___x_1416_ = l_Lean_mkOr(v_arg_1379_, v_arg_1398_);
lean_inc_ref(v_arg_1399_);
v___x_1417_ = l_Lean_mkOr(v_arg_1399_, v___x_1416_);
v___x_1418_ = lean_obj_once(&l_Lean_Meta_Grind_simpOr___redArg___closed__5, &l_Lean_Meta_Grind_simpOr___redArg___closed__5_once, _init_l_Lean_Meta_Grind_simpOr___redArg___closed__5);
v___x_1419_ = l_Lean_mkApp3(v___x_1418_, v_arg_1379_, v_arg_1399_, v_arg_1398_);
v___x_1420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1420_, 0, v___x_1419_);
v___x_1421_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1421_, 0, v___x_1417_);
lean_ctor_set(v___x_1421_, 1, v___x_1420_);
lean_ctor_set_uint8(v___x_1421_, sizeof(void*)*2, v___x_1396_);
v___x_1422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1422_, 0, v___x_1421_);
if (v_isShared_1386_ == 0)
{
lean_ctor_set(v___x_1385_, 0, v___x_1422_);
v___x_1424_ = v___x_1385_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v___x_1422_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
}
else
{
lean_object* v___x_1426_; lean_object* v___x_1428_; 
lean_dec_ref(v___x_1393_);
lean_dec_ref(v___x_1387_);
lean_dec_ref(v_arg_1379_);
v___x_1426_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
if (v_isShared_1386_ == 0)
{
lean_ctor_set(v___x_1385_, 0, v___x_1426_);
v___x_1428_ = v___x_1385_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v___x_1426_);
v___x_1428_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
return v___x_1428_;
}
}
}
}
}
}
else
{
lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1436_; 
lean_dec_ref(v___x_1387_);
v___x_1430_ = lean_obj_once(&l_Lean_Meta_Grind_simpOr___redArg___closed__8, &l_Lean_Meta_Grind_simpOr___redArg___closed__8_once, _init_l_Lean_Meta_Grind_simpOr___redArg___closed__8);
v___x_1431_ = l_Lean_Expr_app___override(v___x_1430_, v_arg_1379_);
v___x_1432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1431_);
v___x_1433_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1433_, 0, v_arg_1378_);
lean_ctor_set(v___x_1433_, 1, v___x_1432_);
lean_ctor_set_uint8(v___x_1433_, sizeof(void*)*2, v___x_1391_);
v___x_1434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1434_, 0, v___x_1433_);
if (v_isShared_1386_ == 0)
{
lean_ctor_set(v___x_1385_, 0, v___x_1434_);
v___x_1436_ = v___x_1385_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v___x_1434_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
else
{
lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1444_; 
lean_dec_ref(v___x_1387_);
lean_dec_ref(v_arg_1378_);
v___x_1438_ = lean_obj_once(&l_Lean_Meta_Grind_simpOr___redArg___closed__11, &l_Lean_Meta_Grind_simpOr___redArg___closed__11_once, _init_l_Lean_Meta_Grind_simpOr___redArg___closed__11);
lean_inc_ref(v_arg_1379_);
v___x_1439_ = l_Lean_Expr_app___override(v___x_1438_, v_arg_1379_);
v___x_1440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1440_, 0, v___x_1439_);
v___x_1441_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1441_, 0, v_arg_1379_);
lean_ctor_set(v___x_1441_, 1, v___x_1440_);
lean_ctor_set_uint8(v___x_1441_, sizeof(void*)*2, v___x_1389_);
v___x_1442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1442_, 0, v___x_1441_);
if (v_isShared_1386_ == 0)
{
lean_ctor_set(v___x_1385_, 0, v___x_1442_);
v___x_1444_ = v___x_1385_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v___x_1442_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
}
else
{
lean_object* v_a_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1454_; 
lean_dec_ref(v_arg_1379_);
lean_dec_ref(v_arg_1378_);
v_a_1447_ = lean_ctor_get(v___x_1382_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1449_ = v___x_1382_;
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_a_1447_);
lean_dec(v___x_1382_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1452_; 
if (v_isShared_1450_ == 0)
{
v___x_1452_ = v___x_1449_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_a_1447_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
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
lean_object* v_a_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1514_; 
v_a_1507_ = lean_ctor_get(v___x_1369_, 0);
v_isSharedCheck_1514_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1514_ == 0)
{
v___x_1509_ = v___x_1369_;
v_isShared_1510_ = v_isSharedCheck_1514_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_a_1507_);
lean_dec(v___x_1369_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1514_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v___x_1512_; 
if (v_isShared_1510_ == 0)
{
v___x_1512_ = v___x_1509_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v_a_1507_);
v___x_1512_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
return v___x_1512_;
}
}
}
v___jp_1363_:
{
lean_object* v___x_1364_; lean_object* v___x_1365_; 
v___x_1364_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
v___x_1365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1365_, 0, v___x_1364_);
return v___x_1365_;
}
v___jp_1366_:
{
lean_object* v___x_1367_; lean_object* v___x_1368_; 
v___x_1367_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
v___x_1368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1368_, 0, v___x_1367_);
return v___x_1368_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpOr___redArg___boxed(lean_object* v_e_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_){
_start:
{
lean_object* v_res_1518_; 
v_res_1518_ = l_Lean_Meta_Grind_simpOr___redArg(v_e_1515_, v_a_1516_);
lean_dec(v_a_1516_);
return v_res_1518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpOr(lean_object* v_e_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_){
_start:
{
lean_object* v___x_1528_; 
v___x_1528_ = l_Lean_Meta_Grind_simpOr___redArg(v_e_1519_, v_a_1524_);
return v___x_1528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpOr___boxed(lean_object* v_e_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l_Lean_Meta_Grind_simpOr(v_e_1529_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_);
lean_dec(v_a_1536_);
lean_dec_ref(v_a_1535_);
lean_dec(v_a_1534_);
lean_dec_ref(v_a_1533_);
lean_dec(v_a_1532_);
lean_dec_ref(v_a_1531_);
lean_dec(v_a_1530_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_12_(){
_start:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1556_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_12_));
v___x_1557_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_12_));
v___x_1558_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpOr___boxed), 9, 0);
v___x_1559_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_1556_, v___x_1557_, v___x_1558_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_12____boxed(lean_object* v_a_1560_){
_start:
{
lean_object* v_res_1561_; 
v_res_1561_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_12_();
return v_res_1561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reduceCtorEqCheap___lam__0(uint8_t v___x_1562_, uint8_t v___x_1563_, lean_object* v_h_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_){
_start:
{
lean_object* v___x_1573_; lean_object* v___y_1575_; lean_object* v___x_1595_; 
v___x_1573_ = lean_obj_once(&l_Lean_Meta_Grind_simpEq___redArg___closed__14, &l_Lean_Meta_Grind_simpEq___redArg___closed__14_once, _init_l_Lean_Meta_Grind_simpEq___redArg___closed__14);
lean_inc_ref(v_h_1564_);
v___x_1595_ = l_Lean_Meta_mkNoConfusion(v___x_1573_, v_h_1564_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_);
if (lean_obj_tag(v___x_1595_) == 0)
{
lean_object* v_a_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; uint8_t v___x_1600_; lean_object* v___x_1601_; 
v_a_1596_ = lean_ctor_get(v___x_1595_, 0);
lean_inc(v_a_1596_);
lean_dec_ref_known(v___x_1595_, 1);
v___x_1597_ = lean_unsigned_to_nat(1u);
v___x_1598_ = lean_mk_empty_array_with_capacity(v___x_1597_);
v___x_1599_ = lean_array_push(v___x_1598_, v_h_1564_);
v___x_1600_ = 1;
v___x_1601_ = l_Lean_Meta_mkLambdaFVars(v___x_1599_, v_a_1596_, v___x_1563_, v___x_1562_, v___x_1563_, v___x_1562_, v___x_1600_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_);
lean_dec_ref(v___x_1599_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_object* v_a_1602_; lean_object* v___x_1603_; uint8_t v_transparency_1604_; uint8_t v___x_1605_; uint8_t v___x_1606_; 
v_a_1602_ = lean_ctor_get(v___x_1601_, 0);
lean_inc(v_a_1602_);
lean_dec_ref_known(v___x_1601_, 1);
v___x_1603_ = l_Lean_Meta_Context_config(v___y_1568_);
v_transparency_1604_ = lean_ctor_get_uint8(v___x_1603_, 9);
lean_dec_ref(v___x_1603_);
v___x_1605_ = 1;
v___x_1606_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_1604_, v___x_1605_);
if (v___x_1606_ == 0)
{
lean_object* v_keyedConfig_1607_; uint8_t v_trackZetaDelta_1608_; lean_object* v_zetaDeltaSet_1609_; lean_object* v_lctx_1610_; lean_object* v_localInstances_1611_; lean_object* v_defEqCtx_x3f_1612_; lean_object* v_synthPendingDepth_1613_; lean_object* v_customCanUnfoldPredicate_x3f_1614_; uint8_t v_univApprox_1615_; uint8_t v_inTypeClassResolution_1616_; uint8_t v_cacheInferType_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
v_keyedConfig_1607_ = lean_ctor_get(v___y_1568_, 0);
v_trackZetaDelta_1608_ = lean_ctor_get_uint8(v___y_1568_, sizeof(void*)*7);
v_zetaDeltaSet_1609_ = lean_ctor_get(v___y_1568_, 1);
v_lctx_1610_ = lean_ctor_get(v___y_1568_, 2);
v_localInstances_1611_ = lean_ctor_get(v___y_1568_, 3);
v_defEqCtx_x3f_1612_ = lean_ctor_get(v___y_1568_, 4);
v_synthPendingDepth_1613_ = lean_ctor_get(v___y_1568_, 5);
v_customCanUnfoldPredicate_x3f_1614_ = lean_ctor_get(v___y_1568_, 6);
v_univApprox_1615_ = lean_ctor_get_uint8(v___y_1568_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1616_ = lean_ctor_get_uint8(v___y_1568_, sizeof(void*)*7 + 2);
v_cacheInferType_1617_ = lean_ctor_get_uint8(v___y_1568_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_1607_);
v___x_1618_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_1605_, v_keyedConfig_1607_);
lean_inc(v_customCanUnfoldPredicate_x3f_1614_);
lean_inc(v_synthPendingDepth_1613_);
lean_inc(v_defEqCtx_x3f_1612_);
lean_inc_ref(v_localInstances_1611_);
lean_inc_ref(v_lctx_1610_);
lean_inc(v_zetaDeltaSet_1609_);
v___x_1619_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1619_, 0, v___x_1618_);
lean_ctor_set(v___x_1619_, 1, v_zetaDeltaSet_1609_);
lean_ctor_set(v___x_1619_, 2, v_lctx_1610_);
lean_ctor_set(v___x_1619_, 3, v_localInstances_1611_);
lean_ctor_set(v___x_1619_, 4, v_defEqCtx_x3f_1612_);
lean_ctor_set(v___x_1619_, 5, v_synthPendingDepth_1613_);
lean_ctor_set(v___x_1619_, 6, v_customCanUnfoldPredicate_x3f_1614_);
lean_ctor_set_uint8(v___x_1619_, sizeof(void*)*7, v_trackZetaDelta_1608_);
lean_ctor_set_uint8(v___x_1619_, sizeof(void*)*7 + 1, v_univApprox_1615_);
lean_ctor_set_uint8(v___x_1619_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1616_);
lean_ctor_set_uint8(v___x_1619_, sizeof(void*)*7 + 3, v_cacheInferType_1617_);
v___x_1620_ = l_Lean_Meta_mkEqFalse_x27(v_a_1602_, v___x_1619_, v___y_1569_, v___y_1570_, v___y_1571_);
lean_dec_ref_known(v___x_1619_, 7);
v___y_1575_ = v___x_1620_;
goto v___jp_1574_;
}
else
{
lean_object* v___x_1621_; 
v___x_1621_ = l_Lean_Meta_mkEqFalse_x27(v_a_1602_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_);
v___y_1575_ = v___x_1621_;
goto v___jp_1574_;
}
}
else
{
lean_object* v_a_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1629_; 
v_a_1622_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1624_ = v___x_1601_;
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_a_1622_);
lean_dec(v___x_1601_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1627_; 
if (v_isShared_1625_ == 0)
{
v___x_1627_ = v___x_1624_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_a_1622_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
}
}
else
{
lean_object* v_a_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1637_; 
lean_dec_ref(v_h_1564_);
v_a_1630_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1632_ = v___x_1595_;
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_a_1630_);
lean_dec(v___x_1595_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1635_; 
if (v_isShared_1633_ == 0)
{
v___x_1635_ = v___x_1632_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_a_1630_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
}
v___jp_1574_:
{
if (lean_obj_tag(v___y_1575_) == 0)
{
lean_object* v_a_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1586_; 
v_a_1576_ = lean_ctor_get(v___y_1575_, 0);
v_isSharedCheck_1586_ = !lean_is_exclusive(v___y_1575_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1578_ = v___y_1575_;
v_isShared_1579_ = v_isSharedCheck_1586_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_a_1576_);
lean_dec(v___y_1575_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1586_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1584_; 
v___x_1580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1580_, 0, v_a_1576_);
v___x_1581_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1581_, 0, v___x_1573_);
lean_ctor_set(v___x_1581_, 1, v___x_1580_);
lean_ctor_set_uint8(v___x_1581_, sizeof(void*)*2, v___x_1562_);
v___x_1582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1582_, 0, v___x_1581_);
if (v_isShared_1579_ == 0)
{
lean_ctor_set(v___x_1578_, 0, v___x_1582_);
v___x_1584_ = v___x_1578_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v___x_1582_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
}
else
{
lean_object* v_a_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1594_; 
v_a_1587_ = lean_ctor_get(v___y_1575_, 0);
v_isSharedCheck_1594_ = !lean_is_exclusive(v___y_1575_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1589_ = v___y_1575_;
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_a_1587_);
lean_dec(v___y_1575_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___x_1592_; 
if (v_isShared_1590_ == 0)
{
v___x_1592_ = v___x_1589_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_a_1587_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reduceCtorEqCheap___lam__0___boxed(lean_object* v___x_1638_, lean_object* v___x_1639_, lean_object* v_h_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_){
_start:
{
uint8_t v___x_12418__boxed_1649_; uint8_t v___x_12419__boxed_1650_; lean_object* v_res_1651_; 
v___x_12418__boxed_1649_ = lean_unbox(v___x_1638_);
v___x_12419__boxed_1650_ = lean_unbox(v___x_1639_);
v_res_1651_ = l_Lean_Meta_Grind_reduceCtorEqCheap___lam__0(v___x_12418__boxed_1649_, v___x_12419__boxed_1650_, v_h_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_);
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
lean_dec(v___y_1643_);
lean_dec_ref(v___y_1642_);
lean_dec(v___y_1641_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___redArg___lam__0(lean_object* v_k_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v_b_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_){
_start:
{
lean_object* v___x_1662_; 
lean_inc(v___y_1660_);
lean_inc_ref(v___y_1659_);
lean_inc(v___y_1658_);
lean_inc_ref(v___y_1657_);
lean_inc(v___y_1655_);
lean_inc_ref(v___y_1654_);
lean_inc(v___y_1653_);
v___x_1662_ = lean_apply_9(v_k_1652_, v_b_1656_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, lean_box(0));
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v_b_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___redArg___lam__0(v_k_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v_b_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
lean_dec(v___y_1669_);
lean_dec_ref(v___y_1668_);
lean_dec(v___y_1666_);
lean_dec_ref(v___y_1665_);
lean_dec(v___y_1664_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___redArg(lean_object* v_name_1674_, uint8_t v_bi_1675_, lean_object* v_type_1676_, lean_object* v_k_1677_, uint8_t v_kind_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_){
_start:
{
lean_object* v___f_1687_; lean_object* v___x_1688_; 
lean_inc(v___y_1681_);
lean_inc_ref(v___y_1680_);
lean_inc(v___y_1679_);
v___f_1687_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1687_, 0, v_k_1677_);
lean_closure_set(v___f_1687_, 1, v___y_1679_);
lean_closure_set(v___f_1687_, 2, v___y_1680_);
lean_closure_set(v___f_1687_, 3, v___y_1681_);
v___x_1688_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1674_, v_bi_1675_, v_type_1676_, v___f_1687_, v_kind_1678_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_);
if (lean_obj_tag(v___x_1688_) == 0)
{
return v___x_1688_;
}
else
{
lean_object* v_a_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1696_; 
v_a_1689_ = lean_ctor_get(v___x_1688_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1688_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1691_ = v___x_1688_;
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_a_1689_);
lean_dec(v___x_1688_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v___x_1694_; 
if (v_isShared_1692_ == 0)
{
v___x_1694_ = v___x_1691_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_a_1689_);
v___x_1694_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
return v___x_1694_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___redArg___boxed(lean_object* v_name_1697_, lean_object* v_bi_1698_, lean_object* v_type_1699_, lean_object* v_k_1700_, lean_object* v_kind_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_){
_start:
{
uint8_t v_bi_boxed_1710_; uint8_t v_kind_boxed_1711_; lean_object* v_res_1712_; 
v_bi_boxed_1710_ = lean_unbox(v_bi_1698_);
v_kind_boxed_1711_ = lean_unbox(v_kind_1701_);
v_res_1712_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___redArg(v_name_1697_, v_bi_boxed_1710_, v_type_1699_, v_k_1700_, v_kind_boxed_1711_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_);
lean_dec(v___y_1708_);
lean_dec_ref(v___y_1707_);
lean_dec(v___y_1706_);
lean_dec_ref(v___y_1705_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
lean_dec(v___y_1702_);
return v_res_1712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0___redArg(lean_object* v_name_1713_, lean_object* v_type_1714_, lean_object* v_k_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_){
_start:
{
uint8_t v___x_1724_; uint8_t v___x_1725_; lean_object* v___x_1726_; 
v___x_1724_ = 0;
v___x_1725_ = 0;
v___x_1726_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___redArg(v_name_1713_, v___x_1724_, v_type_1714_, v_k_1715_, v___x_1725_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
return v___x_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0___redArg___boxed(lean_object* v_name_1727_, lean_object* v_type_1728_, lean_object* v_k_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0___redArg(v_name_1727_, v_type_1728_, v_k_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
lean_dec(v___y_1736_);
lean_dec_ref(v___y_1735_);
lean_dec(v___y_1734_);
lean_dec_ref(v___y_1733_);
lean_dec(v___y_1732_);
lean_dec_ref(v___y_1731_);
lean_dec(v___y_1730_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reduceCtorEqCheap(lean_object* v_e_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_){
_start:
{
lean_object* v___x_1754_; 
lean_inc_ref(v_e_1742_);
v___x_1754_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1742_, v_a_1747_);
if (lean_obj_tag(v___x_1754_) == 0)
{
lean_object* v_a_1755_; lean_object* v___x_1756_; uint8_t v___x_1757_; 
v_a_1755_ = lean_ctor_get(v___x_1754_, 0);
lean_inc(v_a_1755_);
lean_dec_ref_known(v___x_1754_, 1);
v___x_1756_ = l_Lean_Expr_cleanupAnnotations(v_a_1755_);
lean_dec(v_a_1755_);
v___x_1757_ = l_Lean_Expr_isApp(v___x_1756_);
if (v___x_1757_ == 0)
{
lean_dec_ref(v___x_1756_);
lean_dec_ref(v_e_1742_);
goto v___jp_1751_;
}
else
{
lean_object* v___x_1758_; uint8_t v___x_1759_; 
v___x_1758_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1756_);
v___x_1759_ = l_Lean_Expr_isApp(v___x_1758_);
if (v___x_1759_ == 0)
{
lean_dec_ref(v___x_1758_);
lean_dec_ref(v___x_1756_);
lean_dec_ref(v_e_1742_);
goto v___jp_1751_;
}
else
{
lean_object* v___x_1760_; uint8_t v___x_1761_; 
v___x_1760_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1758_);
v___x_1761_ = l_Lean_Expr_isApp(v___x_1760_);
if (v___x_1761_ == 0)
{
lean_dec_ref(v___x_1760_);
lean_dec_ref(v___x_1758_);
lean_dec_ref(v___x_1756_);
lean_dec_ref(v_e_1742_);
goto v___jp_1751_;
}
else
{
lean_object* v___x_1762_; lean_object* v___x_1763_; uint8_t v___x_1764_; 
v___x_1762_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1760_);
lean_dec_ref(v___x_1760_);
v___x_1763_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__2));
v___x_1764_ = l_Lean_Expr_isConstOf(v___x_1762_, v___x_1763_);
lean_dec_ref(v___x_1762_);
if (v___x_1764_ == 0)
{
lean_dec_ref(v___x_1758_);
lean_dec_ref(v___x_1756_);
lean_dec_ref(v_e_1742_);
goto v___jp_1751_;
}
else
{
lean_object* v_arg_1765_; lean_object* v_arg_1766_; lean_object* v___x_1767_; 
v_arg_1765_ = lean_ctor_get(v___x_1756_, 1);
lean_inc_ref(v_arg_1765_);
lean_dec_ref(v___x_1756_);
v_arg_1766_ = lean_ctor_get(v___x_1758_, 1);
lean_inc_ref(v_arg_1766_);
lean_dec_ref(v___x_1758_);
v___x_1767_ = l_Lean_Meta_isConstructorApp_x3f(v_arg_1766_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_);
if (lean_obj_tag(v___x_1767_) == 0)
{
lean_object* v_a_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1810_; 
v_a_1768_ = lean_ctor_get(v___x_1767_, 0);
v_isSharedCheck_1810_ = !lean_is_exclusive(v___x_1767_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1770_ = v___x_1767_;
v_isShared_1771_ = v_isSharedCheck_1810_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_a_1768_);
lean_dec(v___x_1767_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1810_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
if (lean_obj_tag(v_a_1768_) == 1)
{
lean_object* v_val_1772_; lean_object* v___x_1773_; 
lean_del_object(v___x_1770_);
v_val_1772_ = lean_ctor_get(v_a_1768_, 0);
lean_inc(v_val_1772_);
lean_dec_ref_known(v_a_1768_, 1);
v___x_1773_ = l_Lean_Meta_isConstructorApp_x3f(v_arg_1765_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_);
if (lean_obj_tag(v___x_1773_) == 0)
{
lean_object* v_a_1774_; lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1797_; 
v_a_1774_ = lean_ctor_get(v___x_1773_, 0);
v_isSharedCheck_1797_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1797_ == 0)
{
v___x_1776_ = v___x_1773_;
v_isShared_1777_ = v_isSharedCheck_1797_;
goto v_resetjp_1775_;
}
else
{
lean_inc(v_a_1774_);
lean_dec(v___x_1773_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1797_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
if (lean_obj_tag(v_a_1774_) == 1)
{
lean_object* v_toConstantVal_1778_; lean_object* v_val_1779_; lean_object* v_toConstantVal_1780_; lean_object* v_name_1781_; lean_object* v_name_1782_; uint8_t v___x_1783_; 
v_toConstantVal_1778_ = lean_ctor_get(v_val_1772_, 0);
lean_inc_ref(v_toConstantVal_1778_);
lean_dec(v_val_1772_);
v_val_1779_ = lean_ctor_get(v_a_1774_, 0);
lean_inc(v_val_1779_);
lean_dec_ref_known(v_a_1774_, 1);
v_toConstantVal_1780_ = lean_ctor_get(v_val_1779_, 0);
lean_inc_ref(v_toConstantVal_1780_);
lean_dec(v_val_1779_);
v_name_1781_ = lean_ctor_get(v_toConstantVal_1778_, 0);
lean_inc(v_name_1781_);
lean_dec_ref(v_toConstantVal_1778_);
v_name_1782_ = lean_ctor_get(v_toConstantVal_1780_, 0);
lean_inc(v_name_1782_);
lean_dec_ref(v_toConstantVal_1780_);
v___x_1783_ = lean_name_eq(v_name_1781_, v_name_1782_);
lean_dec(v_name_1782_);
lean_dec(v_name_1781_);
if (v___x_1783_ == 0)
{
lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___f_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; 
lean_del_object(v___x_1776_);
v___x_1784_ = lean_box(v___x_1764_);
v___x_1785_ = lean_box(v___x_1783_);
v___f_1786_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_reduceCtorEqCheap___lam__0___boxed), 11, 2);
lean_closure_set(v___f_1786_, 0, v___x_1784_);
lean_closure_set(v___f_1786_, 1, v___x_1785_);
v___x_1787_ = ((lean_object*)(l_Lean_Meta_Grind_reduceCtorEqCheap___closed__1));
v___x_1788_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0___redArg(v___x_1787_, v_e_1742_, v___f_1786_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_);
return v___x_1788_;
}
else
{
lean_object* v___x_1789_; lean_object* v___x_1791_; 
lean_dec_ref(v_e_1742_);
v___x_1789_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
if (v_isShared_1777_ == 0)
{
lean_ctor_set(v___x_1776_, 0, v___x_1789_);
v___x_1791_ = v___x_1776_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v___x_1789_);
v___x_1791_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
return v___x_1791_;
}
}
}
else
{
lean_object* v___x_1793_; lean_object* v___x_1795_; 
lean_dec(v_a_1774_);
lean_dec(v_val_1772_);
lean_dec_ref(v_e_1742_);
v___x_1793_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
if (v_isShared_1777_ == 0)
{
lean_ctor_set(v___x_1776_, 0, v___x_1793_);
v___x_1795_ = v___x_1776_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v___x_1793_);
v___x_1795_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
return v___x_1795_;
}
}
}
}
else
{
lean_object* v_a_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1805_; 
lean_dec(v_val_1772_);
lean_dec_ref(v_e_1742_);
v_a_1798_ = lean_ctor_get(v___x_1773_, 0);
v_isSharedCheck_1805_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1805_ == 0)
{
v___x_1800_ = v___x_1773_;
v_isShared_1801_ = v_isSharedCheck_1805_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_a_1798_);
lean_dec(v___x_1773_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1805_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v___x_1803_; 
if (v_isShared_1801_ == 0)
{
v___x_1803_ = v___x_1800_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v_a_1798_);
v___x_1803_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
return v___x_1803_;
}
}
}
}
else
{
lean_object* v___x_1806_; lean_object* v___x_1808_; 
lean_dec(v_a_1768_);
lean_dec_ref(v_arg_1765_);
lean_dec_ref(v_e_1742_);
v___x_1806_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
if (v_isShared_1771_ == 0)
{
lean_ctor_set(v___x_1770_, 0, v___x_1806_);
v___x_1808_ = v___x_1770_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v___x_1806_);
v___x_1808_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
return v___x_1808_;
}
}
}
}
else
{
lean_object* v_a_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1818_; 
lean_dec_ref(v_arg_1765_);
lean_dec_ref(v_e_1742_);
v_a_1811_ = lean_ctor_get(v___x_1767_, 0);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1767_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1813_ = v___x_1767_;
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_a_1811_);
lean_dec(v___x_1767_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1816_; 
if (v_isShared_1814_ == 0)
{
v___x_1816_ = v___x_1813_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_a_1811_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
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
lean_object* v_a_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1826_; 
lean_dec_ref(v_e_1742_);
v_a_1819_ = lean_ctor_get(v___x_1754_, 0);
v_isSharedCheck_1826_ = !lean_is_exclusive(v___x_1754_);
if (v_isSharedCheck_1826_ == 0)
{
v___x_1821_ = v___x_1754_;
v_isShared_1822_ = v_isSharedCheck_1826_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_a_1819_);
lean_dec(v___x_1754_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1826_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v___x_1824_; 
if (v_isShared_1822_ == 0)
{
v___x_1824_ = v___x_1821_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v_a_1819_);
v___x_1824_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
return v___x_1824_;
}
}
}
v___jp_1751_:
{
lean_object* v___x_1752_; lean_object* v___x_1753_; 
v___x_1752_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
v___x_1753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1753_, 0, v___x_1752_);
return v___x_1753_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reduceCtorEqCheap___boxed(lean_object* v_e_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_){
_start:
{
lean_object* v_res_1836_; 
v_res_1836_ = l_Lean_Meta_Grind_reduceCtorEqCheap(v_e_1827_, v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_, v_a_1833_, v_a_1834_);
lean_dec(v_a_1834_);
lean_dec_ref(v_a_1833_);
lean_dec(v_a_1832_);
lean_dec_ref(v_a_1831_);
lean_dec(v_a_1830_);
lean_dec_ref(v_a_1829_);
lean_dec(v_a_1828_);
return v_res_1836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0(lean_object* v_00_u03b1_1837_, lean_object* v_name_1838_, uint8_t v_bi_1839_, lean_object* v_type_1840_, lean_object* v_k_1841_, uint8_t v_kind_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_){
_start:
{
lean_object* v___x_1851_; 
v___x_1851_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___redArg(v_name_1838_, v_bi_1839_, v_type_1840_, v_k_1841_, v_kind_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_);
return v___x_1851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1852_, lean_object* v_name_1853_, lean_object* v_bi_1854_, lean_object* v_type_1855_, lean_object* v_k_1856_, lean_object* v_kind_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_){
_start:
{
uint8_t v_bi_boxed_1866_; uint8_t v_kind_boxed_1867_; lean_object* v_res_1868_; 
v_bi_boxed_1866_ = lean_unbox(v_bi_1854_);
v_kind_boxed_1867_ = lean_unbox(v_kind_1857_);
v_res_1868_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0(v_00_u03b1_1852_, v_name_1853_, v_bi_boxed_1866_, v_type_1855_, v_k_1856_, v_kind_boxed_1867_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
lean_dec(v___y_1864_);
lean_dec_ref(v___y_1863_);
lean_dec(v___y_1862_);
lean_dec_ref(v___y_1861_);
lean_dec(v___y_1860_);
lean_dec_ref(v___y_1859_);
lean_dec(v___y_1858_);
return v_res_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0(lean_object* v_00_u03b1_1869_, lean_object* v_name_1870_, lean_object* v_type_1871_, lean_object* v_k_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_){
_start:
{
lean_object* v___x_1881_; 
v___x_1881_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0___redArg(v_name_1870_, v_type_1871_, v_k_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_);
return v___x_1881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0___boxed(lean_object* v_00_u03b1_1882_, lean_object* v_name_1883_, lean_object* v_type_1884_, lean_object* v_k_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_){
_start:
{
lean_object* v_res_1894_; 
v_res_1894_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0(v_00_u03b1_1882_, v_name_1883_, v_type_1884_, v_k_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
lean_dec(v___y_1890_);
lean_dec_ref(v___y_1889_);
lean_dec(v___y_1888_);
lean_dec_ref(v___y_1887_);
lean_dec(v___y_1886_);
return v_res_1894_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_14_(){
_start:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1902_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_14_));
v___x_1903_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__4_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13_));
v___x_1904_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_reduceCtorEqCheap___boxed), 9, 0);
v___x_1905_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_1902_, v___x_1903_, v___x_1904_);
return v___x_1905_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_14____boxed(lean_object* v_a_1906_){
_start:
{
lean_object* v_res_1907_; 
v_res_1907_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_14_();
return v_res_1907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_unfoldReducibleSimproc___redArg(lean_object* v_e_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_){
_start:
{
lean_object* v___x_1914_; 
v___x_1914_ = l_Lean_Meta_Sym_unfoldReducibleStep(v_e_1908_, v_a_1909_, v_a_1910_, v_a_1911_, v_a_1912_);
return v___x_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_unfoldReducibleSimproc___redArg___boxed(lean_object* v_e_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_){
_start:
{
lean_object* v_res_1921_; 
v_res_1921_ = l_Lean_Meta_Grind_unfoldReducibleSimproc___redArg(v_e_1915_, v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_);
lean_dec(v_a_1919_);
lean_dec_ref(v_a_1918_);
lean_dec(v_a_1917_);
lean_dec_ref(v_a_1916_);
return v_res_1921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_unfoldReducibleSimproc(lean_object* v_e_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_){
_start:
{
lean_object* v___x_1931_; 
v___x_1931_ = l_Lean_Meta_Sym_unfoldReducibleStep(v_e_1922_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_);
return v___x_1931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_unfoldReducibleSimproc___boxed(lean_object* v_e_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_){
_start:
{
lean_object* v_res_1941_; 
v_res_1941_ = l_Lean_Meta_Grind_unfoldReducibleSimproc(v_e_1932_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_);
lean_dec(v_a_1939_);
lean_dec_ref(v_a_1938_);
lean_dec(v_a_1937_);
lean_dec_ref(v_a_1936_);
lean_dec(v_a_1935_);
lean_dec_ref(v_a_1934_);
lean_dec(v_a_1933_);
return v_res_1941_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___lam__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_10_(lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_){
_start:
{
lean_object* v___x_1951_; 
v___x_1951_ = l_Lean_Meta_Sym_unfoldReducibleStep(v___y_1942_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_);
return v___x_1951_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___lam__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_10____boxed(lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_){
_start:
{
lean_object* v_res_1961_; 
v_res_1961_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___lam__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_10_(v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
lean_dec(v___y_1957_);
lean_dec_ref(v___y_1956_);
lean_dec(v___y_1955_);
lean_dec_ref(v___y_1954_);
lean_dec(v___y_1953_);
return v_res_1961_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_10_(){
_start:
{
lean_object* v___f_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; 
v___f_1974_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_10_));
v___x_1975_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_10_));
v___x_1976_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_10_));
v___x_1977_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1975_, v___x_1976_, v___f_1974_);
return v___x_1977_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_10____boxed(lean_object* v_a_1978_){
_start:
{
lean_object* v_res_1979_; 
v_res_1979_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_10_();
return v_res_1979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimprocs___redArg(lean_object* v_a_1988_, lean_object* v_a_1989_){
_start:
{
lean_object* v___x_1991_; 
v___x_1991_ = l_Lean_Meta_Simp_getSEvalSimprocs___redArg(v_a_1989_);
if (lean_obj_tag(v___x_1991_) == 0)
{
lean_object* v_a_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; uint8_t v___x_1998_; lean_object* v___x_1999_; 
v_a_1992_ = lean_ctor_get(v___x_1991_, 0);
lean_inc(v_a_1992_);
lean_dec_ref_known(v___x_1991_, 1);
v___x_1993_ = ((lean_object*)(l_Lean_Meta_Grind_getSimprocs___redArg___closed__2));
v___x_1994_ = l_Lean_Meta_Simp_Simprocs_erase(v_a_1992_, v___x_1993_);
v___x_1995_ = ((lean_object*)(l_Lean_Meta_Grind_getSimprocs___redArg___closed__4));
v___x_1996_ = l_Lean_Meta_Simp_Simprocs_erase(v___x_1994_, v___x_1995_);
v___x_1997_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_14_));
v___x_1998_ = 1;
v___x_1999_ = l_Lean_Meta_Simp_Simprocs_add(v___x_1996_, v___x_1997_, v___x_1998_, v_a_1988_, v_a_1989_);
if (lean_obj_tag(v___x_1999_) == 0)
{
lean_object* v_a_2000_; lean_object* v___x_2001_; 
v_a_2000_ = lean_ctor_get(v___x_1999_, 0);
lean_inc(v_a_2000_);
lean_dec_ref_known(v___x_1999_, 1);
v___x_2001_ = l_Lean_Meta_Grind_addSimpMatchDiscrsOnly(v_a_2000_, v_a_1988_, v_a_1989_);
if (lean_obj_tag(v___x_2001_) == 0)
{
lean_object* v_a_2002_; lean_object* v___x_2003_; 
v_a_2002_ = lean_ctor_get(v___x_2001_, 0);
lean_inc(v_a_2002_);
lean_dec_ref_known(v___x_2001_, 1);
v___x_2003_ = l_Lean_Meta_Grind_addPreMatchCondSimproc(v_a_2002_, v_a_1988_, v_a_1989_);
if (lean_obj_tag(v___x_2003_) == 0)
{
lean_object* v_a_2004_; lean_object* v___x_2005_; 
v_a_2004_ = lean_ctor_get(v___x_2003_, 0);
lean_inc(v_a_2004_);
lean_dec_ref_known(v___x_2003_, 1);
v___x_2005_ = l_Lean_Meta_Grind_Arith_addSimproc(v_a_2004_, v_a_1988_, v_a_1989_);
if (lean_obj_tag(v___x_2005_) == 0)
{
lean_object* v_a_2006_; lean_object* v___x_2007_; 
v_a_2006_ = lean_ctor_get(v___x_2005_, 0);
lean_inc(v_a_2006_);
lean_dec_ref_known(v___x_2005_, 1);
v___x_2007_ = l_Lean_Meta_Grind_addForallSimproc(v_a_2006_, v_a_1988_, v_a_1989_);
if (lean_obj_tag(v___x_2007_) == 0)
{
lean_object* v_a_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; 
v_a_2008_ = lean_ctor_get(v___x_2007_, 0);
lean_inc(v_a_2008_);
lean_dec_ref_known(v___x_2007_, 1);
v___x_2009_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13_));
v___x_2010_ = l_Lean_Meta_Simp_Simprocs_add(v_a_2008_, v___x_2009_, v___x_1998_, v_a_1988_, v_a_1989_);
if (lean_obj_tag(v___x_2010_) == 0)
{
lean_object* v_a_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; 
v_a_2011_ = lean_ctor_get(v___x_2010_, 0);
lean_inc(v_a_2011_);
lean_dec_ref_known(v___x_2010_, 1);
v___x_2012_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_12_));
v___x_2013_ = l_Lean_Meta_Simp_Simprocs_add(v_a_2011_, v___x_2012_, v___x_1998_, v_a_1988_, v_a_1989_);
if (lean_obj_tag(v___x_2013_) == 0)
{
lean_object* v_a_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; 
v_a_2014_ = lean_ctor_get(v___x_2013_, 0);
lean_inc(v_a_2014_);
lean_dec_ref_known(v___x_2013_, 1);
v___x_2015_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_14_));
v___x_2016_ = l_Lean_Meta_Simp_Simprocs_add(v_a_2014_, v___x_2015_, v___x_1998_, v_a_1988_, v_a_1989_);
if (lean_obj_tag(v___x_2016_) == 0)
{
lean_object* v_a_2017_; lean_object* v___x_2018_; uint8_t v___x_2019_; lean_object* v___x_2020_; 
v_a_2017_ = lean_ctor_get(v___x_2016_, 0);
lean_inc(v_a_2017_);
lean_dec_ref_known(v___x_2016_, 1);
v___x_2018_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2942474041____hygCtx___hyg_11_));
v___x_2019_ = 0;
v___x_2020_ = l_Lean_Meta_Simp_Simprocs_add(v_a_2017_, v___x_2018_, v___x_2019_, v_a_1988_, v_a_1989_);
if (lean_obj_tag(v___x_2020_) == 0)
{
lean_object* v_a_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; 
v_a_2021_ = lean_ctor_get(v___x_2020_, 0);
lean_inc(v_a_2021_);
lean_dec_ref_known(v___x_2020_, 1);
v___x_2022_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_10_));
v___x_2023_ = l_Lean_Meta_Simp_Simprocs_add(v_a_2021_, v___x_2022_, v___x_2019_, v_a_1988_, v_a_1989_);
if (lean_obj_tag(v___x_2023_) == 0)
{
lean_object* v_a_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2034_; 
v_a_2024_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2034_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2034_ == 0)
{
v___x_2026_ = v___x_2023_;
v_isShared_2027_ = v_isSharedCheck_2034_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_a_2024_);
lean_dec(v___x_2023_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2034_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2032_; 
v___x_2028_ = lean_unsigned_to_nat(1u);
v___x_2029_ = lean_mk_empty_array_with_capacity(v___x_2028_);
v___x_2030_ = lean_array_push(v___x_2029_, v_a_2024_);
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 0, v___x_2030_);
v___x_2032_ = v___x_2026_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v___x_2030_);
v___x_2032_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
return v___x_2032_;
}
}
}
else
{
lean_object* v_a_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2042_; 
v_a_2035_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2042_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2037_ = v___x_2023_;
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_a_2035_);
lean_dec(v___x_2023_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___x_2040_; 
if (v_isShared_2038_ == 0)
{
v___x_2040_ = v___x_2037_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_a_2035_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
}
}
else
{
lean_object* v_a_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2050_; 
v_a_2043_ = lean_ctor_get(v___x_2020_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_2020_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2045_ = v___x_2020_;
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_a_2043_);
lean_dec(v___x_2020_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2048_; 
if (v_isShared_2046_ == 0)
{
v___x_2048_ = v___x_2045_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_a_2043_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
return v___x_2048_;
}
}
}
}
else
{
lean_object* v_a_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2058_; 
v_a_2051_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2053_ = v___x_2016_;
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_a_2051_);
lean_dec(v___x_2016_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2056_; 
if (v_isShared_2054_ == 0)
{
v___x_2056_ = v___x_2053_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_a_2051_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
}
else
{
lean_object* v_a_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2066_; 
v_a_2059_ = lean_ctor_get(v___x_2013_, 0);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_2013_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2061_ = v___x_2013_;
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_a_2059_);
lean_dec(v___x_2013_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2064_; 
if (v_isShared_2062_ == 0)
{
v___x_2064_ = v___x_2061_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v_a_2059_);
v___x_2064_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
return v___x_2064_;
}
}
}
}
else
{
lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2074_; 
v_a_2067_ = lean_ctor_get(v___x_2010_, 0);
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2069_ = v___x_2010_;
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___x_2010_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2072_; 
if (v_isShared_2070_ == 0)
{
v___x_2072_ = v___x_2069_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_a_2067_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
return v___x_2072_;
}
}
}
}
else
{
lean_object* v_a_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2082_; 
v_a_2075_ = lean_ctor_get(v___x_2007_, 0);
v_isSharedCheck_2082_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2077_ = v___x_2007_;
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_a_2075_);
lean_dec(v___x_2007_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v___x_2080_; 
if (v_isShared_2078_ == 0)
{
v___x_2080_ = v___x_2077_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v_a_2075_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
return v___x_2080_;
}
}
}
}
else
{
lean_object* v_a_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2090_; 
v_a_2083_ = lean_ctor_get(v___x_2005_, 0);
v_isSharedCheck_2090_ = !lean_is_exclusive(v___x_2005_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2085_ = v___x_2005_;
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_a_2083_);
lean_dec(v___x_2005_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
lean_object* v___x_2088_; 
if (v_isShared_2086_ == 0)
{
v___x_2088_ = v___x_2085_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v_a_2083_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
return v___x_2088_;
}
}
}
}
else
{
lean_object* v_a_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2098_; 
v_a_2091_ = lean_ctor_get(v___x_2003_, 0);
v_isSharedCheck_2098_ = !lean_is_exclusive(v___x_2003_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2093_ = v___x_2003_;
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_a_2091_);
lean_dec(v___x_2003_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v___x_2096_; 
if (v_isShared_2094_ == 0)
{
v___x_2096_ = v___x_2093_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_a_2091_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
return v___x_2096_;
}
}
}
}
else
{
lean_object* v_a_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2106_; 
v_a_2099_ = lean_ctor_get(v___x_2001_, 0);
v_isSharedCheck_2106_ = !lean_is_exclusive(v___x_2001_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2101_ = v___x_2001_;
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_a_2099_);
lean_dec(v___x_2001_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2104_; 
if (v_isShared_2102_ == 0)
{
v___x_2104_ = v___x_2101_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v_a_2099_);
v___x_2104_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
return v___x_2104_;
}
}
}
}
else
{
lean_object* v_a_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2114_; 
v_a_2107_ = lean_ctor_get(v___x_1999_, 0);
v_isSharedCheck_2114_ = !lean_is_exclusive(v___x_1999_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2109_ = v___x_1999_;
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_a_2107_);
lean_dec(v___x_1999_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___x_2112_; 
if (v_isShared_2110_ == 0)
{
v___x_2112_ = v___x_2109_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v_a_2107_);
v___x_2112_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
return v___x_2112_;
}
}
}
}
else
{
lean_object* v_a_2115_; lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2122_; 
v_a_2115_ = lean_ctor_get(v___x_1991_, 0);
v_isSharedCheck_2122_ = !lean_is_exclusive(v___x_1991_);
if (v_isSharedCheck_2122_ == 0)
{
v___x_2117_ = v___x_1991_;
v_isShared_2118_ = v_isSharedCheck_2122_;
goto v_resetjp_2116_;
}
else
{
lean_inc(v_a_2115_);
lean_dec(v___x_1991_);
v___x_2117_ = lean_box(0);
v_isShared_2118_ = v_isSharedCheck_2122_;
goto v_resetjp_2116_;
}
v_resetjp_2116_:
{
lean_object* v___x_2120_; 
if (v_isShared_2118_ == 0)
{
v___x_2120_ = v___x_2117_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v_a_2115_);
v___x_2120_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
return v___x_2120_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimprocs___redArg___boxed(lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_){
_start:
{
lean_object* v_res_2126_; 
v_res_2126_ = l_Lean_Meta_Grind_getSimprocs___redArg(v_a_2123_, v_a_2124_);
lean_dec(v_a_2124_);
lean_dec_ref(v_a_2123_);
return v_res_2126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimprocs(lean_object* v_a_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_){
_start:
{
lean_object* v___x_2132_; 
v___x_2132_ = l_Lean_Meta_Grind_getSimprocs___redArg(v_a_2129_, v_a_2130_);
return v___x_2132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimprocs___boxed(lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_){
_start:
{
lean_object* v_res_2138_; 
v_res_2138_ = l_Lean_Meta_Grind_getSimprocs(v_a_2133_, v_a_2134_, v_a_2135_, v_a_2136_);
lean_dec(v_a_2136_);
lean_dec_ref(v_a_2135_);
lean_dec(v_a_2134_);
lean_dec_ref(v_a_2133_);
return v_res_2138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_addDeclToUnfold(lean_object* v_s_2139_, lean_object* v_declName_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_){
_start:
{
lean_object* v___x_2146_; lean_object* v_env_2147_; uint8_t v___x_2148_; uint8_t v___x_2149_; 
v___x_2146_ = lean_st_ref_get(v_a_2144_);
v_env_2147_ = lean_ctor_get(v___x_2146_, 0);
lean_inc_ref(v_env_2147_);
lean_dec(v___x_2146_);
v___x_2148_ = 1;
lean_inc(v_declName_2140_);
v___x_2149_ = l_Lean_Environment_contains(v_env_2147_, v_declName_2140_, v___x_2148_);
if (v___x_2149_ == 0)
{
lean_object* v___x_2150_; 
lean_dec(v_declName_2140_);
v___x_2150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2150_, 0, v_s_2139_);
return v___x_2150_;
}
else
{
lean_object* v___x_2151_; 
v___x_2151_ = l_Lean_Meta_SimpTheorems_addDeclToUnfold(v_s_2139_, v_declName_2140_, v_a_2141_, v_a_2142_, v_a_2143_, v_a_2144_);
return v___x_2151_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_addDeclToUnfold___boxed(lean_object* v_s_2152_, lean_object* v_declName_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_){
_start:
{
lean_object* v_res_2159_; 
v_res_2159_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_addDeclToUnfold(v_s_2152_, v_declName_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_);
lean_dec(v_a_2157_);
lean_dec_ref(v_a_2156_);
lean_dec(v_a_2155_);
lean_dec_ref(v_a_2154_);
return v_res_2159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNormTheorems(lean_object* v_a_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_){
_start:
{
lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2165_ = l_Lean_Meta_Grind_normExt;
v___x_2166_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v___x_2165_, v_a_2163_);
if (lean_obj_tag(v___x_2166_) == 0)
{
lean_object* v_a_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; 
v_a_2167_ = lean_ctor_get(v___x_2166_, 0);
lean_inc(v_a_2167_);
lean_dec_ref_known(v___x_2166_, 1);
v___x_2168_ = ((lean_object*)(l_Lean_Meta_Grind_registerNormTheorems___closed__7));
v___x_2169_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_addDeclToUnfold(v_a_2167_, v___x_2168_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_);
if (lean_obj_tag(v___x_2169_) == 0)
{
lean_object* v_a_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; 
v_a_2170_ = lean_ctor_get(v___x_2169_, 0);
lean_inc(v_a_2170_);
lean_dec_ref_known(v___x_2169_, 1);
v___x_2171_ = ((lean_object*)(l_Lean_Meta_Grind_registerNormTheorems___closed__10));
v___x_2172_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_addDeclToUnfold(v_a_2170_, v___x_2171_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_);
if (lean_obj_tag(v___x_2172_) == 0)
{
lean_object* v_a_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; 
v_a_2173_ = lean_ctor_get(v___x_2172_, 0);
lean_inc(v_a_2173_);
lean_dec_ref_known(v___x_2172_, 1);
v___x_2174_ = ((lean_object*)(l_Lean_Meta_Grind_registerNormTheorems___closed__12));
v___x_2175_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_addDeclToUnfold(v_a_2173_, v___x_2174_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_);
if (lean_obj_tag(v___x_2175_) == 0)
{
lean_object* v_a_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; 
v_a_2176_ = lean_ctor_get(v___x_2175_, 0);
lean_inc(v_a_2176_);
lean_dec_ref_known(v___x_2175_, 1);
v___x_2177_ = ((lean_object*)(l_Lean_Meta_Grind_registerNormTheorems___closed__15));
v___x_2178_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_addDeclToUnfold(v_a_2176_, v___x_2177_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_);
if (lean_obj_tag(v___x_2178_) == 0)
{
lean_object* v_a_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; 
v_a_2179_ = lean_ctor_get(v___x_2178_, 0);
lean_inc(v_a_2179_);
lean_dec_ref_known(v___x_2178_, 1);
v___x_2180_ = ((lean_object*)(l_Lean_Meta_Grind_registerNormTheorems___closed__17));
v___x_2181_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_addDeclToUnfold(v_a_2179_, v___x_2180_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_);
return v___x_2181_;
}
else
{
return v___x_2178_;
}
}
else
{
return v___x_2175_;
}
}
else
{
return v___x_2172_;
}
}
else
{
return v___x_2169_;
}
}
else
{
return v___x_2166_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNormTheorems___boxed(lean_object* v_a_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_){
_start:
{
lean_object* v_res_2187_; 
v_res_2187_ = l_Lean_Meta_Grind_getNormTheorems(v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_);
lean_dec(v_a_2185_);
lean_dec_ref(v_a_2184_);
lean_dec(v_a_2183_);
lean_dec_ref(v_a_2182_);
return v_res_2187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimpContext(lean_object* v_config_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_){
_start:
{
lean_object* v___x_2194_; 
v___x_2194_ = l_Lean_Meta_Grind_getNormTheorems(v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_);
if (lean_obj_tag(v___x_2194_) == 0)
{
lean_object* v_a_2195_; lean_object* v___x_2196_; 
v_a_2195_ = lean_ctor_get(v___x_2194_, 0);
lean_inc(v_a_2195_);
lean_dec_ref_known(v___x_2194_, 1);
v___x_2196_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_2192_);
if (lean_obj_tag(v___x_2196_) == 0)
{
lean_object* v_a_2197_; uint8_t v_zetaDelta_2198_; uint8_t v_zeta_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; uint8_t v___x_2202_; uint8_t v___x_2203_; uint8_t v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; 
v_a_2197_ = lean_ctor_get(v___x_2196_, 0);
lean_inc(v_a_2197_);
lean_dec_ref_known(v___x_2196_, 1);
v_zetaDelta_2198_ = lean_ctor_get_uint8(v_config_2188_, sizeof(void*)*17 + 19);
v_zeta_2199_ = lean_ctor_get_uint8(v_config_2188_, sizeof(void*)*17 + 20);
v___x_2200_ = lean_unsigned_to_nat(100000u);
v___x_2201_ = lean_unsigned_to_nat(2u);
v___x_2202_ = 0;
v___x_2203_ = 1;
v___x_2204_ = 0;
v___x_2205_ = lean_box(0);
v___x_2206_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_2206_, 0, v___x_2200_);
lean_ctor_set(v___x_2206_, 1, v___x_2201_);
lean_ctor_set(v___x_2206_, 2, v___x_2205_);
lean_ctor_set_uint8(v___x_2206_, sizeof(void*)*3, v___x_2202_);
lean_ctor_set_uint8(v___x_2206_, sizeof(void*)*3 + 1, v___x_2203_);
lean_ctor_set_uint8(v___x_2206_, sizeof(void*)*3 + 2, v___x_2202_);
lean_ctor_set_uint8(v___x_2206_, sizeof(void*)*3 + 3, v_zeta_2199_);
lean_ctor_set_uint8(v___x_2206_, sizeof(void*)*3 + 4, v___x_2203_);
lean_ctor_set_uint8(v___x_2206_, sizeof(void*)*3 + 5, v___x_2203_);
lean_ctor_set_uint8(v___x_2206_, sizeof(void*)*3 + 6, v___x_2204_);
lean_ctor_set_uint8(v___x_2206_, sizeof(void*)*3 + 7, v___x_2203_);
lean_ctor_set_uint8(v___x_2206_, sizeof(void*)*3 + 8, v___x_2203_);
lean_ctor_set_uint8(v___x_2206_, sizeof(void*)*3 + 9, v___x_2202_);
lean_ctor_set_uint8(v___x_2206_, sizeof(void*)*3 + 10, v___x_2203_);
lean_ctor_set_uint8(v___x_2206_, sizeof(void*)*3 + 11, v___x_2202_);
lean_ctor_set_uint8(v___x_2206_, sizeof(void*)*3 + 12, v___x_2203_);
lean_ctor_set_uint8(v___x_2206_, sizeof(void*)*3 + 13, v___x_2203_);
lean_ctor_set_uint8(v___x_2206_, sizeof(void*)*3 + 14, v___x_2202_);
lean_ctor_set_uint8(v___x_2206_, sizeof(void*)*3 + 15, v___x_2202_);
lean_ctor_set_uint8(v___x_2206_, sizeof(void*)*3 + 16, v_zetaDelta_2198_);
lean_ctor_set_uint8(v___x_2206_, sizeof(void*)*3 + 17, v___x_2203_);
lean_ctor_set_uint8(v___x_2206_, sizeof(void*)*3 + 18, v___x_2202_);
lean_ctor_set_uint8(v___x_2206_, sizeof(void*)*3 + 19, v___x_2203_);
lean_ctor_set_uint8(v___x_2206_, sizeof(void*)*3 + 20, v___x_2202_);
lean_ctor_set_uint8(v___x_2206_, sizeof(void*)*3 + 21, v___x_2203_);
lean_ctor_set_uint8(v___x_2206_, sizeof(void*)*3 + 22, v___x_2203_);
lean_ctor_set_uint8(v___x_2206_, sizeof(void*)*3 + 23, v___x_2203_);
lean_ctor_set_uint8(v___x_2206_, sizeof(void*)*3 + 24, v___x_2202_);
lean_ctor_set_uint8(v___x_2206_, sizeof(void*)*3 + 25, v___x_2202_);
lean_ctor_set_uint8(v___x_2206_, sizeof(void*)*3 + 26, v___x_2202_);
lean_ctor_set_uint8(v___x_2206_, sizeof(void*)*3 + 27, v___x_2202_);
lean_ctor_set_uint8(v___x_2206_, sizeof(void*)*3 + 28, v___x_2202_);
v___x_2207_ = lean_unsigned_to_nat(1u);
v___x_2208_ = lean_mk_empty_array_with_capacity(v___x_2207_);
v___x_2209_ = lean_array_push(v___x_2208_, v_a_2195_);
v___x_2210_ = l_Lean_Options_empty;
v___x_2211_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_2206_, v___x_2209_, v_a_2197_, v___x_2210_, v_a_2189_, v_a_2191_, v_a_2192_);
return v___x_2211_;
}
else
{
lean_object* v_a_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2219_; 
lean_dec(v_a_2195_);
v_a_2212_ = lean_ctor_get(v___x_2196_, 0);
v_isSharedCheck_2219_ = !lean_is_exclusive(v___x_2196_);
if (v_isSharedCheck_2219_ == 0)
{
v___x_2214_ = v___x_2196_;
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_a_2212_);
lean_dec(v___x_2196_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v___x_2217_; 
if (v_isShared_2215_ == 0)
{
v___x_2217_ = v___x_2214_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v_a_2212_);
v___x_2217_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
return v___x_2217_;
}
}
}
}
else
{
lean_object* v_a_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2227_; 
v_a_2220_ = lean_ctor_get(v___x_2194_, 0);
v_isSharedCheck_2227_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2222_ = v___x_2194_;
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_a_2220_);
lean_dec(v___x_2194_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2225_; 
if (v_isShared_2223_ == 0)
{
v___x_2225_ = v___x_2222_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_a_2220_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimpContext___boxed(lean_object* v_config_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_){
_start:
{
lean_object* v_res_2234_; 
v_res_2234_ = l_Lean_Meta_Grind_getSimpContext(v_config_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_);
lean_dec(v_a_2232_);
lean_dec_ref(v_a_2231_);
lean_dec(v_a_2230_);
lean_dec_ref(v_a_2229_);
lean_dec_ref(v_config_2228_);
return v_res_2234_;
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
