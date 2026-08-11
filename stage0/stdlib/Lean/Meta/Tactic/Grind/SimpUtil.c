// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.SimpUtil
// Imports: public import Lean.Meta.Tactic.Simp.Simproc import Lean.Meta.Tactic.Grind.MatchDiscrOnly import Lean.Meta.Tactic.Grind.ForallProp import Lean.Meta.Tactic.Grind.Arith.Simproc import Lean.Meta.Tactic.Simp.BuiltinSimprocs.List import Lean.Meta.Tactic.Simp.BuiltinSimprocs.Core import Lean.Meta.Tactic.Grind.Util import Lean.Meta.Sym.Util import Init.Grind.Norm public import Init.Grind.Config import Init.ByCases import Lean.Meta.Tactic.Simp.Main import Lean.OrderLevel
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_PersistentHashMap_Node_isEmpty___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_Meta_mkEqFalse_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAnd(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isProp(lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_leCarrierIsSort(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_mkIntLit(lean_object*);
lean_object* l_Lean_mkIntAdd(lean_object*, lean_object*);
lean_object* l_Lean_mkIntLE(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_mkNatAdd(lean_object*, lean_object*);
lean_object* l_Lean_mkNatLE(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_mkBVar(lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinSimproc(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_mkOr(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_getSEvalSimprocs___redArg(lean_object*);
lean_object* l_Lean_Meta_Simp_Simprocs_erase(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Simprocs_add(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_addSimpMatchDiscrsOnly(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_addPreMatchCondSimproc(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_addSimproc(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_addForallSimproc(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_normExt;
lean_object* l_Lean_Meta_SimpExtension_getTheorems___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_SimpTheorems_addDeclToUnfold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSimpCongrTheorems___redArg(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Meta_Simp_mkContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinDSimproc(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_addSimpTheorem(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_registerNormTheorems_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_registerNormTheorems_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_registerNormTheorems_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_registerNormTheorems_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_registerNormTheorems_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_registerNormTheorems___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "`grind` normalization theorems have already been initialized"};
static const lean_object* l_Lean_Meta_Grind_registerNormTheorems___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_registerNormTheorems___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_registerNormTheorems___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_registerNormTheorems___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerNormTheorems(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerNormTheorems___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "not"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__1_value),LEAN_SCALAR_PTR_LITERAL(208, 215, 171, 150, 192, 180, 249, 22)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "BEq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "beq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__3_value),LEAN_SCALAR_PTR_LITERAL(195, 188, 39, 55, 57, 152, 88, 223)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__4_value),LEAN_SCALAR_PTR_LITERAL(82, 52, 243, 194, 7, 226, 90, 135)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Decidable"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "decide"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__6_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__7_value),LEAN_SCALAR_PTR_LITERAL(16, 96, 65, 173, 152, 155, 4, 222)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "and"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__9_value),LEAN_SCALAR_PTR_LITERAL(160, 26, 8, 228, 104, 32, 82, 85)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__10_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "or"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__11_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__11_value),LEAN_SCALAR_PTR_LITERAL(90, 191, 239, 225, 113, 224, 109, 182)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__12_value;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___boxed(lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_simpEq___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_simpEq___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpEq___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpEq___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_simpEq___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpEq___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Grind_simpEq___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__6;
static const lean_string_object l_Lean_Meta_Grind_simpEq___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpEq___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Grind_simpEq___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__9;
static const lean_string_object l_Lean_Meta_Grind_simpEq___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__10_value;
static const lean_string_object l_Lean_Meta_Grind_simpEq___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__11_value;
static const lean_string_object l_Lean_Meta_Grind_simpEq___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "eq_false_eq"};
static const lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__12_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpEq___redArg___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpEq___redArg___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__13_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpEq___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__13_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__12_value),LEAN_SCALAR_PTR_LITERAL(79, 24, 241, 157, 245, 218, 196, 160)}};
static const lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__13 = (const lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__13_value;
static lean_once_cell_t l_Lean_Meta_Grind_simpEq___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__14;
static const lean_string_object l_Lean_Meta_Grind_simpEq___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "eq_true_eq"};
static const lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__15 = (const lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__15_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpEq___redArg___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpEq___redArg___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__16_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpEq___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__16_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__15_value),LEAN_SCALAR_PTR_LITERAL(100, 12, 190, 92, 208, 172, 117, 90)}};
static const lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__16 = (const lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__16_value;
static lean_once_cell_t l_Lean_Meta_Grind_simpEq___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__17;
static const lean_string_object l_Lean_Meta_Grind_simpEq___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "eq_self"};
static const lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__18 = (const lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__18_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpEq___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__18_value),LEAN_SCALAR_PTR_LITERAL(224, 148, 98, 216, 254, 239, 13, 169)}};
static const lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__19 = (const lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__19_value;
static const lean_string_object l_Lean_Meta_Grind_simpEq___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__20 = (const lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__20_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpEq___redArg___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpEq___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__21_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__20_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__21 = (const lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__21_value;
static lean_once_cell_t l_Lean_Meta_Grind_simpEq___redArg___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__22;
static const lean_string_object l_Lean_Meta_Grind_simpEq___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "bool_eq_to_prop"};
static const lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__23 = (const lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__23_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpEq___redArg___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpEq___redArg___closed__24_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__24_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpEq___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__24_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__23_value),LEAN_SCALAR_PTR_LITERAL(79, 89, 141, 151, 119, 96, 24, 167)}};
static const lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__24 = (const lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__24_value;
static lean_once_cell_t l_Lean_Meta_Grind_simpEq___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__25;
static const lean_string_object l_Lean_Meta_Grind_simpEq___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "flip_bool_eq"};
static const lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__26 = (const lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__26_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpEq___redArg___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpEq___redArg___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__27_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpEq___redArg___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__27_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__26_value),LEAN_SCALAR_PTR_LITERAL(19, 65, 30, 112, 127, 84, 12, 55)}};
static const lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__27 = (const lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__27_value;
static lean_once_cell_t l_Lean_Meta_Grind_simpEq___redArg___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__28;
static const lean_string_object l_Lean_Meta_Grind_simpEq___redArg___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_Meta_Grind_simpEq___redArg___closed__29 = (const lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__29_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpEq___redArg___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13__value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_14__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_14__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_14__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_14__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_14__value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
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
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(133, 192, 91, 90, 91, 211, 131, 26)}};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__5_value;
static const lean_string_object l_Lean_Meta_Grind_pushNot___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "not_implies"};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
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
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__17_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__17_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__16_value),LEAN_SCALAR_PTR_LITERAL(132, 165, 120, 219, 71, 87, 242, 138)}};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__17 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__17_value;
static lean_once_cell_t l_Lean_Meta_Grind_pushNot___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__18;
static const lean_string_object l_Lean_Meta_Grind_pushNot___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__19 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__19_value;
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__19_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__20 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__20_value;
static const lean_string_object l_Lean_Meta_Grind_pushNot___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__21 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__21_value;
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__21_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__22 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__22_value;
static lean_once_cell_t l_Lean_Meta_Grind_pushNot___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__23;
static lean_once_cell_t l_Lean_Meta_Grind_pushNot___redArg___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__24;
static const lean_string_object l_Lean_Meta_Grind_pushNot___redArg___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "not_le_eq"};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__25 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__25_value;
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__21_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__26_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__25_value),LEAN_SCALAR_PTR_LITERAL(77, 74, 162, 108, 148, 71, 165, 71)}};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__26 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__26_value;
static lean_once_cell_t l_Lean_Meta_Grind_pushNot___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__27;
static lean_once_cell_t l_Lean_Meta_Grind_pushNot___redArg___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__28;
static lean_once_cell_t l_Lean_Meta_Grind_pushNot___redArg___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__29;
static lean_once_cell_t l_Lean_Meta_Grind_pushNot___redArg___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__30;
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__19_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__31_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__25_value),LEAN_SCALAR_PTR_LITERAL(235, 23, 140, 144, 182, 73, 3, 60)}};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__31 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__31_value;
static lean_once_cell_t l_Lean_Meta_Grind_pushNot___redArg___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__32;
static lean_once_cell_t l_Lean_Meta_Grind_pushNot___redArg___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__33;
static const lean_string_object l_Lean_Meta_Grind_pushNot___redArg___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "not_eq_true"};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__34 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__34_value;
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__35_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__34_value),LEAN_SCALAR_PTR_LITERAL(225, 244, 63, 40, 164, 6, 8, 162)}};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__35 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__35_value;
static lean_once_cell_t l_Lean_Meta_Grind_pushNot___redArg___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__36;
static const lean_string_object l_Lean_Meta_Grind_pushNot___redArg___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "not_eq_false"};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__37 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__37_value;
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__38_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__38_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__37_value),LEAN_SCALAR_PTR_LITERAL(83, 226, 87, 91, 103, 177, 77, 30)}};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__38 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__38_value;
static lean_once_cell_t l_Lean_Meta_Grind_pushNot___redArg___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__39;
static const lean_string_object l_Lean_Meta_Grind_pushNot___redArg___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "not_eq_prop"};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__40 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__40_value;
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__41_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__41_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__41_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__41_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__40_value),LEAN_SCALAR_PTR_LITERAL(93, 9, 240, 16, 38, 110, 5, 203)}};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__41 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__41_value;
static lean_once_cell_t l_Lean_Meta_Grind_pushNot___redArg___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__42;
static lean_once_cell_t l_Lean_Meta_Grind_pushNot___redArg___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__43;
static const lean_string_object l_Lean_Meta_Grind_pushNot___redArg___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "not_and"};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__44 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__44_value;
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__45_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__45_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__45_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__45_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__44_value),LEAN_SCALAR_PTR_LITERAL(239, 225, 24, 71, 205, 142, 249, 26)}};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__45 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__45_value;
static lean_once_cell_t l_Lean_Meta_Grind_pushNot___redArg___closed__46_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__46;
static lean_once_cell_t l_Lean_Meta_Grind_pushNot___redArg___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__47;
static const lean_string_object l_Lean_Meta_Grind_pushNot___redArg___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "not_or"};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__48 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__48_value;
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__49_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__49_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__49_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__49_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__48_value),LEAN_SCALAR_PTR_LITERAL(235, 74, 178, 162, 31, 3, 143, 38)}};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__49 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__49_value;
static lean_once_cell_t l_Lean_Meta_Grind_pushNot___redArg___closed__50_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__50;
static const lean_string_object l_Lean_Meta_Grind_pushNot___redArg___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "a"};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__51 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__51_value;
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__51_value),LEAN_SCALAR_PTR_LITERAL(247, 80, 99, 121, 74, 33, 203, 108)}};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__52 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__52_value;
static lean_once_cell_t l_Lean_Meta_Grind_pushNot___redArg___closed__53_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__53;
static const lean_string_object l_Lean_Meta_Grind_pushNot___redArg___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "not_exists"};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__54 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__54_value;
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__55_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__55_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__55_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__55_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__54_value),LEAN_SCALAR_PTR_LITERAL(122, 84, 103, 56, 9, 28, 88, 199)}};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__55 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__55_value;
static const lean_string_object l_Lean_Meta_Grind_pushNot___redArg___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "not_not"};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__56 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__56_value;
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__57_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__57_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__57_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__57_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__56_value),LEAN_SCALAR_PTR_LITERAL(37, 13, 167, 116, 75, 172, 227, 19)}};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__57 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__57_value;
static lean_once_cell_t l_Lean_Meta_Grind_pushNot___redArg___closed__58_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__58;
static const lean_string_object l_Lean_Meta_Grind_pushNot___redArg___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "not_true"};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__59 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__59_value;
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__60_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__60_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__60_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__60_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__59_value),LEAN_SCALAR_PTR_LITERAL(189, 233, 184, 33, 201, 88, 141, 182)}};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__60 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__60_value;
static lean_once_cell_t l_Lean_Meta_Grind_pushNot___redArg___closed__61_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__61;
static lean_once_cell_t l_Lean_Meta_Grind_pushNot___redArg___closed__62_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__62;
static const lean_string_object l_Lean_Meta_Grind_pushNot___redArg___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "not_false"};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__63 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__63_value;
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__64_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__64_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__64_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_pushNot___redArg___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__64_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__63_value),LEAN_SCALAR_PTR_LITERAL(32, 161, 26, 17, 134, 82, 22, 22)}};
static const lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__64 = (const lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__64_value;
static lean_once_cell_t l_Lean_Meta_Grind_pushNot___redArg___closed__65_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__65;
static lean_once_cell_t l_Lean_Meta_Grind_pushNot___redArg___closed__66_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_pushNot___redArg___closed__66;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNot___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNot___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNot(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNot___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3828017814____hygCtx___hyg_11__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "pushNot"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3828017814____hygCtx___hyg_11_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3828017814____hygCtx___hyg_11__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3828017814____hygCtx___hyg_11__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3828017814____hygCtx___hyg_11__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3828017814____hygCtx___hyg_11__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3828017814____hygCtx___hyg_11__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3828017814____hygCtx___hyg_11__value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3828017814____hygCtx___hyg_11__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3828017814____hygCtx___hyg_11__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3828017814____hygCtx___hyg_11__value),LEAN_SCALAR_PTR_LITERAL(189, 165, 185, 106, 181, 96, 32, 196)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3828017814____hygCtx___hyg_11_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3828017814____hygCtx___hyg_11__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3828017814____hygCtx___hyg_11__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3828017814____hygCtx___hyg_11_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3828017814____hygCtx___hyg_11__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3828017814____hygCtx___hyg_11__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3828017814____hygCtx___hyg_11__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3828017814____hygCtx___hyg_11_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3828017814____hygCtx___hyg_11__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3828017814____hygCtx___hyg_11_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3828017814____hygCtx___hyg_11____boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_simpOr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "or_swap13"};
static const lean_object* l_Lean_Meta_Grind_simpOr___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_simpOr___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpOr___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpOr___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpOr___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpOr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpOr___redArg___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpOr___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(240, 5, 180, 71, 127, 106, 169, 101)}};
static const lean_object* l_Lean_Meta_Grind_simpOr___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_simpOr___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Grind_simpOr___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpOr___redArg___closed__2;
static const lean_string_object l_Lean_Meta_Grind_simpOr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "or_swap12"};
static const lean_object* l_Lean_Meta_Grind_simpOr___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_simpOr___redArg___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpOr___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpOr___redArg___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpOr___redArg___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
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
static const lean_ctor_object l_Lean_Meta_Grind_simpOr___redArg___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpOr___redArg___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpOr___redArg___closed__13_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_12__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_12__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_12__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_12__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_12__value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_14__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_14__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_14__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_14__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_14__value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_10__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_10__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_10__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_10__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_10__value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpEq___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
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
static const lean_string_object l_Lean_Meta_Grind_getNormTheorems___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "GE"};
static const lean_object* l_Lean_Meta_Grind_getNormTheorems___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_getNormTheorems___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_getNormTheorems___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ge"};
static const lean_object* l_Lean_Meta_Grind_getNormTheorems___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_getNormTheorems___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_getNormTheorems___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_getNormTheorems___closed__0_value),LEAN_SCALAR_PTR_LITERAL(74, 169, 4, 72, 62, 21, 91, 24)}};
static const lean_ctor_object l_Lean_Meta_Grind_getNormTheorems___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getNormTheorems___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getNormTheorems___closed__1_value),LEAN_SCALAR_PTR_LITERAL(71, 88, 92, 156, 129, 215, 23, 77)}};
static const lean_object* l_Lean_Meta_Grind_getNormTheorems___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_getNormTheorems___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_getNormTheorems___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "GT"};
static const lean_object* l_Lean_Meta_Grind_getNormTheorems___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_getNormTheorems___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_getNormTheorems___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "gt"};
static const lean_object* l_Lean_Meta_Grind_getNormTheorems___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_getNormTheorems___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_getNormTheorems___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_getNormTheorems___closed__3_value),LEAN_SCALAR_PTR_LITERAL(240, 16, 15, 58, 66, 186, 138, 31)}};
static const lean_ctor_object l_Lean_Meta_Grind_getNormTheorems___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getNormTheorems___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getNormTheorems___closed__4_value),LEAN_SCALAR_PTR_LITERAL(239, 75, 137, 103, 59, 22, 209, 130)}};
static const lean_object* l_Lean_Meta_Grind_getNormTheorems___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_getNormTheorems___closed__5_value;
static const lean_string_object l_Lean_Meta_Grind_getNormTheorems___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cast"};
static const lean_object* l_Lean_Meta_Grind_getNormTheorems___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_getNormTheorems___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_getNormTheorems___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_pushNot___redArg___closed__19_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_Grind_getNormTheorems___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getNormTheorems___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getNormTheorems___closed__6_value),LEAN_SCALAR_PTR_LITERAL(19, 237, 167, 212, 100, 179, 19, 112)}};
static const lean_object* l_Lean_Meta_Grind_getNormTheorems___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_getNormTheorems___closed__7_value;
static const lean_string_object l_Lean_Meta_Grind_getNormTheorems___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "xor"};
static const lean_object* l_Lean_Meta_Grind_getNormTheorems___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_getNormTheorems___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Grind_getNormTheorems___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Meta_Grind_getNormTheorems___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getNormTheorems___closed__9_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getNormTheorems___closed__8_value),LEAN_SCALAR_PTR_LITERAL(159, 35, 146, 118, 24, 65, 174, 144)}};
static const lean_object* l_Lean_Meta_Grind_getNormTheorems___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_getNormTheorems___closed__9_value;
static const lean_string_object l_Lean_Meta_Grind_getNormTheorems___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Ne"};
static const lean_object* l_Lean_Meta_Grind_getNormTheorems___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_getNormTheorems___closed__10_value;
static const lean_ctor_object l_Lean_Meta_Grind_getNormTheorems___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_getNormTheorems___closed__10_value),LEAN_SCALAR_PTR_LITERAL(161, 247, 70, 70, 118, 145, 235, 92)}};
static const lean_object* l_Lean_Meta_Grind_getNormTheorems___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_getNormTheorems___closed__11_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNormTheorems(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNormTheorems___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimpContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimpContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_normalizeImp___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_normalizeImp___closed__0;
static lean_once_cell_t l_Lean_Meta_Grind_normalizeImp___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_normalizeImp___closed__1;
static lean_once_cell_t l_Lean_Meta_Grind_normalizeImp___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_normalizeImp___closed__2;
static lean_once_cell_t l_Lean_Meta_Grind_normalizeImp___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_normalizeImp___closed__3;
static lean_once_cell_t l_Lean_Meta_Grind_normalizeImp___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_normalizeImp___closed__4;
static lean_once_cell_t l_Lean_Meta_Grind_normalizeImp___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_normalizeImp___closed__5;
static lean_once_cell_t l_Lean_Meta_Grind_normalizeImp___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_normalizeImp___closed__6;
LEAN_EXPORT lean_object* lean_grind_normalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normalizeImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg(lean_object* v_x_1_){
_start:
{
uint8_t v___x_2_; 
v___x_2_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___boxed(lean_object* v_x_3_){
_start:
{
uint8_t v_res_4_; lean_object* v_r_5_; 
v_res_4_ = l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg(v_x_3_);
lean_dec_ref(v_x_3_);
v_r_5_ = lean_box(v_res_4_);
return v_r_5_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_registerNormTheorems_spec__2(lean_object* v_00_u03b2_6_, lean_object* v_x_7_){
_start:
{
uint8_t v___x_8_; 
v___x_8_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___boxed(lean_object* v_00_u03b2_9_, lean_object* v_x_10_){
_start:
{
uint8_t v_res_11_; lean_object* v_r_12_; 
v_res_11_ = l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_registerNormTheorems_spec__2(v_00_u03b2_9_, v_x_10_);
lean_dec_ref(v_x_10_);
v_r_12_ = lean_box(v_res_11_);
return v_r_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__3_spec__3(lean_object* v_msgData_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_){
_start:
{
lean_object* v___x_19_; lean_object* v_env_20_; lean_object* v___x_21_; lean_object* v_mctx_22_; lean_object* v_lctx_23_; lean_object* v_options_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_19_ = lean_st_ref_get(v___y_17_);
v_env_20_ = lean_ctor_get(v___x_19_, 0);
lean_inc_ref(v_env_20_);
lean_dec(v___x_19_);
v___x_21_ = lean_st_ref_get(v___y_15_);
v_mctx_22_ = lean_ctor_get(v___x_21_, 0);
lean_inc_ref(v_mctx_22_);
lean_dec(v___x_21_);
v_lctx_23_ = lean_ctor_get(v___y_14_, 2);
v_options_24_ = lean_ctor_get(v___y_16_, 2);
lean_inc_ref(v_options_24_);
lean_inc_ref(v_lctx_23_);
v___x_25_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_25_, 0, v_env_20_);
lean_ctor_set(v___x_25_, 1, v_mctx_22_);
lean_ctor_set(v___x_25_, 2, v_lctx_23_);
lean_ctor_set(v___x_25_, 3, v_options_24_);
v___x_26_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_26_, 0, v___x_25_);
lean_ctor_set(v___x_26_, 1, v_msgData_13_);
v___x_27_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_27_, 0, v___x_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__3_spec__3___boxed(lean_object* v_msgData_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__3_spec__3(v_msgData_28_, v___y_29_, v___y_30_, v___y_31_, v___y_32_);
lean_dec(v___y_32_);
lean_dec_ref(v___y_31_);
lean_dec(v___y_30_);
lean_dec_ref(v___y_29_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__3___redArg(lean_object* v_msg_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_){
_start:
{
lean_object* v_ref_41_; lean_object* v___x_42_; lean_object* v_a_43_; lean_object* v___x_45_; uint8_t v_isShared_46_; uint8_t v_isSharedCheck_51_; 
v_ref_41_ = lean_ctor_get(v___y_38_, 5);
v___x_42_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__3_spec__3(v_msg_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_);
v_a_43_ = lean_ctor_get(v___x_42_, 0);
v_isSharedCheck_51_ = !lean_is_exclusive(v___x_42_);
if (v_isSharedCheck_51_ == 0)
{
v___x_45_ = v___x_42_;
v_isShared_46_ = v_isSharedCheck_51_;
goto v_resetjp_44_;
}
else
{
lean_inc(v_a_43_);
lean_dec(v___x_42_);
v___x_45_ = lean_box(0);
v_isShared_46_ = v_isSharedCheck_51_;
goto v_resetjp_44_;
}
v_resetjp_44_:
{
lean_object* v___x_47_; lean_object* v___x_49_; 
lean_inc(v_ref_41_);
v___x_47_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_47_, 0, v_ref_41_);
lean_ctor_set(v___x_47_, 1, v_a_43_);
if (v_isShared_46_ == 0)
{
lean_ctor_set_tag(v___x_45_, 1);
lean_ctor_set(v___x_45_, 0, v___x_47_);
v___x_49_ = v___x_45_;
goto v_reusejp_48_;
}
else
{
lean_object* v_reuseFailAlloc_50_; 
v_reuseFailAlloc_50_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_50_, 0, v___x_47_);
v___x_49_ = v_reuseFailAlloc_50_;
goto v_reusejp_48_;
}
v_reusejp_48_:
{
return v___x_49_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__3___redArg___boxed(lean_object* v_msg_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__3___redArg(v_msg_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_);
lean_dec(v___y_56_);
lean_dec_ref(v___y_55_);
lean_dec(v___y_54_);
lean_dec_ref(v___y_53_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_registerNormTheorems_spec__1(lean_object* v_as_59_, size_t v_sz_60_, size_t v_i_61_, lean_object* v_b_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_){
_start:
{
uint8_t v___x_68_; 
v___x_68_ = lean_usize_dec_lt(v_i_61_, v_sz_60_);
if (v___x_68_ == 0)
{
lean_object* v___x_69_; 
v___x_69_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_69_, 0, v_b_62_);
return v___x_69_;
}
else
{
lean_object* v___x_70_; lean_object* v_a_71_; uint8_t v___x_72_; uint8_t v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_70_ = l_Lean_Meta_Grind_normExt;
v_a_71_ = lean_array_uget_borrowed(v_as_59_, v_i_61_);
v___x_72_ = 0;
v___x_73_ = 0;
v___x_74_ = lean_unsigned_to_nat(1000u);
lean_inc(v_a_71_);
v___x_75_ = l_Lean_Meta_addSimpTheorem(v___x_70_, v_a_71_, v___x_68_, v___x_72_, v___x_73_, v___x_74_, v___y_63_, v___y_64_, v___y_65_, v___y_66_);
if (lean_obj_tag(v___x_75_) == 0)
{
lean_object* v___x_76_; size_t v___x_77_; size_t v___x_78_; 
lean_dec_ref_known(v___x_75_, 1);
v___x_76_ = lean_box(0);
v___x_77_ = ((size_t)1ULL);
v___x_78_ = lean_usize_add(v_i_61_, v___x_77_);
v_i_61_ = v___x_78_;
v_b_62_ = v___x_76_;
goto _start;
}
else
{
return v___x_75_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_registerNormTheorems_spec__1___boxed(lean_object* v_as_80_, lean_object* v_sz_81_, lean_object* v_i_82_, lean_object* v_b_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_){
_start:
{
size_t v_sz_boxed_89_; size_t v_i_boxed_90_; lean_object* v_res_91_; 
v_sz_boxed_89_ = lean_unbox_usize(v_sz_81_);
lean_dec(v_sz_81_);
v_i_boxed_90_ = lean_unbox_usize(v_i_82_);
lean_dec(v_i_82_);
v_res_91_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_registerNormTheorems_spec__1(v_as_80_, v_sz_boxed_89_, v_i_boxed_90_, v_b_83_, v___y_84_, v___y_85_, v___y_86_, v___y_87_);
lean_dec(v___y_87_);
lean_dec_ref(v___y_86_);
lean_dec(v___y_85_);
lean_dec_ref(v___y_84_);
lean_dec_ref(v_as_80_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_registerNormTheorems_spec__0(lean_object* v_as_92_, size_t v_sz_93_, size_t v_i_94_, lean_object* v_b_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_){
_start:
{
uint8_t v___x_101_; 
v___x_101_ = lean_usize_dec_lt(v_i_94_, v_sz_93_);
if (v___x_101_ == 0)
{
lean_object* v___x_102_; 
v___x_102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_102_, 0, v_b_95_);
return v___x_102_;
}
else
{
lean_object* v___x_103_; lean_object* v_a_104_; uint8_t v___x_105_; uint8_t v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_103_ = l_Lean_Meta_Grind_normExt;
v_a_104_ = lean_array_uget_borrowed(v_as_92_, v_i_94_);
v___x_105_ = 0;
v___x_106_ = 0;
v___x_107_ = lean_unsigned_to_nat(1000u);
lean_inc(v_a_104_);
v___x_108_ = l_Lean_Meta_addSimpTheorem(v___x_103_, v_a_104_, v___x_105_, v___x_105_, v___x_106_, v___x_107_, v___y_96_, v___y_97_, v___y_98_, v___y_99_);
if (lean_obj_tag(v___x_108_) == 0)
{
lean_object* v___x_109_; size_t v___x_110_; size_t v___x_111_; 
lean_dec_ref_known(v___x_108_, 1);
v___x_109_ = lean_box(0);
v___x_110_ = ((size_t)1ULL);
v___x_111_ = lean_usize_add(v_i_94_, v___x_110_);
v_i_94_ = v___x_111_;
v_b_95_ = v___x_109_;
goto _start;
}
else
{
return v___x_108_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_registerNormTheorems_spec__0___boxed(lean_object* v_as_113_, lean_object* v_sz_114_, lean_object* v_i_115_, lean_object* v_b_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_){
_start:
{
size_t v_sz_boxed_122_; size_t v_i_boxed_123_; lean_object* v_res_124_; 
v_sz_boxed_122_ = lean_unbox_usize(v_sz_114_);
lean_dec(v_sz_114_);
v_i_boxed_123_ = lean_unbox_usize(v_i_115_);
lean_dec(v_i_115_);
v_res_124_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_registerNormTheorems_spec__0(v_as_113_, v_sz_boxed_122_, v_i_boxed_123_, v_b_116_, v___y_117_, v___y_118_, v___y_119_, v___y_120_);
lean_dec(v___y_120_);
lean_dec_ref(v___y_119_);
lean_dec(v___y_118_);
lean_dec_ref(v___y_117_);
lean_dec_ref(v_as_113_);
return v_res_124_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_registerNormTheorems___closed__1(void){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_126_ = ((lean_object*)(l_Lean_Meta_Grind_registerNormTheorems___closed__0));
v___x_127_ = l_Lean_stringToMessageData(v___x_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerNormTheorems(lean_object* v_preDeclNames_128_, lean_object* v_postDeclNames_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_){
_start:
{
lean_object* v___y_136_; lean_object* v___y_137_; lean_object* v___y_138_; lean_object* v___y_139_; lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_154_ = l_Lean_Meta_Grind_normExt;
v___x_155_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v___x_154_, v_a_133_);
if (lean_obj_tag(v___x_155_) == 0)
{
lean_object* v_a_156_; lean_object* v_lemmaNames_157_; uint8_t v___x_158_; 
v_a_156_ = lean_ctor_get(v___x_155_, 0);
lean_inc(v_a_156_);
lean_dec_ref_known(v___x_155_, 1);
v_lemmaNames_157_ = lean_ctor_get(v_a_156_, 2);
lean_inc_ref(v_lemmaNames_157_);
lean_dec(v_a_156_);
v___x_158_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_lemmaNames_157_);
lean_dec_ref(v_lemmaNames_157_);
if (v___x_158_ == 0)
{
lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_159_ = lean_obj_once(&l_Lean_Meta_Grind_registerNormTheorems___closed__1, &l_Lean_Meta_Grind_registerNormTheorems___closed__1_once, _init_l_Lean_Meta_Grind_registerNormTheorems___closed__1);
v___x_160_ = l_Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__3___redArg(v___x_159_, v_a_130_, v_a_131_, v_a_132_, v_a_133_);
return v___x_160_;
}
else
{
v___y_136_ = v_a_130_;
v___y_137_ = v_a_131_;
v___y_138_ = v_a_132_;
v___y_139_ = v_a_133_;
goto v___jp_135_;
}
}
else
{
lean_object* v_a_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_168_; 
v_a_161_ = lean_ctor_get(v___x_155_, 0);
v_isSharedCheck_168_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_168_ == 0)
{
v___x_163_ = v___x_155_;
v_isShared_164_ = v_isSharedCheck_168_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_a_161_);
lean_dec(v___x_155_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_168_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
lean_object* v___x_166_; 
if (v_isShared_164_ == 0)
{
v___x_166_ = v___x_163_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v_a_161_);
v___x_166_ = v_reuseFailAlloc_167_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
return v___x_166_;
}
}
}
v___jp_135_:
{
lean_object* v___x_140_; size_t v_sz_141_; size_t v___x_142_; lean_object* v___x_143_; 
v___x_140_ = lean_box(0);
v_sz_141_ = lean_array_size(v_preDeclNames_128_);
v___x_142_ = ((size_t)0ULL);
v___x_143_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_registerNormTheorems_spec__0(v_preDeclNames_128_, v_sz_141_, v___x_142_, v___x_140_, v___y_136_, v___y_137_, v___y_138_, v___y_139_);
if (lean_obj_tag(v___x_143_) == 0)
{
size_t v_sz_144_; lean_object* v___x_145_; 
lean_dec_ref_known(v___x_143_, 1);
v_sz_144_ = lean_array_size(v_postDeclNames_129_);
v___x_145_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_registerNormTheorems_spec__1(v_postDeclNames_129_, v_sz_144_, v___x_142_, v___x_140_, v___y_136_, v___y_137_, v___y_138_, v___y_139_);
if (lean_obj_tag(v___x_145_) == 0)
{
lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_152_; 
v_isSharedCheck_152_ = !lean_is_exclusive(v___x_145_);
if (v_isSharedCheck_152_ == 0)
{
lean_object* v_unused_153_; 
v_unused_153_ = lean_ctor_get(v___x_145_, 0);
lean_dec(v_unused_153_);
v___x_147_ = v___x_145_;
v_isShared_148_ = v_isSharedCheck_152_;
goto v_resetjp_146_;
}
else
{
lean_dec(v___x_145_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_152_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v___x_150_; 
if (v_isShared_148_ == 0)
{
lean_ctor_set(v___x_147_, 0, v___x_140_);
v___x_150_ = v___x_147_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v___x_140_);
v___x_150_ = v_reuseFailAlloc_151_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
return v___x_150_;
}
}
}
else
{
return v___x_145_;
}
}
else
{
return v___x_143_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerNormTheorems___boxed(lean_object* v_preDeclNames_169_, lean_object* v_postDeclNames_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Lean_Meta_Grind_registerNormTheorems(v_preDeclNames_169_, v_postDeclNames_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_);
lean_dec(v_a_174_);
lean_dec_ref(v_a_173_);
lean_dec(v_a_172_);
lean_dec_ref(v_a_171_);
lean_dec_ref(v_postDeclNames_170_);
lean_dec_ref(v_preDeclNames_169_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__3(lean_object* v_00_u03b1_177_, lean_object* v_msg_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = l_Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__3___redArg(v_msg_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__3___boxed(lean_object* v_00_u03b1_185_, lean_object* v_msg_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__3(v_00_u03b1_185_, v_msg_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_);
lean_dec(v___y_190_);
lean_dec_ref(v___y_189_);
lean_dec(v___y_188_);
lean_dec_ref(v___y_187_);
return v_res_192_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget(lean_object* v_declName_216_){
_start:
{
uint8_t v___y_218_; lean_object* v___x_225_; uint8_t v___x_226_; 
v___x_225_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__10));
v___x_226_ = lean_name_eq(v_declName_216_, v___x_225_);
if (v___x_226_ == 0)
{
lean_object* v___x_227_; uint8_t v___x_228_; 
v___x_227_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__12));
v___x_228_ = lean_name_eq(v_declName_216_, v___x_227_);
v___y_218_ = v___x_228_;
goto v___jp_217_;
}
else
{
v___y_218_ = v___x_226_;
goto v___jp_217_;
}
v___jp_217_:
{
if (v___y_218_ == 0)
{
lean_object* v___x_219_; uint8_t v___x_220_; 
v___x_219_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__2));
v___x_220_ = lean_name_eq(v_declName_216_, v___x_219_);
if (v___x_220_ == 0)
{
lean_object* v___x_221_; uint8_t v___x_222_; 
v___x_221_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__5));
v___x_222_ = lean_name_eq(v_declName_216_, v___x_221_);
if (v___x_222_ == 0)
{
lean_object* v___x_223_; uint8_t v___x_224_; 
v___x_223_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__8));
v___x_224_ = lean_name_eq(v_declName_216_, v___x_223_);
return v___x_224_;
}
else
{
return v___x_222_;
}
}
else
{
return v___x_220_;
}
}
else
{
return v___y_218_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___boxed(lean_object* v_declName_229_){
_start:
{
uint8_t v_res_230_; lean_object* v_r_231_; 
v_res_230_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget(v_declName_229_);
lean_dec(v_declName_229_);
v_r_231_ = lean_box(v_res_230_);
return v_r_231_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpEq___redArg___closed__6(void){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_242_ = lean_box(0);
v___x_243_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__5));
v___x_244_ = l_Lean_mkConst(v___x_243_, v___x_242_);
return v___x_244_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpEq___redArg___closed__9(void){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_248_ = lean_box(0);
v___x_249_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__8));
v___x_250_ = l_Lean_mkConst(v___x_249_, v___x_248_);
return v___x_250_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpEq___redArg___closed__14(void){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_258_ = lean_box(0);
v___x_259_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__13));
v___x_260_ = l_Lean_mkConst(v___x_259_, v___x_258_);
return v___x_260_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpEq___redArg___closed__17(void){
_start:
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_266_ = lean_box(0);
v___x_267_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__16));
v___x_268_ = l_Lean_mkConst(v___x_267_, v___x_266_);
return v___x_268_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpEq___redArg___closed__22(void){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_276_ = lean_box(0);
v___x_277_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__21));
v___x_278_ = l_Lean_mkConst(v___x_277_, v___x_276_);
return v___x_278_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpEq___redArg___closed__25(void){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_284_ = lean_box(0);
v___x_285_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__24));
v___x_286_ = l_Lean_mkConst(v___x_285_, v___x_284_);
return v___x_286_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpEq___redArg___closed__28(void){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_292_ = lean_box(0);
v___x_293_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__27));
v___x_294_ = l_Lean_mkConst(v___x_293_, v___x_292_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpEq___redArg(lean_object* v_e_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_){
_start:
{
lean_object* v___x_305_; 
v___x_305_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_299_, v_a_301_);
if (lean_obj_tag(v___x_305_) == 0)
{
lean_object* v_a_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_445_; 
v_a_306_ = lean_ctor_get(v___x_305_, 0);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_305_);
if (v_isSharedCheck_445_ == 0)
{
v___x_308_ = v___x_305_;
v_isShared_309_ = v_isSharedCheck_445_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_a_306_);
lean_dec(v___x_305_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_445_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_315_; uint8_t v___x_316_; 
v___x_315_ = l_Lean_Expr_cleanupAnnotations(v_a_306_);
v___x_316_ = l_Lean_Expr_isApp(v___x_315_);
if (v___x_316_ == 0)
{
lean_dec_ref(v___x_315_);
goto v___jp_310_;
}
else
{
lean_object* v_arg_317_; lean_object* v___x_318_; uint8_t v___x_319_; 
v_arg_317_ = lean_ctor_get(v___x_315_, 1);
lean_inc_ref(v_arg_317_);
v___x_318_ = l_Lean_Expr_appFnCleanup___redArg(v___x_315_);
v___x_319_ = l_Lean_Expr_isApp(v___x_318_);
if (v___x_319_ == 0)
{
lean_dec_ref(v___x_318_);
lean_dec_ref(v_arg_317_);
goto v___jp_310_;
}
else
{
lean_object* v_arg_320_; lean_object* v___x_321_; uint8_t v___x_322_; 
v_arg_320_ = lean_ctor_get(v___x_318_, 1);
lean_inc_ref(v_arg_320_);
v___x_321_ = l_Lean_Expr_appFnCleanup___redArg(v___x_318_);
v___x_322_ = l_Lean_Expr_isApp(v___x_321_);
if (v___x_322_ == 0)
{
lean_dec_ref(v___x_321_);
lean_dec_ref(v_arg_320_);
lean_dec_ref(v_arg_317_);
goto v___jp_310_;
}
else
{
lean_object* v_arg_323_; lean_object* v___x_324_; lean_object* v___x_325_; uint8_t v___x_326_; 
v_arg_323_ = lean_ctor_get(v___x_321_, 1);
lean_inc_ref(v_arg_323_);
v___x_324_ = l_Lean_Expr_appFnCleanup___redArg(v___x_321_);
v___x_325_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__2));
v___x_326_ = l_Lean_Expr_isConstOf(v___x_324_, v___x_325_);
if (v___x_326_ == 0)
{
lean_dec_ref(v___x_324_);
lean_dec_ref(v_arg_323_);
lean_dec_ref(v_arg_320_);
lean_dec_ref(v_arg_317_);
goto v___jp_310_;
}
else
{
lean_object* v___x_327_; 
lean_del_object(v___x_308_);
lean_inc_ref(v_arg_323_);
v___x_327_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_323_, v_a_301_);
if (lean_obj_tag(v___x_327_) == 0)
{
lean_object* v_a_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_436_; 
v_a_328_ = lean_ctor_get(v___x_327_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_327_);
if (v_isSharedCheck_436_ == 0)
{
v___x_330_ = v___x_327_;
v_isShared_331_ = v_isSharedCheck_436_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_a_328_);
lean_dec(v___x_327_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_436_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_332_; lean_object* v___x_333_; uint8_t v___x_334_; 
v___x_332_ = l_Lean_Expr_cleanupAnnotations(v_a_328_);
v___x_333_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__3));
v___x_334_ = l_Lean_Expr_isConstOf(v___x_332_, v___x_333_);
lean_dec_ref(v___x_332_);
if (v___x_334_ == 0)
{
uint8_t v___x_335_; 
v___x_335_ = lean_expr_eqv(v_arg_320_, v_arg_317_);
if (v___x_335_ == 0)
{
lean_object* v___x_336_; uint8_t v___x_337_; 
lean_dec_ref(v___x_324_);
lean_dec_ref(v_arg_323_);
v___x_336_ = lean_obj_once(&l_Lean_Meta_Grind_simpEq___redArg___closed__6, &l_Lean_Meta_Grind_simpEq___redArg___closed__6_once, _init_l_Lean_Meta_Grind_simpEq___redArg___closed__6);
v___x_337_ = lean_expr_eqv(v_arg_317_, v___x_336_);
if (v___x_337_ == 0)
{
lean_object* v___x_338_; uint8_t v___x_339_; 
v___x_338_ = lean_obj_once(&l_Lean_Meta_Grind_simpEq___redArg___closed__9, &l_Lean_Meta_Grind_simpEq___redArg___closed__9_once, _init_l_Lean_Meta_Grind_simpEq___redArg___closed__9);
v___x_339_ = lean_expr_eqv(v_arg_317_, v___x_338_);
lean_dec_ref(v_arg_317_);
if (v___x_339_ == 0)
{
lean_object* v___x_340_; lean_object* v___x_342_; 
lean_dec_ref(v_arg_320_);
v___x_340_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 0, v___x_340_);
v___x_342_ = v___x_330_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v___x_340_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
else
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_351_; 
lean_inc_ref(v_arg_320_);
v___x_344_ = l_Lean_mkNot(v_arg_320_);
v___x_345_ = lean_obj_once(&l_Lean_Meta_Grind_simpEq___redArg___closed__14, &l_Lean_Meta_Grind_simpEq___redArg___closed__14_once, _init_l_Lean_Meta_Grind_simpEq___redArg___closed__14);
v___x_346_ = l_Lean_Expr_app___override(v___x_345_, v_arg_320_);
v___x_347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_347_, 0, v___x_346_);
v___x_348_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_348_, 0, v___x_344_);
lean_ctor_set(v___x_348_, 1, v___x_347_);
lean_ctor_set_uint8(v___x_348_, sizeof(void*)*2, v___x_326_);
v___x_349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_349_, 0, v___x_348_);
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 0, v___x_349_);
v___x_351_ = v___x_330_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v___x_349_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
return v___x_351_;
}
}
}
else
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_359_; 
lean_dec_ref(v_arg_317_);
v___x_353_ = lean_obj_once(&l_Lean_Meta_Grind_simpEq___redArg___closed__17, &l_Lean_Meta_Grind_simpEq___redArg___closed__17_once, _init_l_Lean_Meta_Grind_simpEq___redArg___closed__17);
lean_inc_ref(v_arg_320_);
v___x_354_ = l_Lean_Expr_app___override(v___x_353_, v_arg_320_);
v___x_355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_355_, 0, v___x_354_);
v___x_356_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_356_, 0, v_arg_320_);
lean_ctor_set(v___x_356_, 1, v___x_355_);
lean_ctor_set_uint8(v___x_356_, sizeof(void*)*2, v___x_326_);
v___x_357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_357_, 0, v___x_356_);
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 0, v___x_357_);
v___x_359_ = v___x_330_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v___x_357_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
return v___x_359_;
}
}
}
else
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_370_; 
lean_dec_ref(v_arg_317_);
v___x_361_ = l_Lean_Expr_constLevels_x21(v___x_324_);
lean_dec_ref(v___x_324_);
v___x_362_ = lean_obj_once(&l_Lean_Meta_Grind_simpEq___redArg___closed__6, &l_Lean_Meta_Grind_simpEq___redArg___closed__6_once, _init_l_Lean_Meta_Grind_simpEq___redArg___closed__6);
v___x_363_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__19));
v___x_364_ = l_Lean_mkConst(v___x_363_, v___x_361_);
v___x_365_ = l_Lean_mkAppB(v___x_364_, v_arg_323_, v_arg_320_);
v___x_366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_366_, 0, v___x_365_);
v___x_367_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_367_, 0, v___x_362_);
lean_ctor_set(v___x_367_, 1, v___x_366_);
lean_ctor_set_uint8(v___x_367_, sizeof(void*)*2, v___x_326_);
v___x_368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_368_, 0, v___x_367_);
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 0, v___x_368_);
v___x_370_ = v___x_330_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v___x_368_);
v___x_370_ = v_reuseFailAlloc_371_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
return v___x_370_;
}
}
}
else
{
lean_object* v___x_372_; 
v___x_372_ = l_Lean_Expr_getAppFn(v_arg_317_);
if (lean_obj_tag(v___x_372_) == 4)
{
lean_object* v_declName_373_; lean_object* v___x_374_; uint8_t v___y_376_; lean_object* v___y_407_; uint8_t v___y_408_; uint8_t v___y_419_; uint8_t v___x_429_; 
v_declName_373_ = lean_ctor_get(v___x_372_, 0);
lean_inc(v_declName_373_);
lean_dec_ref_known(v___x_372_, 2);
v___x_374_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__21));
v___x_429_ = lean_name_eq(v_declName_373_, v___x_374_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; uint8_t v___x_431_; 
v___x_430_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__30));
v___x_431_ = lean_name_eq(v_declName_373_, v___x_430_);
v___y_419_ = v___x_431_;
goto v___jp_418_;
}
else
{
v___y_419_ = v___x_429_;
goto v___jp_418_;
}
v___jp_375_:
{
if (v___y_376_ == 0)
{
lean_object* v___x_377_; lean_object* v___x_379_; 
lean_dec_ref(v___x_324_);
lean_dec_ref(v_arg_323_);
lean_dec_ref(v_arg_320_);
lean_dec_ref(v_arg_317_);
v___x_377_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 0, v___x_377_);
v___x_379_ = v___x_330_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v___x_377_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
else
{
lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
lean_del_object(v___x_330_);
v___x_381_ = lean_obj_once(&l_Lean_Meta_Grind_simpEq___redArg___closed__22, &l_Lean_Meta_Grind_simpEq___redArg___closed__22_once, _init_l_Lean_Meta_Grind_simpEq___redArg___closed__22);
lean_inc_ref(v_arg_320_);
lean_inc_ref(v_arg_323_);
lean_inc_ref(v___x_324_);
v___x_382_ = l_Lean_mkApp3(v___x_324_, v_arg_323_, v_arg_320_, v___x_381_);
lean_inc_ref(v_arg_317_);
v___x_383_ = l_Lean_mkApp3(v___x_324_, v_arg_323_, v_arg_317_, v___x_381_);
v___x_384_ = l_Lean_Meta_mkEq(v___x_382_, v___x_383_, v_a_300_, v_a_301_, v_a_302_, v_a_303_);
if (lean_obj_tag(v___x_384_) == 0)
{
lean_object* v_a_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_397_; 
v_a_385_ = lean_ctor_get(v___x_384_, 0);
v_isSharedCheck_397_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_397_ == 0)
{
v___x_387_ = v___x_384_;
v_isShared_388_ = v_isSharedCheck_397_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_a_385_);
lean_dec(v___x_384_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_397_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_395_; 
v___x_389_ = lean_obj_once(&l_Lean_Meta_Grind_simpEq___redArg___closed__25, &l_Lean_Meta_Grind_simpEq___redArg___closed__25_once, _init_l_Lean_Meta_Grind_simpEq___redArg___closed__25);
v___x_390_ = l_Lean_mkAppB(v___x_389_, v_arg_320_, v_arg_317_);
v___x_391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_391_, 0, v___x_390_);
v___x_392_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_392_, 0, v_a_385_);
lean_ctor_set(v___x_392_, 1, v___x_391_);
lean_ctor_set_uint8(v___x_392_, sizeof(void*)*2, v___x_334_);
v___x_393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_393_, 0, v___x_392_);
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 0, v___x_393_);
v___x_395_ = v___x_387_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v___x_393_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
}
else
{
lean_object* v_a_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_405_; 
lean_dec_ref(v_arg_320_);
lean_dec_ref(v_arg_317_);
v_a_398_ = lean_ctor_get(v___x_384_, 0);
v_isSharedCheck_405_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_405_ == 0)
{
v___x_400_ = v___x_384_;
v_isShared_401_ = v_isSharedCheck_405_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_a_398_);
lean_dec(v___x_384_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_405_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_403_; 
if (v_isShared_401_ == 0)
{
v___x_403_ = v___x_400_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_a_398_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
}
}
}
v___jp_406_:
{
if (v___y_408_ == 0)
{
uint8_t v___x_409_; 
v___x_409_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget(v___y_407_);
lean_dec(v___y_407_);
if (v___x_409_ == 0)
{
uint8_t v___x_410_; 
v___x_410_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget(v_declName_373_);
lean_dec(v_declName_373_);
v___y_376_ = v___x_410_;
goto v___jp_375_;
}
else
{
lean_dec(v_declName_373_);
v___y_376_ = v___x_409_;
goto v___jp_375_;
}
}
else
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
lean_dec(v___y_407_);
lean_dec(v_declName_373_);
lean_del_object(v___x_330_);
lean_inc_ref(v_arg_320_);
lean_inc_ref(v_arg_317_);
v___x_411_ = l_Lean_mkApp3(v___x_324_, v_arg_323_, v_arg_317_, v_arg_320_);
v___x_412_ = lean_obj_once(&l_Lean_Meta_Grind_simpEq___redArg___closed__28, &l_Lean_Meta_Grind_simpEq___redArg___closed__28_once, _init_l_Lean_Meta_Grind_simpEq___redArg___closed__28);
v___x_413_ = l_Lean_mkAppB(v___x_412_, v_arg_320_, v_arg_317_);
v___x_414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_414_, 0, v___x_413_);
v___x_415_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_415_, 0, v___x_411_);
lean_ctor_set(v___x_415_, 1, v___x_414_);
lean_ctor_set_uint8(v___x_415_, sizeof(void*)*2, v___x_334_);
v___x_416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_416_, 0, v___x_415_);
v___x_417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_417_, 0, v___x_416_);
return v___x_417_;
}
}
v___jp_418_:
{
if (v___y_419_ == 0)
{
lean_object* v___x_420_; 
v___x_420_ = l_Lean_Expr_getAppFn(v_arg_320_);
if (lean_obj_tag(v___x_420_) == 4)
{
lean_object* v_declName_421_; uint8_t v___x_422_; 
v_declName_421_ = lean_ctor_get(v___x_420_, 0);
lean_inc(v_declName_421_);
lean_dec_ref_known(v___x_420_, 2);
v___x_422_ = lean_name_eq(v_declName_421_, v___x_374_);
if (v___x_422_ == 0)
{
lean_object* v___x_423_; uint8_t v___x_424_; 
v___x_423_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__30));
v___x_424_ = lean_name_eq(v_declName_421_, v___x_423_);
v___y_407_ = v_declName_421_;
v___y_408_ = v___x_424_;
goto v___jp_406_;
}
else
{
v___y_407_ = v_declName_421_;
v___y_408_ = v___x_422_;
goto v___jp_406_;
}
}
else
{
lean_object* v___x_425_; lean_object* v___x_426_; 
lean_dec_ref(v___x_420_);
lean_dec(v_declName_373_);
lean_del_object(v___x_330_);
lean_dec_ref(v___x_324_);
lean_dec_ref(v_arg_323_);
lean_dec_ref(v_arg_320_);
lean_dec_ref(v_arg_317_);
v___x_425_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
v___x_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_426_, 0, v___x_425_);
return v___x_426_;
}
}
else
{
lean_object* v___x_427_; lean_object* v___x_428_; 
lean_dec(v_declName_373_);
lean_del_object(v___x_330_);
lean_dec_ref(v___x_324_);
lean_dec_ref(v_arg_323_);
lean_dec_ref(v_arg_320_);
lean_dec_ref(v_arg_317_);
v___x_427_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
v___x_428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_428_, 0, v___x_427_);
return v___x_428_;
}
}
}
else
{
lean_object* v___x_432_; lean_object* v___x_434_; 
lean_dec_ref(v___x_372_);
lean_dec_ref(v___x_324_);
lean_dec_ref(v_arg_323_);
lean_dec_ref(v_arg_320_);
lean_dec_ref(v_arg_317_);
v___x_432_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 0, v___x_432_);
v___x_434_ = v___x_330_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v___x_432_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
}
}
else
{
lean_object* v_a_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_444_; 
lean_dec_ref(v___x_324_);
lean_dec_ref(v_arg_323_);
lean_dec_ref(v_arg_320_);
lean_dec_ref(v_arg_317_);
v_a_437_ = lean_ctor_get(v___x_327_, 0);
v_isSharedCheck_444_ = !lean_is_exclusive(v___x_327_);
if (v_isSharedCheck_444_ == 0)
{
v___x_439_ = v___x_327_;
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_a_437_);
lean_dec(v___x_327_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_442_; 
if (v_isShared_440_ == 0)
{
v___x_442_ = v___x_439_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_a_437_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
}
}
}
}
v___jp_310_:
{
lean_object* v___x_311_; lean_object* v___x_313_; 
v___x_311_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 0, v___x_311_);
v___x_313_ = v___x_308_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v___x_311_);
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
else
{
lean_object* v_a_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_453_; 
v_a_446_ = lean_ctor_get(v___x_305_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_305_);
if (v_isSharedCheck_453_ == 0)
{
v___x_448_ = v___x_305_;
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_a_446_);
lean_dec(v___x_305_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_451_; 
if (v_isShared_449_ == 0)
{
v___x_451_ = v___x_448_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_a_446_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpEq___redArg___boxed(lean_object* v_e_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l_Lean_Meta_Grind_simpEq___redArg(v_e_454_, v_a_455_, v_a_456_, v_a_457_, v_a_458_);
lean_dec(v_a_458_);
lean_dec_ref(v_a_457_);
lean_dec(v_a_456_);
lean_dec_ref(v_a_455_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpEq(lean_object* v_e_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_){
_start:
{
lean_object* v___x_470_; 
v___x_470_ = l_Lean_Meta_Grind_simpEq___redArg(v_e_461_, v_a_465_, v_a_466_, v_a_467_, v_a_468_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpEq___boxed(lean_object* v_e_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Lean_Meta_Grind_simpEq(v_e_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_);
lean_dec(v_a_478_);
lean_dec_ref(v_a_477_);
lean_dec(v_a_476_);
lean_dec_ref(v_a_475_);
lean_dec(v_a_474_);
lean_dec_ref(v_a_473_);
lean_dec(v_a_472_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13_(){
_start:
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_500_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13_));
v___x_501_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__4_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13_));
v___x_502_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpEq___boxed), 9, 0);
v___x_503_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_500_, v___x_501_, v___x_502_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13____boxed(lean_object* v_a_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13_();
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpDIte___redArg(lean_object* v_e_515_, lean_object* v_a_516_){
_start:
{
lean_object* v___x_518_; 
v___x_518_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_515_, v_a_516_);
if (lean_obj_tag(v___x_518_) == 0)
{
lean_object* v_a_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_569_; 
v_a_519_ = lean_ctor_get(v___x_518_, 0);
v_isSharedCheck_569_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_569_ == 0)
{
v___x_521_ = v___x_518_;
v_isShared_522_ = v_isSharedCheck_569_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_a_519_);
lean_dec(v___x_518_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_569_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_528_; uint8_t v___x_529_; 
v___x_528_ = l_Lean_Expr_cleanupAnnotations(v_a_519_);
v___x_529_ = l_Lean_Expr_isApp(v___x_528_);
if (v___x_529_ == 0)
{
lean_dec_ref(v___x_528_);
goto v___jp_523_;
}
else
{
lean_object* v_arg_530_; lean_object* v___x_531_; uint8_t v___x_532_; 
v_arg_530_ = lean_ctor_get(v___x_528_, 1);
lean_inc_ref(v_arg_530_);
v___x_531_ = l_Lean_Expr_appFnCleanup___redArg(v___x_528_);
v___x_532_ = l_Lean_Expr_isApp(v___x_531_);
if (v___x_532_ == 0)
{
lean_dec_ref(v___x_531_);
lean_dec_ref(v_arg_530_);
goto v___jp_523_;
}
else
{
lean_object* v_arg_533_; lean_object* v___x_534_; uint8_t v___x_535_; 
v_arg_533_ = lean_ctor_get(v___x_531_, 1);
lean_inc_ref(v_arg_533_);
v___x_534_ = l_Lean_Expr_appFnCleanup___redArg(v___x_531_);
v___x_535_ = l_Lean_Expr_isApp(v___x_534_);
if (v___x_535_ == 0)
{
lean_dec_ref(v___x_534_);
lean_dec_ref(v_arg_533_);
lean_dec_ref(v_arg_530_);
goto v___jp_523_;
}
else
{
lean_object* v_arg_536_; lean_object* v___x_537_; uint8_t v___x_538_; 
v_arg_536_ = lean_ctor_get(v___x_534_, 1);
lean_inc_ref(v_arg_536_);
v___x_537_ = l_Lean_Expr_appFnCleanup___redArg(v___x_534_);
v___x_538_ = l_Lean_Expr_isApp(v___x_537_);
if (v___x_538_ == 0)
{
lean_dec_ref(v___x_537_);
lean_dec_ref(v_arg_536_);
lean_dec_ref(v_arg_533_);
lean_dec_ref(v_arg_530_);
goto v___jp_523_;
}
else
{
lean_object* v_arg_539_; lean_object* v___x_540_; uint8_t v___x_541_; 
v_arg_539_ = lean_ctor_get(v___x_537_, 1);
lean_inc_ref(v_arg_539_);
v___x_540_ = l_Lean_Expr_appFnCleanup___redArg(v___x_537_);
v___x_541_ = l_Lean_Expr_isApp(v___x_540_);
if (v___x_541_ == 0)
{
lean_dec_ref(v___x_540_);
lean_dec_ref(v_arg_539_);
lean_dec_ref(v_arg_536_);
lean_dec_ref(v_arg_533_);
lean_dec_ref(v_arg_530_);
goto v___jp_523_;
}
else
{
lean_object* v_arg_542_; lean_object* v___x_543_; lean_object* v___x_544_; uint8_t v___x_545_; 
v_arg_542_ = lean_ctor_get(v___x_540_, 1);
lean_inc_ref(v_arg_542_);
v___x_543_ = l_Lean_Expr_appFnCleanup___redArg(v___x_540_);
v___x_544_ = ((lean_object*)(l_Lean_Meta_Grind_simpDIte___redArg___closed__1));
v___x_545_ = l_Lean_Expr_isConstOf(v___x_543_, v___x_544_);
if (v___x_545_ == 0)
{
lean_dec_ref(v___x_543_);
lean_dec_ref(v_arg_542_);
lean_dec_ref(v_arg_539_);
lean_dec_ref(v_arg_536_);
lean_dec_ref(v_arg_533_);
lean_dec_ref(v_arg_530_);
goto v___jp_523_;
}
else
{
lean_del_object(v___x_521_);
if (lean_obj_tag(v_arg_533_) == 6)
{
lean_object* v_body_546_; uint8_t v___x_547_; 
v_body_546_ = lean_ctor_get(v_arg_533_, 2);
lean_inc_ref(v_body_546_);
lean_dec_ref_known(v_arg_533_, 3);
v___x_547_ = l_Lean_Expr_hasLooseBVars(v_body_546_);
if (v___x_547_ == 0)
{
if (lean_obj_tag(v_arg_530_) == 6)
{
lean_object* v_body_548_; uint8_t v___x_549_; 
v_body_548_ = lean_ctor_get(v_arg_530_, 2);
lean_inc_ref(v_body_548_);
lean_dec_ref_known(v_arg_530_, 3);
v___x_549_ = l_Lean_Expr_hasLooseBVars(v_body_548_);
if (v___x_549_ == 0)
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_550_ = l_Lean_Expr_constLevels_x21(v___x_543_);
lean_dec_ref(v___x_543_);
v___x_551_ = ((lean_object*)(l_Lean_Meta_Grind_simpDIte___redArg___closed__3));
lean_inc(v___x_550_);
v___x_552_ = l_Lean_mkConst(v___x_551_, v___x_550_);
lean_inc_ref(v_body_548_);
lean_inc_ref(v_body_546_);
lean_inc_ref(v_arg_536_);
lean_inc_ref(v_arg_539_);
lean_inc_ref(v_arg_542_);
v___x_553_ = l_Lean_mkApp5(v___x_552_, v_arg_542_, v_arg_539_, v_arg_536_, v_body_546_, v_body_548_);
v___x_554_ = ((lean_object*)(l_Lean_Meta_Grind_simpDIte___redArg___closed__5));
v___x_555_ = l_Lean_mkConst(v___x_554_, v___x_550_);
v___x_556_ = l_Lean_mkApp5(v___x_555_, v_arg_539_, v_arg_542_, v_body_546_, v_body_548_, v_arg_536_);
v___x_557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_557_, 0, v___x_556_);
v___x_558_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_558_, 0, v___x_553_);
lean_ctor_set(v___x_558_, 1, v___x_557_);
lean_ctor_set_uint8(v___x_558_, sizeof(void*)*2, v___x_545_);
v___x_559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_559_, 0, v___x_558_);
v___x_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_560_, 0, v___x_559_);
return v___x_560_;
}
else
{
lean_object* v___x_561_; lean_object* v___x_562_; 
lean_dec_ref(v_body_548_);
lean_dec_ref(v_body_546_);
lean_dec_ref(v___x_543_);
lean_dec_ref(v_arg_542_);
lean_dec_ref(v_arg_539_);
lean_dec_ref(v_arg_536_);
v___x_561_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
v___x_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_562_, 0, v___x_561_);
return v___x_562_;
}
}
else
{
lean_object* v___x_563_; lean_object* v___x_564_; 
lean_dec_ref(v_body_546_);
lean_dec_ref(v___x_543_);
lean_dec_ref(v_arg_542_);
lean_dec_ref(v_arg_539_);
lean_dec_ref(v_arg_536_);
lean_dec_ref(v_arg_530_);
v___x_563_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
v___x_564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_564_, 0, v___x_563_);
return v___x_564_;
}
}
else
{
lean_object* v___x_565_; lean_object* v___x_566_; 
lean_dec_ref(v_body_546_);
lean_dec_ref(v___x_543_);
lean_dec_ref(v_arg_542_);
lean_dec_ref(v_arg_539_);
lean_dec_ref(v_arg_536_);
lean_dec_ref(v_arg_530_);
v___x_565_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
v___x_566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_566_, 0, v___x_565_);
return v___x_566_;
}
}
else
{
lean_object* v___x_567_; lean_object* v___x_568_; 
lean_dec_ref(v___x_543_);
lean_dec_ref(v_arg_542_);
lean_dec_ref(v_arg_539_);
lean_dec_ref(v_arg_536_);
lean_dec_ref(v_arg_533_);
lean_dec_ref(v_arg_530_);
v___x_567_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
v___x_568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_568_, 0, v___x_567_);
return v___x_568_;
}
}
}
}
}
}
}
v___jp_523_:
{
lean_object* v___x_524_; lean_object* v___x_526_; 
v___x_524_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 0, v___x_524_);
v___x_526_ = v___x_521_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v___x_524_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
}
}
else
{
lean_object* v_a_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_577_; 
v_a_570_ = lean_ctor_get(v___x_518_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_577_ == 0)
{
v___x_572_ = v___x_518_;
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_a_570_);
lean_dec(v___x_518_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_575_; 
if (v_isShared_573_ == 0)
{
v___x_575_ = v___x_572_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v_a_570_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpDIte___redArg___boxed(lean_object* v_e_578_, lean_object* v_a_579_, lean_object* v_a_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_Lean_Meta_Grind_simpDIte___redArg(v_e_578_, v_a_579_);
lean_dec(v_a_579_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpDIte(lean_object* v_e_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = l_Lean_Meta_Grind_simpDIte___redArg(v_e_582_, v_a_587_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpDIte___boxed(lean_object* v_e_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Lean_Meta_Grind_simpDIte(v_e_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_);
lean_dec(v_a_599_);
lean_dec_ref(v_a_598_);
lean_dec(v_a_597_);
lean_dec_ref(v_a_596_);
lean_dec(v_a_595_);
lean_dec_ref(v_a_594_);
lean_dec(v_a_593_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_14_(){
_start:
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_622_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_14_));
v___x_623_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_14_));
v___x_624_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpDIte___boxed), 9, 0);
v___x_625_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_622_, v___x_623_, v___x_624_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_14____boxed(lean_object* v_a_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_14_();
return v_res_627_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__8(void){
_start:
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_644_ = lean_box(0);
v___x_645_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__7));
v___x_646_ = l_Lean_mkConst(v___x_645_, v___x_644_);
return v___x_646_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__18(void){
_start:
{
lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_663_ = lean_box(0);
v___x_664_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__17));
v___x_665_ = l_Lean_mkConst(v___x_664_, v___x_663_);
return v___x_665_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__23(void){
_start:
{
lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_672_ = lean_unsigned_to_nat(1u);
v___x_673_ = lean_nat_to_int(v___x_672_);
return v___x_673_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__24(void){
_start:
{
lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_674_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__23, &l_Lean_Meta_Grind_pushNot___redArg___closed__23_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__23);
v___x_675_ = l_Lean_mkIntLit(v___x_674_);
return v___x_675_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__27(void){
_start:
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_680_ = lean_box(0);
v___x_681_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__26));
v___x_682_ = l_Lean_mkConst(v___x_681_, v___x_680_);
return v___x_682_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__28(void){
_start:
{
lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_683_ = lean_unsigned_to_nat(0u);
v___x_684_ = l_Lean_Level_ofNat(v___x_683_);
return v___x_684_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__29(void){
_start:
{
lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_685_ = lean_unsigned_to_nat(1u);
v___x_686_ = l_Lean_Level_ofNat(v___x_685_);
return v___x_686_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__30(void){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_687_ = lean_unsigned_to_nat(1u);
v___x_688_ = l_Lean_mkNatLit(v___x_687_);
return v___x_688_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__32(void){
_start:
{
lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_692_ = lean_box(0);
v___x_693_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__31));
v___x_694_ = l_Lean_mkConst(v___x_693_, v___x_692_);
return v___x_694_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__33(void){
_start:
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_695_ = lean_box(0);
v___x_696_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__30));
v___x_697_ = l_Lean_mkConst(v___x_696_, v___x_695_);
return v___x_697_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__36(void){
_start:
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_702_ = lean_box(0);
v___x_703_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__35));
v___x_704_ = l_Lean_mkConst(v___x_703_, v___x_702_);
return v___x_704_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__39(void){
_start:
{
lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_709_ = lean_box(0);
v___x_710_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__38));
v___x_711_ = l_Lean_mkConst(v___x_710_, v___x_709_);
return v___x_711_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__42(void){
_start:
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_717_ = lean_box(0);
v___x_718_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__41));
v___x_719_ = l_Lean_mkConst(v___x_718_, v___x_717_);
return v___x_719_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__43(void){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_720_ = lean_box(0);
v___x_721_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__10));
v___x_722_ = l_Lean_mkConst(v___x_721_, v___x_720_);
return v___x_722_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__46(void){
_start:
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_728_ = lean_box(0);
v___x_729_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__45));
v___x_730_ = l_Lean_mkConst(v___x_729_, v___x_728_);
return v___x_730_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__47(void){
_start:
{
lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_731_ = lean_box(0);
v___x_732_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__12));
v___x_733_ = l_Lean_mkConst(v___x_732_, v___x_731_);
return v___x_733_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__50(void){
_start:
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_739_ = lean_box(0);
v___x_740_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__49));
v___x_741_ = l_Lean_mkConst(v___x_740_, v___x_739_);
return v___x_741_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__53(void){
_start:
{
lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_745_ = lean_unsigned_to_nat(0u);
v___x_746_ = l_Lean_mkBVar(v___x_745_);
return v___x_746_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__58(void){
_start:
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_757_ = lean_box(0);
v___x_758_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__57));
v___x_759_ = l_Lean_mkConst(v___x_758_, v___x_757_);
return v___x_759_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__61(void){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_765_ = lean_box(0);
v___x_766_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__60));
v___x_767_ = l_Lean_mkConst(v___x_766_, v___x_765_);
return v___x_767_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__62(void){
_start:
{
lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_768_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__61, &l_Lean_Meta_Grind_pushNot___redArg___closed__61_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__61);
v___x_769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_769_, 0, v___x_768_);
return v___x_769_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__65(void){
_start:
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_775_ = lean_box(0);
v___x_776_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__64));
v___x_777_ = l_Lean_mkConst(v___x_776_, v___x_775_);
return v___x_777_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNot___redArg___closed__66(void){
_start:
{
lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_778_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__65, &l_Lean_Meta_Grind_pushNot___redArg___closed__65_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__65);
v___x_779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_779_, 0, v___x_778_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNot___redArg(lean_object* v_e_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_){
_start:
{
lean_object* v___x_786_; 
lean_inc_ref(v_e_780_);
v___x_786_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_780_, v_a_782_);
if (lean_obj_tag(v___x_786_) == 0)
{
lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_1145_; 
v_a_787_ = lean_ctor_get(v___x_786_, 0);
v_isSharedCheck_1145_ = !lean_is_exclusive(v___x_786_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_789_ = v___x_786_;
v_isShared_790_ = v_isSharedCheck_1145_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v___x_786_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_1145_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_796_; uint8_t v___x_797_; 
v___x_796_ = l_Lean_Expr_cleanupAnnotations(v_a_787_);
v___x_797_ = l_Lean_Expr_isApp(v___x_796_);
if (v___x_797_ == 0)
{
lean_dec_ref(v___x_796_);
lean_dec_ref(v_e_780_);
goto v___jp_791_;
}
else
{
lean_object* v_arg_798_; lean_object* v___x_799_; lean_object* v___x_800_; uint8_t v___x_801_; lean_object* v___y_803_; lean_object* v___y_804_; lean_object* v___y_805_; uint8_t v___y_806_; lean_object* v___y_807_; lean_object* v___y_808_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___y_843_; lean_object* v___y_844_; lean_object* v___y_845_; uint8_t v___y_846_; lean_object* v___y_847_; lean_object* v___y_848_; lean_object* v___y_849_; lean_object* v___y_850_; uint8_t v___y_851_; lean_object* v___y_861_; lean_object* v___y_862_; lean_object* v___y_863_; lean_object* v___y_864_; 
v_arg_798_ = lean_ctor_get(v___x_796_, 1);
lean_inc_ref(v_arg_798_);
v___x_799_ = l_Lean_Expr_appFnCleanup___redArg(v___x_796_);
v___x_800_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__1));
v___x_801_ = l_Lean_Expr_isConstOf(v___x_799_, v___x_800_);
lean_dec_ref(v___x_799_);
if (v___x_801_ == 0)
{
lean_dec_ref(v_arg_798_);
lean_dec_ref(v_e_780_);
goto v___jp_791_;
}
else
{
lean_object* v___x_873_; 
lean_del_object(v___x_789_);
v___x_873_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_798_, v_a_782_);
if (lean_obj_tag(v___x_873_) == 0)
{
lean_object* v_a_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_1136_; 
v_a_874_ = lean_ctor_get(v___x_873_, 0);
v_isSharedCheck_1136_ = !lean_is_exclusive(v___x_873_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_876_ = v___x_873_;
v_isShared_877_ = v_isSharedCheck_1136_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_a_874_);
lean_dec(v___x_873_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_1136_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___x_878_; lean_object* v___x_879_; uint8_t v___x_880_; 
v___x_878_ = l_Lean_Expr_cleanupAnnotations(v_a_874_);
v___x_879_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__8));
v___x_880_ = l_Lean_Expr_isConstOf(v___x_878_, v___x_879_);
if (v___x_880_ == 0)
{
lean_object* v___x_881_; uint8_t v___x_882_; 
v___x_881_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__5));
v___x_882_ = l_Lean_Expr_isConstOf(v___x_878_, v___x_881_);
if (v___x_882_ == 0)
{
uint8_t v___x_883_; 
v___x_883_ = l_Lean_Expr_isApp(v___x_878_);
if (v___x_883_ == 0)
{
lean_dec_ref(v___x_878_);
lean_del_object(v___x_876_);
v___y_861_ = v_a_781_;
v___y_862_ = v_a_782_;
v___y_863_ = v_a_783_;
v___y_864_ = v_a_784_;
goto v___jp_860_;
}
else
{
lean_object* v_arg_884_; lean_object* v___x_885_; uint8_t v___x_886_; 
v_arg_884_ = lean_ctor_get(v___x_878_, 1);
lean_inc_ref(v_arg_884_);
v___x_885_ = l_Lean_Expr_appFnCleanup___redArg(v___x_878_);
v___x_886_ = l_Lean_Expr_isConstOf(v___x_885_, v___x_800_);
if (v___x_886_ == 0)
{
uint8_t v___x_887_; 
v___x_887_ = l_Lean_Expr_isApp(v___x_885_);
if (v___x_887_ == 0)
{
lean_dec_ref(v___x_885_);
lean_dec_ref(v_arg_884_);
lean_del_object(v___x_876_);
v___y_861_ = v_a_781_;
v___y_862_ = v_a_782_;
v___y_863_ = v_a_783_;
v___y_864_ = v_a_784_;
goto v___jp_860_;
}
else
{
lean_object* v_arg_888_; lean_object* v___x_889_; lean_object* v___x_890_; uint8_t v___x_891_; 
v_arg_888_ = lean_ctor_get(v___x_885_, 1);
lean_inc_ref(v_arg_888_);
v___x_889_ = l_Lean_Expr_appFnCleanup___redArg(v___x_885_);
v___x_890_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__3));
v___x_891_ = l_Lean_Expr_isConstOf(v___x_889_, v___x_890_);
if (v___x_891_ == 0)
{
lean_object* v___x_892_; uint8_t v___x_893_; 
v___x_892_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__10));
v___x_893_ = l_Lean_Expr_isConstOf(v___x_889_, v___x_892_);
if (v___x_893_ == 0)
{
lean_object* v___x_894_; uint8_t v___x_895_; 
v___x_894_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__12));
v___x_895_ = l_Lean_Expr_isConstOf(v___x_889_, v___x_894_);
if (v___x_895_ == 0)
{
uint8_t v___x_896_; 
v___x_896_ = l_Lean_Expr_isApp(v___x_889_);
if (v___x_896_ == 0)
{
lean_dec_ref(v___x_889_);
lean_dec_ref(v_arg_888_);
lean_dec_ref(v_arg_884_);
lean_del_object(v___x_876_);
v___y_861_ = v_a_781_;
v___y_862_ = v_a_782_;
v___y_863_ = v_a_783_;
v___y_864_ = v_a_784_;
goto v___jp_860_;
}
else
{
lean_object* v_arg_897_; lean_object* v___x_898_; lean_object* v___x_899_; uint8_t v___x_900_; 
v_arg_897_ = lean_ctor_get(v___x_889_, 1);
lean_inc_ref(v_arg_897_);
v___x_898_ = l_Lean_Expr_appFnCleanup___redArg(v___x_889_);
v___x_899_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__2));
v___x_900_ = l_Lean_Expr_isConstOf(v___x_898_, v___x_899_);
if (v___x_900_ == 0)
{
uint8_t v___x_901_; 
v___x_901_ = l_Lean_Expr_isApp(v___x_898_);
if (v___x_901_ == 0)
{
lean_dec_ref(v___x_898_);
lean_dec_ref(v_arg_897_);
lean_dec_ref(v_arg_888_);
lean_dec_ref(v_arg_884_);
lean_del_object(v___x_876_);
v___y_861_ = v_a_781_;
v___y_862_ = v_a_782_;
v___y_863_ = v_a_783_;
v___y_864_ = v_a_784_;
goto v___jp_860_;
}
else
{
lean_object* v_arg_902_; lean_object* v___x_903_; lean_object* v___x_904_; uint8_t v___x_905_; 
v_arg_902_ = lean_ctor_get(v___x_898_, 1);
lean_inc_ref(v_arg_902_);
v___x_903_ = l_Lean_Expr_appFnCleanup___redArg(v___x_898_);
v___x_904_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__15));
v___x_905_ = l_Lean_Expr_isConstOf(v___x_903_, v___x_904_);
if (v___x_905_ == 0)
{
uint8_t v___x_906_; 
v___x_906_ = l_Lean_Expr_isApp(v___x_903_);
if (v___x_906_ == 0)
{
lean_dec_ref(v___x_903_);
lean_dec_ref(v_arg_902_);
lean_dec_ref(v_arg_897_);
lean_dec_ref(v_arg_888_);
lean_dec_ref(v_arg_884_);
lean_del_object(v___x_876_);
v___y_861_ = v_a_781_;
v___y_862_ = v_a_782_;
v___y_863_ = v_a_783_;
v___y_864_ = v_a_784_;
goto v___jp_860_;
}
else
{
lean_object* v_arg_907_; lean_object* v___x_908_; lean_object* v___x_909_; uint8_t v___x_910_; 
v_arg_907_ = lean_ctor_get(v___x_903_, 1);
lean_inc_ref(v_arg_907_);
v___x_908_ = l_Lean_Expr_appFnCleanup___redArg(v___x_903_);
v___x_909_ = ((lean_object*)(l_Lean_Meta_Grind_simpDIte___redArg___closed__3));
v___x_910_ = l_Lean_Expr_isConstOf(v___x_908_, v___x_909_);
if (v___x_910_ == 0)
{
lean_dec_ref(v___x_908_);
lean_dec_ref(v_arg_907_);
lean_dec_ref(v_arg_902_);
lean_dec_ref(v_arg_897_);
lean_dec_ref(v_arg_888_);
lean_dec_ref(v_arg_884_);
lean_del_object(v___x_876_);
v___y_861_ = v_a_781_;
v___y_862_ = v_a_782_;
v___y_863_ = v_a_783_;
v___y_864_ = v_a_784_;
goto v___jp_860_;
}
else
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_920_; 
lean_dec_ref(v_e_780_);
lean_inc_ref(v_arg_888_);
v___x_911_ = l_Lean_mkNot(v_arg_888_);
lean_inc_ref(v_arg_884_);
v___x_912_ = l_Lean_mkNot(v_arg_884_);
lean_inc_ref(v_arg_897_);
lean_inc_ref(v_arg_902_);
v___x_913_ = l_Lean_mkApp5(v___x_908_, v_arg_907_, v_arg_902_, v_arg_897_, v___x_911_, v___x_912_);
v___x_914_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__18, &l_Lean_Meta_Grind_pushNot___redArg___closed__18_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__18);
v___x_915_ = l_Lean_mkApp4(v___x_914_, v_arg_902_, v_arg_897_, v_arg_888_, v_arg_884_);
v___x_916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_916_, 0, v___x_915_);
v___x_917_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_917_, 0, v___x_913_);
lean_ctor_set(v___x_917_, 1, v___x_916_);
lean_ctor_set_uint8(v___x_917_, sizeof(void*)*2, v___x_910_);
v___x_918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_918_, 0, v___x_917_);
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 0, v___x_918_);
v___x_920_ = v___x_876_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v___x_918_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
}
else
{
lean_object* v___x_922_; 
lean_dec_ref(v___x_903_);
lean_dec_ref(v_arg_897_);
lean_del_object(v___x_876_);
lean_dec_ref(v_e_780_);
v___x_922_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_902_, v_a_782_);
if (lean_obj_tag(v___x_922_) == 0)
{
lean_object* v_a_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_996_; 
v_a_923_ = lean_ctor_get(v___x_922_, 0);
v_isSharedCheck_996_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_996_ == 0)
{
v___x_925_ = v___x_922_;
v_isShared_926_ = v_isSharedCheck_996_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_a_923_);
lean_dec(v___x_922_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_996_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_927_; lean_object* v___x_928_; uint8_t v___x_929_; 
v___x_927_ = l_Lean_Expr_cleanupAnnotations(v_a_923_);
v___x_928_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__20));
v___x_929_ = l_Lean_Expr_isConstOf(v___x_927_, v___x_928_);
if (v___x_929_ == 0)
{
lean_object* v___x_930_; uint8_t v___x_931_; 
v___x_930_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__22));
v___x_931_ = l_Lean_Expr_isConstOf(v___x_927_, v___x_930_);
lean_dec_ref(v___x_927_);
if (v___x_931_ == 0)
{
lean_object* v___x_932_; lean_object* v___x_934_; 
lean_dec_ref(v_arg_888_);
lean_dec_ref(v_arg_884_);
v___x_932_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
if (v_isShared_926_ == 0)
{
lean_ctor_set(v___x_925_, 0, v___x_932_);
v___x_934_ = v___x_925_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v___x_932_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
else
{
lean_object* v___x_936_; 
lean_del_object(v___x_925_);
v___x_936_ = l_Lean_leCarrierIsSort(v_a_783_, v_a_784_);
if (lean_obj_tag(v___x_936_) == 0)
{
lean_object* v_a_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_957_; 
v_a_937_ = lean_ctor_get(v___x_936_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_957_ == 0)
{
v___x_939_ = v___x_936_;
v_isShared_940_ = v_isSharedCheck_957_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_a_937_);
lean_dec(v___x_936_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_957_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v_____do__lift_942_; uint8_t v___x_954_; 
v___x_954_ = lean_unbox(v_a_937_);
lean_dec(v_a_937_);
if (v___x_954_ == 0)
{
lean_object* v___x_955_; 
v___x_955_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__28, &l_Lean_Meta_Grind_pushNot___redArg___closed__28_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__28);
v_____do__lift_942_ = v___x_955_;
goto v___jp_941_;
}
else
{
lean_object* v___x_956_; 
v___x_956_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__29, &l_Lean_Meta_Grind_pushNot___redArg___closed__29_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__29);
v_____do__lift_942_ = v___x_956_;
goto v___jp_941_;
}
v___jp_941_:
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_952_; 
v___x_943_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__24, &l_Lean_Meta_Grind_pushNot___redArg___closed__24_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__24);
lean_inc_ref(v_arg_884_);
v___x_944_ = l_Lean_mkIntAdd(v_arg_884_, v___x_943_);
lean_inc_ref(v_arg_888_);
lean_inc(v_____do__lift_942_);
v___x_945_ = l_Lean_mkIntLE(v_____do__lift_942_, v___x_944_, v_arg_888_);
v___x_946_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__27, &l_Lean_Meta_Grind_pushNot___redArg___closed__27_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__27);
v___x_947_ = l_Lean_mkAppB(v___x_946_, v_arg_888_, v_arg_884_);
v___x_948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_948_, 0, v___x_947_);
v___x_949_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_949_, 0, v___x_945_);
lean_ctor_set(v___x_949_, 1, v___x_948_);
lean_ctor_set_uint8(v___x_949_, sizeof(void*)*2, v___x_931_);
v___x_950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_950_, 0, v___x_949_);
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 0, v___x_950_);
v___x_952_ = v___x_939_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v___x_950_);
v___x_952_ = v_reuseFailAlloc_953_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
return v___x_952_;
}
}
}
}
else
{
lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_965_; 
lean_dec_ref(v_arg_888_);
lean_dec_ref(v_arg_884_);
v_a_958_ = lean_ctor_get(v___x_936_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_965_ == 0)
{
v___x_960_ = v___x_936_;
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_a_958_);
lean_dec(v___x_936_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_963_; 
if (v_isShared_961_ == 0)
{
v___x_963_ = v___x_960_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_a_958_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
}
}
else
{
lean_object* v___x_966_; 
lean_dec_ref(v___x_927_);
lean_del_object(v___x_925_);
v___x_966_ = l_Lean_leCarrierIsSort(v_a_783_, v_a_784_);
if (lean_obj_tag(v___x_966_) == 0)
{
lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_987_; 
v_a_967_ = lean_ctor_get(v___x_966_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_987_ == 0)
{
v___x_969_ = v___x_966_;
v_isShared_970_ = v_isSharedCheck_987_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_dec(v___x_966_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_987_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v_____do__lift_972_; uint8_t v___x_984_; 
v___x_984_ = lean_unbox(v_a_967_);
lean_dec(v_a_967_);
if (v___x_984_ == 0)
{
lean_object* v___x_985_; 
v___x_985_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__28, &l_Lean_Meta_Grind_pushNot___redArg___closed__28_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__28);
v_____do__lift_972_ = v___x_985_;
goto v___jp_971_;
}
else
{
lean_object* v___x_986_; 
v___x_986_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__29, &l_Lean_Meta_Grind_pushNot___redArg___closed__29_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__29);
v_____do__lift_972_ = v___x_986_;
goto v___jp_971_;
}
v___jp_971_:
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_982_; 
v___x_973_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__30, &l_Lean_Meta_Grind_pushNot___redArg___closed__30_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__30);
lean_inc_ref(v_arg_884_);
v___x_974_ = l_Lean_mkNatAdd(v_arg_884_, v___x_973_);
lean_inc_ref(v_arg_888_);
lean_inc(v_____do__lift_972_);
v___x_975_ = l_Lean_mkNatLE(v_____do__lift_972_, v___x_974_, v_arg_888_);
v___x_976_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__32, &l_Lean_Meta_Grind_pushNot___redArg___closed__32_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__32);
v___x_977_ = l_Lean_mkAppB(v___x_976_, v_arg_888_, v_arg_884_);
v___x_978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_978_, 0, v___x_977_);
v___x_979_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_979_, 0, v___x_975_);
lean_ctor_set(v___x_979_, 1, v___x_978_);
lean_ctor_set_uint8(v___x_979_, sizeof(void*)*2, v___x_929_);
v___x_980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_980_, 0, v___x_979_);
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 0, v___x_980_);
v___x_982_ = v___x_969_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v___x_980_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
}
}
else
{
lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_995_; 
lean_dec_ref(v_arg_888_);
lean_dec_ref(v_arg_884_);
v_a_988_ = lean_ctor_get(v___x_966_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_995_ == 0)
{
v___x_990_ = v___x_966_;
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_dec(v___x_966_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_993_; 
if (v_isShared_991_ == 0)
{
v___x_993_ = v___x_990_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_a_988_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
}
}
else
{
lean_object* v_a_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1004_; 
lean_dec_ref(v_arg_888_);
lean_dec_ref(v_arg_884_);
v_a_997_ = lean_ctor_get(v___x_922_, 0);
v_isSharedCheck_1004_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_999_ = v___x_922_;
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_a_997_);
lean_dec(v___x_922_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1002_; 
if (v_isShared_1000_ == 0)
{
v___x_1002_ = v___x_999_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_a_997_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
}
}
}
}
else
{
uint8_t v___x_1005_; 
lean_dec_ref(v_e_780_);
v___x_1005_ = l_Lean_Expr_isProp(v_arg_897_);
if (v___x_1005_ == 0)
{
lean_object* v___x_1006_; 
lean_del_object(v___x_876_);
v___x_1006_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_884_, v_a_782_);
if (lean_obj_tag(v___x_1006_) == 0)
{
lean_object* v_a_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1040_; 
v_a_1007_ = lean_ctor_get(v___x_1006_, 0);
v_isSharedCheck_1040_ = !lean_is_exclusive(v___x_1006_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1009_ = v___x_1006_;
v_isShared_1010_ = v_isSharedCheck_1040_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_a_1007_);
lean_dec(v___x_1006_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1040_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; uint8_t v___x_1013_; 
v___x_1011_ = l_Lean_Expr_cleanupAnnotations(v_a_1007_);
v___x_1012_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__30));
v___x_1013_ = l_Lean_Expr_isConstOf(v___x_1011_, v___x_1012_);
if (v___x_1013_ == 0)
{
lean_object* v___x_1014_; uint8_t v___x_1015_; 
v___x_1014_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__21));
v___x_1015_ = l_Lean_Expr_isConstOf(v___x_1011_, v___x_1014_);
lean_dec_ref(v___x_1011_);
if (v___x_1015_ == 0)
{
lean_object* v___x_1016_; lean_object* v___x_1018_; 
lean_dec_ref(v___x_898_);
lean_dec_ref(v_arg_897_);
lean_dec_ref(v_arg_888_);
v___x_1016_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 0, v___x_1016_);
v___x_1018_ = v___x_1009_;
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
else
{
lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1028_; 
v___x_1020_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__33, &l_Lean_Meta_Grind_pushNot___redArg___closed__33_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__33);
lean_inc_ref(v_arg_888_);
v___x_1021_ = l_Lean_mkApp3(v___x_898_, v_arg_897_, v_arg_888_, v___x_1020_);
v___x_1022_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__36, &l_Lean_Meta_Grind_pushNot___redArg___closed__36_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__36);
v___x_1023_ = l_Lean_Expr_app___override(v___x_1022_, v_arg_888_);
v___x_1024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1023_);
v___x_1025_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1025_, 0, v___x_1021_);
lean_ctor_set(v___x_1025_, 1, v___x_1024_);
lean_ctor_set_uint8(v___x_1025_, sizeof(void*)*2, v___x_900_);
v___x_1026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1025_);
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 0, v___x_1026_);
v___x_1028_ = v___x_1009_;
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
lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1038_; 
lean_dec_ref(v___x_1011_);
v___x_1030_ = lean_obj_once(&l_Lean_Meta_Grind_simpEq___redArg___closed__22, &l_Lean_Meta_Grind_simpEq___redArg___closed__22_once, _init_l_Lean_Meta_Grind_simpEq___redArg___closed__22);
lean_inc_ref(v_arg_888_);
v___x_1031_ = l_Lean_mkApp3(v___x_898_, v_arg_897_, v_arg_888_, v___x_1030_);
v___x_1032_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__39, &l_Lean_Meta_Grind_pushNot___redArg___closed__39_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__39);
v___x_1033_ = l_Lean_Expr_app___override(v___x_1032_, v_arg_888_);
v___x_1034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1033_);
v___x_1035_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1035_, 0, v___x_1031_);
lean_ctor_set(v___x_1035_, 1, v___x_1034_);
lean_ctor_set_uint8(v___x_1035_, sizeof(void*)*2, v___x_900_);
v___x_1036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1035_);
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 0, v___x_1036_);
v___x_1038_ = v___x_1009_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v___x_1036_);
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
lean_dec_ref(v___x_898_);
lean_dec_ref(v_arg_897_);
lean_dec_ref(v_arg_888_);
v_a_1041_ = lean_ctor_get(v___x_1006_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_1006_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1043_ = v___x_1006_;
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_a_1041_);
lean_dec(v___x_1006_);
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
else
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1057_; 
lean_inc_ref(v_arg_884_);
v___x_1049_ = l_Lean_mkNot(v_arg_884_);
lean_inc_ref(v_arg_888_);
v___x_1050_ = l_Lean_mkApp3(v___x_898_, v_arg_897_, v_arg_888_, v___x_1049_);
v___x_1051_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__42, &l_Lean_Meta_Grind_pushNot___redArg___closed__42_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__42);
v___x_1052_ = l_Lean_mkAppB(v___x_1051_, v_arg_888_, v_arg_884_);
v___x_1053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1052_);
v___x_1054_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1054_, 0, v___x_1050_);
lean_ctor_set(v___x_1054_, 1, v___x_1053_);
lean_ctor_set_uint8(v___x_1054_, sizeof(void*)*2, v___x_900_);
v___x_1055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1054_);
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 0, v___x_1055_);
v___x_1057_ = v___x_876_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v___x_1055_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
}
else
{
lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1069_; 
lean_dec_ref(v___x_889_);
lean_dec_ref(v_e_780_);
v___x_1059_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__43, &l_Lean_Meta_Grind_pushNot___redArg___closed__43_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__43);
lean_inc_ref(v_arg_888_);
v___x_1060_ = l_Lean_mkNot(v_arg_888_);
lean_inc_ref(v_arg_884_);
v___x_1061_ = l_Lean_mkNot(v_arg_884_);
v___x_1062_ = l_Lean_mkAppB(v___x_1059_, v___x_1060_, v___x_1061_);
v___x_1063_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__46, &l_Lean_Meta_Grind_pushNot___redArg___closed__46_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__46);
v___x_1064_ = l_Lean_mkAppB(v___x_1063_, v_arg_888_, v_arg_884_);
v___x_1065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1064_);
v___x_1066_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1066_, 0, v___x_1062_);
lean_ctor_set(v___x_1066_, 1, v___x_1065_);
lean_ctor_set_uint8(v___x_1066_, sizeof(void*)*2, v___x_895_);
v___x_1067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1066_);
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 0, v___x_1067_);
v___x_1069_ = v___x_876_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1067_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
else
{
lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1081_; 
lean_dec_ref(v___x_889_);
lean_dec_ref(v_e_780_);
v___x_1071_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__47, &l_Lean_Meta_Grind_pushNot___redArg___closed__47_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__47);
lean_inc_ref(v_arg_888_);
v___x_1072_ = l_Lean_mkNot(v_arg_888_);
lean_inc_ref(v_arg_884_);
v___x_1073_ = l_Lean_mkNot(v_arg_884_);
v___x_1074_ = l_Lean_mkAppB(v___x_1071_, v___x_1072_, v___x_1073_);
v___x_1075_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__50, &l_Lean_Meta_Grind_pushNot___redArg___closed__50_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__50);
v___x_1076_ = l_Lean_mkAppB(v___x_1075_, v_arg_888_, v_arg_884_);
v___x_1077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1076_);
v___x_1078_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1078_, 0, v___x_1074_);
lean_ctor_set(v___x_1078_, 1, v___x_1077_);
lean_ctor_set_uint8(v___x_1078_, sizeof(void*)*2, v___x_893_);
v___x_1079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1078_);
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 0, v___x_1079_);
v___x_1081_ = v___x_876_;
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
}
else
{
lean_object* v___x_1083_; uint8_t v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; 
lean_dec_ref(v___x_889_);
lean_del_object(v___x_876_);
lean_dec_ref(v_e_780_);
v___x_1083_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__52));
v___x_1084_ = 0;
v___x_1085_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__53, &l_Lean_Meta_Grind_pushNot___redArg___closed__53_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__53);
lean_inc_ref(v_arg_884_);
v___x_1086_ = l_Lean_Expr_app___override(v_arg_884_, v___x_1085_);
v___x_1087_ = l_Lean_mkNot(v___x_1086_);
lean_inc_ref_n(v_arg_888_, 2);
v___x_1088_ = l_Lean_mkForall(v___x_1083_, v___x_1084_, v_arg_888_, v___x_1087_);
v___x_1089_ = l_Lean_Meta_getLevel(v_arg_888_, v_a_781_, v_a_782_, v_a_783_, v_a_784_);
if (lean_obj_tag(v___x_1089_) == 0)
{
lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1105_; 
v_a_1090_ = lean_ctor_get(v___x_1089_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1092_ = v___x_1089_;
v_isShared_1093_ = v_isSharedCheck_1105_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v___x_1089_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1105_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1103_; 
v___x_1094_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__55));
v___x_1095_ = lean_box(0);
v___x_1096_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1096_, 0, v_a_1090_);
lean_ctor_set(v___x_1096_, 1, v___x_1095_);
v___x_1097_ = l_Lean_mkConst(v___x_1094_, v___x_1096_);
v___x_1098_ = l_Lean_mkAppB(v___x_1097_, v_arg_888_, v_arg_884_);
v___x_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1098_);
v___x_1100_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1100_, 0, v___x_1088_);
lean_ctor_set(v___x_1100_, 1, v___x_1099_);
lean_ctor_set_uint8(v___x_1100_, sizeof(void*)*2, v___x_891_);
v___x_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1100_);
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 0, v___x_1101_);
v___x_1103_ = v___x_1092_;
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
else
{
lean_object* v_a_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1113_; 
lean_dec_ref(v___x_1088_);
lean_dec_ref(v_arg_888_);
lean_dec_ref(v_arg_884_);
v_a_1106_ = lean_ctor_get(v___x_1089_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1108_ = v___x_1089_;
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_a_1106_);
lean_dec(v___x_1089_);
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
lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1120_; 
lean_dec_ref(v___x_885_);
lean_dec_ref(v_e_780_);
v___x_1114_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__58, &l_Lean_Meta_Grind_pushNot___redArg___closed__58_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__58);
lean_inc_ref(v_arg_884_);
v___x_1115_ = l_Lean_Expr_app___override(v___x_1114_, v_arg_884_);
v___x_1116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1115_);
v___x_1117_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1117_, 0, v_arg_884_);
lean_ctor_set(v___x_1117_, 1, v___x_1116_);
lean_ctor_set_uint8(v___x_1117_, sizeof(void*)*2, v___x_886_);
v___x_1118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1117_);
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 0, v___x_1118_);
v___x_1120_ = v___x_876_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v___x_1118_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
}
}
else
{
lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1127_; 
lean_dec_ref(v___x_878_);
lean_dec_ref(v_e_780_);
v___x_1122_ = lean_obj_once(&l_Lean_Meta_Grind_simpEq___redArg___closed__9, &l_Lean_Meta_Grind_simpEq___redArg___closed__9_once, _init_l_Lean_Meta_Grind_simpEq___redArg___closed__9);
v___x_1123_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__62, &l_Lean_Meta_Grind_pushNot___redArg___closed__62_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__62);
v___x_1124_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1124_, 0, v___x_1122_);
lean_ctor_set(v___x_1124_, 1, v___x_1123_);
lean_ctor_set_uint8(v___x_1124_, sizeof(void*)*2, v___x_882_);
v___x_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1124_);
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 0, v___x_1125_);
v___x_1127_ = v___x_876_;
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
}
else
{
lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1134_; 
lean_dec_ref(v___x_878_);
lean_dec_ref(v_e_780_);
v___x_1129_ = lean_obj_once(&l_Lean_Meta_Grind_simpEq___redArg___closed__6, &l_Lean_Meta_Grind_simpEq___redArg___closed__6_once, _init_l_Lean_Meta_Grind_simpEq___redArg___closed__6);
v___x_1130_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__66, &l_Lean_Meta_Grind_pushNot___redArg___closed__66_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__66);
v___x_1131_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1131_, 0, v___x_1129_);
lean_ctor_set(v___x_1131_, 1, v___x_1130_);
lean_ctor_set_uint8(v___x_1131_, sizeof(void*)*2, v___x_880_);
v___x_1132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1131_);
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 0, v___x_1132_);
v___x_1134_ = v___x_876_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v___x_1132_);
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
else
{
lean_object* v_a_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1144_; 
lean_dec_ref(v_e_780_);
v_a_1137_ = lean_ctor_get(v___x_873_, 0);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_873_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1139_ = v___x_873_;
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_a_1137_);
lean_dec(v___x_873_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1142_; 
if (v_isShared_1140_ == 0)
{
v___x_1142_ = v___x_1139_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_a_1137_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
}
}
v___jp_802_:
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
lean_inc_ref(v___y_807_);
lean_inc_ref_n(v___y_810_, 3);
lean_inc(v___y_808_);
v___x_811_ = l_Lean_mkLambda(v___y_808_, v___y_806_, v___y_810_, v___y_807_);
v___x_812_ = l_Lean_mkNot(v___y_807_);
v___x_813_ = l_Lean_mkLambda(v___y_808_, v___y_806_, v___y_810_, v___x_812_);
v___x_814_ = l_Lean_Meta_getLevel(v___y_810_, v___y_809_, v___y_803_, v___y_805_, v___y_804_);
if (lean_obj_tag(v___x_814_) == 0)
{
lean_object* v_a_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_833_; 
v_a_815_ = lean_ctor_get(v___x_814_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_814_);
if (v_isSharedCheck_833_ == 0)
{
v___x_817_ = v___x_814_;
v_isShared_818_ = v_isSharedCheck_833_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_a_815_);
lean_dec(v___x_814_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_833_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_831_; 
v___x_819_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__3));
v___x_820_ = lean_box(0);
v___x_821_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_821_, 0, v_a_815_);
lean_ctor_set(v___x_821_, 1, v___x_820_);
lean_inc_ref(v___x_821_);
v___x_822_ = l_Lean_mkConst(v___x_819_, v___x_821_);
lean_inc_ref(v___y_810_);
v___x_823_ = l_Lean_mkAppB(v___x_822_, v___y_810_, v___x_813_);
v___x_824_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__5));
v___x_825_ = l_Lean_mkConst(v___x_824_, v___x_821_);
v___x_826_ = l_Lean_mkAppB(v___x_825_, v___y_810_, v___x_811_);
v___x_827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_827_, 0, v___x_826_);
v___x_828_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_828_, 0, v___x_823_);
lean_ctor_set(v___x_828_, 1, v___x_827_);
lean_ctor_set_uint8(v___x_828_, sizeof(void*)*2, v___x_801_);
v___x_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_829_, 0, v___x_828_);
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 0, v___x_829_);
v___x_831_ = v___x_817_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v___x_829_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
else
{
lean_object* v_a_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_841_; 
lean_dec_ref(v___x_813_);
lean_dec_ref(v___x_811_);
lean_dec_ref(v___y_810_);
v_a_834_ = lean_ctor_get(v___x_814_, 0);
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_814_);
if (v_isSharedCheck_841_ == 0)
{
v___x_836_ = v___x_814_;
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_a_834_);
lean_dec(v___x_814_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_839_; 
if (v_isShared_837_ == 0)
{
v___x_839_ = v___x_836_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_a_834_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
}
}
v___jp_842_:
{
if (v___y_851_ == 0)
{
v___y_803_ = v___y_843_;
v___y_804_ = v___y_844_;
v___y_805_ = v___y_845_;
v___y_806_ = v___y_846_;
v___y_807_ = v___y_848_;
v___y_808_ = v___y_847_;
v___y_809_ = v___y_850_;
v___y_810_ = v___y_849_;
goto v___jp_802_;
}
else
{
lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
lean_dec(v___y_847_);
lean_inc_ref(v___y_848_);
v___x_852_ = l_Lean_mkNot(v___y_848_);
lean_inc_ref(v___y_849_);
v___x_853_ = l_Lean_mkAnd(v___y_849_, v___x_852_);
v___x_854_ = lean_obj_once(&l_Lean_Meta_Grind_pushNot___redArg___closed__8, &l_Lean_Meta_Grind_pushNot___redArg___closed__8_once, _init_l_Lean_Meta_Grind_pushNot___redArg___closed__8);
v___x_855_ = l_Lean_mkAppB(v___x_854_, v___y_849_, v___y_848_);
v___x_856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_856_, 0, v___x_855_);
v___x_857_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_857_, 0, v___x_853_);
lean_ctor_set(v___x_857_, 1, v___x_856_);
lean_ctor_set_uint8(v___x_857_, sizeof(void*)*2, v___x_801_);
v___x_858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_858_, 0, v___x_857_);
v___x_859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_859_, 0, v___x_858_);
return v___x_859_;
}
}
v___jp_860_:
{
if (lean_obj_tag(v_e_780_) == 7)
{
lean_object* v_binderName_865_; lean_object* v_binderType_866_; lean_object* v_body_867_; uint8_t v_binderInfo_868_; uint8_t v___x_869_; 
v_binderName_865_ = lean_ctor_get(v_e_780_, 0);
lean_inc(v_binderName_865_);
v_binderType_866_ = lean_ctor_get(v_e_780_, 1);
lean_inc_ref(v_binderType_866_);
v_body_867_ = lean_ctor_get(v_e_780_, 2);
lean_inc_ref(v_body_867_);
v_binderInfo_868_ = lean_ctor_get_uint8(v_e_780_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_780_, 3);
v___x_869_ = l_Lean_Expr_isProp(v_binderType_866_);
if (v___x_869_ == 0)
{
v___y_843_ = v___y_862_;
v___y_844_ = v___y_864_;
v___y_845_ = v___y_863_;
v___y_846_ = v_binderInfo_868_;
v___y_847_ = v_binderName_865_;
v___y_848_ = v_body_867_;
v___y_849_ = v_binderType_866_;
v___y_850_ = v___y_861_;
v___y_851_ = v___x_869_;
goto v___jp_842_;
}
else
{
uint8_t v___x_870_; 
v___x_870_ = l_Lean_Expr_hasLooseBVars(v_body_867_);
if (v___x_870_ == 0)
{
v___y_843_ = v___y_862_;
v___y_844_ = v___y_864_;
v___y_845_ = v___y_863_;
v___y_846_ = v_binderInfo_868_;
v___y_847_ = v_binderName_865_;
v___y_848_ = v_body_867_;
v___y_849_ = v_binderType_866_;
v___y_850_ = v___y_861_;
v___y_851_ = v___x_869_;
goto v___jp_842_;
}
else
{
v___y_803_ = v___y_862_;
v___y_804_ = v___y_864_;
v___y_805_ = v___y_863_;
v___y_806_ = v_binderInfo_868_;
v___y_807_ = v_body_867_;
v___y_808_ = v_binderName_865_;
v___y_809_ = v___y_861_;
v___y_810_ = v_binderType_866_;
goto v___jp_802_;
}
}
}
else
{
lean_object* v___x_871_; lean_object* v___x_872_; 
lean_dec_ref(v_e_780_);
v___x_871_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
v___x_872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_872_, 0, v___x_871_);
return v___x_872_;
}
}
}
v___jp_791_:
{
lean_object* v___x_792_; lean_object* v___x_794_; 
v___x_792_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 0, v___x_792_);
v___x_794_ = v___x_789_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v___x_792_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
}
else
{
lean_object* v_a_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1153_; 
lean_dec_ref(v_e_780_);
v_a_1146_ = lean_ctor_get(v___x_786_, 0);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_786_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1148_ = v___x_786_;
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_a_1146_);
lean_dec(v___x_786_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1151_; 
if (v_isShared_1149_ == 0)
{
v___x_1151_ = v___x_1148_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_a_1146_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNot___redArg___boxed(lean_object* v_e_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_){
_start:
{
lean_object* v_res_1160_; 
v_res_1160_ = l_Lean_Meta_Grind_pushNot___redArg(v_e_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_);
lean_dec(v_a_1158_);
lean_dec_ref(v_a_1157_);
lean_dec(v_a_1156_);
lean_dec_ref(v_a_1155_);
return v_res_1160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNot(lean_object* v_e_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_){
_start:
{
lean_object* v___x_1170_; 
v___x_1170_ = l_Lean_Meta_Grind_pushNot___redArg(v_e_1161_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNot___boxed(lean_object* v_e_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_){
_start:
{
lean_object* v_res_1180_; 
v_res_1180_ = l_Lean_Meta_Grind_pushNot(v_e_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_);
lean_dec(v_a_1178_);
lean_dec_ref(v_a_1177_);
lean_dec(v_a_1176_);
lean_dec_ref(v_a_1175_);
lean_dec(v_a_1174_);
lean_dec_ref(v_a_1173_);
lean_dec(v_a_1172_);
return v_res_1180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3828017814____hygCtx___hyg_11_(){
_start:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1197_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3828017814____hygCtx___hyg_11_));
v___x_1198_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3828017814____hygCtx___hyg_11_));
v___x_1199_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_pushNot___boxed), 9, 0);
v___x_1200_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_1197_, v___x_1198_, v___x_1199_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3828017814____hygCtx___hyg_11____boxed(lean_object* v_a_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3828017814____hygCtx___hyg_11_();
return v_res_1202_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpOr___redArg___closed__2(void){
_start:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1208_ = lean_box(0);
v___x_1209_ = ((lean_object*)(l_Lean_Meta_Grind_simpOr___redArg___closed__1));
v___x_1210_ = l_Lean_mkConst(v___x_1209_, v___x_1208_);
return v___x_1210_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpOr___redArg___closed__5(void){
_start:
{
lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1216_ = lean_box(0);
v___x_1217_ = ((lean_object*)(l_Lean_Meta_Grind_simpOr___redArg___closed__4));
v___x_1218_ = l_Lean_mkConst(v___x_1217_, v___x_1216_);
return v___x_1218_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpOr___redArg___closed__8(void){
_start:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1222_ = lean_box(0);
v___x_1223_ = ((lean_object*)(l_Lean_Meta_Grind_simpOr___redArg___closed__7));
v___x_1224_ = l_Lean_mkConst(v___x_1223_, v___x_1222_);
return v___x_1224_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpOr___redArg___closed__11(void){
_start:
{
lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1228_ = lean_box(0);
v___x_1229_ = ((lean_object*)(l_Lean_Meta_Grind_simpOr___redArg___closed__10));
v___x_1230_ = l_Lean_mkConst(v___x_1229_, v___x_1228_);
return v___x_1230_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpOr___redArg___closed__14(void){
_start:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1236_ = lean_box(0);
v___x_1237_ = ((lean_object*)(l_Lean_Meta_Grind_simpOr___redArg___closed__13));
v___x_1238_ = l_Lean_mkConst(v___x_1237_, v___x_1236_);
return v___x_1238_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpOr___redArg___closed__17(void){
_start:
{
lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1242_ = lean_box(0);
v___x_1243_ = ((lean_object*)(l_Lean_Meta_Grind_simpOr___redArg___closed__16));
v___x_1244_ = l_Lean_mkConst(v___x_1243_, v___x_1242_);
return v___x_1244_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpOr___redArg___closed__20(void){
_start:
{
lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1248_ = lean_box(0);
v___x_1249_ = ((lean_object*)(l_Lean_Meta_Grind_simpOr___redArg___closed__19));
v___x_1250_ = l_Lean_mkConst(v___x_1249_, v___x_1248_);
return v___x_1250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpOr___redArg(lean_object* v_e_1251_, lean_object* v_a_1252_){
_start:
{
lean_object* v___x_1257_; 
v___x_1257_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1251_, v_a_1252_);
if (lean_obj_tag(v___x_1257_) == 0)
{
lean_object* v_a_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1404_; 
v_a_1258_ = lean_ctor_get(v___x_1257_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1260_ = v___x_1257_;
v_isShared_1261_ = v_isSharedCheck_1404_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_a_1258_);
lean_dec(v___x_1257_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1404_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v___x_1267_; uint8_t v___x_1268_; 
v___x_1267_ = l_Lean_Expr_cleanupAnnotations(v_a_1258_);
v___x_1268_ = l_Lean_Expr_isApp(v___x_1267_);
if (v___x_1268_ == 0)
{
lean_dec_ref(v___x_1267_);
goto v___jp_1262_;
}
else
{
lean_object* v_arg_1269_; lean_object* v___x_1270_; uint8_t v___x_1271_; 
v_arg_1269_ = lean_ctor_get(v___x_1267_, 1);
lean_inc_ref(v_arg_1269_);
v___x_1270_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1267_);
v___x_1271_ = l_Lean_Expr_isApp(v___x_1270_);
if (v___x_1271_ == 0)
{
lean_dec_ref(v___x_1270_);
lean_dec_ref(v_arg_1269_);
goto v___jp_1262_;
}
else
{
lean_object* v_arg_1272_; lean_object* v___y_1274_; lean_object* v___x_1349_; lean_object* v___x_1350_; uint8_t v___x_1351_; 
v_arg_1272_ = lean_ctor_get(v___x_1270_, 1);
lean_inc_ref(v_arg_1272_);
v___x_1349_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1270_);
v___x_1350_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__10));
v___x_1351_ = l_Lean_Expr_isConstOf(v___x_1349_, v___x_1350_);
lean_dec_ref(v___x_1349_);
if (v___x_1351_ == 0)
{
lean_dec_ref(v_arg_1272_);
lean_dec_ref(v_arg_1269_);
goto v___jp_1262_;
}
else
{
lean_object* v___x_1352_; 
lean_del_object(v___x_1260_);
lean_inc_ref(v_arg_1272_);
v___x_1352_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1272_, v_a_1252_);
if (lean_obj_tag(v___x_1352_) == 0)
{
lean_object* v_a_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1395_; 
v_a_1353_ = lean_ctor_get(v___x_1352_, 0);
v_isSharedCheck_1395_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1355_ = v___x_1352_;
v_isShared_1356_ = v_isSharedCheck_1395_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_a_1353_);
lean_dec(v___x_1352_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1395_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1357_; lean_object* v___x_1358_; uint8_t v___x_1359_; 
v___x_1357_ = l_Lean_Expr_cleanupAnnotations(v_a_1353_);
v___x_1358_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__8));
v___x_1359_ = l_Lean_Expr_isConstOf(v___x_1357_, v___x_1358_);
if (v___x_1359_ == 0)
{
lean_object* v___x_1360_; uint8_t v___x_1361_; 
v___x_1360_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__5));
v___x_1361_ = l_Lean_Expr_isConstOf(v___x_1357_, v___x_1360_);
if (v___x_1361_ == 0)
{
uint8_t v___x_1362_; 
v___x_1362_ = l_Lean_Expr_isApp(v___x_1357_);
if (v___x_1362_ == 0)
{
lean_dec_ref(v___x_1357_);
lean_del_object(v___x_1355_);
v___y_1274_ = v_a_1252_;
goto v___jp_1273_;
}
else
{
lean_object* v_arg_1363_; lean_object* v___x_1364_; uint8_t v___x_1365_; 
v_arg_1363_ = lean_ctor_get(v___x_1357_, 1);
lean_inc_ref(v_arg_1363_);
v___x_1364_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1357_);
v___x_1365_ = l_Lean_Expr_isApp(v___x_1364_);
if (v___x_1365_ == 0)
{
lean_dec_ref(v___x_1364_);
lean_dec_ref(v_arg_1363_);
lean_del_object(v___x_1355_);
v___y_1274_ = v_a_1252_;
goto v___jp_1273_;
}
else
{
lean_object* v_arg_1366_; lean_object* v___x_1367_; uint8_t v___x_1368_; 
v_arg_1366_ = lean_ctor_get(v___x_1364_, 1);
lean_inc_ref(v_arg_1366_);
v___x_1367_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1364_);
v___x_1368_ = l_Lean_Expr_isConstOf(v___x_1367_, v___x_1350_);
lean_dec_ref(v___x_1367_);
if (v___x_1368_ == 0)
{
lean_dec_ref(v_arg_1366_);
lean_dec_ref(v_arg_1363_);
lean_del_object(v___x_1355_);
v___y_1274_ = v_a_1252_;
goto v___jp_1273_;
}
else
{
lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1377_; 
lean_dec_ref(v_arg_1272_);
lean_inc_ref(v_arg_1269_);
lean_inc_ref(v_arg_1363_);
v___x_1369_ = l_Lean_mkOr(v_arg_1363_, v_arg_1269_);
lean_inc_ref(v_arg_1366_);
v___x_1370_ = l_Lean_mkOr(v_arg_1366_, v___x_1369_);
v___x_1371_ = lean_obj_once(&l_Lean_Meta_Grind_simpOr___redArg___closed__14, &l_Lean_Meta_Grind_simpOr___redArg___closed__14_once, _init_l_Lean_Meta_Grind_simpOr___redArg___closed__14);
v___x_1372_ = l_Lean_mkApp3(v___x_1371_, v_arg_1366_, v_arg_1363_, v_arg_1269_);
v___x_1373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1373_, 0, v___x_1372_);
v___x_1374_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1374_, 0, v___x_1370_);
lean_ctor_set(v___x_1374_, 1, v___x_1373_);
lean_ctor_set_uint8(v___x_1374_, sizeof(void*)*2, v___x_1368_);
v___x_1375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1374_);
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 0, v___x_1375_);
v___x_1377_ = v___x_1355_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v___x_1375_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
}
}
else
{
lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1385_; 
lean_dec_ref(v___x_1357_);
v___x_1379_ = lean_obj_once(&l_Lean_Meta_Grind_simpOr___redArg___closed__17, &l_Lean_Meta_Grind_simpOr___redArg___closed__17_once, _init_l_Lean_Meta_Grind_simpOr___redArg___closed__17);
v___x_1380_ = l_Lean_Expr_app___override(v___x_1379_, v_arg_1269_);
v___x_1381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1381_, 0, v___x_1380_);
v___x_1382_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1382_, 0, v_arg_1272_);
lean_ctor_set(v___x_1382_, 1, v___x_1381_);
lean_ctor_set_uint8(v___x_1382_, sizeof(void*)*2, v___x_1361_);
v___x_1383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1382_);
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 0, v___x_1383_);
v___x_1385_ = v___x_1355_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v___x_1383_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
}
else
{
lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1393_; 
lean_dec_ref(v___x_1357_);
lean_dec_ref(v_arg_1272_);
v___x_1387_ = lean_obj_once(&l_Lean_Meta_Grind_simpOr___redArg___closed__20, &l_Lean_Meta_Grind_simpOr___redArg___closed__20_once, _init_l_Lean_Meta_Grind_simpOr___redArg___closed__20);
lean_inc_ref(v_arg_1269_);
v___x_1388_ = l_Lean_Expr_app___override(v___x_1387_, v_arg_1269_);
v___x_1389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1388_);
v___x_1390_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1390_, 0, v_arg_1269_);
lean_ctor_set(v___x_1390_, 1, v___x_1389_);
lean_ctor_set_uint8(v___x_1390_, sizeof(void*)*2, v___x_1359_);
v___x_1391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1391_, 0, v___x_1390_);
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 0, v___x_1391_);
v___x_1393_ = v___x_1355_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v___x_1391_);
v___x_1393_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
return v___x_1393_;
}
}
}
}
else
{
lean_object* v_a_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1403_; 
lean_dec_ref(v_arg_1272_);
lean_dec_ref(v_arg_1269_);
v_a_1396_ = lean_ctor_get(v___x_1352_, 0);
v_isSharedCheck_1403_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1398_ = v___x_1352_;
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_a_1396_);
lean_dec(v___x_1352_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1401_; 
if (v_isShared_1399_ == 0)
{
v___x_1401_ = v___x_1398_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v_a_1396_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
}
}
v___jp_1273_:
{
lean_object* v___x_1275_; 
lean_inc_ref(v_arg_1269_);
v___x_1275_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1269_, v___y_1274_);
if (lean_obj_tag(v___x_1275_) == 0)
{
lean_object* v_a_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1340_; 
v_a_1276_ = lean_ctor_get(v___x_1275_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1278_ = v___x_1275_;
v_isShared_1279_ = v_isSharedCheck_1340_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_a_1276_);
lean_dec(v___x_1275_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1340_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; uint8_t v___x_1282_; 
v___x_1280_ = l_Lean_Expr_cleanupAnnotations(v_a_1276_);
v___x_1281_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__8));
v___x_1282_ = l_Lean_Expr_isConstOf(v___x_1280_, v___x_1281_);
if (v___x_1282_ == 0)
{
lean_object* v___x_1283_; uint8_t v___x_1284_; 
v___x_1283_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__5));
v___x_1284_ = l_Lean_Expr_isConstOf(v___x_1280_, v___x_1283_);
if (v___x_1284_ == 0)
{
uint8_t v___x_1285_; 
lean_dec_ref(v_arg_1269_);
v___x_1285_ = l_Lean_Expr_isApp(v___x_1280_);
if (v___x_1285_ == 0)
{
lean_dec_ref(v___x_1280_);
lean_del_object(v___x_1278_);
lean_dec_ref(v_arg_1272_);
goto v___jp_1254_;
}
else
{
lean_object* v_arg_1286_; lean_object* v___x_1287_; uint8_t v___x_1288_; 
v_arg_1286_ = lean_ctor_get(v___x_1280_, 1);
lean_inc_ref(v_arg_1286_);
v___x_1287_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1280_);
v___x_1288_ = l_Lean_Expr_isApp(v___x_1287_);
if (v___x_1288_ == 0)
{
lean_dec_ref(v___x_1287_);
lean_dec_ref(v_arg_1286_);
lean_del_object(v___x_1278_);
lean_dec_ref(v_arg_1272_);
goto v___jp_1254_;
}
else
{
lean_object* v_arg_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; uint8_t v___x_1292_; 
v_arg_1289_ = lean_ctor_get(v___x_1287_, 1);
lean_inc_ref(v_arg_1289_);
v___x_1290_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1287_);
v___x_1291_ = ((lean_object*)(l_Lean_Meta_Grind_pushNot___redArg___closed__10));
v___x_1292_ = l_Lean_Expr_isConstOf(v___x_1290_, v___x_1291_);
lean_dec_ref(v___x_1290_);
if (v___x_1292_ == 0)
{
lean_dec_ref(v_arg_1289_);
lean_dec_ref(v_arg_1286_);
lean_del_object(v___x_1278_);
lean_dec_ref(v_arg_1272_);
goto v___jp_1254_;
}
else
{
uint8_t v___x_1293_; 
v___x_1293_ = l_Lean_Expr_isForall(v_arg_1272_);
if (v___x_1293_ == 0)
{
uint8_t v___x_1294_; 
v___x_1294_ = l_Lean_Expr_isForall(v_arg_1289_);
if (v___x_1294_ == 0)
{
uint8_t v___x_1295_; 
v___x_1295_ = l_Lean_Expr_isForall(v_arg_1286_);
if (v___x_1295_ == 0)
{
lean_object* v___x_1296_; lean_object* v___x_1298_; 
lean_dec_ref(v_arg_1289_);
lean_dec_ref(v_arg_1286_);
lean_dec_ref(v_arg_1272_);
v___x_1296_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 0, v___x_1296_);
v___x_1298_ = v___x_1278_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v___x_1296_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
return v___x_1298_;
}
}
else
{
lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1308_; 
lean_inc_ref(v_arg_1272_);
lean_inc_ref(v_arg_1289_);
v___x_1300_ = l_Lean_mkOr(v_arg_1289_, v_arg_1272_);
lean_inc_ref(v_arg_1286_);
v___x_1301_ = l_Lean_mkOr(v_arg_1286_, v___x_1300_);
v___x_1302_ = lean_obj_once(&l_Lean_Meta_Grind_simpOr___redArg___closed__2, &l_Lean_Meta_Grind_simpOr___redArg___closed__2_once, _init_l_Lean_Meta_Grind_simpOr___redArg___closed__2);
v___x_1303_ = l_Lean_mkApp3(v___x_1302_, v_arg_1272_, v_arg_1289_, v_arg_1286_);
v___x_1304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1303_);
v___x_1305_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1305_, 0, v___x_1301_);
lean_ctor_set(v___x_1305_, 1, v___x_1304_);
lean_ctor_set_uint8(v___x_1305_, sizeof(void*)*2, v___x_1292_);
v___x_1306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1305_);
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 0, v___x_1306_);
v___x_1308_ = v___x_1278_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v___x_1306_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
}
else
{
lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1318_; 
lean_inc_ref(v_arg_1286_);
lean_inc_ref(v_arg_1272_);
v___x_1310_ = l_Lean_mkOr(v_arg_1272_, v_arg_1286_);
lean_inc_ref(v_arg_1289_);
v___x_1311_ = l_Lean_mkOr(v_arg_1289_, v___x_1310_);
v___x_1312_ = lean_obj_once(&l_Lean_Meta_Grind_simpOr___redArg___closed__5, &l_Lean_Meta_Grind_simpOr___redArg___closed__5_once, _init_l_Lean_Meta_Grind_simpOr___redArg___closed__5);
v___x_1313_ = l_Lean_mkApp3(v___x_1312_, v_arg_1272_, v_arg_1289_, v_arg_1286_);
v___x_1314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1314_, 0, v___x_1313_);
v___x_1315_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1315_, 0, v___x_1311_);
lean_ctor_set(v___x_1315_, 1, v___x_1314_);
lean_ctor_set_uint8(v___x_1315_, sizeof(void*)*2, v___x_1292_);
v___x_1316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1316_, 0, v___x_1315_);
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 0, v___x_1316_);
v___x_1318_ = v___x_1278_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v___x_1316_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
}
else
{
lean_object* v___x_1320_; lean_object* v___x_1322_; 
lean_dec_ref(v_arg_1289_);
lean_dec_ref(v_arg_1286_);
lean_dec_ref(v_arg_1272_);
v___x_1320_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 0, v___x_1320_);
v___x_1322_ = v___x_1278_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v___x_1320_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
}
}
}
else
{
lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1330_; 
lean_dec_ref(v___x_1280_);
v___x_1324_ = lean_obj_once(&l_Lean_Meta_Grind_simpOr___redArg___closed__8, &l_Lean_Meta_Grind_simpOr___redArg___closed__8_once, _init_l_Lean_Meta_Grind_simpOr___redArg___closed__8);
v___x_1325_ = l_Lean_Expr_app___override(v___x_1324_, v_arg_1272_);
v___x_1326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1326_, 0, v___x_1325_);
v___x_1327_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1327_, 0, v_arg_1269_);
lean_ctor_set(v___x_1327_, 1, v___x_1326_);
lean_ctor_set_uint8(v___x_1327_, sizeof(void*)*2, v___x_1284_);
v___x_1328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1327_);
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 0, v___x_1328_);
v___x_1330_ = v___x_1278_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v___x_1328_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
else
{
lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1338_; 
lean_dec_ref(v___x_1280_);
lean_dec_ref(v_arg_1269_);
v___x_1332_ = lean_obj_once(&l_Lean_Meta_Grind_simpOr___redArg___closed__11, &l_Lean_Meta_Grind_simpOr___redArg___closed__11_once, _init_l_Lean_Meta_Grind_simpOr___redArg___closed__11);
lean_inc_ref(v_arg_1272_);
v___x_1333_ = l_Lean_Expr_app___override(v___x_1332_, v_arg_1272_);
v___x_1334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1333_);
v___x_1335_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1335_, 0, v_arg_1272_);
lean_ctor_set(v___x_1335_, 1, v___x_1334_);
lean_ctor_set_uint8(v___x_1335_, sizeof(void*)*2, v___x_1282_);
v___x_1336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1336_, 0, v___x_1335_);
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 0, v___x_1336_);
v___x_1338_ = v___x_1278_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v___x_1336_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
}
}
else
{
lean_object* v_a_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1348_; 
lean_dec_ref(v_arg_1272_);
lean_dec_ref(v_arg_1269_);
v_a_1341_ = lean_ctor_get(v___x_1275_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1343_ = v___x_1275_;
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_a_1341_);
lean_dec(v___x_1275_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___x_1346_; 
if (v_isShared_1344_ == 0)
{
v___x_1346_ = v___x_1343_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_a_1341_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
return v___x_1346_;
}
}
}
}
}
}
v___jp_1262_:
{
lean_object* v___x_1263_; lean_object* v___x_1265_; 
v___x_1263_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
if (v_isShared_1261_ == 0)
{
lean_ctor_set(v___x_1260_, 0, v___x_1263_);
v___x_1265_ = v___x_1260_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v___x_1263_);
v___x_1265_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
return v___x_1265_;
}
}
}
}
else
{
lean_object* v_a_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1412_; 
v_a_1405_ = lean_ctor_get(v___x_1257_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1407_ = v___x_1257_;
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_a_1405_);
lean_dec(v___x_1257_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1410_; 
if (v_isShared_1408_ == 0)
{
v___x_1410_ = v___x_1407_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_a_1405_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
v___jp_1254_:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1255_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
v___x_1256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1255_);
return v___x_1256_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpOr___redArg___boxed(lean_object* v_e_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l_Lean_Meta_Grind_simpOr___redArg(v_e_1413_, v_a_1414_);
lean_dec(v_a_1414_);
return v_res_1416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpOr(lean_object* v_e_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_){
_start:
{
lean_object* v___x_1426_; 
v___x_1426_ = l_Lean_Meta_Grind_simpOr___redArg(v_e_1417_, v_a_1422_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpOr___boxed(lean_object* v_e_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_){
_start:
{
lean_object* v_res_1436_; 
v_res_1436_ = l_Lean_Meta_Grind_simpOr(v_e_1427_, v_a_1428_, v_a_1429_, v_a_1430_, v_a_1431_, v_a_1432_, v_a_1433_, v_a_1434_);
lean_dec(v_a_1434_);
lean_dec_ref(v_a_1433_);
lean_dec(v_a_1432_);
lean_dec_ref(v_a_1431_);
lean_dec(v_a_1430_);
lean_dec_ref(v_a_1429_);
lean_dec(v_a_1428_);
return v_res_1436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_12_(){
_start:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1454_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_12_));
v___x_1455_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_12_));
v___x_1456_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpOr___boxed), 9, 0);
v___x_1457_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_1454_, v___x_1455_, v___x_1456_);
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_12____boxed(lean_object* v_a_1458_){
_start:
{
lean_object* v_res_1459_; 
v_res_1459_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_12_();
return v_res_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reduceCtorEqCheap___lam__0(uint8_t v___x_1460_, uint8_t v___x_1461_, lean_object* v_h_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_){
_start:
{
lean_object* v___x_1471_; lean_object* v_a_1473_; lean_object* v___x_1478_; 
v___x_1471_ = lean_obj_once(&l_Lean_Meta_Grind_simpEq___redArg___closed__9, &l_Lean_Meta_Grind_simpEq___redArg___closed__9_once, _init_l_Lean_Meta_Grind_simpEq___redArg___closed__9);
lean_inc_ref(v_h_1462_);
v___x_1478_ = l_Lean_Meta_mkNoConfusion(v___x_1471_, v_h_1462_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
if (lean_obj_tag(v___x_1478_) == 0)
{
lean_object* v_a_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; uint8_t v___x_1483_; lean_object* v___x_1484_; 
v_a_1479_ = lean_ctor_get(v___x_1478_, 0);
lean_inc(v_a_1479_);
lean_dec_ref_known(v___x_1478_, 1);
v___x_1480_ = lean_unsigned_to_nat(1u);
v___x_1481_ = lean_mk_empty_array_with_capacity(v___x_1480_);
v___x_1482_ = lean_array_push(v___x_1481_, v_h_1462_);
v___x_1483_ = 1;
v___x_1484_ = l_Lean_Meta_mkLambdaFVars(v___x_1482_, v_a_1479_, v___x_1460_, v___x_1461_, v___x_1460_, v___x_1461_, v___x_1483_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
lean_dec_ref(v___x_1482_);
if (lean_obj_tag(v___x_1484_) == 0)
{
lean_object* v_a_1485_; lean_object* v_keyedConfig_1486_; uint8_t v_trackZetaDelta_1487_; lean_object* v_zetaDeltaSet_1488_; lean_object* v_lctx_1489_; lean_object* v_localInstances_1490_; lean_object* v_defEqCtx_x3f_1491_; lean_object* v_synthPendingDepth_1492_; lean_object* v_customCanUnfoldPredicate_x3f_1493_; uint8_t v_univApprox_1494_; uint8_t v_inTypeClassResolution_1495_; uint8_t v_cacheInferType_1496_; uint8_t v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; 
v_a_1485_ = lean_ctor_get(v___x_1484_, 0);
lean_inc(v_a_1485_);
lean_dec_ref_known(v___x_1484_, 1);
v_keyedConfig_1486_ = lean_ctor_get(v___y_1466_, 0);
v_trackZetaDelta_1487_ = lean_ctor_get_uint8(v___y_1466_, sizeof(void*)*7);
v_zetaDeltaSet_1488_ = lean_ctor_get(v___y_1466_, 1);
v_lctx_1489_ = lean_ctor_get(v___y_1466_, 2);
v_localInstances_1490_ = lean_ctor_get(v___y_1466_, 3);
v_defEqCtx_x3f_1491_ = lean_ctor_get(v___y_1466_, 4);
v_synthPendingDepth_1492_ = lean_ctor_get(v___y_1466_, 5);
v_customCanUnfoldPredicate_x3f_1493_ = lean_ctor_get(v___y_1466_, 6);
v_univApprox_1494_ = lean_ctor_get_uint8(v___y_1466_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1495_ = lean_ctor_get_uint8(v___y_1466_, sizeof(void*)*7 + 2);
v_cacheInferType_1496_ = lean_ctor_get_uint8(v___y_1466_, sizeof(void*)*7 + 3);
v___x_1497_ = 1;
lean_inc_ref(v_keyedConfig_1486_);
v___x_1498_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_1497_, v_keyedConfig_1486_);
lean_inc(v_customCanUnfoldPredicate_x3f_1493_);
lean_inc(v_synthPendingDepth_1492_);
lean_inc(v_defEqCtx_x3f_1491_);
lean_inc_ref(v_localInstances_1490_);
lean_inc_ref(v_lctx_1489_);
lean_inc(v_zetaDeltaSet_1488_);
v___x_1499_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1499_, 0, v___x_1498_);
lean_ctor_set(v___x_1499_, 1, v_zetaDeltaSet_1488_);
lean_ctor_set(v___x_1499_, 2, v_lctx_1489_);
lean_ctor_set(v___x_1499_, 3, v_localInstances_1490_);
lean_ctor_set(v___x_1499_, 4, v_defEqCtx_x3f_1491_);
lean_ctor_set(v___x_1499_, 5, v_synthPendingDepth_1492_);
lean_ctor_set(v___x_1499_, 6, v_customCanUnfoldPredicate_x3f_1493_);
lean_ctor_set_uint8(v___x_1499_, sizeof(void*)*7, v_trackZetaDelta_1487_);
lean_ctor_set_uint8(v___x_1499_, sizeof(void*)*7 + 1, v_univApprox_1494_);
lean_ctor_set_uint8(v___x_1499_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1495_);
lean_ctor_set_uint8(v___x_1499_, sizeof(void*)*7 + 3, v_cacheInferType_1496_);
v___x_1500_ = l_Lean_Meta_mkEqFalse_x27(v_a_1485_, v___x_1499_, v___y_1467_, v___y_1468_, v___y_1469_);
lean_dec_ref_known(v___x_1499_, 7);
if (lean_obj_tag(v___x_1500_) == 0)
{
lean_object* v_a_1501_; 
v_a_1501_ = lean_ctor_get(v___x_1500_, 0);
lean_inc(v_a_1501_);
lean_dec_ref_known(v___x_1500_, 1);
v_a_1473_ = v_a_1501_;
goto v___jp_1472_;
}
else
{
if (lean_obj_tag(v___x_1500_) == 0)
{
lean_object* v_a_1502_; 
v_a_1502_ = lean_ctor_get(v___x_1500_, 0);
lean_inc(v_a_1502_);
lean_dec_ref_known(v___x_1500_, 1);
v_a_1473_ = v_a_1502_;
goto v___jp_1472_;
}
else
{
lean_object* v_a_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1510_; 
v_a_1503_ = lean_ctor_get(v___x_1500_, 0);
v_isSharedCheck_1510_ = !lean_is_exclusive(v___x_1500_);
if (v_isSharedCheck_1510_ == 0)
{
v___x_1505_ = v___x_1500_;
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_a_1503_);
lean_dec(v___x_1500_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v___x_1508_; 
if (v_isShared_1506_ == 0)
{
v___x_1508_ = v___x_1505_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v_a_1503_);
v___x_1508_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
return v___x_1508_;
}
}
}
}
}
else
{
lean_object* v_a_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1518_; 
v_a_1511_ = lean_ctor_get(v___x_1484_, 0);
v_isSharedCheck_1518_ = !lean_is_exclusive(v___x_1484_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1513_ = v___x_1484_;
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_a_1511_);
lean_dec(v___x_1484_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v___x_1516_; 
if (v_isShared_1514_ == 0)
{
v___x_1516_ = v___x_1513_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_a_1511_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
return v___x_1516_;
}
}
}
}
else
{
lean_object* v_a_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1526_; 
lean_dec_ref(v_h_1462_);
v_a_1519_ = lean_ctor_get(v___x_1478_, 0);
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1521_ = v___x_1478_;
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_a_1519_);
lean_dec(v___x_1478_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1524_; 
if (v_isShared_1522_ == 0)
{
v___x_1524_ = v___x_1521_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_a_1519_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
return v___x_1524_;
}
}
}
v___jp_1472_:
{
lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; 
v___x_1474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1474_, 0, v_a_1473_);
v___x_1475_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1475_, 0, v___x_1471_);
lean_ctor_set(v___x_1475_, 1, v___x_1474_);
lean_ctor_set_uint8(v___x_1475_, sizeof(void*)*2, v___x_1461_);
v___x_1476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1476_, 0, v___x_1475_);
v___x_1477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1477_, 0, v___x_1476_);
return v___x_1477_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reduceCtorEqCheap___lam__0___boxed(lean_object* v___x_1527_, lean_object* v___x_1528_, lean_object* v_h_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_){
_start:
{
uint8_t v___x_15310__boxed_1538_; uint8_t v___x_15311__boxed_1539_; lean_object* v_res_1540_; 
v___x_15310__boxed_1538_ = lean_unbox(v___x_1527_);
v___x_15311__boxed_1539_ = lean_unbox(v___x_1528_);
v_res_1540_ = l_Lean_Meta_Grind_reduceCtorEqCheap___lam__0(v___x_15310__boxed_1538_, v___x_15311__boxed_1539_, v_h_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
lean_dec(v___y_1536_);
lean_dec_ref(v___y_1535_);
lean_dec(v___y_1534_);
lean_dec_ref(v___y_1533_);
lean_dec(v___y_1532_);
lean_dec_ref(v___y_1531_);
lean_dec(v___y_1530_);
return v_res_1540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___redArg___lam__0(lean_object* v_k_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v_b_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_){
_start:
{
lean_object* v___x_1551_; 
lean_inc(v___y_1549_);
lean_inc_ref(v___y_1548_);
lean_inc(v___y_1547_);
lean_inc_ref(v___y_1546_);
lean_inc(v___y_1544_);
lean_inc_ref(v___y_1543_);
lean_inc(v___y_1542_);
v___x_1551_ = lean_apply_9(v_k_1541_, v_b_1545_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, lean_box(0));
return v___x_1551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v_b_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_){
_start:
{
lean_object* v_res_1562_; 
v_res_1562_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___redArg___lam__0(v_k_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v_b_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_);
lean_dec(v___y_1560_);
lean_dec_ref(v___y_1559_);
lean_dec(v___y_1558_);
lean_dec_ref(v___y_1557_);
lean_dec(v___y_1555_);
lean_dec_ref(v___y_1554_);
lean_dec(v___y_1553_);
return v_res_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___redArg(lean_object* v_name_1563_, uint8_t v_bi_1564_, lean_object* v_type_1565_, lean_object* v_k_1566_, uint8_t v_kind_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_){
_start:
{
lean_object* v___f_1576_; lean_object* v___x_1577_; 
lean_inc(v___y_1570_);
lean_inc_ref(v___y_1569_);
lean_inc(v___y_1568_);
v___f_1576_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1576_, 0, v_k_1566_);
lean_closure_set(v___f_1576_, 1, v___y_1568_);
lean_closure_set(v___f_1576_, 2, v___y_1569_);
lean_closure_set(v___f_1576_, 3, v___y_1570_);
v___x_1577_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1563_, v_bi_1564_, v_type_1565_, v___f_1576_, v_kind_1567_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_);
if (lean_obj_tag(v___x_1577_) == 0)
{
return v___x_1577_;
}
else
{
lean_object* v_a_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1585_; 
v_a_1578_ = lean_ctor_get(v___x_1577_, 0);
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1577_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1580_ = v___x_1577_;
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_a_1578_);
lean_dec(v___x_1577_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v___x_1583_; 
if (v_isShared_1581_ == 0)
{
v___x_1583_ = v___x_1580_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v_a_1578_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___redArg___boxed(lean_object* v_name_1586_, lean_object* v_bi_1587_, lean_object* v_type_1588_, lean_object* v_k_1589_, lean_object* v_kind_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_){
_start:
{
uint8_t v_bi_boxed_1599_; uint8_t v_kind_boxed_1600_; lean_object* v_res_1601_; 
v_bi_boxed_1599_ = lean_unbox(v_bi_1587_);
v_kind_boxed_1600_ = lean_unbox(v_kind_1590_);
v_res_1601_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___redArg(v_name_1586_, v_bi_boxed_1599_, v_type_1588_, v_k_1589_, v_kind_boxed_1600_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_);
lean_dec(v___y_1597_);
lean_dec_ref(v___y_1596_);
lean_dec(v___y_1595_);
lean_dec_ref(v___y_1594_);
lean_dec(v___y_1593_);
lean_dec_ref(v___y_1592_);
lean_dec(v___y_1591_);
return v_res_1601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0___redArg(lean_object* v_name_1602_, lean_object* v_type_1603_, lean_object* v_k_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_){
_start:
{
uint8_t v___x_1613_; uint8_t v___x_1614_; lean_object* v___x_1615_; 
v___x_1613_ = 0;
v___x_1614_ = 0;
v___x_1615_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___redArg(v_name_1602_, v___x_1613_, v_type_1603_, v_k_1604_, v___x_1614_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
return v___x_1615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0___redArg___boxed(lean_object* v_name_1616_, lean_object* v_type_1617_, lean_object* v_k_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_){
_start:
{
lean_object* v_res_1627_; 
v_res_1627_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0___redArg(v_name_1616_, v_type_1617_, v_k_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_);
lean_dec(v___y_1625_);
lean_dec_ref(v___y_1624_);
lean_dec(v___y_1623_);
lean_dec_ref(v___y_1622_);
lean_dec(v___y_1621_);
lean_dec_ref(v___y_1620_);
lean_dec(v___y_1619_);
return v_res_1627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reduceCtorEqCheap(lean_object* v_e_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_){
_start:
{
lean_object* v___x_1640_; 
lean_inc_ref(v_e_1631_);
v___x_1640_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1631_, v_a_1636_);
if (lean_obj_tag(v___x_1640_) == 0)
{
lean_object* v_a_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1714_; 
v_a_1641_ = lean_ctor_get(v___x_1640_, 0);
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1640_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1643_ = v___x_1640_;
v_isShared_1644_ = v_isSharedCheck_1714_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_a_1641_);
lean_dec(v___x_1640_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1714_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1650_; uint8_t v___x_1651_; 
v___x_1650_ = l_Lean_Expr_cleanupAnnotations(v_a_1641_);
v___x_1651_ = l_Lean_Expr_isApp(v___x_1650_);
if (v___x_1651_ == 0)
{
lean_dec_ref(v___x_1650_);
lean_dec_ref(v_e_1631_);
goto v___jp_1645_;
}
else
{
lean_object* v_arg_1652_; lean_object* v___x_1653_; uint8_t v___x_1654_; 
v_arg_1652_ = lean_ctor_get(v___x_1650_, 1);
lean_inc_ref(v_arg_1652_);
v___x_1653_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1650_);
v___x_1654_ = l_Lean_Expr_isApp(v___x_1653_);
if (v___x_1654_ == 0)
{
lean_dec_ref(v___x_1653_);
lean_dec_ref(v_arg_1652_);
lean_dec_ref(v_e_1631_);
goto v___jp_1645_;
}
else
{
lean_object* v_arg_1655_; lean_object* v___x_1656_; uint8_t v___x_1657_; 
v_arg_1655_ = lean_ctor_get(v___x_1653_, 1);
lean_inc_ref(v_arg_1655_);
v___x_1656_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1653_);
v___x_1657_ = l_Lean_Expr_isApp(v___x_1656_);
if (v___x_1657_ == 0)
{
lean_dec_ref(v___x_1656_);
lean_dec_ref(v_arg_1655_);
lean_dec_ref(v_arg_1652_);
lean_dec_ref(v_e_1631_);
goto v___jp_1645_;
}
else
{
lean_object* v___x_1658_; lean_object* v___x_1659_; uint8_t v___x_1660_; 
v___x_1658_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1656_);
v___x_1659_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__2));
v___x_1660_ = l_Lean_Expr_isConstOf(v___x_1658_, v___x_1659_);
lean_dec_ref(v___x_1658_);
if (v___x_1660_ == 0)
{
lean_dec_ref(v_arg_1655_);
lean_dec_ref(v_arg_1652_);
lean_dec_ref(v_e_1631_);
goto v___jp_1645_;
}
else
{
lean_object* v___x_1661_; 
lean_del_object(v___x_1643_);
v___x_1661_ = l_Lean_Meta_isConstructorApp_x3f(v_arg_1655_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1705_; 
v_a_1662_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_1705_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1664_ = v___x_1661_;
v_isShared_1665_ = v_isSharedCheck_1705_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v___x_1661_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1705_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
if (lean_obj_tag(v_a_1662_) == 1)
{
lean_object* v_val_1666_; lean_object* v___x_1667_; 
v_val_1666_ = lean_ctor_get(v_a_1662_, 0);
lean_inc(v_val_1666_);
lean_dec_ref_known(v_a_1662_, 1);
v___x_1667_ = l_Lean_Meta_isConstructorApp_x3f(v_arg_1652_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_);
if (lean_obj_tag(v___x_1667_) == 0)
{
lean_object* v_a_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1692_; 
v_a_1668_ = lean_ctor_get(v___x_1667_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1667_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1670_ = v___x_1667_;
v_isShared_1671_ = v_isSharedCheck_1692_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_a_1668_);
lean_dec(v___x_1667_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1692_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
if (lean_obj_tag(v_a_1668_) == 1)
{
lean_object* v_toConstantVal_1677_; lean_object* v_val_1678_; lean_object* v_toConstantVal_1679_; lean_object* v_name_1680_; lean_object* v_name_1681_; uint8_t v___x_1682_; 
lean_del_object(v___x_1664_);
v_toConstantVal_1677_ = lean_ctor_get(v_val_1666_, 0);
lean_inc_ref(v_toConstantVal_1677_);
lean_dec(v_val_1666_);
v_val_1678_ = lean_ctor_get(v_a_1668_, 0);
lean_inc(v_val_1678_);
lean_dec_ref_known(v_a_1668_, 1);
v_toConstantVal_1679_ = lean_ctor_get(v_val_1678_, 0);
lean_inc_ref(v_toConstantVal_1679_);
lean_dec(v_val_1678_);
v_name_1680_ = lean_ctor_get(v_toConstantVal_1677_, 0);
lean_inc(v_name_1680_);
lean_dec_ref(v_toConstantVal_1677_);
v_name_1681_ = lean_ctor_get(v_toConstantVal_1679_, 0);
lean_inc(v_name_1681_);
lean_dec_ref(v_toConstantVal_1679_);
v___x_1682_ = lean_name_eq(v_name_1680_, v_name_1681_);
lean_dec(v_name_1681_);
lean_dec(v_name_1680_);
if (v___x_1682_ == 0)
{
if (v___x_1660_ == 0)
{
lean_dec_ref(v_e_1631_);
goto v___jp_1672_;
}
else
{
lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___f_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
lean_del_object(v___x_1670_);
v___x_1683_ = lean_box(v___x_1682_);
v___x_1684_ = lean_box(v___x_1660_);
v___f_1685_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_reduceCtorEqCheap___lam__0___boxed), 11, 2);
lean_closure_set(v___f_1685_, 0, v___x_1683_);
lean_closure_set(v___f_1685_, 1, v___x_1684_);
v___x_1686_ = ((lean_object*)(l_Lean_Meta_Grind_reduceCtorEqCheap___closed__1));
v___x_1687_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0___redArg(v___x_1686_, v_e_1631_, v___f_1685_, v_a_1632_, v_a_1633_, v_a_1634_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_);
return v___x_1687_;
}
}
else
{
lean_dec_ref(v_e_1631_);
goto v___jp_1672_;
}
}
else
{
lean_object* v___x_1688_; lean_object* v___x_1690_; 
lean_del_object(v___x_1670_);
lean_dec(v_a_1668_);
lean_dec(v_val_1666_);
lean_dec_ref(v_e_1631_);
v___x_1688_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
if (v_isShared_1665_ == 0)
{
lean_ctor_set(v___x_1664_, 0, v___x_1688_);
v___x_1690_ = v___x_1664_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v___x_1688_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
v___jp_1672_:
{
lean_object* v___x_1673_; lean_object* v___x_1675_; 
v___x_1673_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
if (v_isShared_1671_ == 0)
{
lean_ctor_set(v___x_1670_, 0, v___x_1673_);
v___x_1675_ = v___x_1670_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v___x_1673_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
}
else
{
lean_object* v_a_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1700_; 
lean_dec(v_val_1666_);
lean_del_object(v___x_1664_);
lean_dec_ref(v_e_1631_);
v_a_1693_ = lean_ctor_get(v___x_1667_, 0);
v_isSharedCheck_1700_ = !lean_is_exclusive(v___x_1667_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1695_ = v___x_1667_;
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_a_1693_);
lean_dec(v___x_1667_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1698_; 
if (v_isShared_1696_ == 0)
{
v___x_1698_ = v___x_1695_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_a_1693_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
}
}
else
{
lean_object* v___x_1701_; lean_object* v___x_1703_; 
lean_dec(v_a_1662_);
lean_dec_ref(v_arg_1652_);
lean_dec_ref(v_e_1631_);
v___x_1701_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
if (v_isShared_1665_ == 0)
{
lean_ctor_set(v___x_1664_, 0, v___x_1701_);
v___x_1703_ = v___x_1664_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v___x_1701_);
v___x_1703_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
return v___x_1703_;
}
}
}
}
else
{
lean_object* v_a_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1713_; 
lean_dec_ref(v_arg_1652_);
lean_dec_ref(v_e_1631_);
v_a_1706_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_1713_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1708_ = v___x_1661_;
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_a_1706_);
lean_dec(v___x_1661_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v___x_1711_; 
if (v_isShared_1709_ == 0)
{
v___x_1711_ = v___x_1708_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_a_1706_);
v___x_1711_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
return v___x_1711_;
}
}
}
}
}
}
}
v___jp_1645_:
{
lean_object* v___x_1646_; lean_object* v___x_1648_; 
v___x_1646_ = ((lean_object*)(l_Lean_Meta_Grind_simpEq___redArg___closed__0));
if (v_isShared_1644_ == 0)
{
lean_ctor_set(v___x_1643_, 0, v___x_1646_);
v___x_1648_ = v___x_1643_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v___x_1646_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
}
else
{
lean_object* v_a_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1722_; 
lean_dec_ref(v_e_1631_);
v_a_1715_ = lean_ctor_get(v___x_1640_, 0);
v_isSharedCheck_1722_ = !lean_is_exclusive(v___x_1640_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1717_ = v___x_1640_;
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_a_1715_);
lean_dec(v___x_1640_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1720_; 
if (v_isShared_1718_ == 0)
{
v___x_1720_ = v___x_1717_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v_a_1715_);
v___x_1720_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
return v___x_1720_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reduceCtorEqCheap___boxed(lean_object* v_e_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_){
_start:
{
lean_object* v_res_1732_; 
v_res_1732_ = l_Lean_Meta_Grind_reduceCtorEqCheap(v_e_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_);
lean_dec(v_a_1730_);
lean_dec_ref(v_a_1729_);
lean_dec(v_a_1728_);
lean_dec_ref(v_a_1727_);
lean_dec(v_a_1726_);
lean_dec_ref(v_a_1725_);
lean_dec(v_a_1724_);
return v_res_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0(lean_object* v_00_u03b1_1733_, lean_object* v_name_1734_, uint8_t v_bi_1735_, lean_object* v_type_1736_, lean_object* v_k_1737_, uint8_t v_kind_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_){
_start:
{
lean_object* v___x_1747_; 
v___x_1747_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___redArg(v_name_1734_, v_bi_1735_, v_type_1736_, v_k_1737_, v_kind_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_);
return v___x_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1748_, lean_object* v_name_1749_, lean_object* v_bi_1750_, lean_object* v_type_1751_, lean_object* v_k_1752_, lean_object* v_kind_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_){
_start:
{
uint8_t v_bi_boxed_1762_; uint8_t v_kind_boxed_1763_; lean_object* v_res_1764_; 
v_bi_boxed_1762_ = lean_unbox(v_bi_1750_);
v_kind_boxed_1763_ = lean_unbox(v_kind_1753_);
v_res_1764_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0(v_00_u03b1_1748_, v_name_1749_, v_bi_boxed_1762_, v_type_1751_, v_k_1752_, v_kind_boxed_1763_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_);
lean_dec(v___y_1760_);
lean_dec_ref(v___y_1759_);
lean_dec(v___y_1758_);
lean_dec_ref(v___y_1757_);
lean_dec(v___y_1756_);
lean_dec_ref(v___y_1755_);
lean_dec(v___y_1754_);
return v_res_1764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0(lean_object* v_00_u03b1_1765_, lean_object* v_name_1766_, lean_object* v_type_1767_, lean_object* v_k_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_){
_start:
{
lean_object* v___x_1777_; 
v___x_1777_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0___redArg(v_name_1766_, v_type_1767_, v_k_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_);
return v___x_1777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0___boxed(lean_object* v_00_u03b1_1778_, lean_object* v_name_1779_, lean_object* v_type_1780_, lean_object* v_k_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_){
_start:
{
lean_object* v_res_1790_; 
v_res_1790_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0(v_00_u03b1_1778_, v_name_1779_, v_type_1780_, v_k_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_);
lean_dec(v___y_1788_);
lean_dec_ref(v___y_1787_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
lean_dec(v___y_1784_);
lean_dec_ref(v___y_1783_);
lean_dec(v___y_1782_);
return v_res_1790_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_14_(){
_start:
{
lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1798_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_14_));
v___x_1799_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__4_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13_));
v___x_1800_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_reduceCtorEqCheap___boxed), 9, 0);
v___x_1801_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_1798_, v___x_1799_, v___x_1800_);
return v___x_1801_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_14____boxed(lean_object* v_a_1802_){
_start:
{
lean_object* v_res_1803_; 
v_res_1803_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_14_();
return v_res_1803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_unfoldReducibleSimproc___redArg(lean_object* v_e_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_){
_start:
{
lean_object* v___x_1810_; 
v___x_1810_ = l_Lean_Meta_Sym_unfoldReducibleStep(v_e_1804_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_);
return v___x_1810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_unfoldReducibleSimproc___redArg___boxed(lean_object* v_e_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_){
_start:
{
lean_object* v_res_1817_; 
v_res_1817_ = l_Lean_Meta_Grind_unfoldReducibleSimproc___redArg(v_e_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_);
lean_dec(v_a_1815_);
lean_dec_ref(v_a_1814_);
lean_dec(v_a_1813_);
lean_dec_ref(v_a_1812_);
return v_res_1817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_unfoldReducibleSimproc(lean_object* v_e_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_){
_start:
{
lean_object* v___x_1827_; 
v___x_1827_ = l_Lean_Meta_Sym_unfoldReducibleStep(v_e_1818_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1825_);
return v___x_1827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_unfoldReducibleSimproc___boxed(lean_object* v_e_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_){
_start:
{
lean_object* v_res_1837_; 
v_res_1837_ = l_Lean_Meta_Grind_unfoldReducibleSimproc(v_e_1828_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_);
lean_dec(v_a_1835_);
lean_dec_ref(v_a_1834_);
lean_dec(v_a_1833_);
lean_dec_ref(v_a_1832_);
lean_dec(v_a_1831_);
lean_dec_ref(v_a_1830_);
lean_dec(v_a_1829_);
return v_res_1837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___lam__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_10_(lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_){
_start:
{
lean_object* v___x_1847_; 
v___x_1847_ = l_Lean_Meta_Sym_unfoldReducibleStep(v___y_1838_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_);
return v___x_1847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___lam__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_10____boxed(lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_){
_start:
{
lean_object* v_res_1857_; 
v_res_1857_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___lam__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_10_(v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_);
lean_dec(v___y_1855_);
lean_dec_ref(v___y_1854_);
lean_dec(v___y_1853_);
lean_dec_ref(v___y_1852_);
lean_dec(v___y_1851_);
lean_dec_ref(v___y_1850_);
lean_dec(v___y_1849_);
return v_res_1857_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_10_(){
_start:
{
lean_object* v___f_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; 
v___f_1870_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_10_));
v___x_1871_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_10_));
v___x_1872_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_10_));
v___x_1873_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1871_, v___x_1872_, v___f_1870_);
return v___x_1873_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_10____boxed(lean_object* v_a_1874_){
_start:
{
lean_object* v_res_1875_; 
v_res_1875_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_10_();
return v_res_1875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimprocs___redArg(lean_object* v_a_1884_, lean_object* v_a_1885_){
_start:
{
lean_object* v___x_1887_; 
v___x_1887_ = l_Lean_Meta_Simp_getSEvalSimprocs___redArg(v_a_1885_);
if (lean_obj_tag(v___x_1887_) == 0)
{
lean_object* v_a_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; uint8_t v___x_1894_; lean_object* v___x_1895_; 
v_a_1888_ = lean_ctor_get(v___x_1887_, 0);
lean_inc(v_a_1888_);
lean_dec_ref_known(v___x_1887_, 1);
v___x_1889_ = ((lean_object*)(l_Lean_Meta_Grind_getSimprocs___redArg___closed__2));
v___x_1890_ = l_Lean_Meta_Simp_Simprocs_erase(v_a_1888_, v___x_1889_);
v___x_1891_ = ((lean_object*)(l_Lean_Meta_Grind_getSimprocs___redArg___closed__4));
v___x_1892_ = l_Lean_Meta_Simp_Simprocs_erase(v___x_1890_, v___x_1891_);
v___x_1893_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_14_));
v___x_1894_ = 1;
v___x_1895_ = l_Lean_Meta_Simp_Simprocs_add(v___x_1892_, v___x_1893_, v___x_1894_, v_a_1884_, v_a_1885_);
if (lean_obj_tag(v___x_1895_) == 0)
{
lean_object* v_a_1896_; lean_object* v___x_1897_; 
v_a_1896_ = lean_ctor_get(v___x_1895_, 0);
lean_inc(v_a_1896_);
lean_dec_ref_known(v___x_1895_, 1);
v___x_1897_ = l_Lean_Meta_Grind_addSimpMatchDiscrsOnly(v_a_1896_, v_a_1884_, v_a_1885_);
if (lean_obj_tag(v___x_1897_) == 0)
{
lean_object* v_a_1898_; lean_object* v___x_1899_; 
v_a_1898_ = lean_ctor_get(v___x_1897_, 0);
lean_inc(v_a_1898_);
lean_dec_ref_known(v___x_1897_, 1);
v___x_1899_ = l_Lean_Meta_Grind_addPreMatchCondSimproc(v_a_1898_, v_a_1884_, v_a_1885_);
if (lean_obj_tag(v___x_1899_) == 0)
{
lean_object* v_a_1900_; lean_object* v___x_1901_; 
v_a_1900_ = lean_ctor_get(v___x_1899_, 0);
lean_inc(v_a_1900_);
lean_dec_ref_known(v___x_1899_, 1);
v___x_1901_ = l_Lean_Meta_Grind_Arith_addSimproc(v_a_1900_, v_a_1884_, v_a_1885_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v_a_1902_; lean_object* v___x_1903_; 
v_a_1902_ = lean_ctor_get(v___x_1901_, 0);
lean_inc(v_a_1902_);
lean_dec_ref_known(v___x_1901_, 1);
v___x_1903_ = l_Lean_Meta_Grind_addForallSimproc(v_a_1902_, v_a_1884_, v_a_1885_);
if (lean_obj_tag(v___x_1903_) == 0)
{
lean_object* v_a_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; 
v_a_1904_ = lean_ctor_get(v___x_1903_, 0);
lean_inc(v_a_1904_);
lean_dec_ref_known(v___x_1903_, 1);
v___x_1905_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13_));
v___x_1906_ = l_Lean_Meta_Simp_Simprocs_add(v_a_1904_, v___x_1905_, v___x_1894_, v_a_1884_, v_a_1885_);
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_object* v_a_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; 
v_a_1907_ = lean_ctor_get(v___x_1906_, 0);
lean_inc(v_a_1907_);
lean_dec_ref_known(v___x_1906_, 1);
v___x_1908_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_12_));
v___x_1909_ = l_Lean_Meta_Simp_Simprocs_add(v_a_1907_, v___x_1908_, v___x_1894_, v_a_1884_, v_a_1885_);
if (lean_obj_tag(v___x_1909_) == 0)
{
lean_object* v_a_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; 
v_a_1910_ = lean_ctor_get(v___x_1909_, 0);
lean_inc(v_a_1910_);
lean_dec_ref_known(v___x_1909_, 1);
v___x_1911_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_14_));
v___x_1912_ = l_Lean_Meta_Simp_Simprocs_add(v_a_1910_, v___x_1911_, v___x_1894_, v_a_1884_, v_a_1885_);
if (lean_obj_tag(v___x_1912_) == 0)
{
lean_object* v_a_1913_; lean_object* v___x_1914_; uint8_t v___x_1915_; lean_object* v___x_1916_; 
v_a_1913_ = lean_ctor_get(v___x_1912_, 0);
lean_inc(v_a_1913_);
lean_dec_ref_known(v___x_1912_, 1);
v___x_1914_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3828017814____hygCtx___hyg_11_));
v___x_1915_ = 0;
v___x_1916_ = l_Lean_Meta_Simp_Simprocs_add(v_a_1913_, v___x_1914_, v___x_1915_, v_a_1884_, v_a_1885_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_object* v_a_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
v_a_1917_ = lean_ctor_get(v___x_1916_, 0);
lean_inc(v_a_1917_);
lean_dec_ref_known(v___x_1916_, 1);
v___x_1918_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_10_));
v___x_1919_ = l_Lean_Meta_Simp_Simprocs_add(v_a_1917_, v___x_1918_, v___x_1915_, v_a_1884_, v_a_1885_);
if (lean_obj_tag(v___x_1919_) == 0)
{
lean_object* v_a_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1930_; 
v_a_1920_ = lean_ctor_get(v___x_1919_, 0);
v_isSharedCheck_1930_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1930_ == 0)
{
v___x_1922_ = v___x_1919_;
v_isShared_1923_ = v_isSharedCheck_1930_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_a_1920_);
lean_dec(v___x_1919_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1930_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1928_; 
v___x_1924_ = lean_unsigned_to_nat(1u);
v___x_1925_ = lean_mk_empty_array_with_capacity(v___x_1924_);
v___x_1926_ = lean_array_push(v___x_1925_, v_a_1920_);
if (v_isShared_1923_ == 0)
{
lean_ctor_set(v___x_1922_, 0, v___x_1926_);
v___x_1928_ = v___x_1922_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v___x_1926_);
v___x_1928_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
return v___x_1928_;
}
}
}
else
{
lean_object* v_a_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1938_; 
v_a_1931_ = lean_ctor_get(v___x_1919_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1933_ = v___x_1919_;
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_a_1931_);
lean_dec(v___x_1919_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1936_; 
if (v_isShared_1934_ == 0)
{
v___x_1936_ = v___x_1933_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_a_1931_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
return v___x_1936_;
}
}
}
}
else
{
lean_object* v_a_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1946_; 
v_a_1939_ = lean_ctor_get(v___x_1916_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1941_ = v___x_1916_;
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_a_1939_);
lean_dec(v___x_1916_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1944_; 
if (v_isShared_1942_ == 0)
{
v___x_1944_ = v___x_1941_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_a_1939_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
}
}
}
}
else
{
lean_object* v_a_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1954_; 
v_a_1947_ = lean_ctor_get(v___x_1912_, 0);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___x_1912_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1949_ = v___x_1912_;
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_a_1947_);
lean_dec(v___x_1912_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___x_1952_; 
if (v_isShared_1950_ == 0)
{
v___x_1952_ = v___x_1949_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_a_1947_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
return v___x_1952_;
}
}
}
}
else
{
lean_object* v_a_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1962_; 
v_a_1955_ = lean_ctor_get(v___x_1909_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v___x_1909_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1957_ = v___x_1909_;
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_a_1955_);
lean_dec(v___x_1909_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1960_; 
if (v_isShared_1958_ == 0)
{
v___x_1960_ = v___x_1957_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v_a_1955_);
v___x_1960_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
return v___x_1960_;
}
}
}
}
else
{
lean_object* v_a_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1970_; 
v_a_1963_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_1970_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1965_ = v___x_1906_;
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_a_1963_);
lean_dec(v___x_1906_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___x_1968_; 
if (v_isShared_1966_ == 0)
{
v___x_1968_ = v___x_1965_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v_a_1963_);
v___x_1968_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
return v___x_1968_;
}
}
}
}
else
{
lean_object* v_a_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1978_; 
v_a_1971_ = lean_ctor_get(v___x_1903_, 0);
v_isSharedCheck_1978_ = !lean_is_exclusive(v___x_1903_);
if (v_isSharedCheck_1978_ == 0)
{
v___x_1973_ = v___x_1903_;
v_isShared_1974_ = v_isSharedCheck_1978_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_a_1971_);
lean_dec(v___x_1903_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1978_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v___x_1976_; 
if (v_isShared_1974_ == 0)
{
v___x_1976_ = v___x_1973_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v_a_1971_);
v___x_1976_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
return v___x_1976_;
}
}
}
}
else
{
lean_object* v_a_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_1986_; 
v_a_1979_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_1986_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1986_ == 0)
{
v___x_1981_ = v___x_1901_;
v_isShared_1982_ = v_isSharedCheck_1986_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_a_1979_);
lean_dec(v___x_1901_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_1986_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
lean_object* v___x_1984_; 
if (v_isShared_1982_ == 0)
{
v___x_1984_ = v___x_1981_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v_a_1979_);
v___x_1984_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
return v___x_1984_;
}
}
}
}
else
{
lean_object* v_a_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_1994_; 
v_a_1987_ = lean_ctor_get(v___x_1899_, 0);
v_isSharedCheck_1994_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1989_ = v___x_1899_;
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_a_1987_);
lean_dec(v___x_1899_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v___x_1992_; 
if (v_isShared_1990_ == 0)
{
v___x_1992_ = v___x_1989_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_a_1987_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
return v___x_1992_;
}
}
}
}
else
{
lean_object* v_a_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2002_; 
v_a_1995_ = lean_ctor_get(v___x_1897_, 0);
v_isSharedCheck_2002_ = !lean_is_exclusive(v___x_1897_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1997_ = v___x_1897_;
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_a_1995_);
lean_dec(v___x_1897_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_2000_; 
if (v_isShared_1998_ == 0)
{
v___x_2000_ = v___x_1997_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v_a_1995_);
v___x_2000_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
return v___x_2000_;
}
}
}
}
else
{
lean_object* v_a_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2010_; 
v_a_2003_ = lean_ctor_get(v___x_1895_, 0);
v_isSharedCheck_2010_ = !lean_is_exclusive(v___x_1895_);
if (v_isSharedCheck_2010_ == 0)
{
v___x_2005_ = v___x_1895_;
v_isShared_2006_ = v_isSharedCheck_2010_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_a_2003_);
lean_dec(v___x_1895_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2010_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v___x_2008_; 
if (v_isShared_2006_ == 0)
{
v___x_2008_ = v___x_2005_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v_a_2003_);
v___x_2008_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
return v___x_2008_;
}
}
}
}
else
{
lean_object* v_a_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2018_; 
v_a_2011_ = lean_ctor_get(v___x_1887_, 0);
v_isSharedCheck_2018_ = !lean_is_exclusive(v___x_1887_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_2013_ = v___x_1887_;
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_a_2011_);
lean_dec(v___x_1887_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v___x_2016_; 
if (v_isShared_2014_ == 0)
{
v___x_2016_ = v___x_2013_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v_a_2011_);
v___x_2016_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
return v___x_2016_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimprocs___redArg___boxed(lean_object* v_a_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_){
_start:
{
lean_object* v_res_2022_; 
v_res_2022_ = l_Lean_Meta_Grind_getSimprocs___redArg(v_a_2019_, v_a_2020_);
lean_dec(v_a_2020_);
lean_dec_ref(v_a_2019_);
return v_res_2022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimprocs(lean_object* v_a_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_, lean_object* v_a_2026_){
_start:
{
lean_object* v___x_2028_; 
v___x_2028_ = l_Lean_Meta_Grind_getSimprocs___redArg(v_a_2025_, v_a_2026_);
return v___x_2028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimprocs___boxed(lean_object* v_a_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_, lean_object* v_a_2032_, lean_object* v_a_2033_){
_start:
{
lean_object* v_res_2034_; 
v_res_2034_ = l_Lean_Meta_Grind_getSimprocs(v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_);
lean_dec(v_a_2032_);
lean_dec_ref(v_a_2031_);
lean_dec(v_a_2030_);
lean_dec_ref(v_a_2029_);
return v_res_2034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_addDeclToUnfold(lean_object* v_s_2035_, lean_object* v_declName_2036_, lean_object* v_a_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_){
_start:
{
lean_object* v___x_2042_; lean_object* v_env_2043_; uint8_t v___x_2044_; uint8_t v___x_2045_; 
v___x_2042_ = lean_st_ref_get(v_a_2040_);
v_env_2043_ = lean_ctor_get(v___x_2042_, 0);
lean_inc_ref(v_env_2043_);
lean_dec(v___x_2042_);
v___x_2044_ = 1;
lean_inc(v_declName_2036_);
v___x_2045_ = l_Lean_Environment_contains(v_env_2043_, v_declName_2036_, v___x_2044_);
if (v___x_2045_ == 0)
{
lean_object* v___x_2046_; 
lean_dec(v_declName_2036_);
v___x_2046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2046_, 0, v_s_2035_);
return v___x_2046_;
}
else
{
lean_object* v___x_2047_; 
v___x_2047_ = l_Lean_Meta_SimpTheorems_addDeclToUnfold(v_s_2035_, v_declName_2036_, v_a_2037_, v_a_2038_, v_a_2039_, v_a_2040_);
return v___x_2047_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_addDeclToUnfold___boxed(lean_object* v_s_2048_, lean_object* v_declName_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_){
_start:
{
lean_object* v_res_2055_; 
v_res_2055_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_addDeclToUnfold(v_s_2048_, v_declName_2049_, v_a_2050_, v_a_2051_, v_a_2052_, v_a_2053_);
lean_dec(v_a_2053_);
lean_dec_ref(v_a_2052_);
lean_dec(v_a_2051_);
lean_dec_ref(v_a_2050_);
return v_res_2055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNormTheorems(lean_object* v_a_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_){
_start:
{
lean_object* v___x_2082_; lean_object* v___x_2083_; 
v___x_2082_ = l_Lean_Meta_Grind_normExt;
v___x_2083_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v___x_2082_, v_a_2080_);
if (lean_obj_tag(v___x_2083_) == 0)
{
lean_object* v_a_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; 
v_a_2084_ = lean_ctor_get(v___x_2083_, 0);
lean_inc(v_a_2084_);
lean_dec_ref_known(v___x_2083_, 1);
v___x_2085_ = ((lean_object*)(l_Lean_Meta_Grind_getNormTheorems___closed__2));
v___x_2086_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_addDeclToUnfold(v_a_2084_, v___x_2085_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_);
if (lean_obj_tag(v___x_2086_) == 0)
{
lean_object* v_a_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; 
v_a_2087_ = lean_ctor_get(v___x_2086_, 0);
lean_inc(v_a_2087_);
lean_dec_ref_known(v___x_2086_, 1);
v___x_2088_ = ((lean_object*)(l_Lean_Meta_Grind_getNormTheorems___closed__5));
v___x_2089_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_addDeclToUnfold(v_a_2087_, v___x_2088_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_);
if (lean_obj_tag(v___x_2089_) == 0)
{
lean_object* v_a_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; 
v_a_2090_ = lean_ctor_get(v___x_2089_, 0);
lean_inc(v_a_2090_);
lean_dec_ref_known(v___x_2089_, 1);
v___x_2091_ = ((lean_object*)(l_Lean_Meta_Grind_getNormTheorems___closed__7));
v___x_2092_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_addDeclToUnfold(v_a_2090_, v___x_2091_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_);
if (lean_obj_tag(v___x_2092_) == 0)
{
lean_object* v_a_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; 
v_a_2093_ = lean_ctor_get(v___x_2092_, 0);
lean_inc(v_a_2093_);
lean_dec_ref_known(v___x_2092_, 1);
v___x_2094_ = ((lean_object*)(l_Lean_Meta_Grind_getNormTheorems___closed__9));
v___x_2095_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_addDeclToUnfold(v_a_2093_, v___x_2094_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_);
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_object* v_a_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; 
v_a_2096_ = lean_ctor_get(v___x_2095_, 0);
lean_inc(v_a_2096_);
lean_dec_ref_known(v___x_2095_, 1);
v___x_2097_ = ((lean_object*)(l_Lean_Meta_Grind_getNormTheorems___closed__11));
v___x_2098_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_addDeclToUnfold(v_a_2096_, v___x_2097_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_);
return v___x_2098_;
}
else
{
return v___x_2095_;
}
}
else
{
return v___x_2092_;
}
}
else
{
return v___x_2089_;
}
}
else
{
return v___x_2086_;
}
}
else
{
return v___x_2083_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNormTheorems___boxed(lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_){
_start:
{
lean_object* v_res_2104_; 
v_res_2104_ = l_Lean_Meta_Grind_getNormTheorems(v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_);
lean_dec(v_a_2102_);
lean_dec_ref(v_a_2101_);
lean_dec(v_a_2100_);
lean_dec_ref(v_a_2099_);
return v_res_2104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimpContext(lean_object* v_config_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_){
_start:
{
lean_object* v___x_2111_; 
v___x_2111_ = l_Lean_Meta_Grind_getNormTheorems(v_a_2106_, v_a_2107_, v_a_2108_, v_a_2109_);
if (lean_obj_tag(v___x_2111_) == 0)
{
lean_object* v_a_2112_; lean_object* v___x_2113_; 
v_a_2112_ = lean_ctor_get(v___x_2111_, 0);
lean_inc(v_a_2112_);
lean_dec_ref_known(v___x_2111_, 1);
v___x_2113_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_2109_);
if (lean_obj_tag(v___x_2113_) == 0)
{
lean_object* v_a_2114_; uint8_t v_zetaDelta_2115_; uint8_t v_zeta_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; uint8_t v___x_2119_; uint8_t v___x_2120_; uint8_t v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; 
v_a_2114_ = lean_ctor_get(v___x_2113_, 0);
lean_inc(v_a_2114_);
lean_dec_ref_known(v___x_2113_, 1);
v_zetaDelta_2115_ = lean_ctor_get_uint8(v_config_2105_, sizeof(void*)*14 + 19);
v_zeta_2116_ = lean_ctor_get_uint8(v_config_2105_, sizeof(void*)*14 + 20);
v___x_2117_ = lean_unsigned_to_nat(100000u);
v___x_2118_ = lean_unsigned_to_nat(2u);
v___x_2119_ = 0;
v___x_2120_ = 1;
v___x_2121_ = 0;
v___x_2122_ = lean_box(0);
v___x_2123_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_2123_, 0, v___x_2117_);
lean_ctor_set(v___x_2123_, 1, v___x_2118_);
lean_ctor_set(v___x_2123_, 2, v___x_2122_);
lean_ctor_set_uint8(v___x_2123_, sizeof(void*)*3, v___x_2119_);
lean_ctor_set_uint8(v___x_2123_, sizeof(void*)*3 + 1, v___x_2120_);
lean_ctor_set_uint8(v___x_2123_, sizeof(void*)*3 + 2, v___x_2119_);
lean_ctor_set_uint8(v___x_2123_, sizeof(void*)*3 + 3, v_zeta_2116_);
lean_ctor_set_uint8(v___x_2123_, sizeof(void*)*3 + 4, v___x_2120_);
lean_ctor_set_uint8(v___x_2123_, sizeof(void*)*3 + 5, v___x_2120_);
lean_ctor_set_uint8(v___x_2123_, sizeof(void*)*3 + 6, v___x_2121_);
lean_ctor_set_uint8(v___x_2123_, sizeof(void*)*3 + 7, v___x_2120_);
lean_ctor_set_uint8(v___x_2123_, sizeof(void*)*3 + 8, v___x_2120_);
lean_ctor_set_uint8(v___x_2123_, sizeof(void*)*3 + 9, v___x_2119_);
lean_ctor_set_uint8(v___x_2123_, sizeof(void*)*3 + 10, v___x_2120_);
lean_ctor_set_uint8(v___x_2123_, sizeof(void*)*3 + 11, v___x_2119_);
lean_ctor_set_uint8(v___x_2123_, sizeof(void*)*3 + 12, v___x_2120_);
lean_ctor_set_uint8(v___x_2123_, sizeof(void*)*3 + 13, v___x_2120_);
lean_ctor_set_uint8(v___x_2123_, sizeof(void*)*3 + 14, v___x_2119_);
lean_ctor_set_uint8(v___x_2123_, sizeof(void*)*3 + 15, v___x_2119_);
lean_ctor_set_uint8(v___x_2123_, sizeof(void*)*3 + 16, v_zetaDelta_2115_);
lean_ctor_set_uint8(v___x_2123_, sizeof(void*)*3 + 17, v___x_2120_);
lean_ctor_set_uint8(v___x_2123_, sizeof(void*)*3 + 18, v___x_2119_);
lean_ctor_set_uint8(v___x_2123_, sizeof(void*)*3 + 19, v___x_2120_);
lean_ctor_set_uint8(v___x_2123_, sizeof(void*)*3 + 20, v___x_2119_);
lean_ctor_set_uint8(v___x_2123_, sizeof(void*)*3 + 21, v___x_2120_);
lean_ctor_set_uint8(v___x_2123_, sizeof(void*)*3 + 22, v___x_2120_);
lean_ctor_set_uint8(v___x_2123_, sizeof(void*)*3 + 23, v___x_2120_);
lean_ctor_set_uint8(v___x_2123_, sizeof(void*)*3 + 24, v___x_2119_);
lean_ctor_set_uint8(v___x_2123_, sizeof(void*)*3 + 25, v___x_2119_);
lean_ctor_set_uint8(v___x_2123_, sizeof(void*)*3 + 26, v___x_2119_);
lean_ctor_set_uint8(v___x_2123_, sizeof(void*)*3 + 27, v___x_2119_);
lean_ctor_set_uint8(v___x_2123_, sizeof(void*)*3 + 28, v___x_2119_);
v___x_2124_ = lean_unsigned_to_nat(1u);
v___x_2125_ = lean_mk_empty_array_with_capacity(v___x_2124_);
v___x_2126_ = lean_array_push(v___x_2125_, v_a_2112_);
v___x_2127_ = l_Lean_Options_empty;
v___x_2128_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_2123_, v___x_2126_, v_a_2114_, v___x_2127_, v_a_2106_, v_a_2108_, v_a_2109_);
return v___x_2128_;
}
else
{
lean_object* v_a_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2136_; 
lean_dec(v_a_2112_);
v_a_2129_ = lean_ctor_get(v___x_2113_, 0);
v_isSharedCheck_2136_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2136_ == 0)
{
v___x_2131_ = v___x_2113_;
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_a_2129_);
lean_dec(v___x_2113_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v___x_2134_; 
if (v_isShared_2132_ == 0)
{
v___x_2134_ = v___x_2131_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v_a_2129_);
v___x_2134_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
return v___x_2134_;
}
}
}
}
else
{
lean_object* v_a_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2144_; 
v_a_2137_ = lean_ctor_get(v___x_2111_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2139_ = v___x_2111_;
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_a_2137_);
lean_dec(v___x_2111_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2142_; 
if (v_isShared_2140_ == 0)
{
v___x_2142_ = v___x_2139_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_a_2137_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getSimpContext___boxed(lean_object* v_config_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_){
_start:
{
lean_object* v_res_2151_; 
v_res_2151_ = l_Lean_Meta_Grind_getSimpContext(v_config_2145_, v_a_2146_, v_a_2147_, v_a_2148_, v_a_2149_);
lean_dec(v_a_2149_);
lean_dec_ref(v_a_2148_);
lean_dec(v_a_2147_);
lean_dec_ref(v_a_2146_);
lean_dec_ref(v_config_2145_);
return v_res_2151_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normalizeImp___closed__0(void){
_start:
{
lean_object* v___x_2152_; 
v___x_2152_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2152_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normalizeImp___closed__1(void){
_start:
{
lean_object* v___x_2153_; lean_object* v___x_2154_; 
v___x_2153_ = lean_obj_once(&l_Lean_Meta_Grind_normalizeImp___closed__0, &l_Lean_Meta_Grind_normalizeImp___closed__0_once, _init_l_Lean_Meta_Grind_normalizeImp___closed__0);
v___x_2154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2154_, 0, v___x_2153_);
return v___x_2154_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normalizeImp___closed__2(void){
_start:
{
lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; 
v___x_2155_ = lean_unsigned_to_nat(0u);
v___x_2156_ = lean_obj_once(&l_Lean_Meta_Grind_normalizeImp___closed__1, &l_Lean_Meta_Grind_normalizeImp___closed__1_once, _init_l_Lean_Meta_Grind_normalizeImp___closed__1);
v___x_2157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2157_, 0, v___x_2156_);
lean_ctor_set(v___x_2157_, 1, v___x_2155_);
return v___x_2157_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normalizeImp___closed__3(void){
_start:
{
lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; 
v___x_2158_ = lean_unsigned_to_nat(32u);
v___x_2159_ = lean_mk_empty_array_with_capacity(v___x_2158_);
v___x_2160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2159_);
return v___x_2160_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normalizeImp___closed__4(void){
_start:
{
size_t v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2161_ = ((size_t)5ULL);
v___x_2162_ = lean_unsigned_to_nat(0u);
v___x_2163_ = lean_unsigned_to_nat(32u);
v___x_2164_ = lean_mk_empty_array_with_capacity(v___x_2163_);
v___x_2165_ = lean_obj_once(&l_Lean_Meta_Grind_normalizeImp___closed__3, &l_Lean_Meta_Grind_normalizeImp___closed__3_once, _init_l_Lean_Meta_Grind_normalizeImp___closed__3);
v___x_2166_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2166_, 0, v___x_2165_);
lean_ctor_set(v___x_2166_, 1, v___x_2164_);
lean_ctor_set(v___x_2166_, 2, v___x_2162_);
lean_ctor_set(v___x_2166_, 3, v___x_2162_);
lean_ctor_set_usize(v___x_2166_, 4, v___x_2161_);
return v___x_2166_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normalizeImp___closed__5(void){
_start:
{
lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; 
v___x_2167_ = lean_obj_once(&l_Lean_Meta_Grind_normalizeImp___closed__4, &l_Lean_Meta_Grind_normalizeImp___closed__4_once, _init_l_Lean_Meta_Grind_normalizeImp___closed__4);
v___x_2168_ = lean_obj_once(&l_Lean_Meta_Grind_normalizeImp___closed__1, &l_Lean_Meta_Grind_normalizeImp___closed__1_once, _init_l_Lean_Meta_Grind_normalizeImp___closed__1);
v___x_2169_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2169_, 0, v___x_2168_);
lean_ctor_set(v___x_2169_, 1, v___x_2168_);
lean_ctor_set(v___x_2169_, 2, v___x_2168_);
lean_ctor_set(v___x_2169_, 3, v___x_2167_);
return v___x_2169_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normalizeImp___closed__6(void){
_start:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; 
v___x_2170_ = lean_obj_once(&l_Lean_Meta_Grind_normalizeImp___closed__5, &l_Lean_Meta_Grind_normalizeImp___closed__5_once, _init_l_Lean_Meta_Grind_normalizeImp___closed__5);
v___x_2171_ = lean_obj_once(&l_Lean_Meta_Grind_normalizeImp___closed__2, &l_Lean_Meta_Grind_normalizeImp___closed__2_once, _init_l_Lean_Meta_Grind_normalizeImp___closed__2);
v___x_2172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2172_, 0, v___x_2171_);
lean_ctor_set(v___x_2172_, 1, v___x_2170_);
return v___x_2172_;
}
}
LEAN_EXPORT lean_object* lean_grind_normalize(lean_object* v_e_2173_, lean_object* v_config_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_){
_start:
{
lean_object* v___x_2180_; 
v___x_2180_ = l_Lean_Meta_Grind_getSimpContext(v_config_2174_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_);
lean_dec_ref(v_config_2174_);
if (lean_obj_tag(v___x_2180_) == 0)
{
lean_object* v_a_2181_; lean_object* v___x_2182_; 
v_a_2181_ = lean_ctor_get(v___x_2180_, 0);
lean_inc(v_a_2181_);
lean_dec_ref_known(v___x_2180_, 1);
v___x_2182_ = l_Lean_Meta_Grind_getSimprocs___redArg(v_a_2177_, v_a_2178_);
if (lean_obj_tag(v___x_2182_) == 0)
{
lean_object* v_a_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; 
v_a_2183_ = lean_ctor_get(v___x_2182_, 0);
lean_inc(v_a_2183_);
lean_dec_ref_known(v___x_2182_, 1);
v___x_2184_ = lean_box(0);
v___x_2185_ = lean_obj_once(&l_Lean_Meta_Grind_normalizeImp___closed__6, &l_Lean_Meta_Grind_normalizeImp___closed__6_once, _init_l_Lean_Meta_Grind_normalizeImp___closed__6);
v___x_2186_ = l_Lean_Meta_simp(v_e_2173_, v_a_2181_, v_a_2183_, v___x_2184_, v___x_2185_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_);
lean_dec(v_a_2178_);
lean_dec_ref(v_a_2177_);
lean_dec(v_a_2176_);
lean_dec_ref(v_a_2175_);
if (lean_obj_tag(v___x_2186_) == 0)
{
lean_object* v_a_2187_; lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2196_; 
v_a_2187_ = lean_ctor_get(v___x_2186_, 0);
v_isSharedCheck_2196_ = !lean_is_exclusive(v___x_2186_);
if (v_isSharedCheck_2196_ == 0)
{
v___x_2189_ = v___x_2186_;
v_isShared_2190_ = v_isSharedCheck_2196_;
goto v_resetjp_2188_;
}
else
{
lean_inc(v_a_2187_);
lean_dec(v___x_2186_);
v___x_2189_ = lean_box(0);
v_isShared_2190_ = v_isSharedCheck_2196_;
goto v_resetjp_2188_;
}
v_resetjp_2188_:
{
lean_object* v_fst_2191_; lean_object* v_expr_2192_; lean_object* v___x_2194_; 
v_fst_2191_ = lean_ctor_get(v_a_2187_, 0);
lean_inc(v_fst_2191_);
lean_dec(v_a_2187_);
v_expr_2192_ = lean_ctor_get(v_fst_2191_, 0);
lean_inc_ref(v_expr_2192_);
lean_dec(v_fst_2191_);
if (v_isShared_2190_ == 0)
{
lean_ctor_set(v___x_2189_, 0, v_expr_2192_);
v___x_2194_ = v___x_2189_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v_expr_2192_);
v___x_2194_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
return v___x_2194_;
}
}
}
else
{
lean_object* v_a_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2204_; 
v_a_2197_ = lean_ctor_get(v___x_2186_, 0);
v_isSharedCheck_2204_ = !lean_is_exclusive(v___x_2186_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2199_ = v___x_2186_;
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_a_2197_);
lean_dec(v___x_2186_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
lean_object* v___x_2202_; 
if (v_isShared_2200_ == 0)
{
v___x_2202_ = v___x_2199_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v_a_2197_);
v___x_2202_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
return v___x_2202_;
}
}
}
}
else
{
lean_object* v_a_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2212_; 
lean_dec(v_a_2181_);
lean_dec(v_a_2178_);
lean_dec_ref(v_a_2177_);
lean_dec(v_a_2176_);
lean_dec_ref(v_a_2175_);
lean_dec_ref(v_e_2173_);
v_a_2205_ = lean_ctor_get(v___x_2182_, 0);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2182_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2207_ = v___x_2182_;
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_a_2205_);
lean_dec(v___x_2182_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2210_; 
if (v_isShared_2208_ == 0)
{
v___x_2210_ = v___x_2207_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v_a_2205_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
}
else
{
lean_object* v_a_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2220_; 
lean_dec(v_a_2178_);
lean_dec_ref(v_a_2177_);
lean_dec(v_a_2176_);
lean_dec_ref(v_a_2175_);
lean_dec_ref(v_e_2173_);
v_a_2213_ = lean_ctor_get(v___x_2180_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2180_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2215_ = v___x_2180_;
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_a_2213_);
lean_dec(v___x_2180_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2218_; 
if (v_isShared_2216_ == 0)
{
v___x_2218_ = v___x_2215_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v_a_2213_);
v___x_2218_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
return v___x_2218_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normalizeImp___boxed(lean_object* v_e_2221_, lean_object* v_config_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_){
_start:
{
lean_object* v_res_2228_; 
v_res_2228_ = lean_grind_normalize(v_e_2221_, v_config_2222_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_);
return v_res_2228_;
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
lean_object* runtime_initialize_Lean_OrderLevel(uint8_t builtin);
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
res = runtime_initialize_Lean_OrderLevel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_13_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_14_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3828017814____hygCtx___hyg_11_();
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
lean_object* initialize_Lean_OrderLevel(uint8_t builtin);
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
res = initialize_Lean_OrderLevel(builtin);
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
