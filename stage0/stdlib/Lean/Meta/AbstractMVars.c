// Lean compiler output
// Module: Lean.Meta.AbstractMVars
// Imports: public import Lean.Meta.Basic
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
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_get(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_noption_get(lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableLevelMVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_Lean_instBEqLevelMVarId_beq(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t l_Lean_Level_hasMVar(lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_mkLevelMax_x27(lean_object*, lean_object*);
lean_object* l_Lean_simpLevelMax_x27(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelIMax_x27(lean_object*, lean_object*);
lean_object* l_Lean_simpLevelIMax_x27(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getLevelDepth(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_MetavarContext_getDecl(lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
uint8_t l_ptrEqList___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Expr_instantiateLevelParamsArray(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_AbstractMVarsResult_numMVars(lean_object*);
lean_object* l_Lean_Meta_lambdaMetaTelescope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_mkLambda(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_instMonadMCtxM___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_instMonadMCtxM___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_instMonadMCtxM___lam__1(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_AbstractMVars_instMonadMCtxM___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__0 = (const lean_object*)&l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__0_value;
static const lean_closure_object l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_AbstractMVars_instMonadMCtxM___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__1 = (const lean_object*)&l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__1_value;
static const lean_closure_object l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__2 = (const lean_object*)&l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__2_value;
static const lean_closure_object l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__3 = (const lean_object*)&l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__3_value;
static const lean_closure_object l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__4 = (const lean_object*)&l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__4_value;
static const lean_closure_object l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__5 = (const lean_object*)&l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__5_value;
static const lean_closure_object l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__6 = (const lean_object*)&l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__6_value;
static const lean_closure_object l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__7 = (const lean_object*)&l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__7_value;
static const lean_closure_object l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__8 = (const lean_object*)&l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__8_value;
static const lean_ctor_object l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__2_value),((lean_object*)&l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__3_value)}};
static const lean_object* l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__9 = (const lean_object*)&l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__9_value;
static const lean_ctor_object l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__9_value),((lean_object*)&l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__4_value),((lean_object*)&l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__5_value),((lean_object*)&l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__6_value),((lean_object*)&l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__7_value)}};
static const lean_object* l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__10 = (const lean_object*)&l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__10_value;
static const lean_ctor_object l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__10_value),((lean_object*)&l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__8_value)}};
static const lean_object* l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__11 = (const lean_object*)&l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__11_value;
static const lean_closure_object l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_get, .m_arity = 4, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__11_value)} };
static const lean_object* l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__12 = (const lean_object*)&l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__12_value;
static const lean_closure_object l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_bind, .m_arity = 8, .m_num_fixed = 7, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__12_value),((lean_object*)&l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__0_value)} };
static const lean_object* l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__13 = (const lean_object*)&l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__13_value;
static const lean_ctor_object l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__13_value),((lean_object*)&l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__1_value)}};
static const lean_object* l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__14 = (const lean_object*)&l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__14_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_AbstractMVars_instMonadMCtxM = (const lean_object*)&l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__14_value;
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_mkFreshId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_mkFreshFVarId(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__2_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "_abstMVar"};
static const lean_object* l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___closed__0 = (const lean_object*)&l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 80, 199, 96, 248, 174, 59, 88)}};
static const lean_object* l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___closed__1 = (const lean_object*)&l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__2_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__3_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__3_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__3_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__3___redArg___boxed(lean_object*);
static const lean_string_object l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__0 = (const lean_object*)&l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__0_value;
static const lean_ctor_object l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__1 = (const lean_object*)&l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_abstractExprMVars(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__3_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__3_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_abstractMVars___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_abstractMVars___closed__0 = (const lean_object*)&l_Lean_Meta_abstractMVars___closed__0_value;
static lean_once_cell_t l_Lean_Meta_abstractMVars___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_abstractMVars___closed__1;
static lean_once_cell_t l_Lean_Meta_abstractMVars___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_abstractMVars___closed__2;
static lean_once_cell_t l_Lean_Meta_abstractMVars___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_abstractMVars___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_abstractMVars(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_openAbstractMVarsResult_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_openAbstractMVarsResult_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_openAbstractMVarsResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_openAbstractMVarsResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_instMonadMCtxM___lam__0(lean_object* v_____do__lift_1_, lean_object* v___y_2_){
_start:
{
lean_object* v_mctx_3_; lean_object* v___x_4_; 
v_mctx_3_ = lean_ctor_get(v_____do__lift_1_, 2);
lean_inc_ref(v_mctx_3_);
v___x_4_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4_, 0, v_mctx_3_);
lean_ctor_set(v___x_4_, 1, v___y_2_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_instMonadMCtxM___lam__0___boxed(lean_object* v_____do__lift_5_, lean_object* v___y_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = l_Lean_Meta_AbstractMVars_instMonadMCtxM___lam__0(v_____do__lift_5_, v___y_6_);
lean_dec_ref(v_____do__lift_5_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_instMonadMCtxM___lam__1(lean_object* v_f_8_, lean_object* v___y_9_){
_start:
{
lean_object* v_ngen_10_; lean_object* v_lctx_11_; lean_object* v_mctx_12_; lean_object* v_nextParamIdx_13_; lean_object* v_paramNames_14_; lean_object* v_fvars_15_; lean_object* v_mvars_16_; lean_object* v_lmap_17_; lean_object* v_emap_18_; uint8_t v_abstractLevels_19_; lean_object* v___x_21_; uint8_t v_isShared_22_; uint8_t v_isSharedCheck_29_; 
v_ngen_10_ = lean_ctor_get(v___y_9_, 0);
v_lctx_11_ = lean_ctor_get(v___y_9_, 1);
v_mctx_12_ = lean_ctor_get(v___y_9_, 2);
v_nextParamIdx_13_ = lean_ctor_get(v___y_9_, 3);
v_paramNames_14_ = lean_ctor_get(v___y_9_, 4);
v_fvars_15_ = lean_ctor_get(v___y_9_, 5);
v_mvars_16_ = lean_ctor_get(v___y_9_, 6);
v_lmap_17_ = lean_ctor_get(v___y_9_, 7);
v_emap_18_ = lean_ctor_get(v___y_9_, 8);
v_abstractLevels_19_ = lean_ctor_get_uint8(v___y_9_, sizeof(void*)*9);
v_isSharedCheck_29_ = !lean_is_exclusive(v___y_9_);
if (v_isSharedCheck_29_ == 0)
{
v___x_21_ = v___y_9_;
v_isShared_22_ = v_isSharedCheck_29_;
goto v_resetjp_20_;
}
else
{
lean_inc(v_emap_18_);
lean_inc(v_lmap_17_);
lean_inc(v_mvars_16_);
lean_inc(v_fvars_15_);
lean_inc(v_paramNames_14_);
lean_inc(v_nextParamIdx_13_);
lean_inc(v_mctx_12_);
lean_inc(v_lctx_11_);
lean_inc(v_ngen_10_);
lean_dec(v___y_9_);
v___x_21_ = lean_box(0);
v_isShared_22_ = v_isSharedCheck_29_;
goto v_resetjp_20_;
}
v_resetjp_20_:
{
lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_26_; 
v___x_23_ = lean_box(0);
v___x_24_ = lean_apply_1(v_f_8_, v_mctx_12_);
if (v_isShared_22_ == 0)
{
lean_ctor_set(v___x_21_, 2, v___x_24_);
v___x_26_ = v___x_21_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_28_; 
v_reuseFailAlloc_28_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_28_, 0, v_ngen_10_);
lean_ctor_set(v_reuseFailAlloc_28_, 1, v_lctx_11_);
lean_ctor_set(v_reuseFailAlloc_28_, 2, v___x_24_);
lean_ctor_set(v_reuseFailAlloc_28_, 3, v_nextParamIdx_13_);
lean_ctor_set(v_reuseFailAlloc_28_, 4, v_paramNames_14_);
lean_ctor_set(v_reuseFailAlloc_28_, 5, v_fvars_15_);
lean_ctor_set(v_reuseFailAlloc_28_, 6, v_mvars_16_);
lean_ctor_set(v_reuseFailAlloc_28_, 7, v_lmap_17_);
lean_ctor_set(v_reuseFailAlloc_28_, 8, v_emap_18_);
lean_ctor_set_uint8(v_reuseFailAlloc_28_, sizeof(void*)*9, v_abstractLevels_19_);
v___x_26_ = v_reuseFailAlloc_28_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
lean_object* v___x_27_; 
v___x_27_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_27_, 0, v___x_23_);
lean_ctor_set(v___x_27_, 1, v___x_26_);
return v___x_27_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_mkFreshId(lean_object* v_a_61_){
_start:
{
lean_object* v_ngen_62_; lean_object* v_lctx_63_; lean_object* v_mctx_64_; lean_object* v_nextParamIdx_65_; lean_object* v_paramNames_66_; lean_object* v_fvars_67_; lean_object* v_mvars_68_; lean_object* v_lmap_69_; lean_object* v_emap_70_; uint8_t v_abstractLevels_71_; lean_object* v___x_73_; uint8_t v_isShared_74_; uint8_t v_isSharedCheck_91_; 
v_ngen_62_ = lean_ctor_get(v_a_61_, 0);
v_lctx_63_ = lean_ctor_get(v_a_61_, 1);
v_mctx_64_ = lean_ctor_get(v_a_61_, 2);
v_nextParamIdx_65_ = lean_ctor_get(v_a_61_, 3);
v_paramNames_66_ = lean_ctor_get(v_a_61_, 4);
v_fvars_67_ = lean_ctor_get(v_a_61_, 5);
v_mvars_68_ = lean_ctor_get(v_a_61_, 6);
v_lmap_69_ = lean_ctor_get(v_a_61_, 7);
v_emap_70_ = lean_ctor_get(v_a_61_, 8);
v_abstractLevels_71_ = lean_ctor_get_uint8(v_a_61_, sizeof(void*)*9);
v_isSharedCheck_91_ = !lean_is_exclusive(v_a_61_);
if (v_isSharedCheck_91_ == 0)
{
v___x_73_ = v_a_61_;
v_isShared_74_ = v_isSharedCheck_91_;
goto v_resetjp_72_;
}
else
{
lean_inc(v_emap_70_);
lean_inc(v_lmap_69_);
lean_inc(v_mvars_68_);
lean_inc(v_fvars_67_);
lean_inc(v_paramNames_66_);
lean_inc(v_nextParamIdx_65_);
lean_inc(v_mctx_64_);
lean_inc(v_lctx_63_);
lean_inc(v_ngen_62_);
lean_dec(v_a_61_);
v___x_73_ = lean_box(0);
v_isShared_74_ = v_isSharedCheck_91_;
goto v_resetjp_72_;
}
v_resetjp_72_:
{
lean_object* v_namePrefix_75_; lean_object* v_idx_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_90_; 
v_namePrefix_75_ = lean_ctor_get(v_ngen_62_, 0);
v_idx_76_ = lean_ctor_get(v_ngen_62_, 1);
v_isSharedCheck_90_ = !lean_is_exclusive(v_ngen_62_);
if (v_isSharedCheck_90_ == 0)
{
v___x_78_ = v_ngen_62_;
v_isShared_79_ = v_isSharedCheck_90_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_idx_76_);
lean_inc(v_namePrefix_75_);
lean_dec(v_ngen_62_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_90_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_84_; 
lean_inc(v_idx_76_);
lean_inc(v_namePrefix_75_);
v___x_80_ = l_Lean_Name_num___override(v_namePrefix_75_, v_idx_76_);
v___x_81_ = lean_unsigned_to_nat(1u);
v___x_82_ = lean_nat_add(v_idx_76_, v___x_81_);
lean_dec(v_idx_76_);
if (v_isShared_79_ == 0)
{
lean_ctor_set(v___x_78_, 1, v___x_82_);
v___x_84_ = v___x_78_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v_namePrefix_75_);
lean_ctor_set(v_reuseFailAlloc_89_, 1, v___x_82_);
v___x_84_ = v_reuseFailAlloc_89_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
lean_object* v___x_86_; 
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 0, v___x_84_);
v___x_86_ = v___x_73_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v___x_84_);
lean_ctor_set(v_reuseFailAlloc_88_, 1, v_lctx_63_);
lean_ctor_set(v_reuseFailAlloc_88_, 2, v_mctx_64_);
lean_ctor_set(v_reuseFailAlloc_88_, 3, v_nextParamIdx_65_);
lean_ctor_set(v_reuseFailAlloc_88_, 4, v_paramNames_66_);
lean_ctor_set(v_reuseFailAlloc_88_, 5, v_fvars_67_);
lean_ctor_set(v_reuseFailAlloc_88_, 6, v_mvars_68_);
lean_ctor_set(v_reuseFailAlloc_88_, 7, v_lmap_69_);
lean_ctor_set(v_reuseFailAlloc_88_, 8, v_emap_70_);
lean_ctor_set_uint8(v_reuseFailAlloc_88_, sizeof(void*)*9, v_abstractLevels_71_);
v___x_86_ = v_reuseFailAlloc_88_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
lean_object* v___x_87_; 
v___x_87_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_87_, 0, v___x_80_);
lean_ctor_set(v___x_87_, 1, v___x_86_);
return v___x_87_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_mkFreshFVarId(lean_object* v_a_92_){
_start:
{
lean_object* v___x_93_; lean_object* v_fst_94_; lean_object* v_snd_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_102_; 
v___x_93_ = l_Lean_Meta_AbstractMVars_mkFreshId(v_a_92_);
v_fst_94_ = lean_ctor_get(v___x_93_, 0);
v_snd_95_ = lean_ctor_get(v___x_93_, 1);
v_isSharedCheck_102_ = !lean_is_exclusive(v___x_93_);
if (v_isSharedCheck_102_ == 0)
{
v___x_97_ = v___x_93_;
v_isShared_98_ = v_isSharedCheck_102_;
goto v_resetjp_96_;
}
else
{
lean_inc(v_snd_95_);
lean_inc(v_fst_94_);
lean_dec(v___x_93_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_102_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
lean_object* v___x_100_; 
if (v_isShared_98_ == 0)
{
v___x_100_ = v___x_97_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v_fst_94_);
lean_ctor_set(v_reuseFailAlloc_101_, 1, v_snd_95_);
v___x_100_ = v_reuseFailAlloc_101_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
return v___x_100_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2___redArg(lean_object* v_m_103_, lean_object* v_query_104_, lean_object* v_x_105_, lean_object* v_x_106_, lean_object* v_x_107_){
_start:
{
lean_object* v_zero_108_; uint8_t v_isZero_109_; 
v_zero_108_ = lean_unsigned_to_nat(0u);
v_isZero_109_ = lean_nat_dec_eq(v_x_106_, v_zero_108_);
if (v_isZero_109_ == 1)
{
lean_dec(v_x_107_);
lean_dec(v_x_106_);
if (lean_obj_tag(v_x_105_) == 0)
{
lean_object* v___x_110_; 
v___x_110_ = lean_box(2);
return v___x_110_;
}
else
{
lean_object* v_val_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_118_; 
v_val_111_ = lean_ctor_get(v_x_105_, 0);
v_isSharedCheck_118_ = !lean_is_exclusive(v_x_105_);
if (v_isSharedCheck_118_ == 0)
{
v___x_113_ = v_x_105_;
v_isShared_114_ = v_isSharedCheck_118_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_val_111_);
lean_dec(v_x_105_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_118_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v___x_116_; 
if (v_isShared_114_ == 0)
{
v___x_116_ = v___x_113_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v_val_111_);
v___x_116_ = v_reuseFailAlloc_117_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
return v___x_116_;
}
}
}
}
else
{
lean_object* v_keyArray_119_; lean_object* v_valueArray_120_; lean_object* v___x_121_; uint8_t v_isSome_122_; 
v_keyArray_119_ = lean_ctor_get(v_m_103_, 1);
v_valueArray_120_ = lean_ctor_get(v_m_103_, 2);
v___x_121_ = lean_array_fget_borrowed(v_keyArray_119_, v_x_107_);
v_isSome_122_ = lean_noption_is_some(v___x_121_);
if (v_isSome_122_ == 0)
{
lean_dec(v_x_106_);
if (lean_obj_tag(v_x_105_) == 0)
{
lean_object* v___x_123_; 
v___x_123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_123_, 0, v_x_107_);
return v___x_123_;
}
else
{
lean_object* v_val_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_131_; 
lean_dec(v_x_107_);
v_val_124_ = lean_ctor_get(v_x_105_, 0);
v_isSharedCheck_131_ = !lean_is_exclusive(v_x_105_);
if (v_isSharedCheck_131_ == 0)
{
v___x_126_ = v_x_105_;
v_isShared_127_ = v_isSharedCheck_131_;
goto v_resetjp_125_;
}
else
{
lean_inc(v_val_124_);
lean_dec(v_x_105_);
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
lean_ctor_set(v_reuseFailAlloc_130_, 0, v_val_124_);
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
lean_object* v_one_132_; lean_object* v_n_133_; lean_object* v___y_135_; 
v_one_132_ = lean_unsigned_to_nat(1u);
v_n_133_ = lean_nat_sub(v_x_106_, v_one_132_);
lean_dec(v_x_106_);
if (v_isSome_122_ == 0)
{
goto v___jp_141_;
}
else
{
lean_object* v___x_143_; uint8_t v_isSome_144_; 
v___x_143_ = lean_array_fget_borrowed(v_valueArray_120_, v_x_107_);
v_isSome_144_ = lean_noption_is_some(v___x_143_);
if (v_isSome_144_ == 0)
{
goto v___jp_141_;
}
else
{
lean_object* v_val_145_; uint8_t v___x_146_; 
lean_inc(v___x_121_);
v_val_145_ = lean_noption_get(v___x_121_);
v___x_146_ = l_Lean_instBEqLevelMVarId_beq(v_val_145_, v_query_104_);
if (v___x_146_ == 0)
{
lean_object* v___x_147_; lean_object* v___x_148_; uint8_t v___x_149_; 
lean_dec(v_val_145_);
v___x_147_ = lean_array_get_size(v_keyArray_119_);
v___x_148_ = lean_nat_add(v_x_107_, v_one_132_);
lean_dec(v_x_107_);
v___x_149_ = lean_nat_dec_lt(v___x_148_, v___x_147_);
if (v___x_149_ == 0)
{
lean_dec(v___x_148_);
v_x_106_ = v_n_133_;
v_x_107_ = v_zero_108_;
goto _start;
}
else
{
v_x_106_ = v_n_133_;
v_x_107_ = v___x_148_;
goto _start;
}
}
else
{
lean_object* v_val_152_; lean_object* v___x_153_; 
lean_dec(v_n_133_);
lean_dec(v_x_105_);
lean_inc(v___x_143_);
v_val_152_ = lean_noption_get(v___x_143_);
v___x_153_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_153_, 0, v_x_107_);
lean_ctor_set(v___x_153_, 1, v_val_145_);
lean_ctor_set(v___x_153_, 2, v_val_152_);
return v___x_153_;
}
}
}
v___jp_134_:
{
lean_object* v___x_136_; lean_object* v___x_137_; uint8_t v___x_138_; 
v___x_136_ = lean_array_get_size(v_keyArray_119_);
v___x_137_ = lean_nat_add(v_x_107_, v_one_132_);
lean_dec(v_x_107_);
v___x_138_ = lean_nat_dec_lt(v___x_137_, v___x_136_);
if (v___x_138_ == 0)
{
lean_dec(v___x_137_);
v_x_105_ = v___y_135_;
v_x_106_ = v_n_133_;
v_x_107_ = v_zero_108_;
goto _start;
}
else
{
v_x_105_ = v___y_135_;
v_x_106_ = v_n_133_;
v_x_107_ = v___x_137_;
goto _start;
}
}
v___jp_141_:
{
if (lean_obj_tag(v_x_105_) == 0)
{
lean_object* v___x_142_; 
lean_inc(v_x_107_);
v___x_142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_142_, 0, v_x_107_);
v___y_135_ = v___x_142_;
goto v___jp_134_;
}
else
{
v___y_135_ = v_x_105_;
goto v___jp_134_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2___redArg___boxed(lean_object* v_m_154_, lean_object* v_query_155_, lean_object* v_x_156_, lean_object* v_x_157_, lean_object* v_x_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2___redArg(v_m_154_, v_query_155_, v_x_156_, v_x_157_, v_x_158_);
lean_dec(v_query_155_);
lean_dec_ref(v_m_154_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1___redArg(lean_object* v_m_160_, lean_object* v_query_161_){
_start:
{
lean_object* v_keyArray_162_; lean_object* v___x_163_; uint64_t v___x_164_; uint64_t v___x_165_; uint64_t v___x_166_; uint64_t v_fold_167_; uint64_t v___x_168_; uint64_t v___x_169_; uint64_t v___x_170_; size_t v___x_171_; size_t v___x_172_; size_t v___x_173_; size_t v___x_174_; size_t v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v_keyArray_162_ = lean_ctor_get(v_m_160_, 1);
v___x_163_ = lean_array_get_size(v_keyArray_162_);
v___x_164_ = l_Lean_instHashableLevelMVarId_hash(v_query_161_);
v___x_165_ = 32ULL;
v___x_166_ = lean_uint64_shift_right(v___x_164_, v___x_165_);
v_fold_167_ = lean_uint64_xor(v___x_164_, v___x_166_);
v___x_168_ = 16ULL;
v___x_169_ = lean_uint64_shift_right(v_fold_167_, v___x_168_);
v___x_170_ = lean_uint64_xor(v_fold_167_, v___x_169_);
v___x_171_ = lean_uint64_to_usize(v___x_170_);
v___x_172_ = lean_usize_of_nat(v___x_163_);
v___x_173_ = ((size_t)1ULL);
v___x_174_ = lean_usize_sub(v___x_172_, v___x_173_);
v___x_175_ = lean_usize_land(v___x_171_, v___x_174_);
v___x_176_ = lean_usize_to_nat(v___x_175_);
v___x_177_ = lean_box(0);
v___x_178_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2___redArg(v_m_160_, v_query_161_, v___x_177_, v___x_163_, v___x_176_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1___redArg___boxed(lean_object* v_m_179_, lean_object* v_query_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1___redArg(v_m_179_, v_query_180_);
lean_dec(v_query_180_);
lean_dec_ref(v_m_179_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__2_spec__4_spec__5___redArg(lean_object* v_b_182_, lean_object* v_acc_183_, lean_object* v_i_184_){
_start:
{
lean_object* v___y_186_; lean_object* v_keyArray_194_; lean_object* v_valueArray_195_; lean_object* v___x_196_; uint8_t v___x_197_; 
v_keyArray_194_ = lean_ctor_get(v_b_182_, 1);
v_valueArray_195_ = lean_ctor_get(v_b_182_, 2);
v___x_196_ = lean_array_get_size(v_keyArray_194_);
v___x_197_ = lean_nat_dec_lt(v_i_184_, v___x_196_);
if (v___x_197_ == 0)
{
lean_dec(v_i_184_);
return v_acc_183_;
}
else
{
lean_object* v___x_198_; uint8_t v_isSome_199_; 
v___x_198_ = lean_array_fget_borrowed(v_keyArray_194_, v_i_184_);
v_isSome_199_ = lean_noption_is_some(v___x_198_);
if (v_isSome_199_ == 0)
{
goto v___jp_190_;
}
else
{
lean_object* v___x_200_; uint8_t v_isSome_201_; 
v___x_200_ = lean_array_fget_borrowed(v_valueArray_195_, v_i_184_);
v_isSome_201_ = lean_noption_is_some(v___x_200_);
if (v_isSome_201_ == 0)
{
goto v___jp_190_;
}
else
{
lean_object* v_val_202_; lean_object* v_val_203_; lean_object* v_i_205_; lean_object* v___x_210_; 
lean_inc(v___x_198_);
v_val_202_ = lean_noption_get(v___x_198_);
lean_inc(v___x_200_);
v_val_203_ = lean_noption_get(v___x_200_);
v___x_210_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1___redArg(v_acc_183_, v_val_202_);
switch(lean_obj_tag(v___x_210_))
{
case 0:
{
lean_object* v_index_211_; lean_object* v_size_212_; lean_object* v___x_213_; 
v_index_211_ = lean_ctor_get(v___x_210_, 0);
lean_inc(v_index_211_);
lean_dec_ref_known(v___x_210_, 3);
v_size_212_ = lean_ctor_get(v_acc_183_, 0);
lean_inc(v_size_212_);
v___x_213_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_183_, v_size_212_, v_index_211_, v_val_202_, v_val_203_);
lean_dec(v_index_211_);
v___y_186_ = v___x_213_;
goto v___jp_185_;
}
case 1:
{
lean_object* v_index_214_; 
v_index_214_ = lean_ctor_get(v___x_210_, 0);
lean_inc(v_index_214_);
lean_dec_ref_known(v___x_210_, 1);
v_i_205_ = v_index_214_;
goto v___jp_204_;
}
default: 
{
lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_215_ = lean_unsigned_to_nat(0u);
v___x_216_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_183_, v___x_215_);
if (lean_obj_tag(v___x_216_) == 0)
{
lean_object* v_index_217_; 
v_index_217_ = lean_ctor_get(v___x_216_, 0);
lean_inc(v_index_217_);
lean_dec_ref_known(v___x_216_, 1);
v_i_205_ = v_index_217_;
goto v___jp_204_;
}
else
{
lean_dec(v_val_203_);
lean_dec(v_val_202_);
v___y_186_ = v_acc_183_;
goto v___jp_185_;
}
}
}
v___jp_204_:
{
lean_object* v_size_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v_size_206_ = lean_ctor_get(v_acc_183_, 0);
v___x_207_ = lean_unsigned_to_nat(1u);
v___x_208_ = lean_nat_add(v_size_206_, v___x_207_);
v___x_209_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_183_, v___x_208_, v_i_205_, v_val_202_, v_val_203_);
lean_dec(v_i_205_);
v___y_186_ = v___x_209_;
goto v___jp_185_;
}
}
}
}
v___jp_185_:
{
lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_187_ = lean_unsigned_to_nat(1u);
v___x_188_ = lean_nat_add(v_i_184_, v___x_187_);
lean_dec(v_i_184_);
v_acc_183_ = v___y_186_;
v_i_184_ = v___x_188_;
goto _start;
}
v___jp_190_:
{
lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_191_ = lean_unsigned_to_nat(1u);
v___x_192_ = lean_nat_add(v_i_184_, v___x_191_);
lean_dec(v_i_184_);
v_i_184_ = v___x_192_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_b_218_, lean_object* v_acc_219_, lean_object* v_i_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__2_spec__4_spec__5___redArg(v_b_218_, v_acc_219_, v_i_220_);
lean_dec_ref(v_b_218_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__2_spec__4___redArg(lean_object* v_init_222_, lean_object* v_b_223_){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_224_ = lean_unsigned_to_nat(0u);
v___x_225_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__2_spec__4_spec__5___redArg(v_b_223_, v_init_222_, v___x_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__2_spec__4___redArg___boxed(lean_object* v_init_226_, lean_object* v_b_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__2_spec__4___redArg(v_init_226_, v_b_227_);
lean_dec_ref(v_b_227_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__2___redArg(lean_object* v_m_229_){
_start:
{
lean_object* v_keyArray_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v_cellCount_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v_target_237_; lean_object* v___x_238_; 
v_keyArray_230_ = lean_ctor_get(v_m_229_, 1);
v___x_231_ = lean_array_get_size(v_keyArray_230_);
v___x_232_ = lean_unsigned_to_nat(2u);
v_cellCount_233_ = lean_nat_mul(v___x_231_, v___x_232_);
v___x_234_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_233_);
v___x_235_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_233_);
v___x_236_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_233_);
v_target_237_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_237_, 0, v___x_234_);
lean_ctor_set(v_target_237_, 1, v___x_235_);
lean_ctor_set(v_target_237_, 2, v___x_236_);
v___x_238_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__2_spec__4___redArg(v_target_237_, v_m_229_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__2___redArg___boxed(lean_object* v_m_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__2___redArg(v_m_239_);
lean_dec_ref(v_m_239_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0___redArg(lean_object* v_m_241_, lean_object* v_query_242_){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1___redArg(v_m_241_, v_query_242_);
if (lean_obj_tag(v___x_243_) == 0)
{
lean_object* v_index_244_; lean_object* v_key_245_; lean_object* v_value_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_253_; 
v_index_244_ = lean_ctor_get(v___x_243_, 0);
v_key_245_ = lean_ctor_get(v___x_243_, 1);
v_value_246_ = lean_ctor_get(v___x_243_, 2);
v_isSharedCheck_253_ = !lean_is_exclusive(v___x_243_);
if (v_isSharedCheck_253_ == 0)
{
v___x_248_ = v___x_243_;
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_value_246_);
lean_inc(v_key_245_);
lean_inc(v_index_244_);
lean_dec(v___x_243_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_251_; 
if (v_isShared_249_ == 0)
{
v___x_251_ = v___x_248_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v_index_244_);
lean_ctor_set(v_reuseFailAlloc_252_, 1, v_key_245_);
lean_ctor_set(v_reuseFailAlloc_252_, 2, v_value_246_);
v___x_251_ = v_reuseFailAlloc_252_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
return v___x_251_;
}
}
}
else
{
lean_object* v___x_254_; 
lean_dec(v___x_243_);
v___x_254_ = lean_box(1);
return v___x_254_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0___redArg___boxed(lean_object* v_m_255_, lean_object* v_query_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0___redArg(v_m_255_, v_query_256_);
lean_dec(v_query_256_);
lean_dec_ref(v_m_255_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___redArg(lean_object* v_m_258_, lean_object* v_a_259_){
_start:
{
lean_object* v___x_260_; 
v___x_260_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0___redArg(v_m_258_, v_a_259_);
if (lean_obj_tag(v___x_260_) == 0)
{
lean_object* v_value_261_; lean_object* v___x_262_; 
v_value_261_ = lean_ctor_get(v___x_260_, 2);
lean_inc(v_value_261_);
lean_dec_ref_known(v___x_260_, 3);
v___x_262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_262_, 0, v_value_261_);
return v___x_262_;
}
else
{
lean_object* v___x_263_; 
v___x_263_ = lean_box(0);
return v___x_263_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___redArg___boxed(lean_object* v_m_264_, lean_object* v_a_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___redArg(v_m_264_, v_a_265_);
lean_dec(v_a_265_);
lean_dec_ref(v_m_264_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(lean_object* v_u_270_, lean_object* v_a_271_){
_start:
{
uint8_t v_abstractLevels_272_; 
v_abstractLevels_272_ = lean_ctor_get_uint8(v_a_271_, sizeof(void*)*9);
if (v_abstractLevels_272_ == 0)
{
lean_object* v___x_273_; 
v___x_273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_273_, 0, v_u_270_);
lean_ctor_set(v___x_273_, 1, v_a_271_);
return v___x_273_;
}
else
{
lean_object* v_ngen_274_; lean_object* v_lctx_275_; lean_object* v_mctx_276_; lean_object* v_nextParamIdx_277_; lean_object* v_paramNames_278_; lean_object* v_fvars_279_; lean_object* v_mvars_280_; lean_object* v_lmap_281_; lean_object* v_emap_282_; uint8_t v___x_283_; 
v_ngen_274_ = lean_ctor_get(v_a_271_, 0);
v_lctx_275_ = lean_ctor_get(v_a_271_, 1);
v_mctx_276_ = lean_ctor_get(v_a_271_, 2);
v_nextParamIdx_277_ = lean_ctor_get(v_a_271_, 3);
v_paramNames_278_ = lean_ctor_get(v_a_271_, 4);
v_fvars_279_ = lean_ctor_get(v_a_271_, 5);
v_mvars_280_ = lean_ctor_get(v_a_271_, 6);
v_lmap_281_ = lean_ctor_get(v_a_271_, 7);
v_emap_282_ = lean_ctor_get(v_a_271_, 8);
v___x_283_ = l_Lean_Level_hasMVar(v_u_270_);
if (v___x_283_ == 0)
{
lean_object* v___x_284_; 
v___x_284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_284_, 0, v_u_270_);
lean_ctor_set(v___x_284_, 1, v_a_271_);
return v___x_284_;
}
else
{
switch(lean_obj_tag(v_u_270_))
{
case 1:
{
lean_object* v_a_285_; lean_object* v___x_286_; lean_object* v_fst_287_; lean_object* v_snd_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_302_; 
v_a_285_ = lean_ctor_get(v_u_270_, 0);
lean_inc(v_a_285_);
v___x_286_ = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(v_a_285_, v_a_271_);
v_fst_287_ = lean_ctor_get(v___x_286_, 0);
v_snd_288_ = lean_ctor_get(v___x_286_, 1);
v_isSharedCheck_302_ = !lean_is_exclusive(v___x_286_);
if (v_isSharedCheck_302_ == 0)
{
v___x_290_ = v___x_286_;
v_isShared_291_ = v_isSharedCheck_302_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_snd_288_);
lean_inc(v_fst_287_);
lean_dec(v___x_286_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_302_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
size_t v___x_292_; size_t v___x_293_; uint8_t v___x_294_; 
v___x_292_ = lean_ptr_addr(v_a_285_);
v___x_293_ = lean_ptr_addr(v_fst_287_);
v___x_294_ = lean_usize_dec_eq(v___x_292_, v___x_293_);
if (v___x_294_ == 0)
{
lean_object* v___x_295_; lean_object* v___x_297_; 
lean_dec_ref_known(v_u_270_, 1);
v___x_295_ = l_Lean_Level_succ___override(v_fst_287_);
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 0, v___x_295_);
v___x_297_ = v___x_290_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v___x_295_);
lean_ctor_set(v_reuseFailAlloc_298_, 1, v_snd_288_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
else
{
lean_object* v___x_300_; 
lean_dec(v_fst_287_);
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 0, v_u_270_);
v___x_300_ = v___x_290_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v_u_270_);
lean_ctor_set(v_reuseFailAlloc_301_, 1, v_snd_288_);
v___x_300_ = v_reuseFailAlloc_301_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
return v___x_300_;
}
}
}
}
case 2:
{
lean_object* v_a_303_; lean_object* v_a_304_; lean_object* v___x_305_; lean_object* v_fst_306_; lean_object* v_snd_307_; lean_object* v___x_308_; lean_object* v_fst_309_; lean_object* v_snd_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_330_; 
v_a_303_ = lean_ctor_get(v_u_270_, 0);
v_a_304_ = lean_ctor_get(v_u_270_, 1);
lean_inc(v_a_303_);
v___x_305_ = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(v_a_303_, v_a_271_);
v_fst_306_ = lean_ctor_get(v___x_305_, 0);
lean_inc(v_fst_306_);
v_snd_307_ = lean_ctor_get(v___x_305_, 1);
lean_inc(v_snd_307_);
lean_dec_ref(v___x_305_);
lean_inc(v_a_304_);
v___x_308_ = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(v_a_304_, v_snd_307_);
v_fst_309_ = lean_ctor_get(v___x_308_, 0);
v_snd_310_ = lean_ctor_get(v___x_308_, 1);
v_isSharedCheck_330_ = !lean_is_exclusive(v___x_308_);
if (v_isSharedCheck_330_ == 0)
{
v___x_312_ = v___x_308_;
v_isShared_313_ = v_isSharedCheck_330_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_snd_310_);
lean_inc(v_fst_309_);
lean_dec(v___x_308_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_330_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
uint8_t v___y_315_; size_t v___x_324_; size_t v___x_325_; uint8_t v___x_326_; 
v___x_324_ = lean_ptr_addr(v_a_303_);
v___x_325_ = lean_ptr_addr(v_fst_306_);
v___x_326_ = lean_usize_dec_eq(v___x_324_, v___x_325_);
if (v___x_326_ == 0)
{
v___y_315_ = v___x_326_;
goto v___jp_314_;
}
else
{
size_t v___x_327_; size_t v___x_328_; uint8_t v___x_329_; 
v___x_327_ = lean_ptr_addr(v_a_304_);
v___x_328_ = lean_ptr_addr(v_fst_309_);
v___x_329_ = lean_usize_dec_eq(v___x_327_, v___x_328_);
v___y_315_ = v___x_329_;
goto v___jp_314_;
}
v___jp_314_:
{
if (v___y_315_ == 0)
{
lean_object* v___x_316_; lean_object* v___x_318_; 
lean_dec_ref_known(v_u_270_, 2);
v___x_316_ = l_Lean_mkLevelMax_x27(v_fst_306_, v_fst_309_);
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 0, v___x_316_);
v___x_318_ = v___x_312_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v___x_316_);
lean_ctor_set(v_reuseFailAlloc_319_, 1, v_snd_310_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
else
{
lean_object* v___x_320_; lean_object* v___x_322_; 
v___x_320_ = l_Lean_simpLevelMax_x27(v_fst_306_, v_fst_309_, v_u_270_);
lean_dec_ref_known(v_u_270_, 2);
lean_dec(v_fst_309_);
lean_dec(v_fst_306_);
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 0, v___x_320_);
v___x_322_ = v___x_312_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v___x_320_);
lean_ctor_set(v_reuseFailAlloc_323_, 1, v_snd_310_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
}
}
}
case 3:
{
lean_object* v_a_331_; lean_object* v_a_332_; lean_object* v___x_333_; lean_object* v_fst_334_; lean_object* v_snd_335_; lean_object* v___x_336_; lean_object* v_fst_337_; lean_object* v_snd_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_358_; 
v_a_331_ = lean_ctor_get(v_u_270_, 0);
v_a_332_ = lean_ctor_get(v_u_270_, 1);
lean_inc(v_a_331_);
v___x_333_ = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(v_a_331_, v_a_271_);
v_fst_334_ = lean_ctor_get(v___x_333_, 0);
lean_inc(v_fst_334_);
v_snd_335_ = lean_ctor_get(v___x_333_, 1);
lean_inc(v_snd_335_);
lean_dec_ref(v___x_333_);
lean_inc(v_a_332_);
v___x_336_ = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(v_a_332_, v_snd_335_);
v_fst_337_ = lean_ctor_get(v___x_336_, 0);
v_snd_338_ = lean_ctor_get(v___x_336_, 1);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_336_);
if (v_isSharedCheck_358_ == 0)
{
v___x_340_ = v___x_336_;
v_isShared_341_ = v_isSharedCheck_358_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_snd_338_);
lean_inc(v_fst_337_);
lean_dec(v___x_336_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_358_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
uint8_t v___y_343_; size_t v___x_352_; size_t v___x_353_; uint8_t v___x_354_; 
v___x_352_ = lean_ptr_addr(v_a_331_);
v___x_353_ = lean_ptr_addr(v_fst_334_);
v___x_354_ = lean_usize_dec_eq(v___x_352_, v___x_353_);
if (v___x_354_ == 0)
{
v___y_343_ = v___x_354_;
goto v___jp_342_;
}
else
{
size_t v___x_355_; size_t v___x_356_; uint8_t v___x_357_; 
v___x_355_ = lean_ptr_addr(v_a_332_);
v___x_356_ = lean_ptr_addr(v_fst_337_);
v___x_357_ = lean_usize_dec_eq(v___x_355_, v___x_356_);
v___y_343_ = v___x_357_;
goto v___jp_342_;
}
v___jp_342_:
{
if (v___y_343_ == 0)
{
lean_object* v___x_344_; lean_object* v___x_346_; 
lean_dec_ref_known(v_u_270_, 2);
v___x_344_ = l_Lean_mkLevelIMax_x27(v_fst_334_, v_fst_337_);
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 0, v___x_344_);
v___x_346_ = v___x_340_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v___x_344_);
lean_ctor_set(v_reuseFailAlloc_347_, 1, v_snd_338_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
else
{
lean_object* v___x_348_; lean_object* v___x_350_; 
v___x_348_ = l_Lean_simpLevelIMax_x27(v_fst_334_, v_fst_337_, v_u_270_);
lean_dec_ref_known(v_u_270_, 2);
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 0, v___x_348_);
v___x_350_ = v___x_340_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v___x_348_);
lean_ctor_set(v_reuseFailAlloc_351_, 1, v_snd_338_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
}
}
}
case 5:
{
lean_object* v_a_359_; lean_object* v_depth_360_; lean_object* v___x_361_; uint8_t v___x_362_; 
v_a_359_ = lean_ctor_get(v_u_270_, 0);
v_depth_360_ = lean_ctor_get(v_mctx_276_, 0);
lean_inc(v_a_359_);
v___x_361_ = l_Lean_MetavarContext_getLevelDepth(v_mctx_276_, v_a_359_);
v___x_362_ = lean_nat_dec_eq(v___x_361_, v_depth_360_);
lean_dec(v___x_361_);
if (v___x_362_ == 0)
{
lean_object* v___x_363_; 
v___x_363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_363_, 0, v_u_270_);
lean_ctor_set(v___x_363_, 1, v_a_271_);
return v___x_363_;
}
else
{
lean_object* v___x_364_; 
lean_inc(v_a_359_);
lean_dec_ref_known(v_u_270_, 1);
v___x_364_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___redArg(v_lmap_281_, v_a_359_);
if (lean_obj_tag(v___x_364_) == 0)
{
lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_440_; 
lean_inc_ref(v_emap_282_);
lean_inc_ref(v_lmap_281_);
lean_inc_ref(v_mvars_280_);
lean_inc_ref(v_fvars_279_);
lean_inc_ref(v_paramNames_278_);
lean_inc(v_nextParamIdx_277_);
lean_inc_ref(v_mctx_276_);
lean_inc_ref(v_lctx_275_);
lean_inc_ref(v_ngen_274_);
v_isSharedCheck_440_ = !lean_is_exclusive(v_a_271_);
if (v_isSharedCheck_440_ == 0)
{
lean_object* v_unused_441_; lean_object* v_unused_442_; lean_object* v_unused_443_; lean_object* v_unused_444_; lean_object* v_unused_445_; lean_object* v_unused_446_; lean_object* v_unused_447_; lean_object* v_unused_448_; lean_object* v_unused_449_; 
v_unused_441_ = lean_ctor_get(v_a_271_, 8);
lean_dec(v_unused_441_);
v_unused_442_ = lean_ctor_get(v_a_271_, 7);
lean_dec(v_unused_442_);
v_unused_443_ = lean_ctor_get(v_a_271_, 6);
lean_dec(v_unused_443_);
v_unused_444_ = lean_ctor_get(v_a_271_, 5);
lean_dec(v_unused_444_);
v_unused_445_ = lean_ctor_get(v_a_271_, 4);
lean_dec(v_unused_445_);
v_unused_446_ = lean_ctor_get(v_a_271_, 3);
lean_dec(v_unused_446_);
v_unused_447_ = lean_ctor_get(v_a_271_, 2);
lean_dec(v_unused_447_);
v_unused_448_ = lean_ctor_get(v_a_271_, 1);
lean_dec(v_unused_448_);
v_unused_449_ = lean_ctor_get(v_a_271_, 0);
lean_dec(v_unused_449_);
v___x_366_ = v_a_271_;
v_isShared_367_ = v_isSharedCheck_440_;
goto v_resetjp_365_;
}
else
{
lean_dec(v_a_271_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_440_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___y_375_; lean_object* v___y_381_; lean_object* v_i_382_; lean_object* v___y_397_; lean_object* v_i_398_; lean_object* v___y_403_; lean_object* v___x_412_; 
v___x_368_ = ((lean_object*)(l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___closed__1));
lean_inc(v_nextParamIdx_277_);
v___x_369_ = l_Lean_Name_num___override(v___x_368_, v_nextParamIdx_277_);
lean_inc(v___x_369_);
v___x_370_ = l_Lean_mkLevelParam(v___x_369_);
v___x_371_ = lean_unsigned_to_nat(1u);
v___x_372_ = lean_nat_add(v_nextParamIdx_277_, v___x_371_);
lean_dec(v_nextParamIdx_277_);
v___x_373_ = lean_array_push(v_paramNames_278_, v___x_369_);
v___x_412_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1___redArg(v_lmap_281_, v_a_359_);
switch(lean_obj_tag(v___x_412_))
{
case 0:
{
lean_object* v_index_413_; lean_object* v_size_414_; lean_object* v___x_415_; 
v_index_413_ = lean_ctor_get(v___x_412_, 0);
lean_inc(v_index_413_);
lean_dec_ref_known(v___x_412_, 3);
v_size_414_ = lean_ctor_get(v_lmap_281_, 0);
lean_inc(v_size_414_);
lean_inc(v___x_370_);
v___x_415_ = l_Std_DHashMap_Raw_setEntry___redArg(v_lmap_281_, v_size_414_, v_index_413_, v_a_359_, v___x_370_);
lean_dec(v_index_413_);
v___y_375_ = v___x_415_;
goto v___jp_374_;
}
case 1:
{
lean_object* v_index_416_; lean_object* v_size_417_; lean_object* v_keyArray_418_; lean_object* v___x_419_; lean_object* v___x_420_; uint8_t v___x_421_; 
v_index_416_ = lean_ctor_get(v___x_412_, 0);
lean_inc(v_index_416_);
lean_dec_ref_known(v___x_412_, 1);
v_size_417_ = lean_ctor_get(v_lmap_281_, 0);
v_keyArray_418_ = lean_ctor_get(v_lmap_281_, 1);
v___x_419_ = lean_nat_add(v_size_417_, v___x_371_);
v___x_420_ = lean_array_get_size(v_keyArray_418_);
v___x_421_ = lean_nat_dec_lt(v___x_419_, v___x_420_);
if (v___x_421_ == 0)
{
lean_dec(v___x_419_);
lean_dec(v_index_416_);
goto v___jp_386_;
}
else
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; uint8_t v___x_426_; 
v___x_422_ = lean_unsigned_to_nat(4u);
v___x_423_ = lean_nat_mul(v___x_419_, v___x_422_);
v___x_424_ = lean_unsigned_to_nat(3u);
v___x_425_ = lean_nat_mul(v___x_420_, v___x_424_);
v___x_426_ = lean_nat_dec_le(v___x_423_, v___x_425_);
lean_dec(v___x_425_);
lean_dec(v___x_423_);
if (v___x_426_ == 0)
{
lean_dec(v___x_419_);
lean_dec(v_index_416_);
goto v___jp_386_;
}
else
{
lean_object* v___x_427_; 
lean_inc(v___x_370_);
v___x_427_ = l_Std_DHashMap_Raw_setEntry___redArg(v_lmap_281_, v___x_419_, v_index_416_, v_a_359_, v___x_370_);
lean_dec(v_index_416_);
v___y_375_ = v___x_427_;
goto v___jp_374_;
}
}
}
default: 
{
lean_object* v_size_428_; lean_object* v_keyArray_429_; lean_object* v___x_430_; lean_object* v___x_431_; uint8_t v___x_432_; 
v_size_428_ = lean_ctor_get(v_lmap_281_, 0);
v_keyArray_429_ = lean_ctor_get(v_lmap_281_, 1);
v___x_430_ = lean_nat_add(v_size_428_, v___x_371_);
v___x_431_ = lean_array_get_size(v_keyArray_429_);
v___x_432_ = lean_nat_dec_lt(v___x_430_, v___x_431_);
if (v___x_432_ == 0)
{
lean_object* v___x_433_; 
lean_dec(v___x_430_);
v___x_433_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__2___redArg(v_lmap_281_);
lean_dec_ref(v_lmap_281_);
v___y_403_ = v___x_433_;
goto v___jp_402_;
}
else
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; uint8_t v___x_438_; 
v___x_434_ = lean_unsigned_to_nat(4u);
v___x_435_ = lean_nat_mul(v___x_430_, v___x_434_);
lean_dec(v___x_430_);
v___x_436_ = lean_unsigned_to_nat(3u);
v___x_437_ = lean_nat_mul(v___x_431_, v___x_436_);
v___x_438_ = lean_nat_dec_le(v___x_435_, v___x_437_);
lean_dec(v___x_437_);
lean_dec(v___x_435_);
if (v___x_438_ == 0)
{
lean_object* v___x_439_; 
v___x_439_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__2___redArg(v_lmap_281_);
lean_dec_ref(v_lmap_281_);
v___y_403_ = v___x_439_;
goto v___jp_402_;
}
else
{
v___y_403_ = v_lmap_281_;
goto v___jp_402_;
}
}
}
}
v___jp_374_:
{
lean_object* v___x_377_; 
if (v_isShared_367_ == 0)
{
lean_ctor_set(v___x_366_, 7, v___y_375_);
lean_ctor_set(v___x_366_, 4, v___x_373_);
lean_ctor_set(v___x_366_, 3, v___x_372_);
v___x_377_ = v___x_366_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_ngen_274_);
lean_ctor_set(v_reuseFailAlloc_379_, 1, v_lctx_275_);
lean_ctor_set(v_reuseFailAlloc_379_, 2, v_mctx_276_);
lean_ctor_set(v_reuseFailAlloc_379_, 3, v___x_372_);
lean_ctor_set(v_reuseFailAlloc_379_, 4, v___x_373_);
lean_ctor_set(v_reuseFailAlloc_379_, 5, v_fvars_279_);
lean_ctor_set(v_reuseFailAlloc_379_, 6, v_mvars_280_);
lean_ctor_set(v_reuseFailAlloc_379_, 7, v___y_375_);
lean_ctor_set(v_reuseFailAlloc_379_, 8, v_emap_282_);
lean_ctor_set_uint8(v_reuseFailAlloc_379_, sizeof(void*)*9, v_abstractLevels_272_);
v___x_377_ = v_reuseFailAlloc_379_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
lean_object* v___x_378_; 
v___x_378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_378_, 0, v___x_370_);
lean_ctor_set(v___x_378_, 1, v___x_377_);
return v___x_378_;
}
}
v___jp_380_:
{
lean_object* v_size_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v_size_383_ = lean_ctor_get(v___y_381_, 0);
v___x_384_ = lean_nat_add(v_size_383_, v___x_371_);
lean_inc(v___x_370_);
v___x_385_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_381_, v___x_384_, v_i_382_, v_a_359_, v___x_370_);
lean_dec(v_i_382_);
v___y_375_ = v___x_385_;
goto v___jp_374_;
}
v___jp_386_:
{
lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_387_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__2___redArg(v_lmap_281_);
lean_dec_ref(v_lmap_281_);
v___x_388_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1___redArg(v___x_387_, v_a_359_);
switch(lean_obj_tag(v___x_388_))
{
case 0:
{
lean_object* v_index_389_; lean_object* v_size_390_; lean_object* v___x_391_; 
v_index_389_ = lean_ctor_get(v___x_388_, 0);
lean_inc(v_index_389_);
lean_dec_ref_known(v___x_388_, 3);
v_size_390_ = lean_ctor_get(v___x_387_, 0);
lean_inc(v_size_390_);
lean_inc(v___x_370_);
v___x_391_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_387_, v_size_390_, v_index_389_, v_a_359_, v___x_370_);
lean_dec(v_index_389_);
v___y_375_ = v___x_391_;
goto v___jp_374_;
}
case 1:
{
lean_object* v_index_392_; 
v_index_392_ = lean_ctor_get(v___x_388_, 0);
lean_inc(v_index_392_);
lean_dec_ref_known(v___x_388_, 1);
v___y_381_ = v___x_387_;
v_i_382_ = v_index_392_;
goto v___jp_380_;
}
default: 
{
lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_393_ = lean_unsigned_to_nat(0u);
v___x_394_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_387_, v___x_393_);
if (lean_obj_tag(v___x_394_) == 0)
{
lean_object* v_index_395_; 
v_index_395_ = lean_ctor_get(v___x_394_, 0);
lean_inc(v_index_395_);
lean_dec_ref_known(v___x_394_, 1);
v___y_381_ = v___x_387_;
v_i_382_ = v_index_395_;
goto v___jp_380_;
}
else
{
lean_dec(v_a_359_);
v___y_375_ = v___x_387_;
goto v___jp_374_;
}
}
}
}
v___jp_396_:
{
lean_object* v_size_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v_size_399_ = lean_ctor_get(v___y_397_, 0);
v___x_400_ = lean_nat_add(v_size_399_, v___x_371_);
lean_inc(v___x_370_);
v___x_401_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_397_, v___x_400_, v_i_398_, v_a_359_, v___x_370_);
lean_dec(v_i_398_);
v___y_375_ = v___x_401_;
goto v___jp_374_;
}
v___jp_402_:
{
lean_object* v___x_404_; 
v___x_404_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1___redArg(v___y_403_, v_a_359_);
switch(lean_obj_tag(v___x_404_))
{
case 0:
{
lean_object* v_index_405_; lean_object* v_size_406_; lean_object* v___x_407_; 
v_index_405_ = lean_ctor_get(v___x_404_, 0);
lean_inc(v_index_405_);
lean_dec_ref_known(v___x_404_, 3);
v_size_406_ = lean_ctor_get(v___y_403_, 0);
lean_inc(v_size_406_);
lean_inc(v___x_370_);
v___x_407_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_403_, v_size_406_, v_index_405_, v_a_359_, v___x_370_);
lean_dec(v_index_405_);
v___y_375_ = v___x_407_;
goto v___jp_374_;
}
case 1:
{
lean_object* v_index_408_; 
v_index_408_ = lean_ctor_get(v___x_404_, 0);
lean_inc(v_index_408_);
lean_dec_ref_known(v___x_404_, 1);
v___y_397_ = v___y_403_;
v_i_398_ = v_index_408_;
goto v___jp_396_;
}
default: 
{
lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_409_ = lean_unsigned_to_nat(0u);
v___x_410_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_403_, v___x_409_);
if (lean_obj_tag(v___x_410_) == 0)
{
lean_object* v_index_411_; 
v_index_411_ = lean_ctor_get(v___x_410_, 0);
lean_inc(v_index_411_);
lean_dec_ref_known(v___x_410_, 1);
v___y_397_ = v___y_403_;
v_i_398_ = v_index_411_;
goto v___jp_396_;
}
else
{
lean_dec(v_a_359_);
v___y_375_ = v___y_403_;
goto v___jp_374_;
}
}
}
}
}
}
else
{
lean_object* v_val_450_; lean_object* v___x_451_; 
lean_dec(v_a_359_);
v_val_450_ = lean_ctor_get(v___x_364_, 0);
lean_inc(v_val_450_);
lean_dec_ref_known(v___x_364_, 1);
v___x_451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_451_, 0, v_val_450_);
lean_ctor_set(v___x_451_, 1, v_a_271_);
return v___x_451_;
}
}
}
default: 
{
lean_object* v___x_452_; 
v___x_452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_452_, 0, v_u_270_);
lean_ctor_set(v___x_452_, 1, v_a_271_);
return v___x_452_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0(lean_object* v_00_u03b2_453_, lean_object* v_m_454_, lean_object* v_a_455_){
_start:
{
lean_object* v___x_456_; 
v___x_456_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___redArg(v_m_454_, v_a_455_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___boxed(lean_object* v_00_u03b2_457_, lean_object* v_m_458_, lean_object* v_a_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0(v_00_u03b2_457_, v_m_458_, v_a_459_);
lean_dec(v_a_459_);
lean_dec_ref(v_m_458_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1(lean_object* v_00_u03b2_461_, lean_object* v_m_462_, lean_object* v_query_463_){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1___redArg(v_m_462_, v_query_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1___boxed(lean_object* v_00_u03b2_465_, lean_object* v_m_466_, lean_object* v_query_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1(v_00_u03b2_465_, v_m_466_, v_query_467_);
lean_dec(v_query_467_);
lean_dec_ref(v_m_466_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__2(lean_object* v_00_u03b2_469_, lean_object* v_m_470_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__2___redArg(v_m_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__2___boxed(lean_object* v_00_u03b2_472_, lean_object* v_m_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__2(v_00_u03b2_472_, v_m_473_);
lean_dec_ref(v_m_473_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0(lean_object* v_00_u03b2_475_, lean_object* v_m_476_, lean_object* v_query_477_){
_start:
{
lean_object* v___x_478_; 
v___x_478_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0___redArg(v_m_476_, v_query_477_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0___boxed(lean_object* v_00_u03b2_479_, lean_object* v_m_480_, lean_object* v_query_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0(v_00_u03b2_479_, v_m_480_, v_query_481_);
lean_dec(v_query_481_);
lean_dec_ref(v_m_480_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2(lean_object* v_00_u03b2_483_, lean_object* v_m_484_, lean_object* v_query_485_, lean_object* v_x_486_, lean_object* v_x_487_, lean_object* v_x_488_, lean_object* v_x_489_){
_start:
{
lean_object* v___x_490_; 
v___x_490_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2___redArg(v_m_484_, v_query_485_, v_x_486_, v_x_487_, v_x_488_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2___boxed(lean_object* v_00_u03b2_491_, lean_object* v_m_492_, lean_object* v_query_493_, lean_object* v_x_494_, lean_object* v_x_495_, lean_object* v_x_496_, lean_object* v_x_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2(v_00_u03b2_491_, v_m_492_, v_query_493_, v_x_494_, v_x_495_, v_x_496_, v_x_497_);
lean_dec(v_query_493_);
lean_dec_ref(v_m_492_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__2_spec__4(lean_object* v_00_u03b2_499_, lean_object* v_init_500_, lean_object* v_b_501_){
_start:
{
lean_object* v___x_502_; 
v___x_502_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__2_spec__4___redArg(v_init_500_, v_b_501_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__2_spec__4___boxed(lean_object* v_00_u03b2_503_, lean_object* v_init_504_, lean_object* v_b_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__2_spec__4(v_00_u03b2_503_, v_init_504_, v_b_505_);
lean_dec_ref(v_b_505_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_507_, lean_object* v_b_508_, lean_object* v_acc_509_, lean_object* v_i_510_){
_start:
{
lean_object* v___x_511_; 
v___x_511_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__2_spec__4_spec__5___redArg(v_b_508_, v_acc_509_, v_i_510_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__2_spec__4_spec__5___boxed(lean_object* v_00_u03b2_512_, lean_object* v_b_513_, lean_object* v_acc_514_, lean_object* v_i_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__2_spec__4_spec__5(v_00_u03b2_512_, v_b_513_, v_acc_514_, v_i_515_);
lean_dec_ref(v_b_513_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__1(lean_object* v_e_517_, lean_object* v___y_518_){
_start:
{
uint8_t v___x_519_; 
v___x_519_ = l_Lean_Expr_hasMVar(v_e_517_);
if (v___x_519_ == 0)
{
lean_object* v___x_520_; 
v___x_520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_520_, 0, v_e_517_);
lean_ctor_set(v___x_520_, 1, v___y_518_);
return v___x_520_;
}
else
{
lean_object* v_ngen_521_; lean_object* v_lctx_522_; lean_object* v_mctx_523_; lean_object* v_nextParamIdx_524_; lean_object* v_paramNames_525_; lean_object* v_fvars_526_; lean_object* v_mvars_527_; lean_object* v_lmap_528_; lean_object* v_emap_529_; uint8_t v_abstractLevels_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_547_; 
v_ngen_521_ = lean_ctor_get(v___y_518_, 0);
v_lctx_522_ = lean_ctor_get(v___y_518_, 1);
v_mctx_523_ = lean_ctor_get(v___y_518_, 2);
v_nextParamIdx_524_ = lean_ctor_get(v___y_518_, 3);
v_paramNames_525_ = lean_ctor_get(v___y_518_, 4);
v_fvars_526_ = lean_ctor_get(v___y_518_, 5);
v_mvars_527_ = lean_ctor_get(v___y_518_, 6);
v_lmap_528_ = lean_ctor_get(v___y_518_, 7);
v_emap_529_ = lean_ctor_get(v___y_518_, 8);
v_abstractLevels_530_ = lean_ctor_get_uint8(v___y_518_, sizeof(void*)*9);
v_isSharedCheck_547_ = !lean_is_exclusive(v___y_518_);
if (v_isSharedCheck_547_ == 0)
{
v___x_532_ = v___y_518_;
v_isShared_533_ = v_isSharedCheck_547_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_emap_529_);
lean_inc(v_lmap_528_);
lean_inc(v_mvars_527_);
lean_inc(v_fvars_526_);
lean_inc(v_paramNames_525_);
lean_inc(v_nextParamIdx_524_);
lean_inc(v_mctx_523_);
lean_inc(v_lctx_522_);
lean_inc(v_ngen_521_);
lean_dec(v___y_518_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_547_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_534_; lean_object* v_fst_535_; lean_object* v_snd_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_546_; 
v___x_534_ = l_Lean_instantiateMVarsCore(v_mctx_523_, v_e_517_);
v_fst_535_ = lean_ctor_get(v___x_534_, 0);
v_snd_536_ = lean_ctor_get(v___x_534_, 1);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_534_);
if (v_isSharedCheck_546_ == 0)
{
v___x_538_ = v___x_534_;
v_isShared_539_ = v_isSharedCheck_546_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_snd_536_);
lean_inc(v_fst_535_);
lean_dec(v___x_534_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_546_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_541_; 
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 2, v_snd_536_);
v___x_541_ = v___x_532_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_ngen_521_);
lean_ctor_set(v_reuseFailAlloc_545_, 1, v_lctx_522_);
lean_ctor_set(v_reuseFailAlloc_545_, 2, v_snd_536_);
lean_ctor_set(v_reuseFailAlloc_545_, 3, v_nextParamIdx_524_);
lean_ctor_set(v_reuseFailAlloc_545_, 4, v_paramNames_525_);
lean_ctor_set(v_reuseFailAlloc_545_, 5, v_fvars_526_);
lean_ctor_set(v_reuseFailAlloc_545_, 6, v_mvars_527_);
lean_ctor_set(v_reuseFailAlloc_545_, 7, v_lmap_528_);
lean_ctor_set(v_reuseFailAlloc_545_, 8, v_emap_529_);
lean_ctor_set_uint8(v_reuseFailAlloc_545_, sizeof(void*)*9, v_abstractLevels_530_);
v___x_541_ = v_reuseFailAlloc_545_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
lean_object* v___x_543_; 
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 1, v___x_541_);
v___x_543_ = v___x_538_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_fst_535_);
lean_ctor_set(v_reuseFailAlloc_544_, 1, v___x_541_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3___redArg(lean_object* v_m_548_, lean_object* v_query_549_, lean_object* v_x_550_, lean_object* v_x_551_, lean_object* v_x_552_){
_start:
{
lean_object* v_zero_553_; uint8_t v_isZero_554_; 
v_zero_553_ = lean_unsigned_to_nat(0u);
v_isZero_554_ = lean_nat_dec_eq(v_x_551_, v_zero_553_);
if (v_isZero_554_ == 1)
{
lean_dec(v_x_552_);
lean_dec(v_x_551_);
if (lean_obj_tag(v_x_550_) == 0)
{
lean_object* v___x_555_; 
v___x_555_ = lean_box(2);
return v___x_555_;
}
else
{
lean_object* v_val_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_563_; 
v_val_556_ = lean_ctor_get(v_x_550_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v_x_550_);
if (v_isSharedCheck_563_ == 0)
{
v___x_558_ = v_x_550_;
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_val_556_);
lean_dec(v_x_550_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_561_; 
if (v_isShared_559_ == 0)
{
v___x_561_ = v___x_558_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_val_556_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
}
else
{
lean_object* v_keyArray_564_; lean_object* v_valueArray_565_; lean_object* v___x_566_; uint8_t v_isSome_567_; 
v_keyArray_564_ = lean_ctor_get(v_m_548_, 1);
v_valueArray_565_ = lean_ctor_get(v_m_548_, 2);
v___x_566_ = lean_array_fget_borrowed(v_keyArray_564_, v_x_552_);
v_isSome_567_ = lean_noption_is_some(v___x_566_);
if (v_isSome_567_ == 0)
{
lean_dec(v_x_551_);
if (lean_obj_tag(v_x_550_) == 0)
{
lean_object* v___x_568_; 
v___x_568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_568_, 0, v_x_552_);
return v___x_568_;
}
else
{
lean_object* v_val_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_576_; 
lean_dec(v_x_552_);
v_val_569_ = lean_ctor_get(v_x_550_, 0);
v_isSharedCheck_576_ = !lean_is_exclusive(v_x_550_);
if (v_isSharedCheck_576_ == 0)
{
v___x_571_ = v_x_550_;
v_isShared_572_ = v_isSharedCheck_576_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_val_569_);
lean_dec(v_x_550_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_576_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___x_574_; 
if (v_isShared_572_ == 0)
{
v___x_574_ = v___x_571_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v_val_569_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
}
}
else
{
lean_object* v_one_577_; lean_object* v_n_578_; lean_object* v___y_580_; 
v_one_577_ = lean_unsigned_to_nat(1u);
v_n_578_ = lean_nat_sub(v_x_551_, v_one_577_);
lean_dec(v_x_551_);
if (v_isSome_567_ == 0)
{
goto v___jp_586_;
}
else
{
lean_object* v___x_588_; uint8_t v_isSome_589_; 
v___x_588_ = lean_array_fget_borrowed(v_valueArray_565_, v_x_552_);
v_isSome_589_ = lean_noption_is_some(v___x_588_);
if (v_isSome_589_ == 0)
{
goto v___jp_586_;
}
else
{
lean_object* v_val_590_; uint8_t v___x_591_; 
lean_inc(v___x_566_);
v_val_590_ = lean_noption_get(v___x_566_);
v___x_591_ = l_Lean_instBEqMVarId_beq(v_val_590_, v_query_549_);
if (v___x_591_ == 0)
{
lean_object* v___x_592_; lean_object* v___x_593_; uint8_t v___x_594_; 
lean_dec(v_val_590_);
v___x_592_ = lean_array_get_size(v_keyArray_564_);
v___x_593_ = lean_nat_add(v_x_552_, v_one_577_);
lean_dec(v_x_552_);
v___x_594_ = lean_nat_dec_lt(v___x_593_, v___x_592_);
if (v___x_594_ == 0)
{
lean_dec(v___x_593_);
v_x_551_ = v_n_578_;
v_x_552_ = v_zero_553_;
goto _start;
}
else
{
v_x_551_ = v_n_578_;
v_x_552_ = v___x_593_;
goto _start;
}
}
else
{
lean_object* v_val_597_; lean_object* v___x_598_; 
lean_dec(v_n_578_);
lean_dec(v_x_550_);
lean_inc(v___x_588_);
v_val_597_ = lean_noption_get(v___x_588_);
v___x_598_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_598_, 0, v_x_552_);
lean_ctor_set(v___x_598_, 1, v_val_590_);
lean_ctor_set(v___x_598_, 2, v_val_597_);
return v___x_598_;
}
}
}
v___jp_579_:
{
lean_object* v___x_581_; lean_object* v___x_582_; uint8_t v___x_583_; 
v___x_581_ = lean_array_get_size(v_keyArray_564_);
v___x_582_ = lean_nat_add(v_x_552_, v_one_577_);
lean_dec(v_x_552_);
v___x_583_ = lean_nat_dec_lt(v___x_582_, v___x_581_);
if (v___x_583_ == 0)
{
lean_dec(v___x_582_);
v_x_550_ = v___y_580_;
v_x_551_ = v_n_578_;
v_x_552_ = v_zero_553_;
goto _start;
}
else
{
v_x_550_ = v___y_580_;
v_x_551_ = v_n_578_;
v_x_552_ = v___x_582_;
goto _start;
}
}
v___jp_586_:
{
if (lean_obj_tag(v_x_550_) == 0)
{
lean_object* v___x_587_; 
lean_inc(v_x_552_);
v___x_587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_587_, 0, v_x_552_);
v___y_580_ = v___x_587_;
goto v___jp_579_;
}
else
{
v___y_580_ = v_x_550_;
goto v___jp_579_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3___redArg___boxed(lean_object* v_m_599_, lean_object* v_query_600_, lean_object* v_x_601_, lean_object* v_x_602_, lean_object* v_x_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3___redArg(v_m_599_, v_query_600_, v_x_601_, v_x_602_, v_x_603_);
lean_dec(v_query_600_);
lean_dec_ref(v_m_599_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2___redArg(lean_object* v_m_605_, lean_object* v_query_606_){
_start:
{
lean_object* v_keyArray_607_; lean_object* v___x_608_; uint64_t v___x_609_; uint64_t v___x_610_; uint64_t v___x_611_; uint64_t v_fold_612_; uint64_t v___x_613_; uint64_t v___x_614_; uint64_t v___x_615_; size_t v___x_616_; size_t v___x_617_; size_t v___x_618_; size_t v___x_619_; size_t v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v_keyArray_607_ = lean_ctor_get(v_m_605_, 1);
v___x_608_ = lean_array_get_size(v_keyArray_607_);
v___x_609_ = l_Lean_instHashableMVarId_hash(v_query_606_);
v___x_610_ = 32ULL;
v___x_611_ = lean_uint64_shift_right(v___x_609_, v___x_610_);
v_fold_612_ = lean_uint64_xor(v___x_609_, v___x_611_);
v___x_613_ = 16ULL;
v___x_614_ = lean_uint64_shift_right(v_fold_612_, v___x_613_);
v___x_615_ = lean_uint64_xor(v_fold_612_, v___x_614_);
v___x_616_ = lean_uint64_to_usize(v___x_615_);
v___x_617_ = lean_usize_of_nat(v___x_608_);
v___x_618_ = ((size_t)1ULL);
v___x_619_ = lean_usize_sub(v___x_617_, v___x_618_);
v___x_620_ = lean_usize_land(v___x_616_, v___x_619_);
v___x_621_ = lean_usize_to_nat(v___x_620_);
v___x_622_ = lean_box(0);
v___x_623_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3___redArg(v_m_605_, v_query_606_, v___x_622_, v___x_608_, v___x_621_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2___redArg___boxed(lean_object* v_m_624_, lean_object* v_query_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2___redArg(v_m_624_, v_query_625_);
lean_dec(v_query_625_);
lean_dec_ref(v_m_624_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0___redArg(lean_object* v_m_627_, lean_object* v_query_628_){
_start:
{
lean_object* v___x_629_; 
v___x_629_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2___redArg(v_m_627_, v_query_628_);
if (lean_obj_tag(v___x_629_) == 0)
{
lean_object* v_index_630_; lean_object* v_key_631_; lean_object* v_value_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_639_; 
v_index_630_ = lean_ctor_get(v___x_629_, 0);
v_key_631_ = lean_ctor_get(v___x_629_, 1);
v_value_632_ = lean_ctor_get(v___x_629_, 2);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_639_ == 0)
{
v___x_634_ = v___x_629_;
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_value_632_);
lean_inc(v_key_631_);
lean_inc(v_index_630_);
lean_dec(v___x_629_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_637_; 
if (v_isShared_635_ == 0)
{
v___x_637_ = v___x_634_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_index_630_);
lean_ctor_set(v_reuseFailAlloc_638_, 1, v_key_631_);
lean_ctor_set(v_reuseFailAlloc_638_, 2, v_value_632_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
else
{
lean_object* v___x_640_; 
lean_dec(v___x_629_);
v___x_640_ = lean_box(1);
return v___x_640_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0___redArg___boxed(lean_object* v_m_641_, lean_object* v_query_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0___redArg(v_m_641_, v_query_642_);
lean_dec(v_query_642_);
lean_dec_ref(v_m_641_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0___redArg(lean_object* v_m_644_, lean_object* v_a_645_){
_start:
{
lean_object* v___x_646_; 
v___x_646_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0___redArg(v_m_644_, v_a_645_);
if (lean_obj_tag(v___x_646_) == 0)
{
lean_object* v_value_647_; lean_object* v___x_648_; 
v_value_647_ = lean_ctor_get(v___x_646_, 2);
lean_inc(v_value_647_);
lean_dec_ref_known(v___x_646_, 3);
v___x_648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_648_, 0, v_value_647_);
return v___x_648_;
}
else
{
lean_object* v___x_649_; 
v___x_649_ = lean_box(0);
return v___x_649_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0___redArg___boxed(lean_object* v_m_650_, lean_object* v_a_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0___redArg(v_m_650_, v_a_651_);
lean_dec(v_a_651_);
lean_dec_ref(v_m_650_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__4(lean_object* v_x_653_, lean_object* v_x_654_, lean_object* v___y_655_){
_start:
{
if (lean_obj_tag(v_x_653_) == 0)
{
lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_656_ = l_List_reverse___redArg(v_x_654_);
v___x_657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_657_, 0, v___x_656_);
lean_ctor_set(v___x_657_, 1, v___y_655_);
return v___x_657_;
}
else
{
lean_object* v_head_658_; lean_object* v_tail_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_670_; 
v_head_658_ = lean_ctor_get(v_x_653_, 0);
v_tail_659_ = lean_ctor_get(v_x_653_, 1);
v_isSharedCheck_670_ = !lean_is_exclusive(v_x_653_);
if (v_isSharedCheck_670_ == 0)
{
v___x_661_ = v_x_653_;
v_isShared_662_ = v_isSharedCheck_670_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_tail_659_);
lean_inc(v_head_658_);
lean_dec(v_x_653_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_670_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_663_; lean_object* v_fst_664_; lean_object* v_snd_665_; lean_object* v___x_667_; 
v___x_663_ = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(v_head_658_, v___y_655_);
v_fst_664_ = lean_ctor_get(v___x_663_, 0);
lean_inc(v_fst_664_);
v_snd_665_ = lean_ctor_get(v___x_663_, 1);
lean_inc(v_snd_665_);
lean_dec_ref(v___x_663_);
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 1, v_x_654_);
lean_ctor_set(v___x_661_, 0, v_fst_664_);
v___x_667_ = v___x_661_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_fst_664_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v_x_654_);
v___x_667_ = v_reuseFailAlloc_669_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
v_x_653_ = v_tail_659_;
v_x_654_ = v___x_667_;
v___y_655_ = v_snd_665_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__3_spec__5_spec__6___redArg(lean_object* v_b_671_, lean_object* v_acc_672_, lean_object* v_i_673_){
_start:
{
lean_object* v___y_675_; lean_object* v_keyArray_683_; lean_object* v_valueArray_684_; lean_object* v___x_685_; uint8_t v___x_686_; 
v_keyArray_683_ = lean_ctor_get(v_b_671_, 1);
v_valueArray_684_ = lean_ctor_get(v_b_671_, 2);
v___x_685_ = lean_array_get_size(v_keyArray_683_);
v___x_686_ = lean_nat_dec_lt(v_i_673_, v___x_685_);
if (v___x_686_ == 0)
{
lean_dec(v_i_673_);
return v_acc_672_;
}
else
{
lean_object* v___x_687_; uint8_t v_isSome_688_; 
v___x_687_ = lean_array_fget_borrowed(v_keyArray_683_, v_i_673_);
v_isSome_688_ = lean_noption_is_some(v___x_687_);
if (v_isSome_688_ == 0)
{
goto v___jp_679_;
}
else
{
lean_object* v___x_689_; uint8_t v_isSome_690_; 
v___x_689_ = lean_array_fget_borrowed(v_valueArray_684_, v_i_673_);
v_isSome_690_ = lean_noption_is_some(v___x_689_);
if (v_isSome_690_ == 0)
{
goto v___jp_679_;
}
else
{
lean_object* v_val_691_; lean_object* v_val_692_; lean_object* v_i_694_; lean_object* v___x_699_; 
lean_inc(v___x_687_);
v_val_691_ = lean_noption_get(v___x_687_);
lean_inc(v___x_689_);
v_val_692_ = lean_noption_get(v___x_689_);
v___x_699_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2___redArg(v_acc_672_, v_val_691_);
switch(lean_obj_tag(v___x_699_))
{
case 0:
{
lean_object* v_index_700_; lean_object* v_size_701_; lean_object* v___x_702_; 
v_index_700_ = lean_ctor_get(v___x_699_, 0);
lean_inc(v_index_700_);
lean_dec_ref_known(v___x_699_, 3);
v_size_701_ = lean_ctor_get(v_acc_672_, 0);
lean_inc(v_size_701_);
v___x_702_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_672_, v_size_701_, v_index_700_, v_val_691_, v_val_692_);
lean_dec(v_index_700_);
v___y_675_ = v___x_702_;
goto v___jp_674_;
}
case 1:
{
lean_object* v_index_703_; 
v_index_703_ = lean_ctor_get(v___x_699_, 0);
lean_inc(v_index_703_);
lean_dec_ref_known(v___x_699_, 1);
v_i_694_ = v_index_703_;
goto v___jp_693_;
}
default: 
{
lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_704_ = lean_unsigned_to_nat(0u);
v___x_705_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_672_, v___x_704_);
if (lean_obj_tag(v___x_705_) == 0)
{
lean_object* v_index_706_; 
v_index_706_ = lean_ctor_get(v___x_705_, 0);
lean_inc(v_index_706_);
lean_dec_ref_known(v___x_705_, 1);
v_i_694_ = v_index_706_;
goto v___jp_693_;
}
else
{
lean_dec(v_val_692_);
lean_dec(v_val_691_);
v___y_675_ = v_acc_672_;
goto v___jp_674_;
}
}
}
v___jp_693_:
{
lean_object* v_size_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v_size_695_ = lean_ctor_get(v_acc_672_, 0);
v___x_696_ = lean_unsigned_to_nat(1u);
v___x_697_ = lean_nat_add(v_size_695_, v___x_696_);
v___x_698_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_672_, v___x_697_, v_i_694_, v_val_691_, v_val_692_);
lean_dec(v_i_694_);
v___y_675_ = v___x_698_;
goto v___jp_674_;
}
}
}
}
v___jp_674_:
{
lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_676_ = lean_unsigned_to_nat(1u);
v___x_677_ = lean_nat_add(v_i_673_, v___x_676_);
lean_dec(v_i_673_);
v_acc_672_ = v___y_675_;
v_i_673_ = v___x_677_;
goto _start;
}
v___jp_679_:
{
lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_680_ = lean_unsigned_to_nat(1u);
v___x_681_ = lean_nat_add(v_i_673_, v___x_680_);
lean_dec(v_i_673_);
v_i_673_ = v___x_681_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__3_spec__5_spec__6___redArg___boxed(lean_object* v_b_707_, lean_object* v_acc_708_, lean_object* v_i_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__3_spec__5_spec__6___redArg(v_b_707_, v_acc_708_, v_i_709_);
lean_dec_ref(v_b_707_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__3_spec__5___redArg(lean_object* v_init_711_, lean_object* v_b_712_){
_start:
{
lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_713_ = lean_unsigned_to_nat(0u);
v___x_714_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__3_spec__5_spec__6___redArg(v_b_712_, v_init_711_, v___x_713_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__3_spec__5___redArg___boxed(lean_object* v_init_715_, lean_object* v_b_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__3_spec__5___redArg(v_init_715_, v_b_716_);
lean_dec_ref(v_b_716_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__3___redArg(lean_object* v_m_718_){
_start:
{
lean_object* v_keyArray_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v_cellCount_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v_target_726_; lean_object* v___x_727_; 
v_keyArray_719_ = lean_ctor_get(v_m_718_, 1);
v___x_720_ = lean_array_get_size(v_keyArray_719_);
v___x_721_ = lean_unsigned_to_nat(2u);
v_cellCount_722_ = lean_nat_mul(v___x_720_, v___x_721_);
v___x_723_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_722_);
v___x_724_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_722_);
v___x_725_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_722_);
v_target_726_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_726_, 0, v___x_723_);
lean_ctor_set(v_target_726_, 1, v___x_724_);
lean_ctor_set(v_target_726_, 2, v___x_725_);
v___x_727_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__3_spec__5___redArg(v_target_726_, v_m_718_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__3___redArg___boxed(lean_object* v_m_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__3___redArg(v_m_728_);
lean_dec_ref(v_m_728_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_abstractExprMVars(lean_object* v_e_733_, lean_object* v_a_734_){
_start:
{
uint8_t v___x_735_; 
v___x_735_ = l_Lean_Expr_hasMVar(v_e_733_);
if (v___x_735_ == 0)
{
lean_object* v___x_736_; 
v___x_736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_736_, 0, v_e_733_);
lean_ctor_set(v___x_736_, 1, v_a_734_);
return v___x_736_;
}
else
{
switch(lean_obj_tag(v_e_733_))
{
case 2:
{
lean_object* v_mvarId_737_; lean_object* v_mctx_738_; lean_object* v_emap_739_; lean_object* v___x_740_; lean_object* v_userName_741_; lean_object* v_type_742_; lean_object* v_depth_743_; lean_object* v_depth_744_; uint8_t v___x_745_; 
v_mvarId_737_ = lean_ctor_get(v_e_733_, 0);
v_mctx_738_ = lean_ctor_get(v_a_734_, 2);
v_emap_739_ = lean_ctor_get(v_a_734_, 8);
lean_inc(v_mvarId_737_);
v___x_740_ = l_Lean_MetavarContext_getDecl(v_mctx_738_, v_mvarId_737_);
v_userName_741_ = lean_ctor_get(v___x_740_, 0);
lean_inc(v_userName_741_);
v_type_742_ = lean_ctor_get(v___x_740_, 2);
lean_inc_ref(v_type_742_);
v_depth_743_ = lean_ctor_get(v___x_740_, 3);
lean_inc(v_depth_743_);
lean_dec_ref(v___x_740_);
v_depth_744_ = lean_ctor_get(v_mctx_738_, 0);
v___x_745_ = lean_nat_dec_eq(v_depth_743_, v_depth_744_);
lean_dec(v_depth_743_);
if (v___x_745_ == 0)
{
lean_object* v___x_746_; 
lean_dec_ref(v_type_742_);
lean_dec(v_userName_741_);
v___x_746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_746_, 0, v_e_733_);
lean_ctor_set(v___x_746_, 1, v_a_734_);
return v___x_746_;
}
else
{
lean_object* v___x_747_; 
lean_inc(v_mvarId_737_);
v___x_747_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0___redArg(v_emap_739_, v_mvarId_737_);
if (lean_obj_tag(v___x_747_) == 0)
{
lean_object* v___x_748_; lean_object* v_fst_749_; lean_object* v_snd_750_; lean_object* v___x_751_; lean_object* v_fst_752_; lean_object* v_snd_753_; lean_object* v___x_754_; lean_object* v_fst_755_; lean_object* v_snd_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_899_; 
v___x_748_ = l_Lean_instantiateMVars___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__1(v_type_742_, v_a_734_);
v_fst_749_ = lean_ctor_get(v___x_748_, 0);
lean_inc(v_fst_749_);
v_snd_750_ = lean_ctor_get(v___x_748_, 1);
lean_inc(v_snd_750_);
lean_dec_ref(v___x_748_);
v___x_751_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_fst_749_, v_snd_750_);
v_fst_752_ = lean_ctor_get(v___x_751_, 0);
lean_inc(v_fst_752_);
v_snd_753_ = lean_ctor_get(v___x_751_, 1);
lean_inc(v_snd_753_);
lean_dec_ref(v___x_751_);
v___x_754_ = l_Lean_Meta_AbstractMVars_mkFreshFVarId(v_snd_753_);
v_fst_755_ = lean_ctor_get(v___x_754_, 0);
v_snd_756_ = lean_ctor_get(v___x_754_, 1);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_754_);
if (v_isSharedCheck_899_ == 0)
{
v___x_758_ = v___x_754_;
v_isShared_759_ = v_isSharedCheck_899_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_snd_756_);
lean_inc(v_fst_755_);
lean_dec(v___x_754_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_899_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_760_; uint8_t v___y_762_; lean_object* v___y_763_; lean_object* v___y_764_; lean_object* v___y_765_; lean_object* v___y_766_; lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v___y_769_; lean_object* v___y_770_; lean_object* v___y_771_; lean_object* v___y_777_; lean_object* v___y_778_; lean_object* v___y_779_; lean_object* v___y_780_; lean_object* v___y_781_; lean_object* v___y_782_; lean_object* v___y_783_; lean_object* v___y_784_; lean_object* v___y_785_; uint8_t v___y_786_; lean_object* v_i_787_; uint8_t v___y_793_; lean_object* v___y_794_; lean_object* v___y_795_; lean_object* v___y_796_; lean_object* v___y_797_; lean_object* v___y_798_; lean_object* v___y_799_; lean_object* v___y_800_; lean_object* v___y_801_; lean_object* v___y_802_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v___y_819_; lean_object* v___y_820_; uint8_t v___y_821_; lean_object* v_i_822_; uint8_t v___y_828_; lean_object* v___y_829_; lean_object* v___y_830_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___y_833_; lean_object* v___y_834_; lean_object* v___y_835_; lean_object* v___y_836_; lean_object* v___y_837_; lean_object* v_userName_848_; uint8_t v___x_894_; 
lean_inc(v_fst_755_);
v___x_760_ = l_Lean_mkFVar(v_fst_755_);
v___x_894_ = l_Lean_Name_isAnonymous(v_userName_741_);
if (v___x_894_ == 0)
{
v_userName_848_ = v_userName_741_;
goto v___jp_847_;
}
else
{
lean_object* v_fvars_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
lean_dec(v_userName_741_);
v_fvars_895_ = lean_ctor_get(v_snd_756_, 5);
v___x_896_ = ((lean_object*)(l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__1));
v___x_897_ = lean_array_get_size(v_fvars_895_);
v___x_898_ = lean_name_append_index_after(v___x_896_, v___x_897_);
v_userName_848_ = v___x_898_;
goto v___jp_847_;
}
v___jp_761_:
{
lean_object* v___x_772_; lean_object* v___x_774_; 
v___x_772_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v___x_772_, 0, v___y_770_);
lean_ctor_set(v___x_772_, 1, v___y_765_);
lean_ctor_set(v___x_772_, 2, v___y_767_);
lean_ctor_set(v___x_772_, 3, v___y_766_);
lean_ctor_set(v___x_772_, 4, v___y_763_);
lean_ctor_set(v___x_772_, 5, v___y_764_);
lean_ctor_set(v___x_772_, 6, v___y_768_);
lean_ctor_set(v___x_772_, 7, v___y_769_);
lean_ctor_set(v___x_772_, 8, v___y_771_);
lean_ctor_set_uint8(v___x_772_, sizeof(void*)*9, v___y_762_);
if (v_isShared_759_ == 0)
{
lean_ctor_set(v___x_758_, 1, v___x_772_);
lean_ctor_set(v___x_758_, 0, v___x_760_);
v___x_774_ = v___x_758_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v___x_760_);
lean_ctor_set(v_reuseFailAlloc_775_, 1, v___x_772_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
return v___x_774_;
}
}
v___jp_776_:
{
lean_object* v_size_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
v_size_788_ = lean_ctor_get(v___y_781_, 0);
v___x_789_ = lean_unsigned_to_nat(1u);
v___x_790_ = lean_nat_add(v_size_788_, v___x_789_);
lean_inc_ref(v___x_760_);
v___x_791_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_781_, v___x_790_, v_i_787_, v_mvarId_737_, v___x_760_);
lean_dec(v_i_787_);
v___y_762_ = v___y_786_;
v___y_763_ = v___y_778_;
v___y_764_ = v___y_779_;
v___y_765_ = v___y_780_;
v___y_766_ = v___y_782_;
v___y_767_ = v___y_783_;
v___y_768_ = v___y_784_;
v___y_769_ = v___y_785_;
v___y_770_ = v___y_777_;
v___y_771_ = v___x_791_;
goto v___jp_761_;
}
v___jp_792_:
{
lean_object* v___x_803_; 
v___x_803_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2___redArg(v___y_802_, v_mvarId_737_);
switch(lean_obj_tag(v___x_803_))
{
case 0:
{
lean_object* v_index_804_; lean_object* v_size_805_; lean_object* v___x_806_; 
v_index_804_ = lean_ctor_get(v___x_803_, 0);
lean_inc(v_index_804_);
lean_dec_ref_known(v___x_803_, 3);
v_size_805_ = lean_ctor_get(v___y_802_, 0);
lean_inc(v_size_805_);
lean_inc_ref(v___x_760_);
v___x_806_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_802_, v_size_805_, v_index_804_, v_mvarId_737_, v___x_760_);
lean_dec(v_index_804_);
v___y_762_ = v___y_793_;
v___y_763_ = v___y_794_;
v___y_764_ = v___y_795_;
v___y_765_ = v___y_796_;
v___y_766_ = v___y_797_;
v___y_767_ = v___y_798_;
v___y_768_ = v___y_799_;
v___y_769_ = v___y_800_;
v___y_770_ = v___y_801_;
v___y_771_ = v___x_806_;
goto v___jp_761_;
}
case 1:
{
lean_object* v_index_807_; 
v_index_807_ = lean_ctor_get(v___x_803_, 0);
lean_inc(v_index_807_);
lean_dec_ref_known(v___x_803_, 1);
v___y_777_ = v___y_801_;
v___y_778_ = v___y_794_;
v___y_779_ = v___y_795_;
v___y_780_ = v___y_796_;
v___y_781_ = v___y_802_;
v___y_782_ = v___y_797_;
v___y_783_ = v___y_798_;
v___y_784_ = v___y_799_;
v___y_785_ = v___y_800_;
v___y_786_ = v___y_793_;
v_i_787_ = v_index_807_;
goto v___jp_776_;
}
default: 
{
lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_808_ = lean_unsigned_to_nat(0u);
v___x_809_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_802_, v___x_808_);
if (lean_obj_tag(v___x_809_) == 0)
{
lean_object* v_index_810_; 
v_index_810_ = lean_ctor_get(v___x_809_, 0);
lean_inc(v_index_810_);
lean_dec_ref_known(v___x_809_, 1);
v___y_777_ = v___y_801_;
v___y_778_ = v___y_794_;
v___y_779_ = v___y_795_;
v___y_780_ = v___y_796_;
v___y_781_ = v___y_802_;
v___y_782_ = v___y_797_;
v___y_783_ = v___y_798_;
v___y_784_ = v___y_799_;
v___y_785_ = v___y_800_;
v___y_786_ = v___y_793_;
v_i_787_ = v_index_810_;
goto v___jp_776_;
}
else
{
lean_dec(v_mvarId_737_);
v___y_762_ = v___y_793_;
v___y_763_ = v___y_794_;
v___y_764_ = v___y_795_;
v___y_765_ = v___y_796_;
v___y_766_ = v___y_797_;
v___y_767_ = v___y_798_;
v___y_768_ = v___y_799_;
v___y_769_ = v___y_800_;
v___y_770_ = v___y_801_;
v___y_771_ = v___y_802_;
goto v___jp_761_;
}
}
}
}
v___jp_811_:
{
lean_object* v_size_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
v_size_823_ = lean_ctor_get(v___y_814_, 0);
v___x_824_ = lean_unsigned_to_nat(1u);
v___x_825_ = lean_nat_add(v_size_823_, v___x_824_);
lean_inc_ref(v___x_760_);
v___x_826_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_814_, v___x_825_, v_i_822_, v_mvarId_737_, v___x_760_);
lean_dec(v_i_822_);
v___y_762_ = v___y_821_;
v___y_763_ = v___y_813_;
v___y_764_ = v___y_815_;
v___y_765_ = v___y_816_;
v___y_766_ = v___y_817_;
v___y_767_ = v___y_818_;
v___y_768_ = v___y_819_;
v___y_769_ = v___y_820_;
v___y_770_ = v___y_812_;
v___y_771_ = v___x_826_;
goto v___jp_761_;
}
v___jp_827_:
{
lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_838_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__3___redArg(v___y_834_);
lean_dec_ref(v___y_834_);
v___x_839_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2___redArg(v___x_838_, v_mvarId_737_);
switch(lean_obj_tag(v___x_839_))
{
case 0:
{
lean_object* v_index_840_; lean_object* v_size_841_; lean_object* v___x_842_; 
v_index_840_ = lean_ctor_get(v___x_839_, 0);
lean_inc(v_index_840_);
lean_dec_ref_known(v___x_839_, 3);
v_size_841_ = lean_ctor_get(v___x_838_, 0);
lean_inc(v_size_841_);
lean_inc_ref(v___x_760_);
v___x_842_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_838_, v_size_841_, v_index_840_, v_mvarId_737_, v___x_760_);
lean_dec(v_index_840_);
v___y_762_ = v___y_828_;
v___y_763_ = v___y_829_;
v___y_764_ = v___y_830_;
v___y_765_ = v___y_831_;
v___y_766_ = v___y_832_;
v___y_767_ = v___y_833_;
v___y_768_ = v___y_835_;
v___y_769_ = v___y_836_;
v___y_770_ = v___y_837_;
v___y_771_ = v___x_842_;
goto v___jp_761_;
}
case 1:
{
lean_object* v_index_843_; 
v_index_843_ = lean_ctor_get(v___x_839_, 0);
lean_inc(v_index_843_);
lean_dec_ref_known(v___x_839_, 1);
v___y_812_ = v___y_837_;
v___y_813_ = v___y_829_;
v___y_814_ = v___x_838_;
v___y_815_ = v___y_830_;
v___y_816_ = v___y_831_;
v___y_817_ = v___y_832_;
v___y_818_ = v___y_833_;
v___y_819_ = v___y_835_;
v___y_820_ = v___y_836_;
v___y_821_ = v___y_828_;
v_i_822_ = v_index_843_;
goto v___jp_811_;
}
default: 
{
lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_844_ = lean_unsigned_to_nat(0u);
v___x_845_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_838_, v___x_844_);
if (lean_obj_tag(v___x_845_) == 0)
{
lean_object* v_index_846_; 
v_index_846_ = lean_ctor_get(v___x_845_, 0);
lean_inc(v_index_846_);
lean_dec_ref_known(v___x_845_, 1);
v___y_812_ = v___y_837_;
v___y_813_ = v___y_829_;
v___y_814_ = v___x_838_;
v___y_815_ = v___y_830_;
v___y_816_ = v___y_831_;
v___y_817_ = v___y_832_;
v___y_818_ = v___y_833_;
v___y_819_ = v___y_835_;
v___y_820_ = v___y_836_;
v___y_821_ = v___y_828_;
v_i_822_ = v_index_846_;
goto v___jp_811_;
}
else
{
lean_dec(v_mvarId_737_);
v___y_762_ = v___y_828_;
v___y_763_ = v___y_829_;
v___y_764_ = v___y_830_;
v___y_765_ = v___y_831_;
v___y_766_ = v___y_832_;
v___y_767_ = v___y_833_;
v___y_768_ = v___y_835_;
v___y_769_ = v___y_836_;
v___y_770_ = v___y_837_;
v___y_771_ = v___x_838_;
goto v___jp_761_;
}
}
}
}
v___jp_847_:
{
lean_object* v_ngen_849_; lean_object* v_lctx_850_; lean_object* v_mctx_851_; lean_object* v_nextParamIdx_852_; lean_object* v_paramNames_853_; lean_object* v_fvars_854_; lean_object* v_mvars_855_; lean_object* v_lmap_856_; lean_object* v_emap_857_; uint8_t v_abstractLevels_858_; uint8_t v___x_859_; uint8_t v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v_ngen_849_ = lean_ctor_get(v_snd_756_, 0);
lean_inc_ref(v_ngen_849_);
v_lctx_850_ = lean_ctor_get(v_snd_756_, 1);
lean_inc_ref(v_lctx_850_);
v_mctx_851_ = lean_ctor_get(v_snd_756_, 2);
lean_inc_ref(v_mctx_851_);
v_nextParamIdx_852_ = lean_ctor_get(v_snd_756_, 3);
lean_inc(v_nextParamIdx_852_);
v_paramNames_853_ = lean_ctor_get(v_snd_756_, 4);
lean_inc_ref(v_paramNames_853_);
v_fvars_854_ = lean_ctor_get(v_snd_756_, 5);
lean_inc_ref(v_fvars_854_);
v_mvars_855_ = lean_ctor_get(v_snd_756_, 6);
lean_inc_ref(v_mvars_855_);
v_lmap_856_ = lean_ctor_get(v_snd_756_, 7);
lean_inc_ref(v_lmap_856_);
v_emap_857_ = lean_ctor_get(v_snd_756_, 8);
lean_inc_ref(v_emap_857_);
v_abstractLevels_858_ = lean_ctor_get_uint8(v_snd_756_, sizeof(void*)*9);
lean_dec(v_snd_756_);
v___x_859_ = 0;
v___x_860_ = 0;
v___x_861_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_850_, v_fst_755_, v_userName_848_, v_fst_752_, v___x_859_, v___x_860_);
lean_inc_ref(v___x_760_);
v___x_862_ = lean_array_push(v_fvars_854_, v___x_760_);
v___x_863_ = lean_array_push(v_mvars_855_, v_e_733_);
v___x_864_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2___redArg(v_emap_857_, v_mvarId_737_);
switch(lean_obj_tag(v___x_864_))
{
case 0:
{
lean_object* v_index_865_; lean_object* v_size_866_; lean_object* v___x_867_; 
v_index_865_ = lean_ctor_get(v___x_864_, 0);
lean_inc(v_index_865_);
lean_dec_ref_known(v___x_864_, 3);
v_size_866_ = lean_ctor_get(v_emap_857_, 0);
lean_inc(v_size_866_);
lean_inc_ref(v___x_760_);
v___x_867_ = l_Std_DHashMap_Raw_setEntry___redArg(v_emap_857_, v_size_866_, v_index_865_, v_mvarId_737_, v___x_760_);
lean_dec(v_index_865_);
v___y_762_ = v_abstractLevels_858_;
v___y_763_ = v_paramNames_853_;
v___y_764_ = v___x_862_;
v___y_765_ = v___x_861_;
v___y_766_ = v_nextParamIdx_852_;
v___y_767_ = v_mctx_851_;
v___y_768_ = v___x_863_;
v___y_769_ = v_lmap_856_;
v___y_770_ = v_ngen_849_;
v___y_771_ = v___x_867_;
goto v___jp_761_;
}
case 1:
{
lean_object* v_index_868_; lean_object* v_size_869_; lean_object* v_keyArray_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; uint8_t v___x_874_; 
v_index_868_ = lean_ctor_get(v___x_864_, 0);
lean_inc(v_index_868_);
lean_dec_ref_known(v___x_864_, 1);
v_size_869_ = lean_ctor_get(v_emap_857_, 0);
v_keyArray_870_ = lean_ctor_get(v_emap_857_, 1);
v___x_871_ = lean_unsigned_to_nat(1u);
v___x_872_ = lean_nat_add(v_size_869_, v___x_871_);
v___x_873_ = lean_array_get_size(v_keyArray_870_);
v___x_874_ = lean_nat_dec_lt(v___x_872_, v___x_873_);
if (v___x_874_ == 0)
{
lean_dec(v___x_872_);
lean_dec(v_index_868_);
v___y_828_ = v_abstractLevels_858_;
v___y_829_ = v_paramNames_853_;
v___y_830_ = v___x_862_;
v___y_831_ = v___x_861_;
v___y_832_ = v_nextParamIdx_852_;
v___y_833_ = v_mctx_851_;
v___y_834_ = v_emap_857_;
v___y_835_ = v___x_863_;
v___y_836_ = v_lmap_856_;
v___y_837_ = v_ngen_849_;
goto v___jp_827_;
}
else
{
lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; uint8_t v___x_879_; 
v___x_875_ = lean_unsigned_to_nat(4u);
v___x_876_ = lean_nat_mul(v___x_872_, v___x_875_);
v___x_877_ = lean_unsigned_to_nat(3u);
v___x_878_ = lean_nat_mul(v___x_873_, v___x_877_);
v___x_879_ = lean_nat_dec_le(v___x_876_, v___x_878_);
lean_dec(v___x_878_);
lean_dec(v___x_876_);
if (v___x_879_ == 0)
{
lean_dec(v___x_872_);
lean_dec(v_index_868_);
v___y_828_ = v_abstractLevels_858_;
v___y_829_ = v_paramNames_853_;
v___y_830_ = v___x_862_;
v___y_831_ = v___x_861_;
v___y_832_ = v_nextParamIdx_852_;
v___y_833_ = v_mctx_851_;
v___y_834_ = v_emap_857_;
v___y_835_ = v___x_863_;
v___y_836_ = v_lmap_856_;
v___y_837_ = v_ngen_849_;
goto v___jp_827_;
}
else
{
lean_object* v___x_880_; 
lean_inc_ref(v___x_760_);
v___x_880_ = l_Std_DHashMap_Raw_setEntry___redArg(v_emap_857_, v___x_872_, v_index_868_, v_mvarId_737_, v___x_760_);
lean_dec(v_index_868_);
v___y_762_ = v_abstractLevels_858_;
v___y_763_ = v_paramNames_853_;
v___y_764_ = v___x_862_;
v___y_765_ = v___x_861_;
v___y_766_ = v_nextParamIdx_852_;
v___y_767_ = v_mctx_851_;
v___y_768_ = v___x_863_;
v___y_769_ = v_lmap_856_;
v___y_770_ = v_ngen_849_;
v___y_771_ = v___x_880_;
goto v___jp_761_;
}
}
}
default: 
{
lean_object* v_size_881_; lean_object* v_keyArray_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; uint8_t v___x_886_; 
v_size_881_ = lean_ctor_get(v_emap_857_, 0);
v_keyArray_882_ = lean_ctor_get(v_emap_857_, 1);
v___x_883_ = lean_unsigned_to_nat(1u);
v___x_884_ = lean_nat_add(v_size_881_, v___x_883_);
v___x_885_ = lean_array_get_size(v_keyArray_882_);
v___x_886_ = lean_nat_dec_lt(v___x_884_, v___x_885_);
if (v___x_886_ == 0)
{
lean_object* v___x_887_; 
lean_dec(v___x_884_);
v___x_887_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__3___redArg(v_emap_857_);
lean_dec_ref(v_emap_857_);
v___y_793_ = v_abstractLevels_858_;
v___y_794_ = v_paramNames_853_;
v___y_795_ = v___x_862_;
v___y_796_ = v___x_861_;
v___y_797_ = v_nextParamIdx_852_;
v___y_798_ = v_mctx_851_;
v___y_799_ = v___x_863_;
v___y_800_ = v_lmap_856_;
v___y_801_ = v_ngen_849_;
v___y_802_ = v___x_887_;
goto v___jp_792_;
}
else
{
lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; uint8_t v___x_892_; 
v___x_888_ = lean_unsigned_to_nat(4u);
v___x_889_ = lean_nat_mul(v___x_884_, v___x_888_);
lean_dec(v___x_884_);
v___x_890_ = lean_unsigned_to_nat(3u);
v___x_891_ = lean_nat_mul(v___x_885_, v___x_890_);
v___x_892_ = lean_nat_dec_le(v___x_889_, v___x_891_);
lean_dec(v___x_891_);
lean_dec(v___x_889_);
if (v___x_892_ == 0)
{
lean_object* v___x_893_; 
v___x_893_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__3___redArg(v_emap_857_);
lean_dec_ref(v_emap_857_);
v___y_793_ = v_abstractLevels_858_;
v___y_794_ = v_paramNames_853_;
v___y_795_ = v___x_862_;
v___y_796_ = v___x_861_;
v___y_797_ = v_nextParamIdx_852_;
v___y_798_ = v_mctx_851_;
v___y_799_ = v___x_863_;
v___y_800_ = v_lmap_856_;
v___y_801_ = v_ngen_849_;
v___y_802_ = v___x_893_;
goto v___jp_792_;
}
else
{
v___y_793_ = v_abstractLevels_858_;
v___y_794_ = v_paramNames_853_;
v___y_795_ = v___x_862_;
v___y_796_ = v___x_861_;
v___y_797_ = v_nextParamIdx_852_;
v___y_798_ = v_mctx_851_;
v___y_799_ = v___x_863_;
v___y_800_ = v_lmap_856_;
v___y_801_ = v_ngen_849_;
v___y_802_ = v_emap_857_;
goto v___jp_792_;
}
}
}
}
}
}
}
else
{
lean_object* v_val_900_; lean_object* v___x_901_; 
lean_dec_ref(v_type_742_);
lean_dec(v_userName_741_);
lean_dec(v_mvarId_737_);
lean_dec_ref_known(v_e_733_, 1);
v_val_900_ = lean_ctor_get(v___x_747_, 0);
lean_inc(v_val_900_);
lean_dec_ref_known(v___x_747_, 1);
v___x_901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_901_, 0, v_val_900_);
lean_ctor_set(v___x_901_, 1, v_a_734_);
return v___x_901_;
}
}
}
case 3:
{
lean_object* v_u_902_; lean_object* v___x_903_; lean_object* v_fst_904_; lean_object* v_snd_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_919_; 
v_u_902_ = lean_ctor_get(v_e_733_, 0);
lean_inc(v_u_902_);
v___x_903_ = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(v_u_902_, v_a_734_);
v_fst_904_ = lean_ctor_get(v___x_903_, 0);
v_snd_905_ = lean_ctor_get(v___x_903_, 1);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_903_);
if (v_isSharedCheck_919_ == 0)
{
v___x_907_ = v___x_903_;
v_isShared_908_ = v_isSharedCheck_919_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_snd_905_);
lean_inc(v_fst_904_);
lean_dec(v___x_903_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_919_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
size_t v___x_909_; size_t v___x_910_; uint8_t v___x_911_; 
v___x_909_ = lean_ptr_addr(v_u_902_);
v___x_910_ = lean_ptr_addr(v_fst_904_);
v___x_911_ = lean_usize_dec_eq(v___x_909_, v___x_910_);
if (v___x_911_ == 0)
{
lean_object* v___x_912_; lean_object* v___x_914_; 
lean_dec_ref_known(v_e_733_, 1);
v___x_912_ = l_Lean_Expr_sort___override(v_fst_904_);
if (v_isShared_908_ == 0)
{
lean_ctor_set(v___x_907_, 0, v___x_912_);
v___x_914_ = v___x_907_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v___x_912_);
lean_ctor_set(v_reuseFailAlloc_915_, 1, v_snd_905_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
else
{
lean_object* v___x_917_; 
lean_dec(v_fst_904_);
if (v_isShared_908_ == 0)
{
lean_ctor_set(v___x_907_, 0, v_e_733_);
v___x_917_ = v___x_907_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_e_733_);
lean_ctor_set(v_reuseFailAlloc_918_, 1, v_snd_905_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
}
case 4:
{
lean_object* v_declName_920_; lean_object* v_us_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v_fst_924_; lean_object* v_snd_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_937_; 
v_declName_920_ = lean_ctor_get(v_e_733_, 0);
v_us_921_ = lean_ctor_get(v_e_733_, 1);
v___x_922_ = lean_box(0);
lean_inc(v_us_921_);
v___x_923_ = l_List_mapM_loop___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__4(v_us_921_, v___x_922_, v_a_734_);
v_fst_924_ = lean_ctor_get(v___x_923_, 0);
v_snd_925_ = lean_ctor_get(v___x_923_, 1);
v_isSharedCheck_937_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_937_ == 0)
{
v___x_927_ = v___x_923_;
v_isShared_928_ = v_isSharedCheck_937_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_snd_925_);
lean_inc(v_fst_924_);
lean_dec(v___x_923_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_937_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
uint8_t v___x_929_; 
v___x_929_ = l_ptrEqList___redArg(v_us_921_, v_fst_924_);
if (v___x_929_ == 0)
{
lean_object* v___x_930_; lean_object* v___x_932_; 
lean_inc(v_declName_920_);
lean_dec_ref_known(v_e_733_, 2);
v___x_930_ = l_Lean_Expr_const___override(v_declName_920_, v_fst_924_);
if (v_isShared_928_ == 0)
{
lean_ctor_set(v___x_927_, 0, v___x_930_);
v___x_932_ = v___x_927_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v___x_930_);
lean_ctor_set(v_reuseFailAlloc_933_, 1, v_snd_925_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
else
{
lean_object* v___x_935_; 
lean_dec(v_fst_924_);
if (v_isShared_928_ == 0)
{
lean_ctor_set(v___x_927_, 0, v_e_733_);
v___x_935_ = v___x_927_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_e_733_);
lean_ctor_set(v_reuseFailAlloc_936_, 1, v_snd_925_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
}
}
case 5:
{
lean_object* v_fn_938_; lean_object* v_arg_939_; lean_object* v___x_940_; lean_object* v_fst_941_; lean_object* v_snd_942_; lean_object* v___x_943_; lean_object* v_fst_944_; lean_object* v_snd_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_964_; 
v_fn_938_ = lean_ctor_get(v_e_733_, 0);
v_arg_939_ = lean_ctor_get(v_e_733_, 1);
lean_inc_ref(v_fn_938_);
v___x_940_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_fn_938_, v_a_734_);
v_fst_941_ = lean_ctor_get(v___x_940_, 0);
lean_inc(v_fst_941_);
v_snd_942_ = lean_ctor_get(v___x_940_, 1);
lean_inc(v_snd_942_);
lean_dec_ref(v___x_940_);
lean_inc_ref(v_arg_939_);
v___x_943_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_arg_939_, v_snd_942_);
v_fst_944_ = lean_ctor_get(v___x_943_, 0);
v_snd_945_ = lean_ctor_get(v___x_943_, 1);
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_964_ == 0)
{
v___x_947_ = v___x_943_;
v_isShared_948_ = v_isSharedCheck_964_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_snd_945_);
lean_inc(v_fst_944_);
lean_dec(v___x_943_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_964_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
uint8_t v___y_950_; size_t v___x_958_; size_t v___x_959_; uint8_t v___x_960_; 
v___x_958_ = lean_ptr_addr(v_fn_938_);
v___x_959_ = lean_ptr_addr(v_fst_941_);
v___x_960_ = lean_usize_dec_eq(v___x_958_, v___x_959_);
if (v___x_960_ == 0)
{
v___y_950_ = v___x_960_;
goto v___jp_949_;
}
else
{
size_t v___x_961_; size_t v___x_962_; uint8_t v___x_963_; 
v___x_961_ = lean_ptr_addr(v_arg_939_);
v___x_962_ = lean_ptr_addr(v_fst_944_);
v___x_963_ = lean_usize_dec_eq(v___x_961_, v___x_962_);
v___y_950_ = v___x_963_;
goto v___jp_949_;
}
v___jp_949_:
{
if (v___y_950_ == 0)
{
lean_object* v___x_951_; lean_object* v___x_953_; 
lean_dec_ref_known(v_e_733_, 2);
v___x_951_ = l_Lean_Expr_app___override(v_fst_941_, v_fst_944_);
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 0, v___x_951_);
v___x_953_ = v___x_947_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v___x_951_);
lean_ctor_set(v_reuseFailAlloc_954_, 1, v_snd_945_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
else
{
lean_object* v___x_956_; 
lean_dec(v_fst_944_);
lean_dec(v_fst_941_);
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 0, v_e_733_);
v___x_956_ = v___x_947_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_e_733_);
lean_ctor_set(v_reuseFailAlloc_957_, 1, v_snd_945_);
v___x_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
return v___x_956_;
}
}
}
}
}
case 6:
{
lean_object* v_binderName_965_; lean_object* v_binderType_966_; lean_object* v_body_967_; uint8_t v_binderInfo_968_; lean_object* v___x_969_; lean_object* v_fst_970_; lean_object* v_snd_971_; lean_object* v___x_972_; lean_object* v_fst_973_; lean_object* v_snd_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_998_; 
v_binderName_965_ = lean_ctor_get(v_e_733_, 0);
v_binderType_966_ = lean_ctor_get(v_e_733_, 1);
v_body_967_ = lean_ctor_get(v_e_733_, 2);
v_binderInfo_968_ = lean_ctor_get_uint8(v_e_733_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_966_);
v___x_969_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_binderType_966_, v_a_734_);
v_fst_970_ = lean_ctor_get(v___x_969_, 0);
lean_inc(v_fst_970_);
v_snd_971_ = lean_ctor_get(v___x_969_, 1);
lean_inc(v_snd_971_);
lean_dec_ref(v___x_969_);
lean_inc_ref(v_body_967_);
v___x_972_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_body_967_, v_snd_971_);
v_fst_973_ = lean_ctor_get(v___x_972_, 0);
v_snd_974_ = lean_ctor_get(v___x_972_, 1);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_998_ == 0)
{
v___x_976_ = v___x_972_;
v_isShared_977_ = v_isSharedCheck_998_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_snd_974_);
lean_inc(v_fst_973_);
lean_dec(v___x_972_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_998_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
uint8_t v___y_979_; size_t v___x_992_; size_t v___x_993_; uint8_t v___x_994_; 
v___x_992_ = lean_ptr_addr(v_binderType_966_);
v___x_993_ = lean_ptr_addr(v_fst_970_);
v___x_994_ = lean_usize_dec_eq(v___x_992_, v___x_993_);
if (v___x_994_ == 0)
{
v___y_979_ = v___x_994_;
goto v___jp_978_;
}
else
{
size_t v___x_995_; size_t v___x_996_; uint8_t v___x_997_; 
v___x_995_ = lean_ptr_addr(v_body_967_);
v___x_996_ = lean_ptr_addr(v_fst_973_);
v___x_997_ = lean_usize_dec_eq(v___x_995_, v___x_996_);
v___y_979_ = v___x_997_;
goto v___jp_978_;
}
v___jp_978_:
{
if (v___y_979_ == 0)
{
lean_object* v___x_980_; lean_object* v___x_982_; 
lean_inc(v_binderName_965_);
lean_dec_ref_known(v_e_733_, 3);
v___x_980_ = l_Lean_Expr_lam___override(v_binderName_965_, v_fst_970_, v_fst_973_, v_binderInfo_968_);
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 0, v___x_980_);
v___x_982_ = v___x_976_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v___x_980_);
lean_ctor_set(v_reuseFailAlloc_983_, 1, v_snd_974_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
else
{
uint8_t v___x_984_; 
v___x_984_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_968_, v_binderInfo_968_);
if (v___x_984_ == 0)
{
lean_object* v___x_985_; lean_object* v___x_987_; 
lean_inc(v_binderName_965_);
lean_dec_ref_known(v_e_733_, 3);
v___x_985_ = l_Lean_Expr_lam___override(v_binderName_965_, v_fst_970_, v_fst_973_, v_binderInfo_968_);
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 0, v___x_985_);
v___x_987_ = v___x_976_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v___x_985_);
lean_ctor_set(v_reuseFailAlloc_988_, 1, v_snd_974_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
else
{
lean_object* v___x_990_; 
lean_dec(v_fst_973_);
lean_dec(v_fst_970_);
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 0, v_e_733_);
v___x_990_ = v___x_976_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_e_733_);
lean_ctor_set(v_reuseFailAlloc_991_, 1, v_snd_974_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
}
}
}
}
case 7:
{
lean_object* v_binderName_999_; lean_object* v_binderType_1000_; lean_object* v_body_1001_; uint8_t v_binderInfo_1002_; lean_object* v___x_1003_; lean_object* v_fst_1004_; lean_object* v_snd_1005_; lean_object* v___x_1006_; lean_object* v_fst_1007_; lean_object* v_snd_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1032_; 
v_binderName_999_ = lean_ctor_get(v_e_733_, 0);
v_binderType_1000_ = lean_ctor_get(v_e_733_, 1);
v_body_1001_ = lean_ctor_get(v_e_733_, 2);
v_binderInfo_1002_ = lean_ctor_get_uint8(v_e_733_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1000_);
v___x_1003_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_binderType_1000_, v_a_734_);
v_fst_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc(v_fst_1004_);
v_snd_1005_ = lean_ctor_get(v___x_1003_, 1);
lean_inc(v_snd_1005_);
lean_dec_ref(v___x_1003_);
lean_inc_ref(v_body_1001_);
v___x_1006_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_body_1001_, v_snd_1005_);
v_fst_1007_ = lean_ctor_get(v___x_1006_, 0);
v_snd_1008_ = lean_ctor_get(v___x_1006_, 1);
v_isSharedCheck_1032_ = !lean_is_exclusive(v___x_1006_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_1010_ = v___x_1006_;
v_isShared_1011_ = v_isSharedCheck_1032_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_snd_1008_);
lean_inc(v_fst_1007_);
lean_dec(v___x_1006_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1032_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
uint8_t v___y_1013_; size_t v___x_1026_; size_t v___x_1027_; uint8_t v___x_1028_; 
v___x_1026_ = lean_ptr_addr(v_binderType_1000_);
v___x_1027_ = lean_ptr_addr(v_fst_1004_);
v___x_1028_ = lean_usize_dec_eq(v___x_1026_, v___x_1027_);
if (v___x_1028_ == 0)
{
v___y_1013_ = v___x_1028_;
goto v___jp_1012_;
}
else
{
size_t v___x_1029_; size_t v___x_1030_; uint8_t v___x_1031_; 
v___x_1029_ = lean_ptr_addr(v_body_1001_);
v___x_1030_ = lean_ptr_addr(v_fst_1007_);
v___x_1031_ = lean_usize_dec_eq(v___x_1029_, v___x_1030_);
v___y_1013_ = v___x_1031_;
goto v___jp_1012_;
}
v___jp_1012_:
{
if (v___y_1013_ == 0)
{
lean_object* v___x_1014_; lean_object* v___x_1016_; 
lean_inc(v_binderName_999_);
lean_dec_ref_known(v_e_733_, 3);
v___x_1014_ = l_Lean_Expr_forallE___override(v_binderName_999_, v_fst_1004_, v_fst_1007_, v_binderInfo_1002_);
if (v_isShared_1011_ == 0)
{
lean_ctor_set(v___x_1010_, 0, v___x_1014_);
v___x_1016_ = v___x_1010_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v___x_1014_);
lean_ctor_set(v_reuseFailAlloc_1017_, 1, v_snd_1008_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
else
{
uint8_t v___x_1018_; 
v___x_1018_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1002_, v_binderInfo_1002_);
if (v___x_1018_ == 0)
{
lean_object* v___x_1019_; lean_object* v___x_1021_; 
lean_inc(v_binderName_999_);
lean_dec_ref_known(v_e_733_, 3);
v___x_1019_ = l_Lean_Expr_forallE___override(v_binderName_999_, v_fst_1004_, v_fst_1007_, v_binderInfo_1002_);
if (v_isShared_1011_ == 0)
{
lean_ctor_set(v___x_1010_, 0, v___x_1019_);
v___x_1021_ = v___x_1010_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v___x_1019_);
lean_ctor_set(v_reuseFailAlloc_1022_, 1, v_snd_1008_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
}
}
else
{
lean_object* v___x_1024_; 
lean_dec(v_fst_1007_);
lean_dec(v_fst_1004_);
if (v_isShared_1011_ == 0)
{
lean_ctor_set(v___x_1010_, 0, v_e_733_);
v___x_1024_ = v___x_1010_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_e_733_);
lean_ctor_set(v_reuseFailAlloc_1025_, 1, v_snd_1008_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
}
}
}
}
case 8:
{
lean_object* v_declName_1033_; lean_object* v_type_1034_; lean_object* v_value_1035_; lean_object* v_body_1036_; uint8_t v_nondep_1037_; lean_object* v___x_1038_; lean_object* v_fst_1039_; lean_object* v_snd_1040_; lean_object* v___x_1041_; lean_object* v_fst_1042_; lean_object* v_snd_1043_; lean_object* v___x_1044_; lean_object* v_fst_1045_; lean_object* v_snd_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1072_; 
v_declName_1033_ = lean_ctor_get(v_e_733_, 0);
v_type_1034_ = lean_ctor_get(v_e_733_, 1);
v_value_1035_ = lean_ctor_get(v_e_733_, 2);
v_body_1036_ = lean_ctor_get(v_e_733_, 3);
v_nondep_1037_ = lean_ctor_get_uint8(v_e_733_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_1034_);
v___x_1038_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_type_1034_, v_a_734_);
v_fst_1039_ = lean_ctor_get(v___x_1038_, 0);
lean_inc(v_fst_1039_);
v_snd_1040_ = lean_ctor_get(v___x_1038_, 1);
lean_inc(v_snd_1040_);
lean_dec_ref(v___x_1038_);
lean_inc_ref(v_value_1035_);
v___x_1041_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_value_1035_, v_snd_1040_);
v_fst_1042_ = lean_ctor_get(v___x_1041_, 0);
lean_inc(v_fst_1042_);
v_snd_1043_ = lean_ctor_get(v___x_1041_, 1);
lean_inc(v_snd_1043_);
lean_dec_ref(v___x_1041_);
lean_inc_ref(v_body_1036_);
v___x_1044_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_body_1036_, v_snd_1043_);
v_fst_1045_ = lean_ctor_get(v___x_1044_, 0);
v_snd_1046_ = lean_ctor_get(v___x_1044_, 1);
v_isSharedCheck_1072_ = !lean_is_exclusive(v___x_1044_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1048_ = v___x_1044_;
v_isShared_1049_ = v_isSharedCheck_1072_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_snd_1046_);
lean_inc(v_fst_1045_);
lean_dec(v___x_1044_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1072_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
uint8_t v___y_1051_; size_t v___x_1066_; size_t v___x_1067_; uint8_t v___x_1068_; 
v___x_1066_ = lean_ptr_addr(v_type_1034_);
v___x_1067_ = lean_ptr_addr(v_fst_1039_);
v___x_1068_ = lean_usize_dec_eq(v___x_1066_, v___x_1067_);
if (v___x_1068_ == 0)
{
v___y_1051_ = v___x_1068_;
goto v___jp_1050_;
}
else
{
size_t v___x_1069_; size_t v___x_1070_; uint8_t v___x_1071_; 
v___x_1069_ = lean_ptr_addr(v_value_1035_);
v___x_1070_ = lean_ptr_addr(v_fst_1042_);
v___x_1071_ = lean_usize_dec_eq(v___x_1069_, v___x_1070_);
v___y_1051_ = v___x_1071_;
goto v___jp_1050_;
}
v___jp_1050_:
{
if (v___y_1051_ == 0)
{
lean_object* v___x_1052_; lean_object* v___x_1054_; 
lean_inc(v_declName_1033_);
lean_dec_ref_known(v_e_733_, 4);
v___x_1052_ = l_Lean_Expr_letE___override(v_declName_1033_, v_fst_1039_, v_fst_1042_, v_fst_1045_, v_nondep_1037_);
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 0, v___x_1052_);
v___x_1054_ = v___x_1048_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v___x_1052_);
lean_ctor_set(v_reuseFailAlloc_1055_, 1, v_snd_1046_);
v___x_1054_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
return v___x_1054_;
}
}
else
{
size_t v___x_1056_; size_t v___x_1057_; uint8_t v___x_1058_; 
v___x_1056_ = lean_ptr_addr(v_body_1036_);
v___x_1057_ = lean_ptr_addr(v_fst_1045_);
v___x_1058_ = lean_usize_dec_eq(v___x_1056_, v___x_1057_);
if (v___x_1058_ == 0)
{
lean_object* v___x_1059_; lean_object* v___x_1061_; 
lean_inc(v_declName_1033_);
lean_dec_ref_known(v_e_733_, 4);
v___x_1059_ = l_Lean_Expr_letE___override(v_declName_1033_, v_fst_1039_, v_fst_1042_, v_fst_1045_, v_nondep_1037_);
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 0, v___x_1059_);
v___x_1061_ = v___x_1048_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v___x_1059_);
lean_ctor_set(v_reuseFailAlloc_1062_, 1, v_snd_1046_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
else
{
lean_object* v___x_1064_; 
lean_dec(v_fst_1045_);
lean_dec(v_fst_1042_);
lean_dec(v_fst_1039_);
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 0, v_e_733_);
v___x_1064_ = v___x_1048_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v_e_733_);
lean_ctor_set(v_reuseFailAlloc_1065_, 1, v_snd_1046_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
}
}
}
}
}
}
case 10:
{
lean_object* v_data_1073_; lean_object* v_expr_1074_; lean_object* v___x_1075_; lean_object* v_fst_1076_; lean_object* v_snd_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1091_; 
v_data_1073_ = lean_ctor_get(v_e_733_, 0);
v_expr_1074_ = lean_ctor_get(v_e_733_, 1);
lean_inc_ref(v_expr_1074_);
v___x_1075_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_expr_1074_, v_a_734_);
v_fst_1076_ = lean_ctor_get(v___x_1075_, 0);
v_snd_1077_ = lean_ctor_get(v___x_1075_, 1);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1079_ = v___x_1075_;
v_isShared_1080_ = v_isSharedCheck_1091_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_snd_1077_);
lean_inc(v_fst_1076_);
lean_dec(v___x_1075_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1091_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
size_t v___x_1081_; size_t v___x_1082_; uint8_t v___x_1083_; 
v___x_1081_ = lean_ptr_addr(v_expr_1074_);
v___x_1082_ = lean_ptr_addr(v_fst_1076_);
v___x_1083_ = lean_usize_dec_eq(v___x_1081_, v___x_1082_);
if (v___x_1083_ == 0)
{
lean_object* v___x_1084_; lean_object* v___x_1086_; 
lean_inc(v_data_1073_);
lean_dec_ref_known(v_e_733_, 2);
v___x_1084_ = l_Lean_Expr_mdata___override(v_data_1073_, v_fst_1076_);
if (v_isShared_1080_ == 0)
{
lean_ctor_set(v___x_1079_, 0, v___x_1084_);
v___x_1086_ = v___x_1079_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v___x_1084_);
lean_ctor_set(v_reuseFailAlloc_1087_, 1, v_snd_1077_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
else
{
lean_object* v___x_1089_; 
lean_dec(v_fst_1076_);
if (v_isShared_1080_ == 0)
{
lean_ctor_set(v___x_1079_, 0, v_e_733_);
v___x_1089_ = v___x_1079_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_e_733_);
lean_ctor_set(v_reuseFailAlloc_1090_, 1, v_snd_1077_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
}
}
case 11:
{
lean_object* v_typeName_1092_; lean_object* v_idx_1093_; lean_object* v_struct_1094_; lean_object* v___x_1095_; lean_object* v_fst_1096_; lean_object* v_snd_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1111_; 
v_typeName_1092_ = lean_ctor_get(v_e_733_, 0);
v_idx_1093_ = lean_ctor_get(v_e_733_, 1);
v_struct_1094_ = lean_ctor_get(v_e_733_, 2);
lean_inc_ref(v_struct_1094_);
v___x_1095_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_struct_1094_, v_a_734_);
v_fst_1096_ = lean_ctor_get(v___x_1095_, 0);
v_snd_1097_ = lean_ctor_get(v___x_1095_, 1);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_1095_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1099_ = v___x_1095_;
v_isShared_1100_ = v_isSharedCheck_1111_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_snd_1097_);
lean_inc(v_fst_1096_);
lean_dec(v___x_1095_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1111_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
size_t v___x_1101_; size_t v___x_1102_; uint8_t v___x_1103_; 
v___x_1101_ = lean_ptr_addr(v_struct_1094_);
v___x_1102_ = lean_ptr_addr(v_fst_1096_);
v___x_1103_ = lean_usize_dec_eq(v___x_1101_, v___x_1102_);
if (v___x_1103_ == 0)
{
lean_object* v___x_1104_; lean_object* v___x_1106_; 
lean_inc(v_idx_1093_);
lean_inc(v_typeName_1092_);
lean_dec_ref_known(v_e_733_, 3);
v___x_1104_ = l_Lean_Expr_proj___override(v_typeName_1092_, v_idx_1093_, v_fst_1096_);
if (v_isShared_1100_ == 0)
{
lean_ctor_set(v___x_1099_, 0, v___x_1104_);
v___x_1106_ = v___x_1099_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v___x_1104_);
lean_ctor_set(v_reuseFailAlloc_1107_, 1, v_snd_1097_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
else
{
lean_object* v___x_1109_; 
lean_dec(v_fst_1096_);
if (v_isShared_1100_ == 0)
{
lean_ctor_set(v___x_1099_, 0, v_e_733_);
v___x_1109_ = v___x_1099_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_e_733_);
lean_ctor_set(v_reuseFailAlloc_1110_, 1, v_snd_1097_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
}
}
default: 
{
lean_object* v___x_1112_; 
v___x_1112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1112_, 0, v_e_733_);
lean_ctor_set(v___x_1112_, 1, v_a_734_);
return v___x_1112_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0(lean_object* v_00_u03b2_1113_, lean_object* v_m_1114_, lean_object* v_a_1115_){
_start:
{
lean_object* v___x_1116_; 
v___x_1116_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0___redArg(v_m_1114_, v_a_1115_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0___boxed(lean_object* v_00_u03b2_1117_, lean_object* v_m_1118_, lean_object* v_a_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0(v_00_u03b2_1117_, v_m_1118_, v_a_1119_);
lean_dec(v_a_1119_);
lean_dec_ref(v_m_1118_);
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2(lean_object* v_00_u03b2_1121_, lean_object* v_m_1122_, lean_object* v_query_1123_){
_start:
{
lean_object* v___x_1124_; 
v___x_1124_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2___redArg(v_m_1122_, v_query_1123_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2___boxed(lean_object* v_00_u03b2_1125_, lean_object* v_m_1126_, lean_object* v_query_1127_){
_start:
{
lean_object* v_res_1128_; 
v_res_1128_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2(v_00_u03b2_1125_, v_m_1126_, v_query_1127_);
lean_dec(v_query_1127_);
lean_dec_ref(v_m_1126_);
return v_res_1128_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__3(lean_object* v_00_u03b2_1129_, lean_object* v_m_1130_){
_start:
{
lean_object* v___x_1131_; 
v___x_1131_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__3___redArg(v_m_1130_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__3___boxed(lean_object* v_00_u03b2_1132_, lean_object* v_m_1133_){
_start:
{
lean_object* v_res_1134_; 
v_res_1134_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__3(v_00_u03b2_1132_, v_m_1133_);
lean_dec_ref(v_m_1133_);
return v_res_1134_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0(lean_object* v_00_u03b2_1135_, lean_object* v_m_1136_, lean_object* v_query_1137_){
_start:
{
lean_object* v___x_1138_; 
v___x_1138_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0___redArg(v_m_1136_, v_query_1137_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1139_, lean_object* v_m_1140_, lean_object* v_query_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0(v_00_u03b2_1139_, v_m_1140_, v_query_1141_);
lean_dec(v_query_1141_);
lean_dec_ref(v_m_1140_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3(lean_object* v_00_u03b2_1143_, lean_object* v_m_1144_, lean_object* v_query_1145_, lean_object* v_x_1146_, lean_object* v_x_1147_, lean_object* v_x_1148_, lean_object* v_x_1149_){
_start:
{
lean_object* v___x_1150_; 
v___x_1150_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3___redArg(v_m_1144_, v_query_1145_, v_x_1146_, v_x_1147_, v_x_1148_);
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3___boxed(lean_object* v_00_u03b2_1151_, lean_object* v_m_1152_, lean_object* v_query_1153_, lean_object* v_x_1154_, lean_object* v_x_1155_, lean_object* v_x_1156_, lean_object* v_x_1157_){
_start:
{
lean_object* v_res_1158_; 
v_res_1158_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3(v_00_u03b2_1151_, v_m_1152_, v_query_1153_, v_x_1154_, v_x_1155_, v_x_1156_, v_x_1157_);
lean_dec(v_query_1153_);
lean_dec_ref(v_m_1152_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__3_spec__5(lean_object* v_00_u03b2_1159_, lean_object* v_init_1160_, lean_object* v_b_1161_){
_start:
{
lean_object* v___x_1162_; 
v___x_1162_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__3_spec__5___redArg(v_init_1160_, v_b_1161_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__3_spec__5___boxed(lean_object* v_00_u03b2_1163_, lean_object* v_init_1164_, lean_object* v_b_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__3_spec__5(v_00_u03b2_1163_, v_init_1164_, v_b_1165_);
lean_dec_ref(v_b_1165_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_1167_, lean_object* v_b_1168_, lean_object* v_acc_1169_, lean_object* v_i_1170_){
_start:
{
lean_object* v___x_1171_; 
v___x_1171_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__3_spec__5_spec__6___redArg(v_b_1168_, v_acc_1169_, v_i_1170_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__3_spec__5_spec__6___boxed(lean_object* v_00_u03b2_1172_, lean_object* v_b_1173_, lean_object* v_acc_1174_, lean_object* v_i_1175_){
_start:
{
lean_object* v_res_1176_; 
v_res_1176_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__3_spec__5_spec__6(v_00_u03b2_1172_, v_b_1173_, v_acc_1174_, v_i_1175_);
lean_dec_ref(v_b_1173_);
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0___redArg(lean_object* v_e_1177_, lean_object* v___y_1178_){
_start:
{
uint8_t v___x_1180_; 
v___x_1180_ = l_Lean_Expr_hasMVar(v_e_1177_);
if (v___x_1180_ == 0)
{
lean_object* v___x_1181_; 
v___x_1181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1181_, 0, v_e_1177_);
return v___x_1181_;
}
else
{
lean_object* v___x_1182_; lean_object* v_mctx_1183_; lean_object* v___x_1184_; lean_object* v_fst_1185_; lean_object* v_snd_1186_; lean_object* v___x_1187_; lean_object* v_cache_1188_; lean_object* v_zetaDeltaFVarIds_1189_; lean_object* v_postponed_1190_; lean_object* v_diag_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1200_; 
v___x_1182_ = lean_st_ref_get(v___y_1178_);
v_mctx_1183_ = lean_ctor_get(v___x_1182_, 0);
lean_inc_ref(v_mctx_1183_);
lean_dec(v___x_1182_);
v___x_1184_ = l_Lean_instantiateMVarsCore(v_mctx_1183_, v_e_1177_);
v_fst_1185_ = lean_ctor_get(v___x_1184_, 0);
lean_inc(v_fst_1185_);
v_snd_1186_ = lean_ctor_get(v___x_1184_, 1);
lean_inc(v_snd_1186_);
lean_dec_ref(v___x_1184_);
v___x_1187_ = lean_st_ref_take(v___y_1178_);
v_cache_1188_ = lean_ctor_get(v___x_1187_, 1);
v_zetaDeltaFVarIds_1189_ = lean_ctor_get(v___x_1187_, 2);
v_postponed_1190_ = lean_ctor_get(v___x_1187_, 3);
v_diag_1191_ = lean_ctor_get(v___x_1187_, 4);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1187_);
if (v_isSharedCheck_1200_ == 0)
{
lean_object* v_unused_1201_; 
v_unused_1201_ = lean_ctor_get(v___x_1187_, 0);
lean_dec(v_unused_1201_);
v___x_1193_ = v___x_1187_;
v_isShared_1194_ = v_isSharedCheck_1200_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_diag_1191_);
lean_inc(v_postponed_1190_);
lean_inc(v_zetaDeltaFVarIds_1189_);
lean_inc(v_cache_1188_);
lean_dec(v___x_1187_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1200_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1196_; 
if (v_isShared_1194_ == 0)
{
lean_ctor_set(v___x_1193_, 0, v_snd_1186_);
v___x_1196_ = v___x_1193_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_snd_1186_);
lean_ctor_set(v_reuseFailAlloc_1199_, 1, v_cache_1188_);
lean_ctor_set(v_reuseFailAlloc_1199_, 2, v_zetaDeltaFVarIds_1189_);
lean_ctor_set(v_reuseFailAlloc_1199_, 3, v_postponed_1190_);
lean_ctor_set(v_reuseFailAlloc_1199_, 4, v_diag_1191_);
v___x_1196_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1197_ = lean_st_ref_put(v___y_1178_, v___x_1196_);
v___x_1198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1198_, 0, v_fst_1185_);
return v___x_1198_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0___redArg___boxed(lean_object* v_e_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_){
_start:
{
lean_object* v_res_1205_; 
v_res_1205_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0___redArg(v_e_1202_, v___y_1203_);
lean_dec(v___y_1203_);
return v_res_1205_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0(lean_object* v_e_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_){
_start:
{
lean_object* v___x_1212_; 
v___x_1212_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0___redArg(v_e_1206_, v___y_1208_);
return v___x_1212_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0___boxed(lean_object* v_e_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_){
_start:
{
lean_object* v_res_1219_; 
v_res_1219_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0(v_e_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_);
lean_dec(v___y_1217_);
lean_dec_ref(v___y_1216_);
lean_dec(v___y_1215_);
lean_dec_ref(v___y_1214_);
return v_res_1219_;
}
}
static lean_object* _init_l_Lean_Meta_abstractMVars___closed__1(void){
_start:
{
lean_object* v_cellCount_1222_; lean_object* v___x_1223_; 
v_cellCount_1222_ = lean_unsigned_to_nat(16u);
v___x_1223_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1222_);
return v___x_1223_;
}
}
static lean_object* _init_l_Lean_Meta_abstractMVars___closed__2(void){
_start:
{
lean_object* v_cellCount_1224_; lean_object* v___x_1225_; 
v_cellCount_1224_ = lean_unsigned_to_nat(16u);
v___x_1225_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1224_);
return v___x_1225_;
}
}
static lean_object* _init_l_Lean_Meta_abstractMVars___closed__3(void){
_start:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1226_ = lean_obj_once(&l_Lean_Meta_abstractMVars___closed__2, &l_Lean_Meta_abstractMVars___closed__2_once, _init_l_Lean_Meta_abstractMVars___closed__2);
v___x_1227_ = lean_obj_once(&l_Lean_Meta_abstractMVars___closed__1, &l_Lean_Meta_abstractMVars___closed__1_once, _init_l_Lean_Meta_abstractMVars___closed__1);
v___x_1228_ = lean_unsigned_to_nat(0u);
v___x_1229_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1229_, 0, v___x_1228_);
lean_ctor_set(v___x_1229_, 1, v___x_1227_);
lean_ctor_set(v___x_1229_, 2, v___x_1226_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractMVars(lean_object* v_e_1230_, uint8_t v_levels_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_){
_start:
{
lean_object* v___x_1237_; lean_object* v_a_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1299_; 
v___x_1237_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0___redArg(v_e_1230_, v_a_1233_);
v_a_1238_ = lean_ctor_get(v___x_1237_, 0);
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1237_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1240_ = v___x_1237_;
v_isShared_1241_ = v_isSharedCheck_1299_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_a_1238_);
lean_dec(v___x_1237_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1299_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v_mctx_1244_; lean_object* v_lctx_1245_; lean_object* v_ngen_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v_fst_1252_; lean_object* v_snd_1253_; lean_object* v___x_1254_; lean_object* v_ngen_1255_; lean_object* v_lctx_1256_; lean_object* v_mctx_1257_; lean_object* v_paramNames_1258_; lean_object* v_fvars_1259_; lean_object* v_mvars_1260_; lean_object* v_env_1261_; lean_object* v_nextMacroScope_1262_; lean_object* v_auxDeclNGen_1263_; lean_object* v_traceState_1264_; lean_object* v_cache_1265_; lean_object* v_messages_1266_; lean_object* v_infoState_1267_; lean_object* v_snapshotTasks_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1297_; 
v___x_1242_ = lean_st_ref_get(v_a_1233_);
v___x_1243_ = lean_st_ref_get(v_a_1235_);
v_mctx_1244_ = lean_ctor_get(v___x_1242_, 0);
lean_inc_ref(v_mctx_1244_);
lean_dec(v___x_1242_);
v_lctx_1245_ = lean_ctor_get(v_a_1232_, 2);
v_ngen_1246_ = lean_ctor_get(v___x_1243_, 2);
lean_inc_ref(v_ngen_1246_);
lean_dec(v___x_1243_);
v___x_1247_ = lean_unsigned_to_nat(0u);
v___x_1248_ = ((lean_object*)(l_Lean_Meta_abstractMVars___closed__0));
v___x_1249_ = lean_obj_once(&l_Lean_Meta_abstractMVars___closed__3, &l_Lean_Meta_abstractMVars___closed__3_once, _init_l_Lean_Meta_abstractMVars___closed__3);
lean_inc_ref(v_lctx_1245_);
v___x_1250_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v___x_1250_, 0, v_ngen_1246_);
lean_ctor_set(v___x_1250_, 1, v_lctx_1245_);
lean_ctor_set(v___x_1250_, 2, v_mctx_1244_);
lean_ctor_set(v___x_1250_, 3, v___x_1247_);
lean_ctor_set(v___x_1250_, 4, v___x_1248_);
lean_ctor_set(v___x_1250_, 5, v___x_1248_);
lean_ctor_set(v___x_1250_, 6, v___x_1248_);
lean_ctor_set(v___x_1250_, 7, v___x_1249_);
lean_ctor_set(v___x_1250_, 8, v___x_1249_);
lean_ctor_set_uint8(v___x_1250_, sizeof(void*)*9, v_levels_1231_);
v___x_1251_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_a_1238_, v___x_1250_);
v_fst_1252_ = lean_ctor_get(v___x_1251_, 0);
lean_inc(v_fst_1252_);
v_snd_1253_ = lean_ctor_get(v___x_1251_, 1);
lean_inc(v_snd_1253_);
lean_dec_ref(v___x_1251_);
v___x_1254_ = lean_st_ref_take(v_a_1235_);
v_ngen_1255_ = lean_ctor_get(v_snd_1253_, 0);
lean_inc_ref(v_ngen_1255_);
v_lctx_1256_ = lean_ctor_get(v_snd_1253_, 1);
lean_inc_ref(v_lctx_1256_);
v_mctx_1257_ = lean_ctor_get(v_snd_1253_, 2);
lean_inc_ref(v_mctx_1257_);
v_paramNames_1258_ = lean_ctor_get(v_snd_1253_, 4);
lean_inc_ref(v_paramNames_1258_);
v_fvars_1259_ = lean_ctor_get(v_snd_1253_, 5);
lean_inc_ref(v_fvars_1259_);
v_mvars_1260_ = lean_ctor_get(v_snd_1253_, 6);
lean_inc_ref(v_mvars_1260_);
lean_dec(v_snd_1253_);
v_env_1261_ = lean_ctor_get(v___x_1254_, 0);
v_nextMacroScope_1262_ = lean_ctor_get(v___x_1254_, 1);
v_auxDeclNGen_1263_ = lean_ctor_get(v___x_1254_, 3);
v_traceState_1264_ = lean_ctor_get(v___x_1254_, 4);
v_cache_1265_ = lean_ctor_get(v___x_1254_, 5);
v_messages_1266_ = lean_ctor_get(v___x_1254_, 6);
v_infoState_1267_ = lean_ctor_get(v___x_1254_, 7);
v_snapshotTasks_1268_ = lean_ctor_get(v___x_1254_, 8);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1297_ == 0)
{
lean_object* v_unused_1298_; 
v_unused_1298_ = lean_ctor_get(v___x_1254_, 2);
lean_dec(v_unused_1298_);
v___x_1270_ = v___x_1254_;
v_isShared_1271_ = v_isSharedCheck_1297_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_snapshotTasks_1268_);
lean_inc(v_infoState_1267_);
lean_inc(v_messages_1266_);
lean_inc(v_cache_1265_);
lean_inc(v_traceState_1264_);
lean_inc(v_auxDeclNGen_1263_);
lean_inc(v_nextMacroScope_1262_);
lean_inc(v_env_1261_);
lean_dec(v___x_1254_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1297_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1273_; 
if (v_isShared_1271_ == 0)
{
lean_ctor_set(v___x_1270_, 2, v_ngen_1255_);
v___x_1273_ = v___x_1270_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_env_1261_);
lean_ctor_set(v_reuseFailAlloc_1296_, 1, v_nextMacroScope_1262_);
lean_ctor_set(v_reuseFailAlloc_1296_, 2, v_ngen_1255_);
lean_ctor_set(v_reuseFailAlloc_1296_, 3, v_auxDeclNGen_1263_);
lean_ctor_set(v_reuseFailAlloc_1296_, 4, v_traceState_1264_);
lean_ctor_set(v_reuseFailAlloc_1296_, 5, v_cache_1265_);
lean_ctor_set(v_reuseFailAlloc_1296_, 6, v_messages_1266_);
lean_ctor_set(v_reuseFailAlloc_1296_, 7, v_infoState_1267_);
lean_ctor_set(v_reuseFailAlloc_1296_, 8, v_snapshotTasks_1268_);
v___x_1273_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v_cache_1276_; lean_object* v_zetaDeltaFVarIds_1277_; lean_object* v_postponed_1278_; lean_object* v_diag_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1294_; 
v___x_1274_ = lean_st_ref_put(v_a_1235_, v___x_1273_);
v___x_1275_ = lean_st_ref_take(v_a_1233_);
v_cache_1276_ = lean_ctor_get(v___x_1275_, 1);
v_zetaDeltaFVarIds_1277_ = lean_ctor_get(v___x_1275_, 2);
v_postponed_1278_ = lean_ctor_get(v___x_1275_, 3);
v_diag_1279_ = lean_ctor_get(v___x_1275_, 4);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1294_ == 0)
{
lean_object* v_unused_1295_; 
v_unused_1295_ = lean_ctor_get(v___x_1275_, 0);
lean_dec(v_unused_1295_);
v___x_1281_ = v___x_1275_;
v_isShared_1282_ = v_isSharedCheck_1294_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_diag_1279_);
lean_inc(v_postponed_1278_);
lean_inc(v_zetaDeltaFVarIds_1277_);
lean_inc(v_cache_1276_);
lean_dec(v___x_1275_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1294_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v___x_1284_; 
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 0, v_mctx_1257_);
v___x_1284_ = v___x_1281_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_mctx_1257_);
lean_ctor_set(v_reuseFailAlloc_1293_, 1, v_cache_1276_);
lean_ctor_set(v_reuseFailAlloc_1293_, 2, v_zetaDeltaFVarIds_1277_);
lean_ctor_set(v_reuseFailAlloc_1293_, 3, v_postponed_1278_);
lean_ctor_set(v_reuseFailAlloc_1293_, 4, v_diag_1279_);
v___x_1284_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
lean_object* v___x_1285_; uint8_t v___x_1286_; uint8_t v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1291_; 
v___x_1285_ = lean_st_ref_put(v_a_1233_, v___x_1284_);
v___x_1286_ = 1;
v___x_1287_ = 0;
v___x_1288_ = l_Lean_LocalContext_mkLambda(v_lctx_1256_, v_fvars_1259_, v_fst_1252_, v___x_1286_, v___x_1287_);
lean_dec(v_fst_1252_);
lean_dec_ref(v_fvars_1259_);
v___x_1289_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1289_, 0, v_paramNames_1258_);
lean_ctor_set(v___x_1289_, 1, v_mvars_1260_);
lean_ctor_set(v___x_1289_, 2, v___x_1288_);
if (v_isShared_1241_ == 0)
{
lean_ctor_set(v___x_1240_, 0, v___x_1289_);
v___x_1291_ = v___x_1240_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v___x_1289_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractMVars___boxed(lean_object* v_e_1300_, lean_object* v_levels_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_){
_start:
{
uint8_t v_levels_boxed_1307_; lean_object* v_res_1308_; 
v_levels_boxed_1307_ = lean_unbox(v_levels_1301_);
v_res_1308_ = l_Lean_Meta_abstractMVars(v_e_1300_, v_levels_boxed_1307_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_);
lean_dec(v_a_1305_);
lean_dec_ref(v_a_1304_);
lean_dec(v_a_1303_);
lean_dec_ref(v_a_1302_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_openAbstractMVarsResult_spec__0(size_t v_sz_1309_, size_t v_i_1310_, lean_object* v_bs_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_){
_start:
{
uint8_t v___x_1317_; 
v___x_1317_ = lean_usize_dec_lt(v_i_1310_, v_sz_1309_);
if (v___x_1317_ == 0)
{
lean_object* v___x_1318_; 
v___x_1318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1318_, 0, v_bs_1311_);
return v___x_1318_;
}
else
{
lean_object* v___x_1319_; 
v___x_1319_ = l_Lean_Meta_mkFreshLevelMVar(v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
if (lean_obj_tag(v___x_1319_) == 0)
{
lean_object* v_a_1320_; lean_object* v___x_1321_; lean_object* v_bs_x27_1322_; size_t v___x_1323_; size_t v___x_1324_; lean_object* v___x_1325_; 
v_a_1320_ = lean_ctor_get(v___x_1319_, 0);
lean_inc(v_a_1320_);
lean_dec_ref_known(v___x_1319_, 1);
v___x_1321_ = lean_unsigned_to_nat(0u);
v_bs_x27_1322_ = lean_array_uset(v_bs_1311_, v_i_1310_, v___x_1321_);
v___x_1323_ = ((size_t)1ULL);
v___x_1324_ = lean_usize_add(v_i_1310_, v___x_1323_);
v___x_1325_ = lean_array_uset(v_bs_x27_1322_, v_i_1310_, v_a_1320_);
v_i_1310_ = v___x_1324_;
v_bs_1311_ = v___x_1325_;
goto _start;
}
else
{
lean_object* v_a_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1334_; 
lean_dec_ref(v_bs_1311_);
v_a_1327_ = lean_ctor_get(v___x_1319_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1319_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1329_ = v___x_1319_;
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_a_1327_);
lean_dec(v___x_1319_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1332_; 
if (v_isShared_1330_ == 0)
{
v___x_1332_ = v___x_1329_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v_a_1327_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_openAbstractMVarsResult_spec__0___boxed(lean_object* v_sz_1335_, lean_object* v_i_1336_, lean_object* v_bs_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_){
_start:
{
size_t v_sz_boxed_1343_; size_t v_i_boxed_1344_; lean_object* v_res_1345_; 
v_sz_boxed_1343_ = lean_unbox_usize(v_sz_1335_);
lean_dec(v_sz_1335_);
v_i_boxed_1344_ = lean_unbox_usize(v_i_1336_);
lean_dec(v_i_1336_);
v_res_1345_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_openAbstractMVarsResult_spec__0(v_sz_boxed_1343_, v_i_boxed_1344_, v_bs_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_openAbstractMVarsResult(lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_){
_start:
{
lean_object* v_paramNames_1352_; lean_object* v_expr_1353_; size_t v_sz_1354_; size_t v___x_1355_; lean_object* v___x_1356_; 
v_paramNames_1352_ = lean_ctor_get(v_a_1346_, 0);
v_expr_1353_ = lean_ctor_get(v_a_1346_, 2);
v_sz_1354_ = lean_array_size(v_paramNames_1352_);
v___x_1355_ = ((size_t)0ULL);
lean_inc_ref(v_paramNames_1352_);
v___x_1356_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_openAbstractMVarsResult_spec__0(v_sz_1354_, v___x_1355_, v_paramNames_1352_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_);
if (lean_obj_tag(v___x_1356_) == 0)
{
lean_object* v_a_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
v_a_1357_ = lean_ctor_get(v___x_1356_, 0);
lean_inc(v_a_1357_);
lean_dec_ref_known(v___x_1356_, 1);
lean_inc_ref(v_paramNames_1352_);
v___x_1358_ = l_Lean_Expr_instantiateLevelParamsArray(v_expr_1353_, v_paramNames_1352_, v_a_1357_);
v___x_1359_ = l_Lean_Meta_AbstractMVarsResult_numMVars(v_a_1346_);
lean_dec_ref(v_a_1346_);
v___x_1360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1359_);
v___x_1361_ = l_Lean_Meta_lambdaMetaTelescope(v___x_1358_, v___x_1360_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_);
lean_dec_ref_known(v___x_1360_, 1);
lean_dec_ref(v___x_1358_);
return v___x_1361_;
}
else
{
lean_object* v_a_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1369_; 
lean_dec_ref(v_a_1346_);
v_a_1362_ = lean_ctor_get(v___x_1356_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1364_ = v___x_1356_;
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_a_1362_);
lean_dec(v___x_1356_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1367_; 
if (v_isShared_1365_ == 0)
{
v___x_1367_ = v___x_1364_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_a_1362_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_openAbstractMVarsResult___boxed(lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_){
_start:
{
lean_object* v_res_1376_; 
v_res_1376_ = l_Lean_Meta_openAbstractMVarsResult(v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_);
lean_dec(v_a_1374_);
lean_dec_ref(v_a_1373_);
lean_dec(v_a_1372_);
lean_dec_ref(v_a_1371_);
return v_res_1376_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_AbstractMVars(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_AbstractMVars(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_AbstractMVars(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_AbstractMVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_AbstractMVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_AbstractMVars(builtin);
}
#ifdef __cplusplus
}
#endif
