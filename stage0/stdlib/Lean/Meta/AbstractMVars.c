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
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableLevelMVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l_Lean_instBEqLevelMVarId_beq(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_MetavarContext_getDecl(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
uint8_t l_Lean_Level_hasMVar(lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_mkLevelMax_x27(lean_object*, lean_object*);
lean_object* l_Lean_simpLevelMax_x27(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelIMax_x27(lean_object*, lean_object*);
lean_object* l_Lean_simpLevelIMax_x27(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getLevelDepth(lean_object*, lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "_abstMVar"};
static const lean_object* l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___closed__0 = (const lean_object*)&l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 80, 199, 96, 248, 174, 59, 88)}};
static const lean_object* l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___closed__1 = (const lean_object*)&l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4_spec__5_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__3(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__0 = (const lean_object*)&l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__0_value;
static const lean_ctor_object l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__1 = (const lean_object*)&l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_abstractExprMVars(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4_spec__5_spec__7(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_103_, lean_object* v_x_104_){
_start:
{
if (lean_obj_tag(v_x_104_) == 0)
{
return v_x_103_;
}
else
{
lean_object* v_key_105_; lean_object* v_value_106_; lean_object* v_tail_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_130_; 
v_key_105_ = lean_ctor_get(v_x_104_, 0);
v_value_106_ = lean_ctor_get(v_x_104_, 1);
v_tail_107_ = lean_ctor_get(v_x_104_, 2);
v_isSharedCheck_130_ = !lean_is_exclusive(v_x_104_);
if (v_isSharedCheck_130_ == 0)
{
v___x_109_ = v_x_104_;
v_isShared_110_ = v_isSharedCheck_130_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_tail_107_);
lean_inc(v_value_106_);
lean_inc(v_key_105_);
lean_dec(v_x_104_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_130_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_111_; uint64_t v___x_112_; uint64_t v___x_113_; uint64_t v___x_114_; uint64_t v_fold_115_; uint64_t v___x_116_; uint64_t v___x_117_; uint64_t v___x_118_; size_t v___x_119_; size_t v___x_120_; size_t v___x_121_; size_t v___x_122_; size_t v___x_123_; lean_object* v___x_124_; lean_object* v___x_126_; 
v___x_111_ = lean_array_get_size(v_x_103_);
v___x_112_ = l_Lean_instHashableLevelMVarId_hash(v_key_105_);
v___x_113_ = 32ULL;
v___x_114_ = lean_uint64_shift_right(v___x_112_, v___x_113_);
v_fold_115_ = lean_uint64_xor(v___x_112_, v___x_114_);
v___x_116_ = 16ULL;
v___x_117_ = lean_uint64_shift_right(v_fold_115_, v___x_116_);
v___x_118_ = lean_uint64_xor(v_fold_115_, v___x_117_);
v___x_119_ = lean_uint64_to_usize(v___x_118_);
v___x_120_ = lean_usize_of_nat(v___x_111_);
v___x_121_ = ((size_t)1ULL);
v___x_122_ = lean_usize_sub(v___x_120_, v___x_121_);
v___x_123_ = lean_usize_land(v___x_119_, v___x_122_);
v___x_124_ = lean_array_uget_borrowed(v_x_103_, v___x_123_);
lean_inc(v___x_124_);
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 2, v___x_124_);
v___x_126_ = v___x_109_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v_key_105_);
lean_ctor_set(v_reuseFailAlloc_129_, 1, v_value_106_);
lean_ctor_set(v_reuseFailAlloc_129_, 2, v___x_124_);
v___x_126_ = v_reuseFailAlloc_129_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
lean_object* v___x_127_; 
v___x_127_ = lean_array_uset(v_x_103_, v___x_123_, v___x_126_);
v_x_103_ = v___x_127_;
v_x_104_ = v_tail_107_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3_spec__4___redArg(lean_object* v_i_131_, lean_object* v_source_132_, lean_object* v_target_133_){
_start:
{
lean_object* v___x_134_; uint8_t v___x_135_; 
v___x_134_ = lean_array_get_size(v_source_132_);
v___x_135_ = lean_nat_dec_lt(v_i_131_, v___x_134_);
if (v___x_135_ == 0)
{
lean_dec_ref(v_source_132_);
lean_dec(v_i_131_);
return v_target_133_;
}
else
{
lean_object* v_es_136_; lean_object* v___x_137_; lean_object* v_source_138_; lean_object* v_target_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v_es_136_ = lean_array_fget(v_source_132_, v_i_131_);
v___x_137_ = lean_box(0);
v_source_138_ = lean_array_fset(v_source_132_, v_i_131_, v___x_137_);
v_target_139_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3_spec__4_spec__5___redArg(v_target_133_, v_es_136_);
v___x_140_ = lean_unsigned_to_nat(1u);
v___x_141_ = lean_nat_add(v_i_131_, v___x_140_);
lean_dec(v_i_131_);
v_i_131_ = v___x_141_;
v_source_132_ = v_source_138_;
v_target_133_ = v_target_139_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3___redArg(lean_object* v_data_143_){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v_nbuckets_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_144_ = lean_array_get_size(v_data_143_);
v___x_145_ = lean_unsigned_to_nat(2u);
v_nbuckets_146_ = lean_nat_mul(v___x_144_, v___x_145_);
v___x_147_ = lean_unsigned_to_nat(0u);
v___x_148_ = lean_box(0);
v___x_149_ = lean_mk_array(v_nbuckets_146_, v___x_148_);
v___x_150_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3_spec__4___redArg(v___x_147_, v_data_143_, v___x_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__4___redArg(lean_object* v_a_151_, lean_object* v_b_152_, lean_object* v_x_153_){
_start:
{
if (lean_obj_tag(v_x_153_) == 0)
{
lean_dec(v_b_152_);
lean_dec(v_a_151_);
return v_x_153_;
}
else
{
lean_object* v_key_154_; lean_object* v_value_155_; lean_object* v_tail_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_168_; 
v_key_154_ = lean_ctor_get(v_x_153_, 0);
v_value_155_ = lean_ctor_get(v_x_153_, 1);
v_tail_156_ = lean_ctor_get(v_x_153_, 2);
v_isSharedCheck_168_ = !lean_is_exclusive(v_x_153_);
if (v_isSharedCheck_168_ == 0)
{
v___x_158_ = v_x_153_;
v_isShared_159_ = v_isSharedCheck_168_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_tail_156_);
lean_inc(v_value_155_);
lean_inc(v_key_154_);
lean_dec(v_x_153_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_168_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
uint8_t v___x_160_; 
v___x_160_ = l_Lean_instBEqLevelMVarId_beq(v_key_154_, v_a_151_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; lean_object* v___x_163_; 
v___x_161_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__4___redArg(v_a_151_, v_b_152_, v_tail_156_);
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 2, v___x_161_);
v___x_163_ = v___x_158_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v_key_154_);
lean_ctor_set(v_reuseFailAlloc_164_, 1, v_value_155_);
lean_ctor_set(v_reuseFailAlloc_164_, 2, v___x_161_);
v___x_163_ = v_reuseFailAlloc_164_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
return v___x_163_;
}
}
else
{
lean_object* v___x_166_; 
lean_dec(v_value_155_);
lean_dec(v_key_154_);
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 1, v_b_152_);
lean_ctor_set(v___x_158_, 0, v_a_151_);
v___x_166_ = v___x_158_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v_a_151_);
lean_ctor_set(v_reuseFailAlloc_167_, 1, v_b_152_);
lean_ctor_set(v_reuseFailAlloc_167_, 2, v_tail_156_);
v___x_166_ = v_reuseFailAlloc_167_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
return v___x_166_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2___redArg(lean_object* v_a_169_, lean_object* v_x_170_){
_start:
{
if (lean_obj_tag(v_x_170_) == 0)
{
uint8_t v___x_171_; 
v___x_171_ = 0;
return v___x_171_;
}
else
{
lean_object* v_key_172_; lean_object* v_tail_173_; uint8_t v___x_174_; 
v_key_172_ = lean_ctor_get(v_x_170_, 0);
v_tail_173_ = lean_ctor_get(v_x_170_, 2);
v___x_174_ = l_Lean_instBEqLevelMVarId_beq(v_key_172_, v_a_169_);
if (v___x_174_ == 0)
{
v_x_170_ = v_tail_173_;
goto _start;
}
else
{
return v___x_174_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2___redArg___boxed(lean_object* v_a_176_, lean_object* v_x_177_){
_start:
{
uint8_t v_res_178_; lean_object* v_r_179_; 
v_res_178_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2___redArg(v_a_176_, v_x_177_);
lean_dec(v_x_177_);
lean_dec(v_a_176_);
v_r_179_ = lean_box(v_res_178_);
return v_r_179_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1___redArg(lean_object* v_m_180_, lean_object* v_a_181_, lean_object* v_b_182_){
_start:
{
lean_object* v_size_183_; lean_object* v_buckets_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_227_; 
v_size_183_ = lean_ctor_get(v_m_180_, 0);
v_buckets_184_ = lean_ctor_get(v_m_180_, 1);
v_isSharedCheck_227_ = !lean_is_exclusive(v_m_180_);
if (v_isSharedCheck_227_ == 0)
{
v___x_186_ = v_m_180_;
v_isShared_187_ = v_isSharedCheck_227_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_buckets_184_);
lean_inc(v_size_183_);
lean_dec(v_m_180_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_227_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_188_; uint64_t v___x_189_; uint64_t v___x_190_; uint64_t v___x_191_; uint64_t v_fold_192_; uint64_t v___x_193_; uint64_t v___x_194_; uint64_t v___x_195_; size_t v___x_196_; size_t v___x_197_; size_t v___x_198_; size_t v___x_199_; size_t v___x_200_; lean_object* v_bkt_201_; uint8_t v___x_202_; 
v___x_188_ = lean_array_get_size(v_buckets_184_);
v___x_189_ = l_Lean_instHashableLevelMVarId_hash(v_a_181_);
v___x_190_ = 32ULL;
v___x_191_ = lean_uint64_shift_right(v___x_189_, v___x_190_);
v_fold_192_ = lean_uint64_xor(v___x_189_, v___x_191_);
v___x_193_ = 16ULL;
v___x_194_ = lean_uint64_shift_right(v_fold_192_, v___x_193_);
v___x_195_ = lean_uint64_xor(v_fold_192_, v___x_194_);
v___x_196_ = lean_uint64_to_usize(v___x_195_);
v___x_197_ = lean_usize_of_nat(v___x_188_);
v___x_198_ = ((size_t)1ULL);
v___x_199_ = lean_usize_sub(v___x_197_, v___x_198_);
v___x_200_ = lean_usize_land(v___x_196_, v___x_199_);
v_bkt_201_ = lean_array_uget_borrowed(v_buckets_184_, v___x_200_);
v___x_202_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2___redArg(v_a_181_, v_bkt_201_);
if (v___x_202_ == 0)
{
lean_object* v___x_203_; lean_object* v_size_x27_204_; lean_object* v___x_205_; lean_object* v_buckets_x27_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; uint8_t v___x_212_; 
v___x_203_ = lean_unsigned_to_nat(1u);
v_size_x27_204_ = lean_nat_add(v_size_183_, v___x_203_);
lean_dec(v_size_183_);
lean_inc(v_bkt_201_);
v___x_205_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_205_, 0, v_a_181_);
lean_ctor_set(v___x_205_, 1, v_b_182_);
lean_ctor_set(v___x_205_, 2, v_bkt_201_);
v_buckets_x27_206_ = lean_array_uset(v_buckets_184_, v___x_200_, v___x_205_);
v___x_207_ = lean_unsigned_to_nat(4u);
v___x_208_ = lean_nat_mul(v_size_x27_204_, v___x_207_);
v___x_209_ = lean_unsigned_to_nat(3u);
v___x_210_ = lean_nat_div(v___x_208_, v___x_209_);
lean_dec(v___x_208_);
v___x_211_ = lean_array_get_size(v_buckets_x27_206_);
v___x_212_ = lean_nat_dec_le(v___x_210_, v___x_211_);
lean_dec(v___x_210_);
if (v___x_212_ == 0)
{
lean_object* v_val_213_; lean_object* v___x_215_; 
v_val_213_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3___redArg(v_buckets_x27_206_);
if (v_isShared_187_ == 0)
{
lean_ctor_set(v___x_186_, 1, v_val_213_);
lean_ctor_set(v___x_186_, 0, v_size_x27_204_);
v___x_215_ = v___x_186_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v_size_x27_204_);
lean_ctor_set(v_reuseFailAlloc_216_, 1, v_val_213_);
v___x_215_ = v_reuseFailAlloc_216_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
return v___x_215_;
}
}
else
{
lean_object* v___x_218_; 
if (v_isShared_187_ == 0)
{
lean_ctor_set(v___x_186_, 1, v_buckets_x27_206_);
lean_ctor_set(v___x_186_, 0, v_size_x27_204_);
v___x_218_ = v___x_186_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v_size_x27_204_);
lean_ctor_set(v_reuseFailAlloc_219_, 1, v_buckets_x27_206_);
v___x_218_ = v_reuseFailAlloc_219_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
return v___x_218_;
}
}
}
else
{
lean_object* v___x_220_; lean_object* v_buckets_x27_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_225_; 
lean_inc(v_bkt_201_);
v___x_220_ = lean_box(0);
v_buckets_x27_221_ = lean_array_uset(v_buckets_184_, v___x_200_, v___x_220_);
v___x_222_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__4___redArg(v_a_181_, v_b_182_, v_bkt_201_);
v___x_223_ = lean_array_uset(v_buckets_x27_221_, v___x_200_, v___x_222_);
if (v_isShared_187_ == 0)
{
lean_ctor_set(v___x_186_, 1, v___x_223_);
v___x_225_ = v___x_186_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v_size_183_);
lean_ctor_set(v_reuseFailAlloc_226_, 1, v___x_223_);
v___x_225_ = v_reuseFailAlloc_226_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
return v___x_225_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0___redArg(lean_object* v_a_228_, lean_object* v_x_229_){
_start:
{
if (lean_obj_tag(v_x_229_) == 0)
{
lean_object* v___x_230_; 
v___x_230_ = lean_box(0);
return v___x_230_;
}
else
{
lean_object* v_key_231_; lean_object* v_value_232_; lean_object* v_tail_233_; uint8_t v___x_234_; 
v_key_231_ = lean_ctor_get(v_x_229_, 0);
v_value_232_ = lean_ctor_get(v_x_229_, 1);
v_tail_233_ = lean_ctor_get(v_x_229_, 2);
v___x_234_ = l_Lean_instBEqLevelMVarId_beq(v_key_231_, v_a_228_);
if (v___x_234_ == 0)
{
v_x_229_ = v_tail_233_;
goto _start;
}
else
{
lean_object* v___x_236_; 
lean_inc(v_value_232_);
v___x_236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_236_, 0, v_value_232_);
return v___x_236_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0___redArg___boxed(lean_object* v_a_237_, lean_object* v_x_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0___redArg(v_a_237_, v_x_238_);
lean_dec(v_x_238_);
lean_dec(v_a_237_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___redArg(lean_object* v_m_240_, lean_object* v_a_241_){
_start:
{
lean_object* v_buckets_242_; lean_object* v___x_243_; uint64_t v___x_244_; uint64_t v___x_245_; uint64_t v___x_246_; uint64_t v_fold_247_; uint64_t v___x_248_; uint64_t v___x_249_; uint64_t v___x_250_; size_t v___x_251_; size_t v___x_252_; size_t v___x_253_; size_t v___x_254_; size_t v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v_buckets_242_ = lean_ctor_get(v_m_240_, 1);
v___x_243_ = lean_array_get_size(v_buckets_242_);
v___x_244_ = l_Lean_instHashableLevelMVarId_hash(v_a_241_);
v___x_245_ = 32ULL;
v___x_246_ = lean_uint64_shift_right(v___x_244_, v___x_245_);
v_fold_247_ = lean_uint64_xor(v___x_244_, v___x_246_);
v___x_248_ = 16ULL;
v___x_249_ = lean_uint64_shift_right(v_fold_247_, v___x_248_);
v___x_250_ = lean_uint64_xor(v_fold_247_, v___x_249_);
v___x_251_ = lean_uint64_to_usize(v___x_250_);
v___x_252_ = lean_usize_of_nat(v___x_243_);
v___x_253_ = ((size_t)1ULL);
v___x_254_ = lean_usize_sub(v___x_252_, v___x_253_);
v___x_255_ = lean_usize_land(v___x_251_, v___x_254_);
v___x_256_ = lean_array_uget_borrowed(v_buckets_242_, v___x_255_);
v___x_257_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0___redArg(v_a_241_, v___x_256_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___redArg___boxed(lean_object* v_m_258_, lean_object* v_a_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___redArg(v_m_258_, v_a_259_);
lean_dec(v_a_259_);
lean_dec_ref(v_m_258_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(lean_object* v_u_264_, lean_object* v_a_265_){
_start:
{
uint8_t v_abstractLevels_266_; 
v_abstractLevels_266_ = lean_ctor_get_uint8(v_a_265_, sizeof(void*)*9);
if (v_abstractLevels_266_ == 0)
{
lean_object* v___x_267_; 
v___x_267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_267_, 0, v_u_264_);
lean_ctor_set(v___x_267_, 1, v_a_265_);
return v___x_267_;
}
else
{
lean_object* v_ngen_268_; lean_object* v_lctx_269_; lean_object* v_mctx_270_; lean_object* v_nextParamIdx_271_; lean_object* v_paramNames_272_; lean_object* v_fvars_273_; lean_object* v_mvars_274_; lean_object* v_lmap_275_; lean_object* v_emap_276_; uint8_t v___x_277_; 
v_ngen_268_ = lean_ctor_get(v_a_265_, 0);
v_lctx_269_ = lean_ctor_get(v_a_265_, 1);
v_mctx_270_ = lean_ctor_get(v_a_265_, 2);
v_nextParamIdx_271_ = lean_ctor_get(v_a_265_, 3);
v_paramNames_272_ = lean_ctor_get(v_a_265_, 4);
v_fvars_273_ = lean_ctor_get(v_a_265_, 5);
v_mvars_274_ = lean_ctor_get(v_a_265_, 6);
v_lmap_275_ = lean_ctor_get(v_a_265_, 7);
v_emap_276_ = lean_ctor_get(v_a_265_, 8);
v___x_277_ = l_Lean_Level_hasMVar(v_u_264_);
if (v___x_277_ == 0)
{
lean_object* v___x_278_; 
v___x_278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_278_, 0, v_u_264_);
lean_ctor_set(v___x_278_, 1, v_a_265_);
return v___x_278_;
}
else
{
switch(lean_obj_tag(v_u_264_))
{
case 1:
{
lean_object* v_a_279_; lean_object* v___x_280_; lean_object* v_fst_281_; lean_object* v_snd_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_296_; 
v_a_279_ = lean_ctor_get(v_u_264_, 0);
lean_inc(v_a_279_);
v___x_280_ = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(v_a_279_, v_a_265_);
v_fst_281_ = lean_ctor_get(v___x_280_, 0);
v_snd_282_ = lean_ctor_get(v___x_280_, 1);
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_280_);
if (v_isSharedCheck_296_ == 0)
{
v___x_284_ = v___x_280_;
v_isShared_285_ = v_isSharedCheck_296_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_snd_282_);
lean_inc(v_fst_281_);
lean_dec(v___x_280_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_296_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
size_t v___x_286_; size_t v___x_287_; uint8_t v___x_288_; 
v___x_286_ = lean_ptr_addr(v_a_279_);
v___x_287_ = lean_ptr_addr(v_fst_281_);
v___x_288_ = lean_usize_dec_eq(v___x_286_, v___x_287_);
if (v___x_288_ == 0)
{
lean_object* v___x_289_; lean_object* v___x_291_; 
lean_dec_ref_known(v_u_264_, 1);
v___x_289_ = l_Lean_Level_succ___override(v_fst_281_);
if (v_isShared_285_ == 0)
{
lean_ctor_set(v___x_284_, 0, v___x_289_);
v___x_291_ = v___x_284_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v___x_289_);
lean_ctor_set(v_reuseFailAlloc_292_, 1, v_snd_282_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
else
{
lean_object* v___x_294_; 
lean_dec(v_fst_281_);
if (v_isShared_285_ == 0)
{
lean_ctor_set(v___x_284_, 0, v_u_264_);
v___x_294_ = v___x_284_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_u_264_);
lean_ctor_set(v_reuseFailAlloc_295_, 1, v_snd_282_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
}
}
case 2:
{
lean_object* v_a_297_; lean_object* v_a_298_; lean_object* v___x_299_; lean_object* v_fst_300_; lean_object* v_snd_301_; lean_object* v___x_302_; lean_object* v_fst_303_; lean_object* v_snd_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_326_; 
v_a_297_ = lean_ctor_get(v_u_264_, 0);
v_a_298_ = lean_ctor_get(v_u_264_, 1);
lean_inc(v_a_297_);
v___x_299_ = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(v_a_297_, v_a_265_);
v_fst_300_ = lean_ctor_get(v___x_299_, 0);
lean_inc(v_fst_300_);
v_snd_301_ = lean_ctor_get(v___x_299_, 1);
lean_inc(v_snd_301_);
lean_dec_ref(v___x_299_);
lean_inc(v_a_298_);
v___x_302_ = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(v_a_298_, v_snd_301_);
v_fst_303_ = lean_ctor_get(v___x_302_, 0);
v_snd_304_ = lean_ctor_get(v___x_302_, 1);
v_isSharedCheck_326_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_326_ == 0)
{
v___x_306_ = v___x_302_;
v_isShared_307_ = v_isSharedCheck_326_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_snd_304_);
lean_inc(v_fst_303_);
lean_dec(v___x_302_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_326_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
size_t v___x_308_; size_t v___x_309_; uint8_t v___x_310_; 
v___x_308_ = lean_ptr_addr(v_a_297_);
v___x_309_ = lean_ptr_addr(v_fst_300_);
v___x_310_ = lean_usize_dec_eq(v___x_308_, v___x_309_);
if (v___x_310_ == 0)
{
lean_object* v___x_311_; lean_object* v___x_313_; 
lean_dec_ref_known(v_u_264_, 2);
v___x_311_ = l_Lean_mkLevelMax_x27(v_fst_300_, v_fst_303_);
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 0, v___x_311_);
v___x_313_ = v___x_306_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v___x_311_);
lean_ctor_set(v_reuseFailAlloc_314_, 1, v_snd_304_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
else
{
size_t v___x_315_; size_t v___x_316_; uint8_t v___x_317_; 
v___x_315_ = lean_ptr_addr(v_a_298_);
v___x_316_ = lean_ptr_addr(v_fst_303_);
v___x_317_ = lean_usize_dec_eq(v___x_315_, v___x_316_);
if (v___x_317_ == 0)
{
lean_object* v___x_318_; lean_object* v___x_320_; 
lean_dec_ref_known(v_u_264_, 2);
v___x_318_ = l_Lean_mkLevelMax_x27(v_fst_300_, v_fst_303_);
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 0, v___x_318_);
v___x_320_ = v___x_306_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v___x_318_);
lean_ctor_set(v_reuseFailAlloc_321_, 1, v_snd_304_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
return v___x_320_;
}
}
else
{
lean_object* v___x_322_; lean_object* v___x_324_; 
v___x_322_ = l_Lean_simpLevelMax_x27(v_fst_300_, v_fst_303_, v_u_264_);
lean_dec_ref_known(v_u_264_, 2);
lean_dec(v_fst_303_);
lean_dec(v_fst_300_);
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 0, v___x_322_);
v___x_324_ = v___x_306_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v___x_322_);
lean_ctor_set(v_reuseFailAlloc_325_, 1, v_snd_304_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
}
}
case 3:
{
lean_object* v_a_327_; lean_object* v_a_328_; lean_object* v___x_329_; lean_object* v_fst_330_; lean_object* v_snd_331_; lean_object* v___x_332_; lean_object* v_fst_333_; lean_object* v_snd_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_356_; 
v_a_327_ = lean_ctor_get(v_u_264_, 0);
v_a_328_ = lean_ctor_get(v_u_264_, 1);
lean_inc(v_a_327_);
v___x_329_ = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(v_a_327_, v_a_265_);
v_fst_330_ = lean_ctor_get(v___x_329_, 0);
lean_inc(v_fst_330_);
v_snd_331_ = lean_ctor_get(v___x_329_, 1);
lean_inc(v_snd_331_);
lean_dec_ref(v___x_329_);
lean_inc(v_a_328_);
v___x_332_ = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(v_a_328_, v_snd_331_);
v_fst_333_ = lean_ctor_get(v___x_332_, 0);
v_snd_334_ = lean_ctor_get(v___x_332_, 1);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_332_);
if (v_isSharedCheck_356_ == 0)
{
v___x_336_ = v___x_332_;
v_isShared_337_ = v_isSharedCheck_356_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_snd_334_);
lean_inc(v_fst_333_);
lean_dec(v___x_332_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_356_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
size_t v___x_338_; size_t v___x_339_; uint8_t v___x_340_; 
v___x_338_ = lean_ptr_addr(v_a_327_);
v___x_339_ = lean_ptr_addr(v_fst_330_);
v___x_340_ = lean_usize_dec_eq(v___x_338_, v___x_339_);
if (v___x_340_ == 0)
{
lean_object* v___x_341_; lean_object* v___x_343_; 
lean_dec_ref_known(v_u_264_, 2);
v___x_341_ = l_Lean_mkLevelIMax_x27(v_fst_330_, v_fst_333_);
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 0, v___x_341_);
v___x_343_ = v___x_336_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v___x_341_);
lean_ctor_set(v_reuseFailAlloc_344_, 1, v_snd_334_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
else
{
size_t v___x_345_; size_t v___x_346_; uint8_t v___x_347_; 
v___x_345_ = lean_ptr_addr(v_a_328_);
v___x_346_ = lean_ptr_addr(v_fst_333_);
v___x_347_ = lean_usize_dec_eq(v___x_345_, v___x_346_);
if (v___x_347_ == 0)
{
lean_object* v___x_348_; lean_object* v___x_350_; 
lean_dec_ref_known(v_u_264_, 2);
v___x_348_ = l_Lean_mkLevelIMax_x27(v_fst_330_, v_fst_333_);
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 0, v___x_348_);
v___x_350_ = v___x_336_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v___x_348_);
lean_ctor_set(v_reuseFailAlloc_351_, 1, v_snd_334_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
else
{
lean_object* v___x_352_; lean_object* v___x_354_; 
v___x_352_ = l_Lean_simpLevelIMax_x27(v_fst_330_, v_fst_333_, v_u_264_);
lean_dec_ref_known(v_u_264_, 2);
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 0, v___x_352_);
v___x_354_ = v___x_336_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v___x_352_);
lean_ctor_set(v_reuseFailAlloc_355_, 1, v_snd_334_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
}
}
}
case 5:
{
lean_object* v_a_357_; lean_object* v_depth_358_; lean_object* v___x_359_; uint8_t v___x_360_; 
v_a_357_ = lean_ctor_get(v_u_264_, 0);
v_depth_358_ = lean_ctor_get(v_mctx_270_, 0);
lean_inc(v_a_357_);
v___x_359_ = l_Lean_MetavarContext_getLevelDepth(v_mctx_270_, v_a_357_);
v___x_360_ = lean_nat_dec_eq(v___x_359_, v_depth_358_);
lean_dec(v___x_359_);
if (v___x_360_ == 0)
{
lean_object* v___x_361_; 
v___x_361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_361_, 0, v_u_264_);
lean_ctor_set(v___x_361_, 1, v_a_265_);
return v___x_361_;
}
else
{
lean_object* v___x_362_; 
lean_inc(v_a_357_);
lean_dec_ref_known(v_u_264_, 1);
v___x_362_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___redArg(v_lmap_275_, v_a_357_);
if (lean_obj_tag(v___x_362_) == 0)
{
lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_377_; 
lean_inc_ref(v_emap_276_);
lean_inc_ref(v_lmap_275_);
lean_inc_ref(v_mvars_274_);
lean_inc_ref(v_fvars_273_);
lean_inc_ref(v_paramNames_272_);
lean_inc(v_nextParamIdx_271_);
lean_inc_ref(v_mctx_270_);
lean_inc_ref(v_lctx_269_);
lean_inc_ref(v_ngen_268_);
v_isSharedCheck_377_ = !lean_is_exclusive(v_a_265_);
if (v_isSharedCheck_377_ == 0)
{
lean_object* v_unused_378_; lean_object* v_unused_379_; lean_object* v_unused_380_; lean_object* v_unused_381_; lean_object* v_unused_382_; lean_object* v_unused_383_; lean_object* v_unused_384_; lean_object* v_unused_385_; lean_object* v_unused_386_; 
v_unused_378_ = lean_ctor_get(v_a_265_, 8);
lean_dec(v_unused_378_);
v_unused_379_ = lean_ctor_get(v_a_265_, 7);
lean_dec(v_unused_379_);
v_unused_380_ = lean_ctor_get(v_a_265_, 6);
lean_dec(v_unused_380_);
v_unused_381_ = lean_ctor_get(v_a_265_, 5);
lean_dec(v_unused_381_);
v_unused_382_ = lean_ctor_get(v_a_265_, 4);
lean_dec(v_unused_382_);
v_unused_383_ = lean_ctor_get(v_a_265_, 3);
lean_dec(v_unused_383_);
v_unused_384_ = lean_ctor_get(v_a_265_, 2);
lean_dec(v_unused_384_);
v_unused_385_ = lean_ctor_get(v_a_265_, 1);
lean_dec(v_unused_385_);
v_unused_386_ = lean_ctor_get(v_a_265_, 0);
lean_dec(v_unused_386_);
v___x_364_ = v_a_265_;
v_isShared_365_ = v_isSharedCheck_377_;
goto v_resetjp_363_;
}
else
{
lean_dec(v_a_265_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_377_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_374_; 
v___x_366_ = ((lean_object*)(l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___closed__1));
lean_inc(v_nextParamIdx_271_);
v___x_367_ = l_Lean_Name_num___override(v___x_366_, v_nextParamIdx_271_);
lean_inc(v___x_367_);
v___x_368_ = l_Lean_mkLevelParam(v___x_367_);
v___x_369_ = lean_unsigned_to_nat(1u);
v___x_370_ = lean_nat_add(v_nextParamIdx_271_, v___x_369_);
lean_dec(v_nextParamIdx_271_);
v___x_371_ = lean_array_push(v_paramNames_272_, v___x_367_);
lean_inc(v___x_368_);
v___x_372_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1___redArg(v_lmap_275_, v_a_357_, v___x_368_);
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 7, v___x_372_);
lean_ctor_set(v___x_364_, 4, v___x_371_);
lean_ctor_set(v___x_364_, 3, v___x_370_);
v___x_374_ = v___x_364_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_ngen_268_);
lean_ctor_set(v_reuseFailAlloc_376_, 1, v_lctx_269_);
lean_ctor_set(v_reuseFailAlloc_376_, 2, v_mctx_270_);
lean_ctor_set(v_reuseFailAlloc_376_, 3, v___x_370_);
lean_ctor_set(v_reuseFailAlloc_376_, 4, v___x_371_);
lean_ctor_set(v_reuseFailAlloc_376_, 5, v_fvars_273_);
lean_ctor_set(v_reuseFailAlloc_376_, 6, v_mvars_274_);
lean_ctor_set(v_reuseFailAlloc_376_, 7, v___x_372_);
lean_ctor_set(v_reuseFailAlloc_376_, 8, v_emap_276_);
lean_ctor_set_uint8(v_reuseFailAlloc_376_, sizeof(void*)*9, v_abstractLevels_266_);
v___x_374_ = v_reuseFailAlloc_376_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
lean_object* v___x_375_; 
v___x_375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_375_, 0, v___x_368_);
lean_ctor_set(v___x_375_, 1, v___x_374_);
return v___x_375_;
}
}
}
else
{
lean_object* v_val_387_; lean_object* v___x_388_; 
lean_dec(v_a_357_);
v_val_387_ = lean_ctor_get(v___x_362_, 0);
lean_inc(v_val_387_);
lean_dec_ref_known(v___x_362_, 1);
v___x_388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_388_, 0, v_val_387_);
lean_ctor_set(v___x_388_, 1, v_a_265_);
return v___x_388_;
}
}
}
default: 
{
lean_object* v___x_389_; 
v___x_389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_389_, 0, v_u_264_);
lean_ctor_set(v___x_389_, 1, v_a_265_);
return v___x_389_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0(lean_object* v_00_u03b2_390_, lean_object* v_m_391_, lean_object* v_a_392_){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___redArg(v_m_391_, v_a_392_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___boxed(lean_object* v_00_u03b2_394_, lean_object* v_m_395_, lean_object* v_a_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0(v_00_u03b2_394_, v_m_395_, v_a_396_);
lean_dec(v_a_396_);
lean_dec_ref(v_m_395_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1(lean_object* v_00_u03b2_398_, lean_object* v_m_399_, lean_object* v_a_400_, lean_object* v_b_401_){
_start:
{
lean_object* v___x_402_; 
v___x_402_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1___redArg(v_m_399_, v_a_400_, v_b_401_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0(lean_object* v_00_u03b2_403_, lean_object* v_a_404_, lean_object* v_x_405_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0___redArg(v_a_404_, v_x_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0___boxed(lean_object* v_00_u03b2_407_, lean_object* v_a_408_, lean_object* v_x_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0(v_00_u03b2_407_, v_a_408_, v_x_409_);
lean_dec(v_x_409_);
lean_dec(v_a_408_);
return v_res_410_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2(lean_object* v_00_u03b2_411_, lean_object* v_a_412_, lean_object* v_x_413_){
_start:
{
uint8_t v___x_414_; 
v___x_414_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2___redArg(v_a_412_, v_x_413_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2___boxed(lean_object* v_00_u03b2_415_, lean_object* v_a_416_, lean_object* v_x_417_){
_start:
{
uint8_t v_res_418_; lean_object* v_r_419_; 
v_res_418_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2(v_00_u03b2_415_, v_a_416_, v_x_417_);
lean_dec(v_x_417_);
lean_dec(v_a_416_);
v_r_419_ = lean_box(v_res_418_);
return v_r_419_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3(lean_object* v_00_u03b2_420_, lean_object* v_data_421_){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3___redArg(v_data_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__4(lean_object* v_00_u03b2_423_, lean_object* v_a_424_, lean_object* v_b_425_, lean_object* v_x_426_){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__4___redArg(v_a_424_, v_b_425_, v_x_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_428_, lean_object* v_i_429_, lean_object* v_source_430_, lean_object* v_target_431_){
_start:
{
lean_object* v___x_432_; 
v___x_432_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3_spec__4___redArg(v_i_429_, v_source_430_, v_target_431_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_433_, lean_object* v_x_434_, lean_object* v_x_435_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3_spec__4_spec__5___redArg(v_x_434_, v_x_435_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__1(lean_object* v_e_437_, lean_object* v___y_438_){
_start:
{
uint8_t v___x_439_; 
v___x_439_ = l_Lean_Expr_hasMVar(v_e_437_);
if (v___x_439_ == 0)
{
lean_object* v___x_440_; 
v___x_440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_440_, 0, v_e_437_);
lean_ctor_set(v___x_440_, 1, v___y_438_);
return v___x_440_;
}
else
{
lean_object* v_ngen_441_; lean_object* v_lctx_442_; lean_object* v_mctx_443_; lean_object* v_nextParamIdx_444_; lean_object* v_paramNames_445_; lean_object* v_fvars_446_; lean_object* v_mvars_447_; lean_object* v_lmap_448_; lean_object* v_emap_449_; uint8_t v_abstractLevels_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_467_; 
v_ngen_441_ = lean_ctor_get(v___y_438_, 0);
v_lctx_442_ = lean_ctor_get(v___y_438_, 1);
v_mctx_443_ = lean_ctor_get(v___y_438_, 2);
v_nextParamIdx_444_ = lean_ctor_get(v___y_438_, 3);
v_paramNames_445_ = lean_ctor_get(v___y_438_, 4);
v_fvars_446_ = lean_ctor_get(v___y_438_, 5);
v_mvars_447_ = lean_ctor_get(v___y_438_, 6);
v_lmap_448_ = lean_ctor_get(v___y_438_, 7);
v_emap_449_ = lean_ctor_get(v___y_438_, 8);
v_abstractLevels_450_ = lean_ctor_get_uint8(v___y_438_, sizeof(void*)*9);
v_isSharedCheck_467_ = !lean_is_exclusive(v___y_438_);
if (v_isSharedCheck_467_ == 0)
{
v___x_452_ = v___y_438_;
v_isShared_453_ = v_isSharedCheck_467_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_emap_449_);
lean_inc(v_lmap_448_);
lean_inc(v_mvars_447_);
lean_inc(v_fvars_446_);
lean_inc(v_paramNames_445_);
lean_inc(v_nextParamIdx_444_);
lean_inc(v_mctx_443_);
lean_inc(v_lctx_442_);
lean_inc(v_ngen_441_);
lean_dec(v___y_438_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_467_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_454_; lean_object* v_fst_455_; lean_object* v_snd_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_466_; 
v___x_454_ = l_Lean_instantiateMVarsCore(v_mctx_443_, v_e_437_);
v_fst_455_ = lean_ctor_get(v___x_454_, 0);
v_snd_456_ = lean_ctor_get(v___x_454_, 1);
v_isSharedCheck_466_ = !lean_is_exclusive(v___x_454_);
if (v_isSharedCheck_466_ == 0)
{
v___x_458_ = v___x_454_;
v_isShared_459_ = v_isSharedCheck_466_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_snd_456_);
lean_inc(v_fst_455_);
lean_dec(v___x_454_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_466_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_461_; 
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 2, v_snd_456_);
v___x_461_ = v___x_452_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_ngen_441_);
lean_ctor_set(v_reuseFailAlloc_465_, 1, v_lctx_442_);
lean_ctor_set(v_reuseFailAlloc_465_, 2, v_snd_456_);
lean_ctor_set(v_reuseFailAlloc_465_, 3, v_nextParamIdx_444_);
lean_ctor_set(v_reuseFailAlloc_465_, 4, v_paramNames_445_);
lean_ctor_set(v_reuseFailAlloc_465_, 5, v_fvars_446_);
lean_ctor_set(v_reuseFailAlloc_465_, 6, v_mvars_447_);
lean_ctor_set(v_reuseFailAlloc_465_, 7, v_lmap_448_);
lean_ctor_set(v_reuseFailAlloc_465_, 8, v_emap_449_);
lean_ctor_set_uint8(v_reuseFailAlloc_465_, sizeof(void*)*9, v_abstractLevels_450_);
v___x_461_ = v_reuseFailAlloc_465_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
lean_object* v___x_463_; 
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 1, v___x_461_);
v___x_463_ = v___x_458_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_fst_455_);
lean_ctor_set(v_reuseFailAlloc_464_, 1, v___x_461_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0___redArg(lean_object* v_a_468_, lean_object* v_x_469_){
_start:
{
if (lean_obj_tag(v_x_469_) == 0)
{
lean_object* v___x_470_; 
v___x_470_ = lean_box(0);
return v___x_470_;
}
else
{
lean_object* v_key_471_; lean_object* v_value_472_; lean_object* v_tail_473_; uint8_t v___x_474_; 
v_key_471_ = lean_ctor_get(v_x_469_, 0);
v_value_472_ = lean_ctor_get(v_x_469_, 1);
v_tail_473_ = lean_ctor_get(v_x_469_, 2);
v___x_474_ = l_Lean_instBEqMVarId_beq(v_key_471_, v_a_468_);
if (v___x_474_ == 0)
{
v_x_469_ = v_tail_473_;
goto _start;
}
else
{
lean_object* v___x_476_; 
lean_inc(v_value_472_);
v___x_476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_476_, 0, v_value_472_);
return v___x_476_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0___redArg___boxed(lean_object* v_a_477_, lean_object* v_x_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0___redArg(v_a_477_, v_x_478_);
lean_dec(v_x_478_);
lean_dec(v_a_477_);
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0___redArg(lean_object* v_m_480_, lean_object* v_a_481_){
_start:
{
lean_object* v_buckets_482_; lean_object* v___x_483_; uint64_t v___x_484_; uint64_t v___x_485_; uint64_t v___x_486_; uint64_t v_fold_487_; uint64_t v___x_488_; uint64_t v___x_489_; uint64_t v___x_490_; size_t v___x_491_; size_t v___x_492_; size_t v___x_493_; size_t v___x_494_; size_t v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v_buckets_482_ = lean_ctor_get(v_m_480_, 1);
v___x_483_ = lean_array_get_size(v_buckets_482_);
v___x_484_ = l_Lean_instHashableMVarId_hash(v_a_481_);
v___x_485_ = 32ULL;
v___x_486_ = lean_uint64_shift_right(v___x_484_, v___x_485_);
v_fold_487_ = lean_uint64_xor(v___x_484_, v___x_486_);
v___x_488_ = 16ULL;
v___x_489_ = lean_uint64_shift_right(v_fold_487_, v___x_488_);
v___x_490_ = lean_uint64_xor(v_fold_487_, v___x_489_);
v___x_491_ = lean_uint64_to_usize(v___x_490_);
v___x_492_ = lean_usize_of_nat(v___x_483_);
v___x_493_ = ((size_t)1ULL);
v___x_494_ = lean_usize_sub(v___x_492_, v___x_493_);
v___x_495_ = lean_usize_land(v___x_491_, v___x_494_);
v___x_496_ = lean_array_uget_borrowed(v_buckets_482_, v___x_495_);
v___x_497_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0___redArg(v_a_481_, v___x_496_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0___redArg___boxed(lean_object* v_m_498_, lean_object* v_a_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0___redArg(v_m_498_, v_a_499_);
lean_dec(v_a_499_);
lean_dec_ref(v_m_498_);
return v_res_500_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3___redArg(lean_object* v_a_501_, lean_object* v_x_502_){
_start:
{
if (lean_obj_tag(v_x_502_) == 0)
{
uint8_t v___x_503_; 
v___x_503_ = 0;
return v___x_503_;
}
else
{
lean_object* v_key_504_; lean_object* v_tail_505_; uint8_t v___x_506_; 
v_key_504_ = lean_ctor_get(v_x_502_, 0);
v_tail_505_ = lean_ctor_get(v_x_502_, 2);
v___x_506_ = l_Lean_instBEqMVarId_beq(v_key_504_, v_a_501_);
if (v___x_506_ == 0)
{
v_x_502_ = v_tail_505_;
goto _start;
}
else
{
return v___x_506_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3___redArg___boxed(lean_object* v_a_508_, lean_object* v_x_509_){
_start:
{
uint8_t v_res_510_; lean_object* v_r_511_; 
v_res_510_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3___redArg(v_a_508_, v_x_509_);
lean_dec(v_x_509_);
lean_dec(v_a_508_);
v_r_511_ = lean_box(v_res_510_);
return v_r_511_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__5___redArg(lean_object* v_a_512_, lean_object* v_b_513_, lean_object* v_x_514_){
_start:
{
if (lean_obj_tag(v_x_514_) == 0)
{
lean_dec(v_b_513_);
lean_dec(v_a_512_);
return v_x_514_;
}
else
{
lean_object* v_key_515_; lean_object* v_value_516_; lean_object* v_tail_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_529_; 
v_key_515_ = lean_ctor_get(v_x_514_, 0);
v_value_516_ = lean_ctor_get(v_x_514_, 1);
v_tail_517_ = lean_ctor_get(v_x_514_, 2);
v_isSharedCheck_529_ = !lean_is_exclusive(v_x_514_);
if (v_isSharedCheck_529_ == 0)
{
v___x_519_ = v_x_514_;
v_isShared_520_ = v_isSharedCheck_529_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_tail_517_);
lean_inc(v_value_516_);
lean_inc(v_key_515_);
lean_dec(v_x_514_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_529_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
uint8_t v___x_521_; 
v___x_521_ = l_Lean_instBEqMVarId_beq(v_key_515_, v_a_512_);
if (v___x_521_ == 0)
{
lean_object* v___x_522_; lean_object* v___x_524_; 
v___x_522_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__5___redArg(v_a_512_, v_b_513_, v_tail_517_);
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 2, v___x_522_);
v___x_524_ = v___x_519_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v_key_515_);
lean_ctor_set(v_reuseFailAlloc_525_, 1, v_value_516_);
lean_ctor_set(v_reuseFailAlloc_525_, 2, v___x_522_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
else
{
lean_object* v___x_527_; 
lean_dec(v_value_516_);
lean_dec(v_key_515_);
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 1, v_b_513_);
lean_ctor_set(v___x_519_, 0, v_a_512_);
v___x_527_ = v___x_519_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_a_512_);
lean_ctor_set(v_reuseFailAlloc_528_, 1, v_b_513_);
lean_ctor_set(v_reuseFailAlloc_528_, 2, v_tail_517_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4_spec__5_spec__7___redArg(lean_object* v_x_530_, lean_object* v_x_531_){
_start:
{
if (lean_obj_tag(v_x_531_) == 0)
{
return v_x_530_;
}
else
{
lean_object* v_key_532_; lean_object* v_value_533_; lean_object* v_tail_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_557_; 
v_key_532_ = lean_ctor_get(v_x_531_, 0);
v_value_533_ = lean_ctor_get(v_x_531_, 1);
v_tail_534_ = lean_ctor_get(v_x_531_, 2);
v_isSharedCheck_557_ = !lean_is_exclusive(v_x_531_);
if (v_isSharedCheck_557_ == 0)
{
v___x_536_ = v_x_531_;
v_isShared_537_ = v_isSharedCheck_557_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_tail_534_);
lean_inc(v_value_533_);
lean_inc(v_key_532_);
lean_dec(v_x_531_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_557_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_538_; uint64_t v___x_539_; uint64_t v___x_540_; uint64_t v___x_541_; uint64_t v_fold_542_; uint64_t v___x_543_; uint64_t v___x_544_; uint64_t v___x_545_; size_t v___x_546_; size_t v___x_547_; size_t v___x_548_; size_t v___x_549_; size_t v___x_550_; lean_object* v___x_551_; lean_object* v___x_553_; 
v___x_538_ = lean_array_get_size(v_x_530_);
v___x_539_ = l_Lean_instHashableMVarId_hash(v_key_532_);
v___x_540_ = 32ULL;
v___x_541_ = lean_uint64_shift_right(v___x_539_, v___x_540_);
v_fold_542_ = lean_uint64_xor(v___x_539_, v___x_541_);
v___x_543_ = 16ULL;
v___x_544_ = lean_uint64_shift_right(v_fold_542_, v___x_543_);
v___x_545_ = lean_uint64_xor(v_fold_542_, v___x_544_);
v___x_546_ = lean_uint64_to_usize(v___x_545_);
v___x_547_ = lean_usize_of_nat(v___x_538_);
v___x_548_ = ((size_t)1ULL);
v___x_549_ = lean_usize_sub(v___x_547_, v___x_548_);
v___x_550_ = lean_usize_land(v___x_546_, v___x_549_);
v___x_551_ = lean_array_uget_borrowed(v_x_530_, v___x_550_);
lean_inc(v___x_551_);
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 2, v___x_551_);
v___x_553_ = v___x_536_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_key_532_);
lean_ctor_set(v_reuseFailAlloc_556_, 1, v_value_533_);
lean_ctor_set(v_reuseFailAlloc_556_, 2, v___x_551_);
v___x_553_ = v_reuseFailAlloc_556_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
lean_object* v___x_554_; 
v___x_554_ = lean_array_uset(v_x_530_, v___x_550_, v___x_553_);
v_x_530_ = v___x_554_;
v_x_531_ = v_tail_534_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4_spec__5___redArg(lean_object* v_i_558_, lean_object* v_source_559_, lean_object* v_target_560_){
_start:
{
lean_object* v___x_561_; uint8_t v___x_562_; 
v___x_561_ = lean_array_get_size(v_source_559_);
v___x_562_ = lean_nat_dec_lt(v_i_558_, v___x_561_);
if (v___x_562_ == 0)
{
lean_dec_ref(v_source_559_);
lean_dec(v_i_558_);
return v_target_560_;
}
else
{
lean_object* v_es_563_; lean_object* v___x_564_; lean_object* v_source_565_; lean_object* v_target_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v_es_563_ = lean_array_fget(v_source_559_, v_i_558_);
v___x_564_ = lean_box(0);
v_source_565_ = lean_array_fset(v_source_559_, v_i_558_, v___x_564_);
v_target_566_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4_spec__5_spec__7___redArg(v_target_560_, v_es_563_);
v___x_567_ = lean_unsigned_to_nat(1u);
v___x_568_ = lean_nat_add(v_i_558_, v___x_567_);
lean_dec(v_i_558_);
v_i_558_ = v___x_568_;
v_source_559_ = v_source_565_;
v_target_560_ = v_target_566_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4___redArg(lean_object* v_data_570_){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v_nbuckets_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_571_ = lean_array_get_size(v_data_570_);
v___x_572_ = lean_unsigned_to_nat(2u);
v_nbuckets_573_ = lean_nat_mul(v___x_571_, v___x_572_);
v___x_574_ = lean_unsigned_to_nat(0u);
v___x_575_ = lean_box(0);
v___x_576_ = lean_mk_array(v_nbuckets_573_, v___x_575_);
v___x_577_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4_spec__5___redArg(v___x_574_, v_data_570_, v___x_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2___redArg(lean_object* v_m_578_, lean_object* v_a_579_, lean_object* v_b_580_){
_start:
{
lean_object* v_size_581_; lean_object* v_buckets_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_625_; 
v_size_581_ = lean_ctor_get(v_m_578_, 0);
v_buckets_582_ = lean_ctor_get(v_m_578_, 1);
v_isSharedCheck_625_ = !lean_is_exclusive(v_m_578_);
if (v_isSharedCheck_625_ == 0)
{
v___x_584_ = v_m_578_;
v_isShared_585_ = v_isSharedCheck_625_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_buckets_582_);
lean_inc(v_size_581_);
lean_dec(v_m_578_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_625_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_586_; uint64_t v___x_587_; uint64_t v___x_588_; uint64_t v___x_589_; uint64_t v_fold_590_; uint64_t v___x_591_; uint64_t v___x_592_; uint64_t v___x_593_; size_t v___x_594_; size_t v___x_595_; size_t v___x_596_; size_t v___x_597_; size_t v___x_598_; lean_object* v_bkt_599_; uint8_t v___x_600_; 
v___x_586_ = lean_array_get_size(v_buckets_582_);
v___x_587_ = l_Lean_instHashableMVarId_hash(v_a_579_);
v___x_588_ = 32ULL;
v___x_589_ = lean_uint64_shift_right(v___x_587_, v___x_588_);
v_fold_590_ = lean_uint64_xor(v___x_587_, v___x_589_);
v___x_591_ = 16ULL;
v___x_592_ = lean_uint64_shift_right(v_fold_590_, v___x_591_);
v___x_593_ = lean_uint64_xor(v_fold_590_, v___x_592_);
v___x_594_ = lean_uint64_to_usize(v___x_593_);
v___x_595_ = lean_usize_of_nat(v___x_586_);
v___x_596_ = ((size_t)1ULL);
v___x_597_ = lean_usize_sub(v___x_595_, v___x_596_);
v___x_598_ = lean_usize_land(v___x_594_, v___x_597_);
v_bkt_599_ = lean_array_uget_borrowed(v_buckets_582_, v___x_598_);
v___x_600_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3___redArg(v_a_579_, v_bkt_599_);
if (v___x_600_ == 0)
{
lean_object* v___x_601_; lean_object* v_size_x27_602_; lean_object* v___x_603_; lean_object* v_buckets_x27_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; uint8_t v___x_610_; 
v___x_601_ = lean_unsigned_to_nat(1u);
v_size_x27_602_ = lean_nat_add(v_size_581_, v___x_601_);
lean_dec(v_size_581_);
lean_inc(v_bkt_599_);
v___x_603_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_603_, 0, v_a_579_);
lean_ctor_set(v___x_603_, 1, v_b_580_);
lean_ctor_set(v___x_603_, 2, v_bkt_599_);
v_buckets_x27_604_ = lean_array_uset(v_buckets_582_, v___x_598_, v___x_603_);
v___x_605_ = lean_unsigned_to_nat(4u);
v___x_606_ = lean_nat_mul(v_size_x27_602_, v___x_605_);
v___x_607_ = lean_unsigned_to_nat(3u);
v___x_608_ = lean_nat_div(v___x_606_, v___x_607_);
lean_dec(v___x_606_);
v___x_609_ = lean_array_get_size(v_buckets_x27_604_);
v___x_610_ = lean_nat_dec_le(v___x_608_, v___x_609_);
lean_dec(v___x_608_);
if (v___x_610_ == 0)
{
lean_object* v_val_611_; lean_object* v___x_613_; 
v_val_611_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4___redArg(v_buckets_x27_604_);
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 1, v_val_611_);
lean_ctor_set(v___x_584_, 0, v_size_x27_602_);
v___x_613_ = v___x_584_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_size_x27_602_);
lean_ctor_set(v_reuseFailAlloc_614_, 1, v_val_611_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
else
{
lean_object* v___x_616_; 
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 1, v_buckets_x27_604_);
lean_ctor_set(v___x_584_, 0, v_size_x27_602_);
v___x_616_ = v___x_584_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_size_x27_602_);
lean_ctor_set(v_reuseFailAlloc_617_, 1, v_buckets_x27_604_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
}
else
{
lean_object* v___x_618_; lean_object* v_buckets_x27_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_623_; 
lean_inc(v_bkt_599_);
v___x_618_ = lean_box(0);
v_buckets_x27_619_ = lean_array_uset(v_buckets_582_, v___x_598_, v___x_618_);
v___x_620_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__5___redArg(v_a_579_, v_b_580_, v_bkt_599_);
v___x_621_ = lean_array_uset(v_buckets_x27_619_, v___x_598_, v___x_620_);
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 1, v___x_621_);
v___x_623_ = v___x_584_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_size_581_);
lean_ctor_set(v_reuseFailAlloc_624_, 1, v___x_621_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__3(lean_object* v_x_626_, lean_object* v_x_627_, lean_object* v___y_628_){
_start:
{
if (lean_obj_tag(v_x_626_) == 0)
{
lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_629_ = l_List_reverse___redArg(v_x_627_);
v___x_630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
lean_ctor_set(v___x_630_, 1, v___y_628_);
return v___x_630_;
}
else
{
lean_object* v_head_631_; lean_object* v_tail_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_643_; 
v_head_631_ = lean_ctor_get(v_x_626_, 0);
v_tail_632_ = lean_ctor_get(v_x_626_, 1);
v_isSharedCheck_643_ = !lean_is_exclusive(v_x_626_);
if (v_isSharedCheck_643_ == 0)
{
v___x_634_ = v_x_626_;
v_isShared_635_ = v_isSharedCheck_643_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_tail_632_);
lean_inc(v_head_631_);
lean_dec(v_x_626_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_643_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_636_; lean_object* v_fst_637_; lean_object* v_snd_638_; lean_object* v___x_640_; 
v___x_636_ = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(v_head_631_, v___y_628_);
v_fst_637_ = lean_ctor_get(v___x_636_, 0);
lean_inc(v_fst_637_);
v_snd_638_ = lean_ctor_get(v___x_636_, 1);
lean_inc(v_snd_638_);
lean_dec_ref(v___x_636_);
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 1, v_x_627_);
lean_ctor_set(v___x_634_, 0, v_fst_637_);
v___x_640_ = v___x_634_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_fst_637_);
lean_ctor_set(v_reuseFailAlloc_642_, 1, v_x_627_);
v___x_640_ = v_reuseFailAlloc_642_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
v_x_626_ = v_tail_632_;
v_x_627_ = v___x_640_;
v___y_628_ = v_snd_638_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_abstractExprMVars(lean_object* v_e_647_, lean_object* v_a_648_){
_start:
{
uint8_t v___x_649_; 
v___x_649_ = l_Lean_Expr_hasMVar(v_e_647_);
if (v___x_649_ == 0)
{
lean_object* v___x_650_; 
v___x_650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_650_, 0, v_e_647_);
lean_ctor_set(v___x_650_, 1, v_a_648_);
return v___x_650_;
}
else
{
switch(lean_obj_tag(v_e_647_))
{
case 2:
{
lean_object* v_mvarId_651_; lean_object* v_mctx_652_; lean_object* v_emap_653_; lean_object* v___x_654_; lean_object* v_userName_655_; lean_object* v_type_656_; lean_object* v_depth_657_; lean_object* v_depth_658_; uint8_t v___x_659_; 
v_mvarId_651_ = lean_ctor_get(v_e_647_, 0);
v_mctx_652_ = lean_ctor_get(v_a_648_, 2);
v_emap_653_ = lean_ctor_get(v_a_648_, 8);
lean_inc(v_mvarId_651_);
v___x_654_ = l_Lean_MetavarContext_getDecl(v_mctx_652_, v_mvarId_651_);
v_userName_655_ = lean_ctor_get(v___x_654_, 0);
lean_inc(v_userName_655_);
v_type_656_ = lean_ctor_get(v___x_654_, 2);
lean_inc_ref(v_type_656_);
v_depth_657_ = lean_ctor_get(v___x_654_, 3);
lean_inc(v_depth_657_);
lean_dec_ref(v___x_654_);
v_depth_658_ = lean_ctor_get(v_mctx_652_, 0);
v___x_659_ = lean_nat_dec_eq(v_depth_657_, v_depth_658_);
lean_dec(v_depth_657_);
if (v___x_659_ == 0)
{
lean_object* v___x_660_; 
lean_dec_ref(v_type_656_);
lean_dec(v_userName_655_);
v___x_660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_660_, 0, v_e_647_);
lean_ctor_set(v___x_660_, 1, v_a_648_);
return v___x_660_;
}
else
{
lean_object* v___x_661_; 
lean_inc(v_mvarId_651_);
v___x_661_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0___redArg(v_emap_653_, v_mvarId_651_);
if (lean_obj_tag(v___x_661_) == 0)
{
lean_object* v___x_662_; lean_object* v_fst_663_; lean_object* v_snd_664_; lean_object* v___x_665_; lean_object* v_fst_666_; lean_object* v_snd_667_; lean_object* v___x_668_; lean_object* v_fst_669_; lean_object* v_snd_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_708_; 
v___x_662_ = l_Lean_instantiateMVars___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__1(v_type_656_, v_a_648_);
v_fst_663_ = lean_ctor_get(v___x_662_, 0);
lean_inc(v_fst_663_);
v_snd_664_ = lean_ctor_get(v___x_662_, 1);
lean_inc(v_snd_664_);
lean_dec_ref(v___x_662_);
v___x_665_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_fst_663_, v_snd_664_);
v_fst_666_ = lean_ctor_get(v___x_665_, 0);
lean_inc(v_fst_666_);
v_snd_667_ = lean_ctor_get(v___x_665_, 1);
lean_inc(v_snd_667_);
lean_dec_ref(v___x_665_);
v___x_668_ = l_Lean_Meta_AbstractMVars_mkFreshFVarId(v_snd_667_);
v_fst_669_ = lean_ctor_get(v___x_668_, 0);
v_snd_670_ = lean_ctor_get(v___x_668_, 1);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_708_ == 0)
{
v___x_672_ = v___x_668_;
v_isShared_673_ = v_isSharedCheck_708_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_snd_670_);
lean_inc(v_fst_669_);
lean_dec(v___x_668_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_708_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_674_; lean_object* v_userName_676_; uint8_t v___x_703_; 
lean_inc(v_fst_669_);
v___x_674_ = l_Lean_mkFVar(v_fst_669_);
v___x_703_ = l_Lean_Name_isAnonymous(v_userName_655_);
if (v___x_703_ == 0)
{
v_userName_676_ = v_userName_655_;
goto v___jp_675_;
}
else
{
lean_object* v_fvars_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
lean_dec(v_userName_655_);
v_fvars_704_ = lean_ctor_get(v_snd_670_, 5);
v___x_705_ = ((lean_object*)(l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__1));
v___x_706_ = lean_array_get_size(v_fvars_704_);
v___x_707_ = lean_name_append_index_after(v___x_705_, v___x_706_);
v_userName_676_ = v___x_707_;
goto v___jp_675_;
}
v___jp_675_:
{
lean_object* v_ngen_677_; lean_object* v_lctx_678_; lean_object* v_mctx_679_; lean_object* v_nextParamIdx_680_; lean_object* v_paramNames_681_; lean_object* v_fvars_682_; lean_object* v_mvars_683_; lean_object* v_lmap_684_; lean_object* v_emap_685_; uint8_t v_abstractLevels_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_702_; 
v_ngen_677_ = lean_ctor_get(v_snd_670_, 0);
v_lctx_678_ = lean_ctor_get(v_snd_670_, 1);
v_mctx_679_ = lean_ctor_get(v_snd_670_, 2);
v_nextParamIdx_680_ = lean_ctor_get(v_snd_670_, 3);
v_paramNames_681_ = lean_ctor_get(v_snd_670_, 4);
v_fvars_682_ = lean_ctor_get(v_snd_670_, 5);
v_mvars_683_ = lean_ctor_get(v_snd_670_, 6);
v_lmap_684_ = lean_ctor_get(v_snd_670_, 7);
v_emap_685_ = lean_ctor_get(v_snd_670_, 8);
v_abstractLevels_686_ = lean_ctor_get_uint8(v_snd_670_, sizeof(void*)*9);
v_isSharedCheck_702_ = !lean_is_exclusive(v_snd_670_);
if (v_isSharedCheck_702_ == 0)
{
v___x_688_ = v_snd_670_;
v_isShared_689_ = v_isSharedCheck_702_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_emap_685_);
lean_inc(v_lmap_684_);
lean_inc(v_mvars_683_);
lean_inc(v_fvars_682_);
lean_inc(v_paramNames_681_);
lean_inc(v_nextParamIdx_680_);
lean_inc(v_mctx_679_);
lean_inc(v_lctx_678_);
lean_inc(v_ngen_677_);
lean_dec(v_snd_670_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_702_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
uint8_t v___x_690_; uint8_t v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_697_; 
v___x_690_ = 0;
v___x_691_ = 0;
v___x_692_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_678_, v_fst_669_, v_userName_676_, v_fst_666_, v___x_690_, v___x_691_);
lean_inc_ref_n(v___x_674_, 2);
v___x_693_ = lean_array_push(v_fvars_682_, v___x_674_);
v___x_694_ = lean_array_push(v_mvars_683_, v_e_647_);
v___x_695_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2___redArg(v_emap_685_, v_mvarId_651_, v___x_674_);
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 8, v___x_695_);
lean_ctor_set(v___x_688_, 6, v___x_694_);
lean_ctor_set(v___x_688_, 5, v___x_693_);
lean_ctor_set(v___x_688_, 1, v___x_692_);
v___x_697_ = v___x_688_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_ngen_677_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v___x_692_);
lean_ctor_set(v_reuseFailAlloc_701_, 2, v_mctx_679_);
lean_ctor_set(v_reuseFailAlloc_701_, 3, v_nextParamIdx_680_);
lean_ctor_set(v_reuseFailAlloc_701_, 4, v_paramNames_681_);
lean_ctor_set(v_reuseFailAlloc_701_, 5, v___x_693_);
lean_ctor_set(v_reuseFailAlloc_701_, 6, v___x_694_);
lean_ctor_set(v_reuseFailAlloc_701_, 7, v_lmap_684_);
lean_ctor_set(v_reuseFailAlloc_701_, 8, v___x_695_);
lean_ctor_set_uint8(v_reuseFailAlloc_701_, sizeof(void*)*9, v_abstractLevels_686_);
v___x_697_ = v_reuseFailAlloc_701_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
lean_object* v___x_699_; 
if (v_isShared_673_ == 0)
{
lean_ctor_set(v___x_672_, 1, v___x_697_);
lean_ctor_set(v___x_672_, 0, v___x_674_);
v___x_699_ = v___x_672_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v___x_674_);
lean_ctor_set(v_reuseFailAlloc_700_, 1, v___x_697_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
}
}
}
}
else
{
lean_object* v_val_709_; lean_object* v___x_710_; 
lean_dec_ref(v_type_656_);
lean_dec(v_userName_655_);
lean_dec(v_mvarId_651_);
lean_dec_ref_known(v_e_647_, 1);
v_val_709_ = lean_ctor_get(v___x_661_, 0);
lean_inc(v_val_709_);
lean_dec_ref_known(v___x_661_, 1);
v___x_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_710_, 0, v_val_709_);
lean_ctor_set(v___x_710_, 1, v_a_648_);
return v___x_710_;
}
}
}
case 3:
{
lean_object* v_u_711_; lean_object* v___x_712_; lean_object* v_fst_713_; lean_object* v_snd_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_728_; 
v_u_711_ = lean_ctor_get(v_e_647_, 0);
lean_inc(v_u_711_);
v___x_712_ = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(v_u_711_, v_a_648_);
v_fst_713_ = lean_ctor_get(v___x_712_, 0);
v_snd_714_ = lean_ctor_get(v___x_712_, 1);
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_728_ == 0)
{
v___x_716_ = v___x_712_;
v_isShared_717_ = v_isSharedCheck_728_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_snd_714_);
lean_inc(v_fst_713_);
lean_dec(v___x_712_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_728_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
size_t v___x_718_; size_t v___x_719_; uint8_t v___x_720_; 
v___x_718_ = lean_ptr_addr(v_u_711_);
v___x_719_ = lean_ptr_addr(v_fst_713_);
v___x_720_ = lean_usize_dec_eq(v___x_718_, v___x_719_);
if (v___x_720_ == 0)
{
lean_object* v___x_721_; lean_object* v___x_723_; 
lean_dec_ref_known(v_e_647_, 1);
v___x_721_ = l_Lean_Expr_sort___override(v_fst_713_);
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 0, v___x_721_);
v___x_723_ = v___x_716_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v___x_721_);
lean_ctor_set(v_reuseFailAlloc_724_, 1, v_snd_714_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
else
{
lean_object* v___x_726_; 
lean_dec(v_fst_713_);
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 0, v_e_647_);
v___x_726_ = v___x_716_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_e_647_);
lean_ctor_set(v_reuseFailAlloc_727_, 1, v_snd_714_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
}
}
}
}
case 4:
{
lean_object* v_declName_729_; lean_object* v_us_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v_fst_733_; lean_object* v_snd_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_746_; 
v_declName_729_ = lean_ctor_get(v_e_647_, 0);
v_us_730_ = lean_ctor_get(v_e_647_, 1);
v___x_731_ = lean_box(0);
lean_inc(v_us_730_);
v___x_732_ = l_List_mapM_loop___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__3(v_us_730_, v___x_731_, v_a_648_);
v_fst_733_ = lean_ctor_get(v___x_732_, 0);
v_snd_734_ = lean_ctor_get(v___x_732_, 1);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_746_ == 0)
{
v___x_736_ = v___x_732_;
v_isShared_737_ = v_isSharedCheck_746_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_snd_734_);
lean_inc(v_fst_733_);
lean_dec(v___x_732_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_746_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
uint8_t v___x_738_; 
v___x_738_ = l_ptrEqList___redArg(v_us_730_, v_fst_733_);
if (v___x_738_ == 0)
{
lean_object* v___x_739_; lean_object* v___x_741_; 
lean_inc(v_declName_729_);
lean_dec_ref_known(v_e_647_, 2);
v___x_739_ = l_Lean_Expr_const___override(v_declName_729_, v_fst_733_);
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 0, v___x_739_);
v___x_741_ = v___x_736_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v___x_739_);
lean_ctor_set(v_reuseFailAlloc_742_, 1, v_snd_734_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
else
{
lean_object* v___x_744_; 
lean_dec(v_fst_733_);
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 0, v_e_647_);
v___x_744_ = v___x_736_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_e_647_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v_snd_734_);
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
case 5:
{
lean_object* v_fn_747_; lean_object* v_arg_748_; lean_object* v___x_749_; lean_object* v_fst_750_; lean_object* v_snd_751_; lean_object* v___x_752_; lean_object* v_fst_753_; lean_object* v_snd_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_775_; 
v_fn_747_ = lean_ctor_get(v_e_647_, 0);
v_arg_748_ = lean_ctor_get(v_e_647_, 1);
lean_inc_ref(v_fn_747_);
v___x_749_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_fn_747_, v_a_648_);
v_fst_750_ = lean_ctor_get(v___x_749_, 0);
lean_inc(v_fst_750_);
v_snd_751_ = lean_ctor_get(v___x_749_, 1);
lean_inc(v_snd_751_);
lean_dec_ref(v___x_749_);
lean_inc_ref(v_arg_748_);
v___x_752_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_arg_748_, v_snd_751_);
v_fst_753_ = lean_ctor_get(v___x_752_, 0);
v_snd_754_ = lean_ctor_get(v___x_752_, 1);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_752_);
if (v_isSharedCheck_775_ == 0)
{
v___x_756_ = v___x_752_;
v_isShared_757_ = v_isSharedCheck_775_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_snd_754_);
lean_inc(v_fst_753_);
lean_dec(v___x_752_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_775_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
size_t v___x_758_; size_t v___x_759_; uint8_t v___x_760_; 
v___x_758_ = lean_ptr_addr(v_fn_747_);
v___x_759_ = lean_ptr_addr(v_fst_750_);
v___x_760_ = lean_usize_dec_eq(v___x_758_, v___x_759_);
if (v___x_760_ == 0)
{
lean_object* v___x_761_; lean_object* v___x_763_; 
lean_dec_ref_known(v_e_647_, 2);
v___x_761_ = l_Lean_Expr_app___override(v_fst_750_, v_fst_753_);
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 0, v___x_761_);
v___x_763_ = v___x_756_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v___x_761_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v_snd_754_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
else
{
size_t v___x_765_; size_t v___x_766_; uint8_t v___x_767_; 
v___x_765_ = lean_ptr_addr(v_arg_748_);
v___x_766_ = lean_ptr_addr(v_fst_753_);
v___x_767_ = lean_usize_dec_eq(v___x_765_, v___x_766_);
if (v___x_767_ == 0)
{
lean_object* v___x_768_; lean_object* v___x_770_; 
lean_dec_ref_known(v_e_647_, 2);
v___x_768_ = l_Lean_Expr_app___override(v_fst_750_, v_fst_753_);
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 0, v___x_768_);
v___x_770_ = v___x_756_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v___x_768_);
lean_ctor_set(v_reuseFailAlloc_771_, 1, v_snd_754_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
else
{
lean_object* v___x_773_; 
lean_dec(v_fst_753_);
lean_dec(v_fst_750_);
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 0, v_e_647_);
v___x_773_ = v___x_756_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_e_647_);
lean_ctor_set(v_reuseFailAlloc_774_, 1, v_snd_754_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
}
}
case 6:
{
lean_object* v_binderName_776_; lean_object* v_binderType_777_; lean_object* v_body_778_; uint8_t v_binderInfo_779_; lean_object* v___x_780_; lean_object* v_fst_781_; lean_object* v_snd_782_; lean_object* v___x_783_; lean_object* v_fst_784_; lean_object* v_snd_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_811_; 
v_binderName_776_ = lean_ctor_get(v_e_647_, 0);
v_binderType_777_ = lean_ctor_get(v_e_647_, 1);
v_body_778_ = lean_ctor_get(v_e_647_, 2);
v_binderInfo_779_ = lean_ctor_get_uint8(v_e_647_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_777_);
v___x_780_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_binderType_777_, v_a_648_);
v_fst_781_ = lean_ctor_get(v___x_780_, 0);
lean_inc(v_fst_781_);
v_snd_782_ = lean_ctor_get(v___x_780_, 1);
lean_inc(v_snd_782_);
lean_dec_ref(v___x_780_);
lean_inc_ref(v_body_778_);
v___x_783_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_body_778_, v_snd_782_);
v_fst_784_ = lean_ctor_get(v___x_783_, 0);
v_snd_785_ = lean_ctor_get(v___x_783_, 1);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_811_ == 0)
{
v___x_787_ = v___x_783_;
v_isShared_788_ = v_isSharedCheck_811_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_snd_785_);
lean_inc(v_fst_784_);
lean_dec(v___x_783_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_811_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
size_t v___x_789_; size_t v___x_790_; uint8_t v___x_791_; 
v___x_789_ = lean_ptr_addr(v_binderType_777_);
v___x_790_ = lean_ptr_addr(v_fst_781_);
v___x_791_ = lean_usize_dec_eq(v___x_789_, v___x_790_);
if (v___x_791_ == 0)
{
lean_object* v___x_792_; lean_object* v___x_794_; 
lean_inc(v_binderName_776_);
lean_dec_ref_known(v_e_647_, 3);
v___x_792_ = l_Lean_Expr_lam___override(v_binderName_776_, v_fst_781_, v_fst_784_, v_binderInfo_779_);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 0, v___x_792_);
v___x_794_ = v___x_787_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v___x_792_);
lean_ctor_set(v_reuseFailAlloc_795_, 1, v_snd_785_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
else
{
size_t v___x_796_; size_t v___x_797_; uint8_t v___x_798_; 
v___x_796_ = lean_ptr_addr(v_body_778_);
v___x_797_ = lean_ptr_addr(v_fst_784_);
v___x_798_ = lean_usize_dec_eq(v___x_796_, v___x_797_);
if (v___x_798_ == 0)
{
lean_object* v___x_799_; lean_object* v___x_801_; 
lean_inc(v_binderName_776_);
lean_dec_ref_known(v_e_647_, 3);
v___x_799_ = l_Lean_Expr_lam___override(v_binderName_776_, v_fst_781_, v_fst_784_, v_binderInfo_779_);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 0, v___x_799_);
v___x_801_ = v___x_787_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v___x_799_);
lean_ctor_set(v_reuseFailAlloc_802_, 1, v_snd_785_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
else
{
uint8_t v___x_803_; 
v___x_803_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_779_, v_binderInfo_779_);
if (v___x_803_ == 0)
{
lean_object* v___x_804_; lean_object* v___x_806_; 
lean_inc(v_binderName_776_);
lean_dec_ref_known(v_e_647_, 3);
v___x_804_ = l_Lean_Expr_lam___override(v_binderName_776_, v_fst_781_, v_fst_784_, v_binderInfo_779_);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 0, v___x_804_);
v___x_806_ = v___x_787_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v___x_804_);
lean_ctor_set(v_reuseFailAlloc_807_, 1, v_snd_785_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
return v___x_806_;
}
}
else
{
lean_object* v___x_809_; 
lean_dec(v_fst_784_);
lean_dec(v_fst_781_);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 0, v_e_647_);
v___x_809_ = v___x_787_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_e_647_);
lean_ctor_set(v_reuseFailAlloc_810_, 1, v_snd_785_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
}
}
}
}
case 7:
{
lean_object* v_binderName_812_; lean_object* v_binderType_813_; lean_object* v_body_814_; uint8_t v_binderInfo_815_; lean_object* v___x_816_; lean_object* v_fst_817_; lean_object* v_snd_818_; lean_object* v___x_819_; lean_object* v_fst_820_; lean_object* v_snd_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_847_; 
v_binderName_812_ = lean_ctor_get(v_e_647_, 0);
v_binderType_813_ = lean_ctor_get(v_e_647_, 1);
v_body_814_ = lean_ctor_get(v_e_647_, 2);
v_binderInfo_815_ = lean_ctor_get_uint8(v_e_647_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_813_);
v___x_816_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_binderType_813_, v_a_648_);
v_fst_817_ = lean_ctor_get(v___x_816_, 0);
lean_inc(v_fst_817_);
v_snd_818_ = lean_ctor_get(v___x_816_, 1);
lean_inc(v_snd_818_);
lean_dec_ref(v___x_816_);
lean_inc_ref(v_body_814_);
v___x_819_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_body_814_, v_snd_818_);
v_fst_820_ = lean_ctor_get(v___x_819_, 0);
v_snd_821_ = lean_ctor_get(v___x_819_, 1);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_819_);
if (v_isSharedCheck_847_ == 0)
{
v___x_823_ = v___x_819_;
v_isShared_824_ = v_isSharedCheck_847_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_snd_821_);
lean_inc(v_fst_820_);
lean_dec(v___x_819_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_847_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
size_t v___x_825_; size_t v___x_826_; uint8_t v___x_827_; 
v___x_825_ = lean_ptr_addr(v_binderType_813_);
v___x_826_ = lean_ptr_addr(v_fst_817_);
v___x_827_ = lean_usize_dec_eq(v___x_825_, v___x_826_);
if (v___x_827_ == 0)
{
lean_object* v___x_828_; lean_object* v___x_830_; 
lean_inc(v_binderName_812_);
lean_dec_ref_known(v_e_647_, 3);
v___x_828_ = l_Lean_Expr_forallE___override(v_binderName_812_, v_fst_817_, v_fst_820_, v_binderInfo_815_);
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 0, v___x_828_);
v___x_830_ = v___x_823_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v___x_828_);
lean_ctor_set(v_reuseFailAlloc_831_, 1, v_snd_821_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
else
{
size_t v___x_832_; size_t v___x_833_; uint8_t v___x_834_; 
v___x_832_ = lean_ptr_addr(v_body_814_);
v___x_833_ = lean_ptr_addr(v_fst_820_);
v___x_834_ = lean_usize_dec_eq(v___x_832_, v___x_833_);
if (v___x_834_ == 0)
{
lean_object* v___x_835_; lean_object* v___x_837_; 
lean_inc(v_binderName_812_);
lean_dec_ref_known(v_e_647_, 3);
v___x_835_ = l_Lean_Expr_forallE___override(v_binderName_812_, v_fst_817_, v_fst_820_, v_binderInfo_815_);
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 0, v___x_835_);
v___x_837_ = v___x_823_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v___x_835_);
lean_ctor_set(v_reuseFailAlloc_838_, 1, v_snd_821_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
else
{
uint8_t v___x_839_; 
v___x_839_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_815_, v_binderInfo_815_);
if (v___x_839_ == 0)
{
lean_object* v___x_840_; lean_object* v___x_842_; 
lean_inc(v_binderName_812_);
lean_dec_ref_known(v_e_647_, 3);
v___x_840_ = l_Lean_Expr_forallE___override(v_binderName_812_, v_fst_817_, v_fst_820_, v_binderInfo_815_);
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 0, v___x_840_);
v___x_842_ = v___x_823_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v___x_840_);
lean_ctor_set(v_reuseFailAlloc_843_, 1, v_snd_821_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
else
{
lean_object* v___x_845_; 
lean_dec(v_fst_820_);
lean_dec(v_fst_817_);
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 0, v_e_647_);
v___x_845_ = v___x_823_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_e_647_);
lean_ctor_set(v_reuseFailAlloc_846_, 1, v_snd_821_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
}
}
}
case 8:
{
lean_object* v_declName_848_; lean_object* v_type_849_; lean_object* v_value_850_; lean_object* v_body_851_; uint8_t v_nondep_852_; lean_object* v___x_853_; lean_object* v_fst_854_; lean_object* v_snd_855_; lean_object* v___x_856_; lean_object* v_fst_857_; lean_object* v_snd_858_; lean_object* v___x_859_; lean_object* v_fst_860_; lean_object* v_snd_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_889_; 
v_declName_848_ = lean_ctor_get(v_e_647_, 0);
v_type_849_ = lean_ctor_get(v_e_647_, 1);
v_value_850_ = lean_ctor_get(v_e_647_, 2);
v_body_851_ = lean_ctor_get(v_e_647_, 3);
v_nondep_852_ = lean_ctor_get_uint8(v_e_647_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_849_);
v___x_853_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_type_849_, v_a_648_);
v_fst_854_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_fst_854_);
v_snd_855_ = lean_ctor_get(v___x_853_, 1);
lean_inc(v_snd_855_);
lean_dec_ref(v___x_853_);
lean_inc_ref(v_value_850_);
v___x_856_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_value_850_, v_snd_855_);
v_fst_857_ = lean_ctor_get(v___x_856_, 0);
lean_inc(v_fst_857_);
v_snd_858_ = lean_ctor_get(v___x_856_, 1);
lean_inc(v_snd_858_);
lean_dec_ref(v___x_856_);
lean_inc_ref(v_body_851_);
v___x_859_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_body_851_, v_snd_858_);
v_fst_860_ = lean_ctor_get(v___x_859_, 0);
v_snd_861_ = lean_ctor_get(v___x_859_, 1);
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_889_ == 0)
{
v___x_863_ = v___x_859_;
v_isShared_864_ = v_isSharedCheck_889_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_snd_861_);
lean_inc(v_fst_860_);
lean_dec(v___x_859_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_889_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
size_t v___x_865_; size_t v___x_866_; uint8_t v___x_867_; 
v___x_865_ = lean_ptr_addr(v_type_849_);
v___x_866_ = lean_ptr_addr(v_fst_854_);
v___x_867_ = lean_usize_dec_eq(v___x_865_, v___x_866_);
if (v___x_867_ == 0)
{
lean_object* v___x_868_; lean_object* v___x_870_; 
lean_inc(v_declName_848_);
lean_dec_ref_known(v_e_647_, 4);
v___x_868_ = l_Lean_Expr_letE___override(v_declName_848_, v_fst_854_, v_fst_857_, v_fst_860_, v_nondep_852_);
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 0, v___x_868_);
v___x_870_ = v___x_863_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v___x_868_);
lean_ctor_set(v_reuseFailAlloc_871_, 1, v_snd_861_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
else
{
size_t v___x_872_; size_t v___x_873_; uint8_t v___x_874_; 
v___x_872_ = lean_ptr_addr(v_value_850_);
v___x_873_ = lean_ptr_addr(v_fst_857_);
v___x_874_ = lean_usize_dec_eq(v___x_872_, v___x_873_);
if (v___x_874_ == 0)
{
lean_object* v___x_875_; lean_object* v___x_877_; 
lean_inc(v_declName_848_);
lean_dec_ref_known(v_e_647_, 4);
v___x_875_ = l_Lean_Expr_letE___override(v_declName_848_, v_fst_854_, v_fst_857_, v_fst_860_, v_nondep_852_);
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 0, v___x_875_);
v___x_877_ = v___x_863_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v___x_875_);
lean_ctor_set(v_reuseFailAlloc_878_, 1, v_snd_861_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
else
{
size_t v___x_879_; size_t v___x_880_; uint8_t v___x_881_; 
v___x_879_ = lean_ptr_addr(v_body_851_);
v___x_880_ = lean_ptr_addr(v_fst_860_);
v___x_881_ = lean_usize_dec_eq(v___x_879_, v___x_880_);
if (v___x_881_ == 0)
{
lean_object* v___x_882_; lean_object* v___x_884_; 
lean_inc(v_declName_848_);
lean_dec_ref_known(v_e_647_, 4);
v___x_882_ = l_Lean_Expr_letE___override(v_declName_848_, v_fst_854_, v_fst_857_, v_fst_860_, v_nondep_852_);
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 0, v___x_882_);
v___x_884_ = v___x_863_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_882_);
lean_ctor_set(v_reuseFailAlloc_885_, 1, v_snd_861_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
else
{
lean_object* v___x_887_; 
lean_dec(v_fst_860_);
lean_dec(v_fst_857_);
lean_dec(v_fst_854_);
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 0, v_e_647_);
v___x_887_ = v___x_863_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_e_647_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v_snd_861_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
}
}
}
case 10:
{
lean_object* v_data_890_; lean_object* v_expr_891_; lean_object* v___x_892_; lean_object* v_fst_893_; lean_object* v_snd_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_908_; 
v_data_890_ = lean_ctor_get(v_e_647_, 0);
v_expr_891_ = lean_ctor_get(v_e_647_, 1);
lean_inc_ref(v_expr_891_);
v___x_892_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_expr_891_, v_a_648_);
v_fst_893_ = lean_ctor_get(v___x_892_, 0);
v_snd_894_ = lean_ctor_get(v___x_892_, 1);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_892_);
if (v_isSharedCheck_908_ == 0)
{
v___x_896_ = v___x_892_;
v_isShared_897_ = v_isSharedCheck_908_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_snd_894_);
lean_inc(v_fst_893_);
lean_dec(v___x_892_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_908_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
size_t v___x_898_; size_t v___x_899_; uint8_t v___x_900_; 
v___x_898_ = lean_ptr_addr(v_expr_891_);
v___x_899_ = lean_ptr_addr(v_fst_893_);
v___x_900_ = lean_usize_dec_eq(v___x_898_, v___x_899_);
if (v___x_900_ == 0)
{
lean_object* v___x_901_; lean_object* v___x_903_; 
lean_inc(v_data_890_);
lean_dec_ref_known(v_e_647_, 2);
v___x_901_ = l_Lean_Expr_mdata___override(v_data_890_, v_fst_893_);
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 0, v___x_901_);
v___x_903_ = v___x_896_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v___x_901_);
lean_ctor_set(v_reuseFailAlloc_904_, 1, v_snd_894_);
v___x_903_ = v_reuseFailAlloc_904_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
return v___x_903_;
}
}
else
{
lean_object* v___x_906_; 
lean_dec(v_fst_893_);
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 0, v_e_647_);
v___x_906_ = v___x_896_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_e_647_);
lean_ctor_set(v_reuseFailAlloc_907_, 1, v_snd_894_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
}
}
case 11:
{
lean_object* v_typeName_909_; lean_object* v_idx_910_; lean_object* v_struct_911_; lean_object* v___x_912_; lean_object* v_fst_913_; lean_object* v_snd_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_928_; 
v_typeName_909_ = lean_ctor_get(v_e_647_, 0);
v_idx_910_ = lean_ctor_get(v_e_647_, 1);
v_struct_911_ = lean_ctor_get(v_e_647_, 2);
lean_inc_ref(v_struct_911_);
v___x_912_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_struct_911_, v_a_648_);
v_fst_913_ = lean_ctor_get(v___x_912_, 0);
v_snd_914_ = lean_ctor_get(v___x_912_, 1);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_912_);
if (v_isSharedCheck_928_ == 0)
{
v___x_916_ = v___x_912_;
v_isShared_917_ = v_isSharedCheck_928_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_snd_914_);
lean_inc(v_fst_913_);
lean_dec(v___x_912_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_928_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
size_t v___x_918_; size_t v___x_919_; uint8_t v___x_920_; 
v___x_918_ = lean_ptr_addr(v_struct_911_);
v___x_919_ = lean_ptr_addr(v_fst_913_);
v___x_920_ = lean_usize_dec_eq(v___x_918_, v___x_919_);
if (v___x_920_ == 0)
{
lean_object* v___x_921_; lean_object* v___x_923_; 
lean_inc(v_idx_910_);
lean_inc(v_typeName_909_);
lean_dec_ref_known(v_e_647_, 3);
v___x_921_ = l_Lean_Expr_proj___override(v_typeName_909_, v_idx_910_, v_fst_913_);
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 0, v___x_921_);
v___x_923_ = v___x_916_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v___x_921_);
lean_ctor_set(v_reuseFailAlloc_924_, 1, v_snd_914_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
else
{
lean_object* v___x_926_; 
lean_dec(v_fst_913_);
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 0, v_e_647_);
v___x_926_ = v___x_916_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_e_647_);
lean_ctor_set(v_reuseFailAlloc_927_, 1, v_snd_914_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
}
}
}
}
default: 
{
lean_object* v___x_929_; 
v___x_929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_929_, 0, v_e_647_);
lean_ctor_set(v___x_929_, 1, v_a_648_);
return v___x_929_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0(lean_object* v_00_u03b2_930_, lean_object* v_m_931_, lean_object* v_a_932_){
_start:
{
lean_object* v___x_933_; 
v___x_933_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0___redArg(v_m_931_, v_a_932_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0___boxed(lean_object* v_00_u03b2_934_, lean_object* v_m_935_, lean_object* v_a_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0(v_00_u03b2_934_, v_m_935_, v_a_936_);
lean_dec(v_a_936_);
lean_dec_ref(v_m_935_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2(lean_object* v_00_u03b2_938_, lean_object* v_m_939_, lean_object* v_a_940_, lean_object* v_b_941_){
_start:
{
lean_object* v___x_942_; 
v___x_942_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2___redArg(v_m_939_, v_a_940_, v_b_941_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0(lean_object* v_00_u03b2_943_, lean_object* v_a_944_, lean_object* v_x_945_){
_start:
{
lean_object* v___x_946_; 
v___x_946_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0___redArg(v_a_944_, v_x_945_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0___boxed(lean_object* v_00_u03b2_947_, lean_object* v_a_948_, lean_object* v_x_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0(v_00_u03b2_947_, v_a_948_, v_x_949_);
lean_dec(v_x_949_);
lean_dec(v_a_948_);
return v_res_950_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3(lean_object* v_00_u03b2_951_, lean_object* v_a_952_, lean_object* v_x_953_){
_start:
{
uint8_t v___x_954_; 
v___x_954_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3___redArg(v_a_952_, v_x_953_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3___boxed(lean_object* v_00_u03b2_955_, lean_object* v_a_956_, lean_object* v_x_957_){
_start:
{
uint8_t v_res_958_; lean_object* v_r_959_; 
v_res_958_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3(v_00_u03b2_955_, v_a_956_, v_x_957_);
lean_dec(v_x_957_);
lean_dec(v_a_956_);
v_r_959_ = lean_box(v_res_958_);
return v_r_959_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4(lean_object* v_00_u03b2_960_, lean_object* v_data_961_){
_start:
{
lean_object* v___x_962_; 
v___x_962_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4___redArg(v_data_961_);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__5(lean_object* v_00_u03b2_963_, lean_object* v_a_964_, lean_object* v_b_965_, lean_object* v_x_966_){
_start:
{
lean_object* v___x_967_; 
v___x_967_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__5___redArg(v_a_964_, v_b_965_, v_x_966_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_968_, lean_object* v_i_969_, lean_object* v_source_970_, lean_object* v_target_971_){
_start:
{
lean_object* v___x_972_; 
v___x_972_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4_spec__5___redArg(v_i_969_, v_source_970_, v_target_971_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4_spec__5_spec__7(lean_object* v_00_u03b2_973_, lean_object* v_x_974_, lean_object* v_x_975_){
_start:
{
lean_object* v___x_976_; 
v___x_976_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4_spec__5_spec__7___redArg(v_x_974_, v_x_975_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0___redArg(lean_object* v_e_977_, lean_object* v___y_978_){
_start:
{
uint8_t v___x_980_; 
v___x_980_ = l_Lean_Expr_hasMVar(v_e_977_);
if (v___x_980_ == 0)
{
lean_object* v___x_981_; 
v___x_981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_981_, 0, v_e_977_);
return v___x_981_;
}
else
{
lean_object* v___x_982_; lean_object* v_mctx_983_; lean_object* v___x_984_; lean_object* v_fst_985_; lean_object* v_snd_986_; lean_object* v___x_987_; lean_object* v_cache_988_; lean_object* v_zetaDeltaFVarIds_989_; lean_object* v_postponed_990_; lean_object* v_diag_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_1000_; 
v___x_982_ = lean_st_ref_get(v___y_978_);
v_mctx_983_ = lean_ctor_get(v___x_982_, 0);
lean_inc_ref(v_mctx_983_);
lean_dec(v___x_982_);
v___x_984_ = l_Lean_instantiateMVarsCore(v_mctx_983_, v_e_977_);
v_fst_985_ = lean_ctor_get(v___x_984_, 0);
lean_inc(v_fst_985_);
v_snd_986_ = lean_ctor_get(v___x_984_, 1);
lean_inc(v_snd_986_);
lean_dec_ref(v___x_984_);
v___x_987_ = lean_st_ref_take(v___y_978_);
v_cache_988_ = lean_ctor_get(v___x_987_, 1);
v_zetaDeltaFVarIds_989_ = lean_ctor_get(v___x_987_, 2);
v_postponed_990_ = lean_ctor_get(v___x_987_, 3);
v_diag_991_ = lean_ctor_get(v___x_987_, 4);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_1000_ == 0)
{
lean_object* v_unused_1001_; 
v_unused_1001_ = lean_ctor_get(v___x_987_, 0);
lean_dec(v_unused_1001_);
v___x_993_ = v___x_987_;
v_isShared_994_ = v_isSharedCheck_1000_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_diag_991_);
lean_inc(v_postponed_990_);
lean_inc(v_zetaDeltaFVarIds_989_);
lean_inc(v_cache_988_);
lean_dec(v___x_987_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_1000_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_996_; 
if (v_isShared_994_ == 0)
{
lean_ctor_set(v___x_993_, 0, v_snd_986_);
v___x_996_ = v___x_993_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_snd_986_);
lean_ctor_set(v_reuseFailAlloc_999_, 1, v_cache_988_);
lean_ctor_set(v_reuseFailAlloc_999_, 2, v_zetaDeltaFVarIds_989_);
lean_ctor_set(v_reuseFailAlloc_999_, 3, v_postponed_990_);
lean_ctor_set(v_reuseFailAlloc_999_, 4, v_diag_991_);
v___x_996_ = v_reuseFailAlloc_999_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_997_ = lean_st_ref_put(v___y_978_, v___x_996_);
v___x_998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_998_, 0, v_fst_985_);
return v___x_998_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0___redArg___boxed(lean_object* v_e_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0___redArg(v_e_1002_, v___y_1003_);
lean_dec(v___y_1003_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0(lean_object* v_e_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_){
_start:
{
lean_object* v___x_1012_; 
v___x_1012_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0___redArg(v_e_1006_, v___y_1008_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0___boxed(lean_object* v_e_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_){
_start:
{
lean_object* v_res_1019_; 
v_res_1019_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0(v_e_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
return v_res_1019_;
}
}
static lean_object* _init_l_Lean_Meta_abstractMVars___closed__1(void){
_start:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1022_ = lean_box(0);
v___x_1023_ = lean_unsigned_to_nat(16u);
v___x_1024_ = lean_mk_array(v___x_1023_, v___x_1022_);
return v___x_1024_;
}
}
static lean_object* _init_l_Lean_Meta_abstractMVars___closed__2(void){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1025_ = lean_obj_once(&l_Lean_Meta_abstractMVars___closed__1, &l_Lean_Meta_abstractMVars___closed__1_once, _init_l_Lean_Meta_abstractMVars___closed__1);
v___x_1026_ = lean_unsigned_to_nat(0u);
v___x_1027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1026_);
lean_ctor_set(v___x_1027_, 1, v___x_1025_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractMVars(lean_object* v_e_1028_, uint8_t v_levels_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_){
_start:
{
lean_object* v___x_1035_; lean_object* v_a_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1097_; 
v___x_1035_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0___redArg(v_e_1028_, v_a_1031_);
v_a_1036_ = lean_ctor_get(v___x_1035_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1035_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1038_ = v___x_1035_;
v_isShared_1039_ = v_isSharedCheck_1097_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_a_1036_);
lean_dec(v___x_1035_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1097_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v_mctx_1042_; lean_object* v_lctx_1043_; lean_object* v_ngen_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v_fst_1050_; lean_object* v_snd_1051_; lean_object* v___x_1052_; lean_object* v_ngen_1053_; lean_object* v_lctx_1054_; lean_object* v_mctx_1055_; lean_object* v_paramNames_1056_; lean_object* v_fvars_1057_; lean_object* v_mvars_1058_; lean_object* v_env_1059_; lean_object* v_nextMacroScope_1060_; lean_object* v_auxDeclNGen_1061_; lean_object* v_traceState_1062_; lean_object* v_cache_1063_; lean_object* v_messages_1064_; lean_object* v_infoState_1065_; lean_object* v_snapshotTasks_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1095_; 
v___x_1040_ = lean_st_ref_get(v_a_1031_);
v___x_1041_ = lean_st_ref_get(v_a_1033_);
v_mctx_1042_ = lean_ctor_get(v___x_1040_, 0);
lean_inc_ref(v_mctx_1042_);
lean_dec(v___x_1040_);
v_lctx_1043_ = lean_ctor_get(v_a_1030_, 2);
v_ngen_1044_ = lean_ctor_get(v___x_1041_, 2);
lean_inc_ref(v_ngen_1044_);
lean_dec(v___x_1041_);
v___x_1045_ = lean_unsigned_to_nat(0u);
v___x_1046_ = ((lean_object*)(l_Lean_Meta_abstractMVars___closed__0));
v___x_1047_ = lean_obj_once(&l_Lean_Meta_abstractMVars___closed__2, &l_Lean_Meta_abstractMVars___closed__2_once, _init_l_Lean_Meta_abstractMVars___closed__2);
lean_inc_ref(v_lctx_1043_);
v___x_1048_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v___x_1048_, 0, v_ngen_1044_);
lean_ctor_set(v___x_1048_, 1, v_lctx_1043_);
lean_ctor_set(v___x_1048_, 2, v_mctx_1042_);
lean_ctor_set(v___x_1048_, 3, v___x_1045_);
lean_ctor_set(v___x_1048_, 4, v___x_1046_);
lean_ctor_set(v___x_1048_, 5, v___x_1046_);
lean_ctor_set(v___x_1048_, 6, v___x_1046_);
lean_ctor_set(v___x_1048_, 7, v___x_1047_);
lean_ctor_set(v___x_1048_, 8, v___x_1047_);
lean_ctor_set_uint8(v___x_1048_, sizeof(void*)*9, v_levels_1029_);
v___x_1049_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_a_1036_, v___x_1048_);
v_fst_1050_ = lean_ctor_get(v___x_1049_, 0);
lean_inc(v_fst_1050_);
v_snd_1051_ = lean_ctor_get(v___x_1049_, 1);
lean_inc(v_snd_1051_);
lean_dec_ref(v___x_1049_);
v___x_1052_ = lean_st_ref_take(v_a_1033_);
v_ngen_1053_ = lean_ctor_get(v_snd_1051_, 0);
lean_inc_ref(v_ngen_1053_);
v_lctx_1054_ = lean_ctor_get(v_snd_1051_, 1);
lean_inc_ref(v_lctx_1054_);
v_mctx_1055_ = lean_ctor_get(v_snd_1051_, 2);
lean_inc_ref(v_mctx_1055_);
v_paramNames_1056_ = lean_ctor_get(v_snd_1051_, 4);
lean_inc_ref(v_paramNames_1056_);
v_fvars_1057_ = lean_ctor_get(v_snd_1051_, 5);
lean_inc_ref(v_fvars_1057_);
v_mvars_1058_ = lean_ctor_get(v_snd_1051_, 6);
lean_inc_ref(v_mvars_1058_);
lean_dec(v_snd_1051_);
v_env_1059_ = lean_ctor_get(v___x_1052_, 0);
v_nextMacroScope_1060_ = lean_ctor_get(v___x_1052_, 1);
v_auxDeclNGen_1061_ = lean_ctor_get(v___x_1052_, 3);
v_traceState_1062_ = lean_ctor_get(v___x_1052_, 4);
v_cache_1063_ = lean_ctor_get(v___x_1052_, 5);
v_messages_1064_ = lean_ctor_get(v___x_1052_, 6);
v_infoState_1065_ = lean_ctor_get(v___x_1052_, 7);
v_snapshotTasks_1066_ = lean_ctor_get(v___x_1052_, 8);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1095_ == 0)
{
lean_object* v_unused_1096_; 
v_unused_1096_ = lean_ctor_get(v___x_1052_, 2);
lean_dec(v_unused_1096_);
v___x_1068_ = v___x_1052_;
v_isShared_1069_ = v_isSharedCheck_1095_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_snapshotTasks_1066_);
lean_inc(v_infoState_1065_);
lean_inc(v_messages_1064_);
lean_inc(v_cache_1063_);
lean_inc(v_traceState_1062_);
lean_inc(v_auxDeclNGen_1061_);
lean_inc(v_nextMacroScope_1060_);
lean_inc(v_env_1059_);
lean_dec(v___x_1052_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1095_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1071_; 
if (v_isShared_1069_ == 0)
{
lean_ctor_set(v___x_1068_, 2, v_ngen_1053_);
v___x_1071_ = v___x_1068_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_env_1059_);
lean_ctor_set(v_reuseFailAlloc_1094_, 1, v_nextMacroScope_1060_);
lean_ctor_set(v_reuseFailAlloc_1094_, 2, v_ngen_1053_);
lean_ctor_set(v_reuseFailAlloc_1094_, 3, v_auxDeclNGen_1061_);
lean_ctor_set(v_reuseFailAlloc_1094_, 4, v_traceState_1062_);
lean_ctor_set(v_reuseFailAlloc_1094_, 5, v_cache_1063_);
lean_ctor_set(v_reuseFailAlloc_1094_, 6, v_messages_1064_);
lean_ctor_set(v_reuseFailAlloc_1094_, 7, v_infoState_1065_);
lean_ctor_set(v_reuseFailAlloc_1094_, 8, v_snapshotTasks_1066_);
v___x_1071_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v_cache_1074_; lean_object* v_zetaDeltaFVarIds_1075_; lean_object* v_postponed_1076_; lean_object* v_diag_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1092_; 
v___x_1072_ = lean_st_ref_put(v_a_1033_, v___x_1071_);
v___x_1073_ = lean_st_ref_take(v_a_1031_);
v_cache_1074_ = lean_ctor_get(v___x_1073_, 1);
v_zetaDeltaFVarIds_1075_ = lean_ctor_get(v___x_1073_, 2);
v_postponed_1076_ = lean_ctor_get(v___x_1073_, 3);
v_diag_1077_ = lean_ctor_get(v___x_1073_, 4);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1092_ == 0)
{
lean_object* v_unused_1093_; 
v_unused_1093_ = lean_ctor_get(v___x_1073_, 0);
lean_dec(v_unused_1093_);
v___x_1079_ = v___x_1073_;
v_isShared_1080_ = v_isSharedCheck_1092_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_diag_1077_);
lean_inc(v_postponed_1076_);
lean_inc(v_zetaDeltaFVarIds_1075_);
lean_inc(v_cache_1074_);
lean_dec(v___x_1073_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1092_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v___x_1082_; 
if (v_isShared_1080_ == 0)
{
lean_ctor_set(v___x_1079_, 0, v_mctx_1055_);
v___x_1082_ = v___x_1079_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_mctx_1055_);
lean_ctor_set(v_reuseFailAlloc_1091_, 1, v_cache_1074_);
lean_ctor_set(v_reuseFailAlloc_1091_, 2, v_zetaDeltaFVarIds_1075_);
lean_ctor_set(v_reuseFailAlloc_1091_, 3, v_postponed_1076_);
lean_ctor_set(v_reuseFailAlloc_1091_, 4, v_diag_1077_);
v___x_1082_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
lean_object* v___x_1083_; uint8_t v___x_1084_; uint8_t v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1089_; 
v___x_1083_ = lean_st_ref_put(v_a_1031_, v___x_1082_);
v___x_1084_ = 1;
v___x_1085_ = 0;
v___x_1086_ = l_Lean_LocalContext_mkLambda(v_lctx_1054_, v_fvars_1057_, v_fst_1050_, v___x_1084_, v___x_1085_);
lean_dec(v_fst_1050_);
lean_dec_ref(v_fvars_1057_);
v___x_1087_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1087_, 0, v_paramNames_1056_);
lean_ctor_set(v___x_1087_, 1, v_mvars_1058_);
lean_ctor_set(v___x_1087_, 2, v___x_1086_);
if (v_isShared_1039_ == 0)
{
lean_ctor_set(v___x_1038_, 0, v___x_1087_);
v___x_1089_ = v___x_1038_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v___x_1087_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractMVars___boxed(lean_object* v_e_1098_, lean_object* v_levels_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_){
_start:
{
uint8_t v_levels_boxed_1105_; lean_object* v_res_1106_; 
v_levels_boxed_1105_ = lean_unbox(v_levels_1099_);
v_res_1106_ = l_Lean_Meta_abstractMVars(v_e_1098_, v_levels_boxed_1105_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_);
lean_dec(v_a_1103_);
lean_dec_ref(v_a_1102_);
lean_dec(v_a_1101_);
lean_dec_ref(v_a_1100_);
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_openAbstractMVarsResult_spec__0(size_t v_sz_1107_, size_t v_i_1108_, lean_object* v_bs_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_){
_start:
{
uint8_t v___x_1115_; 
v___x_1115_ = lean_usize_dec_lt(v_i_1108_, v_sz_1107_);
if (v___x_1115_ == 0)
{
lean_object* v___x_1116_; 
v___x_1116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1116_, 0, v_bs_1109_);
return v___x_1116_;
}
else
{
lean_object* v___x_1117_; 
v___x_1117_ = l_Lean_Meta_mkFreshLevelMVar(v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v_a_1118_; lean_object* v___x_1119_; lean_object* v_bs_x27_1120_; size_t v___x_1121_; size_t v___x_1122_; lean_object* v___x_1123_; 
v_a_1118_ = lean_ctor_get(v___x_1117_, 0);
lean_inc(v_a_1118_);
lean_dec_ref_known(v___x_1117_, 1);
v___x_1119_ = lean_unsigned_to_nat(0u);
v_bs_x27_1120_ = lean_array_uset(v_bs_1109_, v_i_1108_, v___x_1119_);
v___x_1121_ = ((size_t)1ULL);
v___x_1122_ = lean_usize_add(v_i_1108_, v___x_1121_);
v___x_1123_ = lean_array_uset(v_bs_x27_1120_, v_i_1108_, v_a_1118_);
v_i_1108_ = v___x_1122_;
v_bs_1109_ = v___x_1123_;
goto _start;
}
else
{
lean_object* v_a_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1132_; 
lean_dec_ref(v_bs_1109_);
v_a_1125_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1132_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1127_ = v___x_1117_;
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_a_1125_);
lean_dec(v___x_1117_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1130_; 
if (v_isShared_1128_ == 0)
{
v___x_1130_ = v___x_1127_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_a_1125_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
return v___x_1130_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_openAbstractMVarsResult_spec__0___boxed(lean_object* v_sz_1133_, lean_object* v_i_1134_, lean_object* v_bs_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_){
_start:
{
size_t v_sz_boxed_1141_; size_t v_i_boxed_1142_; lean_object* v_res_1143_; 
v_sz_boxed_1141_ = lean_unbox_usize(v_sz_1133_);
lean_dec(v_sz_1133_);
v_i_boxed_1142_ = lean_unbox_usize(v_i_1134_);
lean_dec(v_i_1134_);
v_res_1143_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_openAbstractMVarsResult_spec__0(v_sz_boxed_1141_, v_i_boxed_1142_, v_bs_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
lean_dec(v___y_1139_);
lean_dec_ref(v___y_1138_);
lean_dec(v___y_1137_);
lean_dec_ref(v___y_1136_);
return v_res_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_openAbstractMVarsResult(lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_){
_start:
{
lean_object* v_paramNames_1150_; lean_object* v_expr_1151_; size_t v_sz_1152_; size_t v___x_1153_; lean_object* v___x_1154_; 
v_paramNames_1150_ = lean_ctor_get(v_a_1144_, 0);
v_expr_1151_ = lean_ctor_get(v_a_1144_, 2);
v_sz_1152_ = lean_array_size(v_paramNames_1150_);
v___x_1153_ = ((size_t)0ULL);
lean_inc_ref(v_paramNames_1150_);
v___x_1154_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_openAbstractMVarsResult_spec__0(v_sz_1152_, v___x_1153_, v_paramNames_1150_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_);
if (lean_obj_tag(v___x_1154_) == 0)
{
lean_object* v_a_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v_a_1155_ = lean_ctor_get(v___x_1154_, 0);
lean_inc(v_a_1155_);
lean_dec_ref_known(v___x_1154_, 1);
lean_inc_ref(v_paramNames_1150_);
v___x_1156_ = l_Lean_Expr_instantiateLevelParamsArray(v_expr_1151_, v_paramNames_1150_, v_a_1155_);
v___x_1157_ = l_Lean_Meta_AbstractMVarsResult_numMVars(v_a_1144_);
lean_dec_ref(v_a_1144_);
v___x_1158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1157_);
v___x_1159_ = l_Lean_Meta_lambdaMetaTelescope(v___x_1156_, v___x_1158_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_);
lean_dec_ref_known(v___x_1158_, 1);
lean_dec_ref(v___x_1156_);
return v___x_1159_;
}
else
{
lean_object* v_a_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1167_; 
lean_dec_ref(v_a_1144_);
v_a_1160_ = lean_ctor_get(v___x_1154_, 0);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1162_ = v___x_1154_;
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_a_1160_);
lean_dec(v___x_1154_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1165_; 
if (v_isShared_1163_ == 0)
{
v___x_1165_ = v___x_1162_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_a_1160_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_openAbstractMVarsResult___boxed(lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l_Lean_Meta_openAbstractMVarsResult(v_a_1168_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_);
lean_dec(v_a_1172_);
lean_dec_ref(v_a_1171_);
lean_dec(v_a_1170_);
lean_dec_ref(v_a_1169_);
return v_res_1174_;
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
