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
uint8_t lean_bool_not(uint8_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
lean_object* v_ngen_266_; lean_object* v_lctx_267_; lean_object* v_mctx_268_; lean_object* v_nextParamIdx_269_; lean_object* v_paramNames_270_; lean_object* v_fvars_271_; lean_object* v_mvars_272_; lean_object* v_lmap_273_; lean_object* v_emap_274_; uint8_t v_abstractLevels_275_; uint8_t v___x_276_; 
v_ngen_266_ = lean_ctor_get(v_a_265_, 0);
v_lctx_267_ = lean_ctor_get(v_a_265_, 1);
v_mctx_268_ = lean_ctor_get(v_a_265_, 2);
v_nextParamIdx_269_ = lean_ctor_get(v_a_265_, 3);
v_paramNames_270_ = lean_ctor_get(v_a_265_, 4);
v_fvars_271_ = lean_ctor_get(v_a_265_, 5);
v_mvars_272_ = lean_ctor_get(v_a_265_, 6);
v_lmap_273_ = lean_ctor_get(v_a_265_, 7);
v_emap_274_ = lean_ctor_get(v_a_265_, 8);
v_abstractLevels_275_ = lean_ctor_get_uint8(v_a_265_, sizeof(void*)*9);
v___x_276_ = lean_bool_not(v_abstractLevels_275_);
if (v___x_276_ == 0)
{
uint8_t v___x_277_; uint8_t v___x_278_; 
v___x_277_ = l_Lean_Level_hasMVar(v_u_264_);
v___x_278_ = lean_bool_not(v___x_277_);
if (v___x_278_ == 0)
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
lean_object* v_a_297_; lean_object* v_a_298_; lean_object* v___x_299_; lean_object* v_fst_300_; lean_object* v_snd_301_; lean_object* v___x_302_; lean_object* v_fst_303_; lean_object* v_snd_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_324_; 
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
v_isSharedCheck_324_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_324_ == 0)
{
v___x_306_ = v___x_302_;
v_isShared_307_ = v_isSharedCheck_324_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_snd_304_);
lean_inc(v_fst_303_);
lean_dec(v___x_302_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_324_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
uint8_t v___y_309_; size_t v___x_318_; size_t v___x_319_; uint8_t v___x_320_; 
v___x_318_ = lean_ptr_addr(v_a_297_);
v___x_319_ = lean_ptr_addr(v_fst_300_);
v___x_320_ = lean_usize_dec_eq(v___x_318_, v___x_319_);
if (v___x_320_ == 0)
{
v___y_309_ = v___x_320_;
goto v___jp_308_;
}
else
{
size_t v___x_321_; size_t v___x_322_; uint8_t v___x_323_; 
v___x_321_ = lean_ptr_addr(v_a_298_);
v___x_322_ = lean_ptr_addr(v_fst_303_);
v___x_323_ = lean_usize_dec_eq(v___x_321_, v___x_322_);
v___y_309_ = v___x_323_;
goto v___jp_308_;
}
v___jp_308_:
{
if (v___y_309_ == 0)
{
lean_object* v___x_310_; lean_object* v___x_312_; 
lean_dec_ref_known(v_u_264_, 2);
v___x_310_ = l_Lean_mkLevelMax_x27(v_fst_300_, v_fst_303_);
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 0, v___x_310_);
v___x_312_ = v___x_306_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v___x_310_);
lean_ctor_set(v_reuseFailAlloc_313_, 1, v_snd_304_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
else
{
lean_object* v___x_314_; lean_object* v___x_316_; 
v___x_314_ = l_Lean_simpLevelMax_x27(v_fst_300_, v_fst_303_, v_u_264_);
lean_dec_ref_known(v_u_264_, 2);
lean_dec(v_fst_303_);
lean_dec(v_fst_300_);
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 0, v___x_314_);
v___x_316_ = v___x_306_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v___x_314_);
lean_ctor_set(v_reuseFailAlloc_317_, 1, v_snd_304_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
return v___x_316_;
}
}
}
}
}
case 3:
{
lean_object* v_a_325_; lean_object* v_a_326_; lean_object* v___x_327_; lean_object* v_fst_328_; lean_object* v_snd_329_; lean_object* v___x_330_; lean_object* v_fst_331_; lean_object* v_snd_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_352_; 
v_a_325_ = lean_ctor_get(v_u_264_, 0);
v_a_326_ = lean_ctor_get(v_u_264_, 1);
lean_inc(v_a_325_);
v___x_327_ = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(v_a_325_, v_a_265_);
v_fst_328_ = lean_ctor_get(v___x_327_, 0);
lean_inc(v_fst_328_);
v_snd_329_ = lean_ctor_get(v___x_327_, 1);
lean_inc(v_snd_329_);
lean_dec_ref(v___x_327_);
lean_inc(v_a_326_);
v___x_330_ = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(v_a_326_, v_snd_329_);
v_fst_331_ = lean_ctor_get(v___x_330_, 0);
v_snd_332_ = lean_ctor_get(v___x_330_, 1);
v_isSharedCheck_352_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_352_ == 0)
{
v___x_334_ = v___x_330_;
v_isShared_335_ = v_isSharedCheck_352_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_snd_332_);
lean_inc(v_fst_331_);
lean_dec(v___x_330_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_352_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
uint8_t v___y_337_; size_t v___x_346_; size_t v___x_347_; uint8_t v___x_348_; 
v___x_346_ = lean_ptr_addr(v_a_325_);
v___x_347_ = lean_ptr_addr(v_fst_328_);
v___x_348_ = lean_usize_dec_eq(v___x_346_, v___x_347_);
if (v___x_348_ == 0)
{
v___y_337_ = v___x_348_;
goto v___jp_336_;
}
else
{
size_t v___x_349_; size_t v___x_350_; uint8_t v___x_351_; 
v___x_349_ = lean_ptr_addr(v_a_326_);
v___x_350_ = lean_ptr_addr(v_fst_331_);
v___x_351_ = lean_usize_dec_eq(v___x_349_, v___x_350_);
v___y_337_ = v___x_351_;
goto v___jp_336_;
}
v___jp_336_:
{
if (v___y_337_ == 0)
{
lean_object* v___x_338_; lean_object* v___x_340_; 
lean_dec_ref_known(v_u_264_, 2);
v___x_338_ = l_Lean_mkLevelIMax_x27(v_fst_328_, v_fst_331_);
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 0, v___x_338_);
v___x_340_ = v___x_334_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v___x_338_);
lean_ctor_set(v_reuseFailAlloc_341_, 1, v_snd_332_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
return v___x_340_;
}
}
else
{
lean_object* v___x_342_; lean_object* v___x_344_; 
v___x_342_ = l_Lean_simpLevelIMax_x27(v_fst_328_, v_fst_331_, v_u_264_);
lean_dec_ref_known(v_u_264_, 2);
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 0, v___x_342_);
v___x_344_ = v___x_334_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v___x_342_);
lean_ctor_set(v_reuseFailAlloc_345_, 1, v_snd_332_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
}
}
}
case 5:
{
lean_object* v_a_353_; lean_object* v_depth_354_; lean_object* v___x_355_; uint8_t v___x_356_; uint8_t v___x_357_; 
v_a_353_ = lean_ctor_get(v_u_264_, 0);
v_depth_354_ = lean_ctor_get(v_mctx_268_, 0);
lean_inc(v_a_353_);
v___x_355_ = l_Lean_MetavarContext_getLevelDepth(v_mctx_268_, v_a_353_);
v___x_356_ = lean_nat_dec_eq(v___x_355_, v_depth_354_);
lean_dec(v___x_355_);
v___x_357_ = lean_bool_not(v___x_356_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; 
lean_inc(v_a_353_);
lean_dec_ref_known(v_u_264_, 1);
v___x_358_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___redArg(v_lmap_273_, v_a_353_);
if (lean_obj_tag(v___x_358_) == 0)
{
lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_373_; 
lean_inc_ref(v_emap_274_);
lean_inc_ref(v_lmap_273_);
lean_inc_ref(v_mvars_272_);
lean_inc_ref(v_fvars_271_);
lean_inc_ref(v_paramNames_270_);
lean_inc(v_nextParamIdx_269_);
lean_inc_ref(v_mctx_268_);
lean_inc_ref(v_lctx_267_);
lean_inc_ref(v_ngen_266_);
v_isSharedCheck_373_ = !lean_is_exclusive(v_a_265_);
if (v_isSharedCheck_373_ == 0)
{
lean_object* v_unused_374_; lean_object* v_unused_375_; lean_object* v_unused_376_; lean_object* v_unused_377_; lean_object* v_unused_378_; lean_object* v_unused_379_; lean_object* v_unused_380_; lean_object* v_unused_381_; lean_object* v_unused_382_; 
v_unused_374_ = lean_ctor_get(v_a_265_, 8);
lean_dec(v_unused_374_);
v_unused_375_ = lean_ctor_get(v_a_265_, 7);
lean_dec(v_unused_375_);
v_unused_376_ = lean_ctor_get(v_a_265_, 6);
lean_dec(v_unused_376_);
v_unused_377_ = lean_ctor_get(v_a_265_, 5);
lean_dec(v_unused_377_);
v_unused_378_ = lean_ctor_get(v_a_265_, 4);
lean_dec(v_unused_378_);
v_unused_379_ = lean_ctor_get(v_a_265_, 3);
lean_dec(v_unused_379_);
v_unused_380_ = lean_ctor_get(v_a_265_, 2);
lean_dec(v_unused_380_);
v_unused_381_ = lean_ctor_get(v_a_265_, 1);
lean_dec(v_unused_381_);
v_unused_382_ = lean_ctor_get(v_a_265_, 0);
lean_dec(v_unused_382_);
v___x_360_ = v_a_265_;
v_isShared_361_ = v_isSharedCheck_373_;
goto v_resetjp_359_;
}
else
{
lean_dec(v_a_265_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_373_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_370_; 
v___x_362_ = ((lean_object*)(l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___closed__1));
lean_inc(v_nextParamIdx_269_);
v___x_363_ = l_Lean_Name_num___override(v___x_362_, v_nextParamIdx_269_);
lean_inc(v___x_363_);
v___x_364_ = l_Lean_mkLevelParam(v___x_363_);
v___x_365_ = lean_unsigned_to_nat(1u);
v___x_366_ = lean_nat_add(v_nextParamIdx_269_, v___x_365_);
lean_dec(v_nextParamIdx_269_);
v___x_367_ = lean_array_push(v_paramNames_270_, v___x_363_);
lean_inc(v___x_364_);
v___x_368_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1___redArg(v_lmap_273_, v_a_353_, v___x_364_);
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 7, v___x_368_);
lean_ctor_set(v___x_360_, 4, v___x_367_);
lean_ctor_set(v___x_360_, 3, v___x_366_);
v___x_370_ = v___x_360_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_ngen_266_);
lean_ctor_set(v_reuseFailAlloc_372_, 1, v_lctx_267_);
lean_ctor_set(v_reuseFailAlloc_372_, 2, v_mctx_268_);
lean_ctor_set(v_reuseFailAlloc_372_, 3, v___x_366_);
lean_ctor_set(v_reuseFailAlloc_372_, 4, v___x_367_);
lean_ctor_set(v_reuseFailAlloc_372_, 5, v_fvars_271_);
lean_ctor_set(v_reuseFailAlloc_372_, 6, v_mvars_272_);
lean_ctor_set(v_reuseFailAlloc_372_, 7, v___x_368_);
lean_ctor_set(v_reuseFailAlloc_372_, 8, v_emap_274_);
lean_ctor_set_uint8(v_reuseFailAlloc_372_, sizeof(void*)*9, v_abstractLevels_275_);
v___x_370_ = v_reuseFailAlloc_372_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
lean_object* v___x_371_; 
v___x_371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_371_, 0, v___x_364_);
lean_ctor_set(v___x_371_, 1, v___x_370_);
return v___x_371_;
}
}
}
else
{
lean_object* v_val_383_; lean_object* v___x_384_; 
lean_dec(v_a_353_);
v_val_383_ = lean_ctor_get(v___x_358_, 0);
lean_inc(v_val_383_);
lean_dec_ref_known(v___x_358_, 1);
v___x_384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_384_, 0, v_val_383_);
lean_ctor_set(v___x_384_, 1, v_a_265_);
return v___x_384_;
}
}
else
{
lean_object* v___x_385_; 
v___x_385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_385_, 0, v_u_264_);
lean_ctor_set(v___x_385_, 1, v_a_265_);
return v___x_385_;
}
}
default: 
{
lean_object* v___x_386_; 
v___x_386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_386_, 0, v_u_264_);
lean_ctor_set(v___x_386_, 1, v_a_265_);
return v___x_386_;
}
}
}
else
{
lean_object* v___x_387_; 
v___x_387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_387_, 0, v_u_264_);
lean_ctor_set(v___x_387_, 1, v_a_265_);
return v___x_387_;
}
}
else
{
lean_object* v___x_388_; 
v___x_388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_388_, 0, v_u_264_);
lean_ctor_set(v___x_388_, 1, v_a_265_);
return v___x_388_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0(lean_object* v_00_u03b2_389_, lean_object* v_m_390_, lean_object* v_a_391_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___redArg(v_m_390_, v_a_391_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___boxed(lean_object* v_00_u03b2_393_, lean_object* v_m_394_, lean_object* v_a_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0(v_00_u03b2_393_, v_m_394_, v_a_395_);
lean_dec(v_a_395_);
lean_dec_ref(v_m_394_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1(lean_object* v_00_u03b2_397_, lean_object* v_m_398_, lean_object* v_a_399_, lean_object* v_b_400_){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1___redArg(v_m_398_, v_a_399_, v_b_400_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0(lean_object* v_00_u03b2_402_, lean_object* v_a_403_, lean_object* v_x_404_){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0___redArg(v_a_403_, v_x_404_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0___boxed(lean_object* v_00_u03b2_406_, lean_object* v_a_407_, lean_object* v_x_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0(v_00_u03b2_406_, v_a_407_, v_x_408_);
lean_dec(v_x_408_);
lean_dec(v_a_407_);
return v_res_409_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2(lean_object* v_00_u03b2_410_, lean_object* v_a_411_, lean_object* v_x_412_){
_start:
{
uint8_t v___x_413_; 
v___x_413_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2___redArg(v_a_411_, v_x_412_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2___boxed(lean_object* v_00_u03b2_414_, lean_object* v_a_415_, lean_object* v_x_416_){
_start:
{
uint8_t v_res_417_; lean_object* v_r_418_; 
v_res_417_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2(v_00_u03b2_414_, v_a_415_, v_x_416_);
lean_dec(v_x_416_);
lean_dec(v_a_415_);
v_r_418_ = lean_box(v_res_417_);
return v_r_418_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3(lean_object* v_00_u03b2_419_, lean_object* v_data_420_){
_start:
{
lean_object* v___x_421_; 
v___x_421_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3___redArg(v_data_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__4(lean_object* v_00_u03b2_422_, lean_object* v_a_423_, lean_object* v_b_424_, lean_object* v_x_425_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__4___redArg(v_a_423_, v_b_424_, v_x_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_427_, lean_object* v_i_428_, lean_object* v_source_429_, lean_object* v_target_430_){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3_spec__4___redArg(v_i_428_, v_source_429_, v_target_430_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_432_, lean_object* v_x_433_, lean_object* v_x_434_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3_spec__4_spec__5___redArg(v_x_433_, v_x_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__1(lean_object* v_e_436_, lean_object* v___y_437_){
_start:
{
uint8_t v___x_438_; uint8_t v___x_439_; 
v___x_438_ = l_Lean_Expr_hasMVar(v_e_436_);
v___x_439_ = lean_bool_not(v___x_438_);
if (v___x_439_ == 0)
{
lean_object* v_ngen_440_; lean_object* v_lctx_441_; lean_object* v_mctx_442_; lean_object* v_nextParamIdx_443_; lean_object* v_paramNames_444_; lean_object* v_fvars_445_; lean_object* v_mvars_446_; lean_object* v_lmap_447_; lean_object* v_emap_448_; uint8_t v_abstractLevels_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_466_; 
v_ngen_440_ = lean_ctor_get(v___y_437_, 0);
v_lctx_441_ = lean_ctor_get(v___y_437_, 1);
v_mctx_442_ = lean_ctor_get(v___y_437_, 2);
v_nextParamIdx_443_ = lean_ctor_get(v___y_437_, 3);
v_paramNames_444_ = lean_ctor_get(v___y_437_, 4);
v_fvars_445_ = lean_ctor_get(v___y_437_, 5);
v_mvars_446_ = lean_ctor_get(v___y_437_, 6);
v_lmap_447_ = lean_ctor_get(v___y_437_, 7);
v_emap_448_ = lean_ctor_get(v___y_437_, 8);
v_abstractLevels_449_ = lean_ctor_get_uint8(v___y_437_, sizeof(void*)*9);
v_isSharedCheck_466_ = !lean_is_exclusive(v___y_437_);
if (v_isSharedCheck_466_ == 0)
{
v___x_451_ = v___y_437_;
v_isShared_452_ = v_isSharedCheck_466_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_emap_448_);
lean_inc(v_lmap_447_);
lean_inc(v_mvars_446_);
lean_inc(v_fvars_445_);
lean_inc(v_paramNames_444_);
lean_inc(v_nextParamIdx_443_);
lean_inc(v_mctx_442_);
lean_inc(v_lctx_441_);
lean_inc(v_ngen_440_);
lean_dec(v___y_437_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_466_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_453_; lean_object* v_fst_454_; lean_object* v_snd_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_465_; 
v___x_453_ = l_Lean_instantiateMVarsCore(v_mctx_442_, v_e_436_);
v_fst_454_ = lean_ctor_get(v___x_453_, 0);
v_snd_455_ = lean_ctor_get(v___x_453_, 1);
v_isSharedCheck_465_ = !lean_is_exclusive(v___x_453_);
if (v_isSharedCheck_465_ == 0)
{
v___x_457_ = v___x_453_;
v_isShared_458_ = v_isSharedCheck_465_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_snd_455_);
lean_inc(v_fst_454_);
lean_dec(v___x_453_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_465_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_460_; 
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 2, v_snd_455_);
v___x_460_ = v___x_451_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_ngen_440_);
lean_ctor_set(v_reuseFailAlloc_464_, 1, v_lctx_441_);
lean_ctor_set(v_reuseFailAlloc_464_, 2, v_snd_455_);
lean_ctor_set(v_reuseFailAlloc_464_, 3, v_nextParamIdx_443_);
lean_ctor_set(v_reuseFailAlloc_464_, 4, v_paramNames_444_);
lean_ctor_set(v_reuseFailAlloc_464_, 5, v_fvars_445_);
lean_ctor_set(v_reuseFailAlloc_464_, 6, v_mvars_446_);
lean_ctor_set(v_reuseFailAlloc_464_, 7, v_lmap_447_);
lean_ctor_set(v_reuseFailAlloc_464_, 8, v_emap_448_);
lean_ctor_set_uint8(v_reuseFailAlloc_464_, sizeof(void*)*9, v_abstractLevels_449_);
v___x_460_ = v_reuseFailAlloc_464_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
lean_object* v___x_462_; 
if (v_isShared_458_ == 0)
{
lean_ctor_set(v___x_457_, 1, v___x_460_);
v___x_462_ = v___x_457_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_fst_454_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v___x_460_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
}
}
else
{
lean_object* v___x_467_; 
v___x_467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_467_, 0, v_e_436_);
lean_ctor_set(v___x_467_, 1, v___y_437_);
return v___x_467_;
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
uint8_t v___x_649_; uint8_t v___x_650_; 
v___x_649_ = l_Lean_Expr_hasMVar(v_e_647_);
v___x_650_ = lean_bool_not(v___x_649_);
if (v___x_650_ == 0)
{
switch(lean_obj_tag(v_e_647_))
{
case 2:
{
lean_object* v_mvarId_651_; lean_object* v_mctx_652_; lean_object* v_emap_653_; lean_object* v___x_654_; lean_object* v_userName_655_; lean_object* v_type_656_; lean_object* v_depth_657_; lean_object* v_depth_658_; uint8_t v___x_659_; uint8_t v___x_660_; 
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
v___x_660_ = lean_bool_not(v___x_659_);
if (v___x_660_ == 0)
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
lean_dec_ref_known(v_e_647_, 1);
lean_dec(v_mvarId_651_);
v_val_709_ = lean_ctor_get(v___x_661_, 0);
lean_inc(v_val_709_);
lean_dec_ref_known(v___x_661_, 1);
v___x_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_710_, 0, v_val_709_);
lean_ctor_set(v___x_710_, 1, v_a_648_);
return v___x_710_;
}
}
else
{
lean_object* v___x_711_; 
lean_dec_ref(v_type_656_);
lean_dec(v_userName_655_);
v___x_711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_711_, 0, v_e_647_);
lean_ctor_set(v___x_711_, 1, v_a_648_);
return v___x_711_;
}
}
case 3:
{
lean_object* v_u_712_; lean_object* v___x_713_; lean_object* v_fst_714_; lean_object* v_snd_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_729_; 
v_u_712_ = lean_ctor_get(v_e_647_, 0);
lean_inc(v_u_712_);
v___x_713_ = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(v_u_712_, v_a_648_);
v_fst_714_ = lean_ctor_get(v___x_713_, 0);
v_snd_715_ = lean_ctor_get(v___x_713_, 1);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_729_ == 0)
{
v___x_717_ = v___x_713_;
v_isShared_718_ = v_isSharedCheck_729_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_snd_715_);
lean_inc(v_fst_714_);
lean_dec(v___x_713_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_729_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
size_t v___x_719_; size_t v___x_720_; uint8_t v___x_721_; 
v___x_719_ = lean_ptr_addr(v_u_712_);
v___x_720_ = lean_ptr_addr(v_fst_714_);
v___x_721_ = lean_usize_dec_eq(v___x_719_, v___x_720_);
if (v___x_721_ == 0)
{
lean_object* v___x_722_; lean_object* v___x_724_; 
lean_dec_ref_known(v_e_647_, 1);
v___x_722_ = l_Lean_Expr_sort___override(v_fst_714_);
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 0, v___x_722_);
v___x_724_ = v___x_717_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v___x_722_);
lean_ctor_set(v_reuseFailAlloc_725_, 1, v_snd_715_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
else
{
lean_object* v___x_727_; 
lean_dec(v_fst_714_);
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 0, v_e_647_);
v___x_727_ = v___x_717_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_e_647_);
lean_ctor_set(v_reuseFailAlloc_728_, 1, v_snd_715_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
}
case 4:
{
lean_object* v_declName_730_; lean_object* v_us_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v_fst_734_; lean_object* v_snd_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_747_; 
v_declName_730_ = lean_ctor_get(v_e_647_, 0);
v_us_731_ = lean_ctor_get(v_e_647_, 1);
v___x_732_ = lean_box(0);
lean_inc(v_us_731_);
v___x_733_ = l_List_mapM_loop___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__3(v_us_731_, v___x_732_, v_a_648_);
v_fst_734_ = lean_ctor_get(v___x_733_, 0);
v_snd_735_ = lean_ctor_get(v___x_733_, 1);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_747_ == 0)
{
v___x_737_ = v___x_733_;
v_isShared_738_ = v_isSharedCheck_747_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_snd_735_);
lean_inc(v_fst_734_);
lean_dec(v___x_733_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_747_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
uint8_t v___x_739_; 
v___x_739_ = l_ptrEqList___redArg(v_us_731_, v_fst_734_);
if (v___x_739_ == 0)
{
lean_object* v___x_740_; lean_object* v___x_742_; 
lean_inc(v_declName_730_);
lean_dec_ref_known(v_e_647_, 2);
v___x_740_ = l_Lean_Expr_const___override(v_declName_730_, v_fst_734_);
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 0, v___x_740_);
v___x_742_ = v___x_737_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v___x_740_);
lean_ctor_set(v_reuseFailAlloc_743_, 1, v_snd_735_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
else
{
lean_object* v___x_745_; 
lean_dec(v_fst_734_);
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 0, v_e_647_);
v___x_745_ = v___x_737_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_e_647_);
lean_ctor_set(v_reuseFailAlloc_746_, 1, v_snd_735_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
}
case 5:
{
lean_object* v_fn_748_; lean_object* v_arg_749_; lean_object* v___x_750_; lean_object* v_fst_751_; lean_object* v_snd_752_; lean_object* v___x_753_; lean_object* v_fst_754_; lean_object* v_snd_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_774_; 
v_fn_748_ = lean_ctor_get(v_e_647_, 0);
v_arg_749_ = lean_ctor_get(v_e_647_, 1);
lean_inc_ref(v_fn_748_);
v___x_750_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_fn_748_, v_a_648_);
v_fst_751_ = lean_ctor_get(v___x_750_, 0);
lean_inc(v_fst_751_);
v_snd_752_ = lean_ctor_get(v___x_750_, 1);
lean_inc(v_snd_752_);
lean_dec_ref(v___x_750_);
lean_inc_ref(v_arg_749_);
v___x_753_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_arg_749_, v_snd_752_);
v_fst_754_ = lean_ctor_get(v___x_753_, 0);
v_snd_755_ = lean_ctor_get(v___x_753_, 1);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_774_ == 0)
{
v___x_757_ = v___x_753_;
v_isShared_758_ = v_isSharedCheck_774_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_snd_755_);
lean_inc(v_fst_754_);
lean_dec(v___x_753_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_774_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
uint8_t v___y_760_; size_t v___x_768_; size_t v___x_769_; uint8_t v___x_770_; 
v___x_768_ = lean_ptr_addr(v_fn_748_);
v___x_769_ = lean_ptr_addr(v_fst_751_);
v___x_770_ = lean_usize_dec_eq(v___x_768_, v___x_769_);
if (v___x_770_ == 0)
{
v___y_760_ = v___x_770_;
goto v___jp_759_;
}
else
{
size_t v___x_771_; size_t v___x_772_; uint8_t v___x_773_; 
v___x_771_ = lean_ptr_addr(v_arg_749_);
v___x_772_ = lean_ptr_addr(v_fst_754_);
v___x_773_ = lean_usize_dec_eq(v___x_771_, v___x_772_);
v___y_760_ = v___x_773_;
goto v___jp_759_;
}
v___jp_759_:
{
if (v___y_760_ == 0)
{
lean_object* v___x_761_; lean_object* v___x_763_; 
lean_dec_ref_known(v_e_647_, 2);
v___x_761_ = l_Lean_Expr_app___override(v_fst_751_, v_fst_754_);
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 0, v___x_761_);
v___x_763_ = v___x_757_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v___x_761_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v_snd_755_);
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
lean_object* v___x_766_; 
lean_dec(v_fst_754_);
lean_dec(v_fst_751_);
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 0, v_e_647_);
v___x_766_ = v___x_757_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_e_647_);
lean_ctor_set(v_reuseFailAlloc_767_, 1, v_snd_755_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
}
}
}
case 6:
{
lean_object* v_binderName_775_; lean_object* v_binderType_776_; lean_object* v_body_777_; uint8_t v_binderInfo_778_; lean_object* v___x_779_; lean_object* v_fst_780_; lean_object* v_snd_781_; lean_object* v___x_782_; lean_object* v_fst_783_; lean_object* v_snd_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_808_; 
v_binderName_775_ = lean_ctor_get(v_e_647_, 0);
v_binderType_776_ = lean_ctor_get(v_e_647_, 1);
v_body_777_ = lean_ctor_get(v_e_647_, 2);
v_binderInfo_778_ = lean_ctor_get_uint8(v_e_647_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_776_);
v___x_779_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_binderType_776_, v_a_648_);
v_fst_780_ = lean_ctor_get(v___x_779_, 0);
lean_inc(v_fst_780_);
v_snd_781_ = lean_ctor_get(v___x_779_, 1);
lean_inc(v_snd_781_);
lean_dec_ref(v___x_779_);
lean_inc_ref(v_body_777_);
v___x_782_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_body_777_, v_snd_781_);
v_fst_783_ = lean_ctor_get(v___x_782_, 0);
v_snd_784_ = lean_ctor_get(v___x_782_, 1);
v_isSharedCheck_808_ = !lean_is_exclusive(v___x_782_);
if (v_isSharedCheck_808_ == 0)
{
v___x_786_ = v___x_782_;
v_isShared_787_ = v_isSharedCheck_808_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_snd_784_);
lean_inc(v_fst_783_);
lean_dec(v___x_782_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_808_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
uint8_t v___y_789_; size_t v___x_802_; size_t v___x_803_; uint8_t v___x_804_; 
v___x_802_ = lean_ptr_addr(v_binderType_776_);
v___x_803_ = lean_ptr_addr(v_fst_780_);
v___x_804_ = lean_usize_dec_eq(v___x_802_, v___x_803_);
if (v___x_804_ == 0)
{
v___y_789_ = v___x_804_;
goto v___jp_788_;
}
else
{
size_t v___x_805_; size_t v___x_806_; uint8_t v___x_807_; 
v___x_805_ = lean_ptr_addr(v_body_777_);
v___x_806_ = lean_ptr_addr(v_fst_783_);
v___x_807_ = lean_usize_dec_eq(v___x_805_, v___x_806_);
v___y_789_ = v___x_807_;
goto v___jp_788_;
}
v___jp_788_:
{
if (v___y_789_ == 0)
{
lean_object* v___x_790_; lean_object* v___x_792_; 
lean_inc(v_binderName_775_);
lean_dec_ref_known(v_e_647_, 3);
v___x_790_ = l_Lean_Expr_lam___override(v_binderName_775_, v_fst_780_, v_fst_783_, v_binderInfo_778_);
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 0, v___x_790_);
v___x_792_ = v___x_786_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v___x_790_);
lean_ctor_set(v_reuseFailAlloc_793_, 1, v_snd_784_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
else
{
uint8_t v___x_794_; 
v___x_794_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_778_, v_binderInfo_778_);
if (v___x_794_ == 0)
{
lean_object* v___x_795_; lean_object* v___x_797_; 
lean_inc(v_binderName_775_);
lean_dec_ref_known(v_e_647_, 3);
v___x_795_ = l_Lean_Expr_lam___override(v_binderName_775_, v_fst_780_, v_fst_783_, v_binderInfo_778_);
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 0, v___x_795_);
v___x_797_ = v___x_786_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v___x_795_);
lean_ctor_set(v_reuseFailAlloc_798_, 1, v_snd_784_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
return v___x_797_;
}
}
else
{
lean_object* v___x_800_; 
lean_dec(v_fst_783_);
lean_dec(v_fst_780_);
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 0, v_e_647_);
v___x_800_ = v___x_786_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_e_647_);
lean_ctor_set(v_reuseFailAlloc_801_, 1, v_snd_784_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
}
}
}
case 7:
{
lean_object* v_binderName_809_; lean_object* v_binderType_810_; lean_object* v_body_811_; uint8_t v_binderInfo_812_; lean_object* v___x_813_; lean_object* v_fst_814_; lean_object* v_snd_815_; lean_object* v___x_816_; lean_object* v_fst_817_; lean_object* v_snd_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_842_; 
v_binderName_809_ = lean_ctor_get(v_e_647_, 0);
v_binderType_810_ = lean_ctor_get(v_e_647_, 1);
v_body_811_ = lean_ctor_get(v_e_647_, 2);
v_binderInfo_812_ = lean_ctor_get_uint8(v_e_647_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_810_);
v___x_813_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_binderType_810_, v_a_648_);
v_fst_814_ = lean_ctor_get(v___x_813_, 0);
lean_inc(v_fst_814_);
v_snd_815_ = lean_ctor_get(v___x_813_, 1);
lean_inc(v_snd_815_);
lean_dec_ref(v___x_813_);
lean_inc_ref(v_body_811_);
v___x_816_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_body_811_, v_snd_815_);
v_fst_817_ = lean_ctor_get(v___x_816_, 0);
v_snd_818_ = lean_ctor_get(v___x_816_, 1);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_842_ == 0)
{
v___x_820_ = v___x_816_;
v_isShared_821_ = v_isSharedCheck_842_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_snd_818_);
lean_inc(v_fst_817_);
lean_dec(v___x_816_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_842_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
uint8_t v___y_823_; size_t v___x_836_; size_t v___x_837_; uint8_t v___x_838_; 
v___x_836_ = lean_ptr_addr(v_binderType_810_);
v___x_837_ = lean_ptr_addr(v_fst_814_);
v___x_838_ = lean_usize_dec_eq(v___x_836_, v___x_837_);
if (v___x_838_ == 0)
{
v___y_823_ = v___x_838_;
goto v___jp_822_;
}
else
{
size_t v___x_839_; size_t v___x_840_; uint8_t v___x_841_; 
v___x_839_ = lean_ptr_addr(v_body_811_);
v___x_840_ = lean_ptr_addr(v_fst_817_);
v___x_841_ = lean_usize_dec_eq(v___x_839_, v___x_840_);
v___y_823_ = v___x_841_;
goto v___jp_822_;
}
v___jp_822_:
{
if (v___y_823_ == 0)
{
lean_object* v___x_824_; lean_object* v___x_826_; 
lean_inc(v_binderName_809_);
lean_dec_ref_known(v_e_647_, 3);
v___x_824_ = l_Lean_Expr_forallE___override(v_binderName_809_, v_fst_814_, v_fst_817_, v_binderInfo_812_);
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 0, v___x_824_);
v___x_826_ = v___x_820_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v___x_824_);
lean_ctor_set(v_reuseFailAlloc_827_, 1, v_snd_818_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
else
{
uint8_t v___x_828_; 
v___x_828_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_812_, v_binderInfo_812_);
if (v___x_828_ == 0)
{
lean_object* v___x_829_; lean_object* v___x_831_; 
lean_inc(v_binderName_809_);
lean_dec_ref_known(v_e_647_, 3);
v___x_829_ = l_Lean_Expr_forallE___override(v_binderName_809_, v_fst_814_, v_fst_817_, v_binderInfo_812_);
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 0, v___x_829_);
v___x_831_ = v___x_820_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v___x_829_);
lean_ctor_set(v_reuseFailAlloc_832_, 1, v_snd_818_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
else
{
lean_object* v___x_834_; 
lean_dec(v_fst_817_);
lean_dec(v_fst_814_);
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 0, v_e_647_);
v___x_834_ = v___x_820_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_e_647_);
lean_ctor_set(v_reuseFailAlloc_835_, 1, v_snd_818_);
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
}
}
case 8:
{
lean_object* v_declName_843_; lean_object* v_type_844_; lean_object* v_value_845_; lean_object* v_body_846_; uint8_t v_nondep_847_; lean_object* v___x_848_; lean_object* v_fst_849_; lean_object* v_snd_850_; lean_object* v___x_851_; lean_object* v_fst_852_; lean_object* v_snd_853_; lean_object* v___x_854_; lean_object* v_fst_855_; lean_object* v_snd_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_882_; 
v_declName_843_ = lean_ctor_get(v_e_647_, 0);
v_type_844_ = lean_ctor_get(v_e_647_, 1);
v_value_845_ = lean_ctor_get(v_e_647_, 2);
v_body_846_ = lean_ctor_get(v_e_647_, 3);
v_nondep_847_ = lean_ctor_get_uint8(v_e_647_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_844_);
v___x_848_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_type_844_, v_a_648_);
v_fst_849_ = lean_ctor_get(v___x_848_, 0);
lean_inc(v_fst_849_);
v_snd_850_ = lean_ctor_get(v___x_848_, 1);
lean_inc(v_snd_850_);
lean_dec_ref(v___x_848_);
lean_inc_ref(v_value_845_);
v___x_851_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_value_845_, v_snd_850_);
v_fst_852_ = lean_ctor_get(v___x_851_, 0);
lean_inc(v_fst_852_);
v_snd_853_ = lean_ctor_get(v___x_851_, 1);
lean_inc(v_snd_853_);
lean_dec_ref(v___x_851_);
lean_inc_ref(v_body_846_);
v___x_854_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_body_846_, v_snd_853_);
v_fst_855_ = lean_ctor_get(v___x_854_, 0);
v_snd_856_ = lean_ctor_get(v___x_854_, 1);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_882_ == 0)
{
v___x_858_ = v___x_854_;
v_isShared_859_ = v_isSharedCheck_882_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_snd_856_);
lean_inc(v_fst_855_);
lean_dec(v___x_854_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_882_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
uint8_t v___y_861_; size_t v___x_876_; size_t v___x_877_; uint8_t v___x_878_; 
v___x_876_ = lean_ptr_addr(v_type_844_);
v___x_877_ = lean_ptr_addr(v_fst_849_);
v___x_878_ = lean_usize_dec_eq(v___x_876_, v___x_877_);
if (v___x_878_ == 0)
{
v___y_861_ = v___x_878_;
goto v___jp_860_;
}
else
{
size_t v___x_879_; size_t v___x_880_; uint8_t v___x_881_; 
v___x_879_ = lean_ptr_addr(v_value_845_);
v___x_880_ = lean_ptr_addr(v_fst_852_);
v___x_881_ = lean_usize_dec_eq(v___x_879_, v___x_880_);
v___y_861_ = v___x_881_;
goto v___jp_860_;
}
v___jp_860_:
{
if (v___y_861_ == 0)
{
lean_object* v___x_862_; lean_object* v___x_864_; 
lean_inc(v_declName_843_);
lean_dec_ref_known(v_e_647_, 4);
v___x_862_ = l_Lean_Expr_letE___override(v_declName_843_, v_fst_849_, v_fst_852_, v_fst_855_, v_nondep_847_);
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 0, v___x_862_);
v___x_864_ = v___x_858_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v___x_862_);
lean_ctor_set(v_reuseFailAlloc_865_, 1, v_snd_856_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
else
{
size_t v___x_866_; size_t v___x_867_; uint8_t v___x_868_; 
v___x_866_ = lean_ptr_addr(v_body_846_);
v___x_867_ = lean_ptr_addr(v_fst_855_);
v___x_868_ = lean_usize_dec_eq(v___x_866_, v___x_867_);
if (v___x_868_ == 0)
{
lean_object* v___x_869_; lean_object* v___x_871_; 
lean_inc(v_declName_843_);
lean_dec_ref_known(v_e_647_, 4);
v___x_869_ = l_Lean_Expr_letE___override(v_declName_843_, v_fst_849_, v_fst_852_, v_fst_855_, v_nondep_847_);
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 0, v___x_869_);
v___x_871_ = v___x_858_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v___x_869_);
lean_ctor_set(v_reuseFailAlloc_872_, 1, v_snd_856_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
else
{
lean_object* v___x_874_; 
lean_dec(v_fst_855_);
lean_dec(v_fst_852_);
lean_dec(v_fst_849_);
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 0, v_e_647_);
v___x_874_ = v___x_858_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_e_647_);
lean_ctor_set(v_reuseFailAlloc_875_, 1, v_snd_856_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
}
}
}
case 10:
{
lean_object* v_data_883_; lean_object* v_expr_884_; lean_object* v___x_885_; lean_object* v_fst_886_; lean_object* v_snd_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_901_; 
v_data_883_ = lean_ctor_get(v_e_647_, 0);
v_expr_884_ = lean_ctor_get(v_e_647_, 1);
lean_inc_ref(v_expr_884_);
v___x_885_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_expr_884_, v_a_648_);
v_fst_886_ = lean_ctor_get(v___x_885_, 0);
v_snd_887_ = lean_ctor_get(v___x_885_, 1);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_901_ == 0)
{
v___x_889_ = v___x_885_;
v_isShared_890_ = v_isSharedCheck_901_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_snd_887_);
lean_inc(v_fst_886_);
lean_dec(v___x_885_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_901_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
size_t v___x_891_; size_t v___x_892_; uint8_t v___x_893_; 
v___x_891_ = lean_ptr_addr(v_expr_884_);
v___x_892_ = lean_ptr_addr(v_fst_886_);
v___x_893_ = lean_usize_dec_eq(v___x_891_, v___x_892_);
if (v___x_893_ == 0)
{
lean_object* v___x_894_; lean_object* v___x_896_; 
lean_inc(v_data_883_);
lean_dec_ref_known(v_e_647_, 2);
v___x_894_ = l_Lean_Expr_mdata___override(v_data_883_, v_fst_886_);
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 0, v___x_894_);
v___x_896_ = v___x_889_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v___x_894_);
lean_ctor_set(v_reuseFailAlloc_897_, 1, v_snd_887_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
else
{
lean_object* v___x_899_; 
lean_dec(v_fst_886_);
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 0, v_e_647_);
v___x_899_ = v___x_889_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_e_647_);
lean_ctor_set(v_reuseFailAlloc_900_, 1, v_snd_887_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
}
case 11:
{
lean_object* v_typeName_902_; lean_object* v_idx_903_; lean_object* v_struct_904_; lean_object* v___x_905_; lean_object* v_fst_906_; lean_object* v_snd_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_921_; 
v_typeName_902_ = lean_ctor_get(v_e_647_, 0);
v_idx_903_ = lean_ctor_get(v_e_647_, 1);
v_struct_904_ = lean_ctor_get(v_e_647_, 2);
lean_inc_ref(v_struct_904_);
v___x_905_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_struct_904_, v_a_648_);
v_fst_906_ = lean_ctor_get(v___x_905_, 0);
v_snd_907_ = lean_ctor_get(v___x_905_, 1);
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_905_);
if (v_isSharedCheck_921_ == 0)
{
v___x_909_ = v___x_905_;
v_isShared_910_ = v_isSharedCheck_921_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_snd_907_);
lean_inc(v_fst_906_);
lean_dec(v___x_905_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_921_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
size_t v___x_911_; size_t v___x_912_; uint8_t v___x_913_; 
v___x_911_ = lean_ptr_addr(v_struct_904_);
v___x_912_ = lean_ptr_addr(v_fst_906_);
v___x_913_ = lean_usize_dec_eq(v___x_911_, v___x_912_);
if (v___x_913_ == 0)
{
lean_object* v___x_914_; lean_object* v___x_916_; 
lean_inc(v_idx_903_);
lean_inc(v_typeName_902_);
lean_dec_ref_known(v_e_647_, 3);
v___x_914_ = l_Lean_Expr_proj___override(v_typeName_902_, v_idx_903_, v_fst_906_);
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 0, v___x_914_);
v___x_916_ = v___x_909_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v___x_914_);
lean_ctor_set(v_reuseFailAlloc_917_, 1, v_snd_907_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
else
{
lean_object* v___x_919_; 
lean_dec(v_fst_906_);
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 0, v_e_647_);
v___x_919_ = v___x_909_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v_e_647_);
lean_ctor_set(v_reuseFailAlloc_920_, 1, v_snd_907_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
}
}
default: 
{
lean_object* v___x_922_; 
v___x_922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_922_, 0, v_e_647_);
lean_ctor_set(v___x_922_, 1, v_a_648_);
return v___x_922_;
}
}
}
else
{
lean_object* v___x_923_; 
v___x_923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_923_, 0, v_e_647_);
lean_ctor_set(v___x_923_, 1, v_a_648_);
return v___x_923_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0(lean_object* v_00_u03b2_924_, lean_object* v_m_925_, lean_object* v_a_926_){
_start:
{
lean_object* v___x_927_; 
v___x_927_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0___redArg(v_m_925_, v_a_926_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0___boxed(lean_object* v_00_u03b2_928_, lean_object* v_m_929_, lean_object* v_a_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0(v_00_u03b2_928_, v_m_929_, v_a_930_);
lean_dec(v_a_930_);
lean_dec_ref(v_m_929_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2(lean_object* v_00_u03b2_932_, lean_object* v_m_933_, lean_object* v_a_934_, lean_object* v_b_935_){
_start:
{
lean_object* v___x_936_; 
v___x_936_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2___redArg(v_m_933_, v_a_934_, v_b_935_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0(lean_object* v_00_u03b2_937_, lean_object* v_a_938_, lean_object* v_x_939_){
_start:
{
lean_object* v___x_940_; 
v___x_940_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0___redArg(v_a_938_, v_x_939_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0___boxed(lean_object* v_00_u03b2_941_, lean_object* v_a_942_, lean_object* v_x_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0(v_00_u03b2_941_, v_a_942_, v_x_943_);
lean_dec(v_x_943_);
lean_dec(v_a_942_);
return v_res_944_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3(lean_object* v_00_u03b2_945_, lean_object* v_a_946_, lean_object* v_x_947_){
_start:
{
uint8_t v___x_948_; 
v___x_948_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3___redArg(v_a_946_, v_x_947_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3___boxed(lean_object* v_00_u03b2_949_, lean_object* v_a_950_, lean_object* v_x_951_){
_start:
{
uint8_t v_res_952_; lean_object* v_r_953_; 
v_res_952_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3(v_00_u03b2_949_, v_a_950_, v_x_951_);
lean_dec(v_x_951_);
lean_dec(v_a_950_);
v_r_953_ = lean_box(v_res_952_);
return v_r_953_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4(lean_object* v_00_u03b2_954_, lean_object* v_data_955_){
_start:
{
lean_object* v___x_956_; 
v___x_956_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4___redArg(v_data_955_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__5(lean_object* v_00_u03b2_957_, lean_object* v_a_958_, lean_object* v_b_959_, lean_object* v_x_960_){
_start:
{
lean_object* v___x_961_; 
v___x_961_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__5___redArg(v_a_958_, v_b_959_, v_x_960_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_962_, lean_object* v_i_963_, lean_object* v_source_964_, lean_object* v_target_965_){
_start:
{
lean_object* v___x_966_; 
v___x_966_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4_spec__5___redArg(v_i_963_, v_source_964_, v_target_965_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4_spec__5_spec__7(lean_object* v_00_u03b2_967_, lean_object* v_x_968_, lean_object* v_x_969_){
_start:
{
lean_object* v___x_970_; 
v___x_970_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4_spec__5_spec__7___redArg(v_x_968_, v_x_969_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0___redArg(lean_object* v_e_971_, lean_object* v___y_972_){
_start:
{
uint8_t v___x_974_; uint8_t v___x_975_; 
v___x_974_ = l_Lean_Expr_hasMVar(v_e_971_);
v___x_975_ = lean_bool_not(v___x_974_);
if (v___x_975_ == 0)
{
lean_object* v___x_976_; lean_object* v_mctx_977_; lean_object* v___x_978_; lean_object* v_fst_979_; lean_object* v_snd_980_; lean_object* v___x_981_; lean_object* v_cache_982_; lean_object* v_zetaDeltaFVarIds_983_; lean_object* v_postponed_984_; lean_object* v_diag_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_994_; 
v___x_976_ = lean_st_ref_get(v___y_972_);
v_mctx_977_ = lean_ctor_get(v___x_976_, 0);
lean_inc_ref(v_mctx_977_);
lean_dec(v___x_976_);
v___x_978_ = l_Lean_instantiateMVarsCore(v_mctx_977_, v_e_971_);
v_fst_979_ = lean_ctor_get(v___x_978_, 0);
lean_inc(v_fst_979_);
v_snd_980_ = lean_ctor_get(v___x_978_, 1);
lean_inc(v_snd_980_);
lean_dec_ref(v___x_978_);
v___x_981_ = lean_st_ref_take(v___y_972_);
v_cache_982_ = lean_ctor_get(v___x_981_, 1);
v_zetaDeltaFVarIds_983_ = lean_ctor_get(v___x_981_, 2);
v_postponed_984_ = lean_ctor_get(v___x_981_, 3);
v_diag_985_ = lean_ctor_get(v___x_981_, 4);
v_isSharedCheck_994_ = !lean_is_exclusive(v___x_981_);
if (v_isSharedCheck_994_ == 0)
{
lean_object* v_unused_995_; 
v_unused_995_ = lean_ctor_get(v___x_981_, 0);
lean_dec(v_unused_995_);
v___x_987_ = v___x_981_;
v_isShared_988_ = v_isSharedCheck_994_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_diag_985_);
lean_inc(v_postponed_984_);
lean_inc(v_zetaDeltaFVarIds_983_);
lean_inc(v_cache_982_);
lean_dec(v___x_981_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_994_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_990_; 
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 0, v_snd_980_);
v___x_990_ = v___x_987_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_snd_980_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v_cache_982_);
lean_ctor_set(v_reuseFailAlloc_993_, 2, v_zetaDeltaFVarIds_983_);
lean_ctor_set(v_reuseFailAlloc_993_, 3, v_postponed_984_);
lean_ctor_set(v_reuseFailAlloc_993_, 4, v_diag_985_);
v___x_990_ = v_reuseFailAlloc_993_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_991_ = lean_st_ref_set(v___y_972_, v___x_990_);
v___x_992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_992_, 0, v_fst_979_);
return v___x_992_;
}
}
}
else
{
lean_object* v___x_996_; 
v___x_996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_996_, 0, v_e_971_);
return v___x_996_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0___redArg___boxed(lean_object* v_e_997_, lean_object* v___y_998_, lean_object* v___y_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0___redArg(v_e_997_, v___y_998_);
lean_dec(v___y_998_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0(lean_object* v_e_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_){
_start:
{
lean_object* v___x_1007_; 
v___x_1007_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0___redArg(v_e_1001_, v___y_1003_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0___boxed(lean_object* v_e_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0(v_e_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_);
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
return v_res_1014_;
}
}
static lean_object* _init_l_Lean_Meta_abstractMVars___closed__1(void){
_start:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1017_ = lean_box(0);
v___x_1018_ = lean_unsigned_to_nat(16u);
v___x_1019_ = lean_mk_array(v___x_1018_, v___x_1017_);
return v___x_1019_;
}
}
static lean_object* _init_l_Lean_Meta_abstractMVars___closed__2(void){
_start:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1020_ = lean_obj_once(&l_Lean_Meta_abstractMVars___closed__1, &l_Lean_Meta_abstractMVars___closed__1_once, _init_l_Lean_Meta_abstractMVars___closed__1);
v___x_1021_ = lean_unsigned_to_nat(0u);
v___x_1022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1021_);
lean_ctor_set(v___x_1022_, 1, v___x_1020_);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractMVars(lean_object* v_e_1023_, uint8_t v_levels_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_){
_start:
{
lean_object* v___x_1030_; lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1092_; 
v___x_1030_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0___redArg(v_e_1023_, v_a_1026_);
v_a_1031_ = lean_ctor_get(v___x_1030_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___x_1030_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1033_ = v___x_1030_;
v_isShared_1034_ = v_isSharedCheck_1092_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_1030_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1092_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v_mctx_1037_; lean_object* v_lctx_1038_; lean_object* v_ngen_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v_fst_1045_; lean_object* v_snd_1046_; lean_object* v___x_1047_; lean_object* v_ngen_1048_; lean_object* v_lctx_1049_; lean_object* v_mctx_1050_; lean_object* v_paramNames_1051_; lean_object* v_fvars_1052_; lean_object* v_mvars_1053_; lean_object* v_env_1054_; lean_object* v_nextMacroScope_1055_; lean_object* v_auxDeclNGen_1056_; lean_object* v_traceState_1057_; lean_object* v_cache_1058_; lean_object* v_messages_1059_; lean_object* v_infoState_1060_; lean_object* v_snapshotTasks_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1090_; 
v___x_1035_ = lean_st_ref_get(v_a_1026_);
v___x_1036_ = lean_st_ref_get(v_a_1028_);
v_mctx_1037_ = lean_ctor_get(v___x_1035_, 0);
lean_inc_ref(v_mctx_1037_);
lean_dec(v___x_1035_);
v_lctx_1038_ = lean_ctor_get(v_a_1025_, 2);
v_ngen_1039_ = lean_ctor_get(v___x_1036_, 2);
lean_inc_ref(v_ngen_1039_);
lean_dec(v___x_1036_);
v___x_1040_ = lean_unsigned_to_nat(0u);
v___x_1041_ = ((lean_object*)(l_Lean_Meta_abstractMVars___closed__0));
v___x_1042_ = lean_obj_once(&l_Lean_Meta_abstractMVars___closed__2, &l_Lean_Meta_abstractMVars___closed__2_once, _init_l_Lean_Meta_abstractMVars___closed__2);
lean_inc_ref(v_lctx_1038_);
v___x_1043_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v___x_1043_, 0, v_ngen_1039_);
lean_ctor_set(v___x_1043_, 1, v_lctx_1038_);
lean_ctor_set(v___x_1043_, 2, v_mctx_1037_);
lean_ctor_set(v___x_1043_, 3, v___x_1040_);
lean_ctor_set(v___x_1043_, 4, v___x_1041_);
lean_ctor_set(v___x_1043_, 5, v___x_1041_);
lean_ctor_set(v___x_1043_, 6, v___x_1041_);
lean_ctor_set(v___x_1043_, 7, v___x_1042_);
lean_ctor_set(v___x_1043_, 8, v___x_1042_);
lean_ctor_set_uint8(v___x_1043_, sizeof(void*)*9, v_levels_1024_);
v___x_1044_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_a_1031_, v___x_1043_);
v_fst_1045_ = lean_ctor_get(v___x_1044_, 0);
lean_inc(v_fst_1045_);
v_snd_1046_ = lean_ctor_get(v___x_1044_, 1);
lean_inc(v_snd_1046_);
lean_dec_ref(v___x_1044_);
v___x_1047_ = lean_st_ref_take(v_a_1028_);
v_ngen_1048_ = lean_ctor_get(v_snd_1046_, 0);
lean_inc_ref(v_ngen_1048_);
v_lctx_1049_ = lean_ctor_get(v_snd_1046_, 1);
lean_inc_ref(v_lctx_1049_);
v_mctx_1050_ = lean_ctor_get(v_snd_1046_, 2);
lean_inc_ref(v_mctx_1050_);
v_paramNames_1051_ = lean_ctor_get(v_snd_1046_, 4);
lean_inc_ref(v_paramNames_1051_);
v_fvars_1052_ = lean_ctor_get(v_snd_1046_, 5);
lean_inc_ref(v_fvars_1052_);
v_mvars_1053_ = lean_ctor_get(v_snd_1046_, 6);
lean_inc_ref(v_mvars_1053_);
lean_dec(v_snd_1046_);
v_env_1054_ = lean_ctor_get(v___x_1047_, 0);
v_nextMacroScope_1055_ = lean_ctor_get(v___x_1047_, 1);
v_auxDeclNGen_1056_ = lean_ctor_get(v___x_1047_, 3);
v_traceState_1057_ = lean_ctor_get(v___x_1047_, 4);
v_cache_1058_ = lean_ctor_get(v___x_1047_, 5);
v_messages_1059_ = lean_ctor_get(v___x_1047_, 6);
v_infoState_1060_ = lean_ctor_get(v___x_1047_, 7);
v_snapshotTasks_1061_ = lean_ctor_get(v___x_1047_, 8);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_1047_);
if (v_isSharedCheck_1090_ == 0)
{
lean_object* v_unused_1091_; 
v_unused_1091_ = lean_ctor_get(v___x_1047_, 2);
lean_dec(v_unused_1091_);
v___x_1063_ = v___x_1047_;
v_isShared_1064_ = v_isSharedCheck_1090_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_snapshotTasks_1061_);
lean_inc(v_infoState_1060_);
lean_inc(v_messages_1059_);
lean_inc(v_cache_1058_);
lean_inc(v_traceState_1057_);
lean_inc(v_auxDeclNGen_1056_);
lean_inc(v_nextMacroScope_1055_);
lean_inc(v_env_1054_);
lean_dec(v___x_1047_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1090_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1066_; 
if (v_isShared_1064_ == 0)
{
lean_ctor_set(v___x_1063_, 2, v_ngen_1048_);
v___x_1066_ = v___x_1063_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_env_1054_);
lean_ctor_set(v_reuseFailAlloc_1089_, 1, v_nextMacroScope_1055_);
lean_ctor_set(v_reuseFailAlloc_1089_, 2, v_ngen_1048_);
lean_ctor_set(v_reuseFailAlloc_1089_, 3, v_auxDeclNGen_1056_);
lean_ctor_set(v_reuseFailAlloc_1089_, 4, v_traceState_1057_);
lean_ctor_set(v_reuseFailAlloc_1089_, 5, v_cache_1058_);
lean_ctor_set(v_reuseFailAlloc_1089_, 6, v_messages_1059_);
lean_ctor_set(v_reuseFailAlloc_1089_, 7, v_infoState_1060_);
lean_ctor_set(v_reuseFailAlloc_1089_, 8, v_snapshotTasks_1061_);
v___x_1066_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v_cache_1069_; lean_object* v_zetaDeltaFVarIds_1070_; lean_object* v_postponed_1071_; lean_object* v_diag_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1087_; 
v___x_1067_ = lean_st_ref_set(v_a_1028_, v___x_1066_);
v___x_1068_ = lean_st_ref_take(v_a_1026_);
v_cache_1069_ = lean_ctor_get(v___x_1068_, 1);
v_zetaDeltaFVarIds_1070_ = lean_ctor_get(v___x_1068_, 2);
v_postponed_1071_ = lean_ctor_get(v___x_1068_, 3);
v_diag_1072_ = lean_ctor_get(v___x_1068_, 4);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1087_ == 0)
{
lean_object* v_unused_1088_; 
v_unused_1088_ = lean_ctor_get(v___x_1068_, 0);
lean_dec(v_unused_1088_);
v___x_1074_ = v___x_1068_;
v_isShared_1075_ = v_isSharedCheck_1087_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_diag_1072_);
lean_inc(v_postponed_1071_);
lean_inc(v_zetaDeltaFVarIds_1070_);
lean_inc(v_cache_1069_);
lean_dec(v___x_1068_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1087_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1077_; 
if (v_isShared_1075_ == 0)
{
lean_ctor_set(v___x_1074_, 0, v_mctx_1050_);
v___x_1077_ = v___x_1074_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_mctx_1050_);
lean_ctor_set(v_reuseFailAlloc_1086_, 1, v_cache_1069_);
lean_ctor_set(v_reuseFailAlloc_1086_, 2, v_zetaDeltaFVarIds_1070_);
lean_ctor_set(v_reuseFailAlloc_1086_, 3, v_postponed_1071_);
lean_ctor_set(v_reuseFailAlloc_1086_, 4, v_diag_1072_);
v___x_1077_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
lean_object* v___x_1078_; uint8_t v___x_1079_; uint8_t v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1084_; 
v___x_1078_ = lean_st_ref_set(v_a_1026_, v___x_1077_);
v___x_1079_ = 1;
v___x_1080_ = 0;
v___x_1081_ = l_Lean_LocalContext_mkLambda(v_lctx_1049_, v_fvars_1052_, v_fst_1045_, v___x_1079_, v___x_1080_);
lean_dec(v_fst_1045_);
lean_dec_ref(v_fvars_1052_);
v___x_1082_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1082_, 0, v_paramNames_1051_);
lean_ctor_set(v___x_1082_, 1, v_mvars_1053_);
lean_ctor_set(v___x_1082_, 2, v___x_1081_);
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 0, v___x_1082_);
v___x_1084_ = v___x_1033_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v___x_1082_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractMVars___boxed(lean_object* v_e_1093_, lean_object* v_levels_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_){
_start:
{
uint8_t v_levels_boxed_1100_; lean_object* v_res_1101_; 
v_levels_boxed_1100_ = lean_unbox(v_levels_1094_);
v_res_1101_ = l_Lean_Meta_abstractMVars(v_e_1093_, v_levels_boxed_1100_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_);
lean_dec(v_a_1098_);
lean_dec_ref(v_a_1097_);
lean_dec(v_a_1096_);
lean_dec_ref(v_a_1095_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_openAbstractMVarsResult_spec__0(size_t v_sz_1102_, size_t v_i_1103_, lean_object* v_bs_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_){
_start:
{
uint8_t v___x_1110_; 
v___x_1110_ = lean_usize_dec_lt(v_i_1103_, v_sz_1102_);
if (v___x_1110_ == 0)
{
lean_object* v___x_1111_; 
v___x_1111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1111_, 0, v_bs_1104_);
return v___x_1111_;
}
else
{
lean_object* v___x_1112_; 
v___x_1112_ = l_Lean_Meta_mkFreshLevelMVar(v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_);
if (lean_obj_tag(v___x_1112_) == 0)
{
lean_object* v_a_1113_; lean_object* v___x_1114_; lean_object* v_bs_x27_1115_; size_t v___x_1116_; size_t v___x_1117_; lean_object* v___x_1118_; 
v_a_1113_ = lean_ctor_get(v___x_1112_, 0);
lean_inc(v_a_1113_);
lean_dec_ref_known(v___x_1112_, 1);
v___x_1114_ = lean_unsigned_to_nat(0u);
v_bs_x27_1115_ = lean_array_uset(v_bs_1104_, v_i_1103_, v___x_1114_);
v___x_1116_ = ((size_t)1ULL);
v___x_1117_ = lean_usize_add(v_i_1103_, v___x_1116_);
v___x_1118_ = lean_array_uset(v_bs_x27_1115_, v_i_1103_, v_a_1113_);
v_i_1103_ = v___x_1117_;
v_bs_1104_ = v___x_1118_;
goto _start;
}
else
{
lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1127_; 
lean_dec_ref(v_bs_1104_);
v_a_1120_ = lean_ctor_get(v___x_1112_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1122_ = v___x_1112_;
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1112_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1125_; 
if (v_isShared_1123_ == 0)
{
v___x_1125_ = v___x_1122_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_a_1120_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_openAbstractMVarsResult_spec__0___boxed(lean_object* v_sz_1128_, lean_object* v_i_1129_, lean_object* v_bs_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_){
_start:
{
size_t v_sz_boxed_1136_; size_t v_i_boxed_1137_; lean_object* v_res_1138_; 
v_sz_boxed_1136_ = lean_unbox_usize(v_sz_1128_);
lean_dec(v_sz_1128_);
v_i_boxed_1137_ = lean_unbox_usize(v_i_1129_);
lean_dec(v_i_1129_);
v_res_1138_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_openAbstractMVarsResult_spec__0(v_sz_boxed_1136_, v_i_boxed_1137_, v_bs_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_);
lean_dec(v___y_1134_);
lean_dec_ref(v___y_1133_);
lean_dec(v___y_1132_);
lean_dec_ref(v___y_1131_);
return v_res_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_openAbstractMVarsResult(lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_){
_start:
{
lean_object* v_paramNames_1145_; lean_object* v_expr_1146_; size_t v_sz_1147_; size_t v___x_1148_; lean_object* v___x_1149_; 
v_paramNames_1145_ = lean_ctor_get(v_a_1139_, 0);
v_expr_1146_ = lean_ctor_get(v_a_1139_, 2);
v_sz_1147_ = lean_array_size(v_paramNames_1145_);
v___x_1148_ = ((size_t)0ULL);
lean_inc_ref(v_paramNames_1145_);
v___x_1149_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_openAbstractMVarsResult_spec__0(v_sz_1147_, v___x_1148_, v_paramNames_1145_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_);
if (lean_obj_tag(v___x_1149_) == 0)
{
lean_object* v_a_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
v_a_1150_ = lean_ctor_get(v___x_1149_, 0);
lean_inc(v_a_1150_);
lean_dec_ref_known(v___x_1149_, 1);
lean_inc_ref(v_paramNames_1145_);
v___x_1151_ = l_Lean_Expr_instantiateLevelParamsArray(v_expr_1146_, v_paramNames_1145_, v_a_1150_);
v___x_1152_ = l_Lean_Meta_AbstractMVarsResult_numMVars(v_a_1139_);
lean_dec_ref(v_a_1139_);
v___x_1153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1152_);
v___x_1154_ = l_Lean_Meta_lambdaMetaTelescope(v___x_1151_, v___x_1153_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_);
lean_dec_ref_known(v___x_1153_, 1);
lean_dec_ref(v___x_1151_);
return v___x_1154_;
}
else
{
lean_object* v_a_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1162_; 
lean_dec_ref(v_a_1139_);
v_a_1155_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1162_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1157_ = v___x_1149_;
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_a_1155_);
lean_dec(v___x_1149_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1160_; 
if (v_isShared_1158_ == 0)
{
v___x_1160_ = v___x_1157_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_a_1155_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_openAbstractMVarsResult___boxed(lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l_Lean_Meta_openAbstractMVarsResult(v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_);
lean_dec(v_a_1167_);
lean_dec_ref(v_a_1166_);
lean_dec(v_a_1165_);
lean_dec_ref(v_a_1164_);
return v_res_1169_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_AbstractMVars(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
