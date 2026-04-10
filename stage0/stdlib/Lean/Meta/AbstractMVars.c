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
lean_dec_ref(v_u_264_);
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
lean_dec_ref(v_u_264_);
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
lean_dec_ref(v_u_264_);
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
lean_dec_ref(v_u_264_);
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
lean_dec_ref(v_u_264_);
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
lean_object* v_a_353_; lean_object* v_depth_354_; lean_object* v___x_355_; uint8_t v___x_356_; 
v_a_353_ = lean_ctor_get(v_u_264_, 0);
v_depth_354_ = lean_ctor_get(v_mctx_270_, 0);
lean_inc(v_a_353_);
lean_inc_ref(v_mctx_270_);
v___x_355_ = l_Lean_MetavarContext_getLevelDepth(v_mctx_270_, v_a_353_);
v___x_356_ = lean_nat_dec_eq(v___x_355_, v_depth_354_);
lean_dec(v___x_355_);
if (v___x_356_ == 0)
{
lean_object* v___x_357_; 
v___x_357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_357_, 0, v_u_264_);
lean_ctor_set(v___x_357_, 1, v_a_265_);
return v___x_357_;
}
else
{
lean_object* v___x_358_; 
lean_inc(v_a_353_);
lean_dec_ref(v_u_264_);
v___x_358_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___redArg(v_lmap_275_, v_a_353_);
if (lean_obj_tag(v___x_358_) == 0)
{
lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_373_; 
lean_inc_ref(v_emap_276_);
lean_inc_ref(v_lmap_275_);
lean_inc_ref(v_mvars_274_);
lean_inc_ref(v_fvars_273_);
lean_inc_ref(v_paramNames_272_);
lean_inc(v_nextParamIdx_271_);
lean_inc_ref(v_mctx_270_);
lean_inc_ref(v_lctx_269_);
lean_inc_ref(v_ngen_268_);
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
lean_inc(v_nextParamIdx_271_);
v___x_363_ = l_Lean_Name_num___override(v___x_362_, v_nextParamIdx_271_);
lean_inc(v___x_363_);
v___x_364_ = l_Lean_mkLevelParam(v___x_363_);
v___x_365_ = lean_unsigned_to_nat(1u);
v___x_366_ = lean_nat_add(v_nextParamIdx_271_, v___x_365_);
lean_dec(v_nextParamIdx_271_);
v___x_367_ = lean_array_push(v_paramNames_272_, v___x_363_);
lean_inc(v___x_364_);
v___x_368_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1___redArg(v_lmap_275_, v_a_353_, v___x_364_);
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
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_ngen_268_);
lean_ctor_set(v_reuseFailAlloc_372_, 1, v_lctx_269_);
lean_ctor_set(v_reuseFailAlloc_372_, 2, v_mctx_270_);
lean_ctor_set(v_reuseFailAlloc_372_, 3, v___x_366_);
lean_ctor_set(v_reuseFailAlloc_372_, 4, v___x_367_);
lean_ctor_set(v_reuseFailAlloc_372_, 5, v_fvars_273_);
lean_ctor_set(v_reuseFailAlloc_372_, 6, v_mvars_274_);
lean_ctor_set(v_reuseFailAlloc_372_, 7, v___x_368_);
lean_ctor_set(v_reuseFailAlloc_372_, 8, v_emap_276_);
lean_ctor_set_uint8(v_reuseFailAlloc_372_, sizeof(void*)*9, v_abstractLevels_266_);
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
lean_dec_ref(v___x_358_);
v___x_384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_384_, 0, v_val_383_);
lean_ctor_set(v___x_384_, 1, v_a_265_);
return v___x_384_;
}
}
}
default: 
{
lean_object* v___x_385_; 
v___x_385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_385_, 0, v_u_264_);
lean_ctor_set(v___x_385_, 1, v_a_265_);
return v___x_385_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0(lean_object* v_00_u03b2_386_, lean_object* v_m_387_, lean_object* v_a_388_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___redArg(v_m_387_, v_a_388_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___boxed(lean_object* v_00_u03b2_390_, lean_object* v_m_391_, lean_object* v_a_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0(v_00_u03b2_390_, v_m_391_, v_a_392_);
lean_dec(v_a_392_);
lean_dec_ref(v_m_391_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1(lean_object* v_00_u03b2_394_, lean_object* v_m_395_, lean_object* v_a_396_, lean_object* v_b_397_){
_start:
{
lean_object* v___x_398_; 
v___x_398_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1___redArg(v_m_395_, v_a_396_, v_b_397_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0(lean_object* v_00_u03b2_399_, lean_object* v_a_400_, lean_object* v_x_401_){
_start:
{
lean_object* v___x_402_; 
v___x_402_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0___redArg(v_a_400_, v_x_401_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0___boxed(lean_object* v_00_u03b2_403_, lean_object* v_a_404_, lean_object* v_x_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0(v_00_u03b2_403_, v_a_404_, v_x_405_);
lean_dec(v_x_405_);
lean_dec(v_a_404_);
return v_res_406_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2(lean_object* v_00_u03b2_407_, lean_object* v_a_408_, lean_object* v_x_409_){
_start:
{
uint8_t v___x_410_; 
v___x_410_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2___redArg(v_a_408_, v_x_409_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2___boxed(lean_object* v_00_u03b2_411_, lean_object* v_a_412_, lean_object* v_x_413_){
_start:
{
uint8_t v_res_414_; lean_object* v_r_415_; 
v_res_414_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2(v_00_u03b2_411_, v_a_412_, v_x_413_);
lean_dec(v_x_413_);
lean_dec(v_a_412_);
v_r_415_ = lean_box(v_res_414_);
return v_r_415_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3(lean_object* v_00_u03b2_416_, lean_object* v_data_417_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3___redArg(v_data_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__4(lean_object* v_00_u03b2_419_, lean_object* v_a_420_, lean_object* v_b_421_, lean_object* v_x_422_){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__4___redArg(v_a_420_, v_b_421_, v_x_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_424_, lean_object* v_i_425_, lean_object* v_source_426_, lean_object* v_target_427_){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3_spec__4___redArg(v_i_425_, v_source_426_, v_target_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_429_, lean_object* v_x_430_, lean_object* v_x_431_){
_start:
{
lean_object* v___x_432_; 
v___x_432_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3_spec__4_spec__5___redArg(v_x_430_, v_x_431_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__1(lean_object* v_e_433_, lean_object* v___y_434_){
_start:
{
uint8_t v___x_435_; 
v___x_435_ = l_Lean_Expr_hasMVar(v_e_433_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; 
v___x_436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_436_, 0, v_e_433_);
lean_ctor_set(v___x_436_, 1, v___y_434_);
return v___x_436_;
}
else
{
lean_object* v_ngen_437_; lean_object* v_lctx_438_; lean_object* v_mctx_439_; lean_object* v_nextParamIdx_440_; lean_object* v_paramNames_441_; lean_object* v_fvars_442_; lean_object* v_mvars_443_; lean_object* v_lmap_444_; lean_object* v_emap_445_; uint8_t v_abstractLevels_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_463_; 
v_ngen_437_ = lean_ctor_get(v___y_434_, 0);
v_lctx_438_ = lean_ctor_get(v___y_434_, 1);
v_mctx_439_ = lean_ctor_get(v___y_434_, 2);
v_nextParamIdx_440_ = lean_ctor_get(v___y_434_, 3);
v_paramNames_441_ = lean_ctor_get(v___y_434_, 4);
v_fvars_442_ = lean_ctor_get(v___y_434_, 5);
v_mvars_443_ = lean_ctor_get(v___y_434_, 6);
v_lmap_444_ = lean_ctor_get(v___y_434_, 7);
v_emap_445_ = lean_ctor_get(v___y_434_, 8);
v_abstractLevels_446_ = lean_ctor_get_uint8(v___y_434_, sizeof(void*)*9);
v_isSharedCheck_463_ = !lean_is_exclusive(v___y_434_);
if (v_isSharedCheck_463_ == 0)
{
v___x_448_ = v___y_434_;
v_isShared_449_ = v_isSharedCheck_463_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_emap_445_);
lean_inc(v_lmap_444_);
lean_inc(v_mvars_443_);
lean_inc(v_fvars_442_);
lean_inc(v_paramNames_441_);
lean_inc(v_nextParamIdx_440_);
lean_inc(v_mctx_439_);
lean_inc(v_lctx_438_);
lean_inc(v_ngen_437_);
lean_dec(v___y_434_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_463_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_450_; lean_object* v_fst_451_; lean_object* v_snd_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_462_; 
v___x_450_ = l_Lean_instantiateMVarsCore(v_mctx_439_, v_e_433_);
v_fst_451_ = lean_ctor_get(v___x_450_, 0);
v_snd_452_ = lean_ctor_get(v___x_450_, 1);
v_isSharedCheck_462_ = !lean_is_exclusive(v___x_450_);
if (v_isSharedCheck_462_ == 0)
{
v___x_454_ = v___x_450_;
v_isShared_455_ = v_isSharedCheck_462_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_snd_452_);
lean_inc(v_fst_451_);
lean_dec(v___x_450_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_462_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_457_; 
if (v_isShared_449_ == 0)
{
lean_ctor_set(v___x_448_, 2, v_snd_452_);
v___x_457_ = v___x_448_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_ngen_437_);
lean_ctor_set(v_reuseFailAlloc_461_, 1, v_lctx_438_);
lean_ctor_set(v_reuseFailAlloc_461_, 2, v_snd_452_);
lean_ctor_set(v_reuseFailAlloc_461_, 3, v_nextParamIdx_440_);
lean_ctor_set(v_reuseFailAlloc_461_, 4, v_paramNames_441_);
lean_ctor_set(v_reuseFailAlloc_461_, 5, v_fvars_442_);
lean_ctor_set(v_reuseFailAlloc_461_, 6, v_mvars_443_);
lean_ctor_set(v_reuseFailAlloc_461_, 7, v_lmap_444_);
lean_ctor_set(v_reuseFailAlloc_461_, 8, v_emap_445_);
lean_ctor_set_uint8(v_reuseFailAlloc_461_, sizeof(void*)*9, v_abstractLevels_446_);
v___x_457_ = v_reuseFailAlloc_461_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
lean_object* v___x_459_; 
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 1, v___x_457_);
v___x_459_ = v___x_454_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_fst_451_);
lean_ctor_set(v_reuseFailAlloc_460_, 1, v___x_457_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0___redArg(lean_object* v_a_464_, lean_object* v_x_465_){
_start:
{
if (lean_obj_tag(v_x_465_) == 0)
{
lean_object* v___x_466_; 
v___x_466_ = lean_box(0);
return v___x_466_;
}
else
{
lean_object* v_key_467_; lean_object* v_value_468_; lean_object* v_tail_469_; uint8_t v___x_470_; 
v_key_467_ = lean_ctor_get(v_x_465_, 0);
v_value_468_ = lean_ctor_get(v_x_465_, 1);
v_tail_469_ = lean_ctor_get(v_x_465_, 2);
v___x_470_ = l_Lean_instBEqMVarId_beq(v_key_467_, v_a_464_);
if (v___x_470_ == 0)
{
v_x_465_ = v_tail_469_;
goto _start;
}
else
{
lean_object* v___x_472_; 
lean_inc(v_value_468_);
v___x_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_472_, 0, v_value_468_);
return v___x_472_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0___redArg___boxed(lean_object* v_a_473_, lean_object* v_x_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0___redArg(v_a_473_, v_x_474_);
lean_dec(v_x_474_);
lean_dec(v_a_473_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0___redArg(lean_object* v_m_476_, lean_object* v_a_477_){
_start:
{
lean_object* v_buckets_478_; lean_object* v___x_479_; uint64_t v___x_480_; uint64_t v___x_481_; uint64_t v___x_482_; uint64_t v_fold_483_; uint64_t v___x_484_; uint64_t v___x_485_; uint64_t v___x_486_; size_t v___x_487_; size_t v___x_488_; size_t v___x_489_; size_t v___x_490_; size_t v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v_buckets_478_ = lean_ctor_get(v_m_476_, 1);
v___x_479_ = lean_array_get_size(v_buckets_478_);
v___x_480_ = l_Lean_instHashableMVarId_hash(v_a_477_);
v___x_481_ = 32ULL;
v___x_482_ = lean_uint64_shift_right(v___x_480_, v___x_481_);
v_fold_483_ = lean_uint64_xor(v___x_480_, v___x_482_);
v___x_484_ = 16ULL;
v___x_485_ = lean_uint64_shift_right(v_fold_483_, v___x_484_);
v___x_486_ = lean_uint64_xor(v_fold_483_, v___x_485_);
v___x_487_ = lean_uint64_to_usize(v___x_486_);
v___x_488_ = lean_usize_of_nat(v___x_479_);
v___x_489_ = ((size_t)1ULL);
v___x_490_ = lean_usize_sub(v___x_488_, v___x_489_);
v___x_491_ = lean_usize_land(v___x_487_, v___x_490_);
v___x_492_ = lean_array_uget_borrowed(v_buckets_478_, v___x_491_);
v___x_493_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0___redArg(v_a_477_, v___x_492_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0___redArg___boxed(lean_object* v_m_494_, lean_object* v_a_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0___redArg(v_m_494_, v_a_495_);
lean_dec(v_a_495_);
lean_dec_ref(v_m_494_);
return v_res_496_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3___redArg(lean_object* v_a_497_, lean_object* v_x_498_){
_start:
{
if (lean_obj_tag(v_x_498_) == 0)
{
uint8_t v___x_499_; 
v___x_499_ = 0;
return v___x_499_;
}
else
{
lean_object* v_key_500_; lean_object* v_tail_501_; uint8_t v___x_502_; 
v_key_500_ = lean_ctor_get(v_x_498_, 0);
v_tail_501_ = lean_ctor_get(v_x_498_, 2);
v___x_502_ = l_Lean_instBEqMVarId_beq(v_key_500_, v_a_497_);
if (v___x_502_ == 0)
{
v_x_498_ = v_tail_501_;
goto _start;
}
else
{
return v___x_502_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3___redArg___boxed(lean_object* v_a_504_, lean_object* v_x_505_){
_start:
{
uint8_t v_res_506_; lean_object* v_r_507_; 
v_res_506_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3___redArg(v_a_504_, v_x_505_);
lean_dec(v_x_505_);
lean_dec(v_a_504_);
v_r_507_ = lean_box(v_res_506_);
return v_r_507_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__5___redArg(lean_object* v_a_508_, lean_object* v_b_509_, lean_object* v_x_510_){
_start:
{
if (lean_obj_tag(v_x_510_) == 0)
{
lean_dec(v_b_509_);
lean_dec(v_a_508_);
return v_x_510_;
}
else
{
lean_object* v_key_511_; lean_object* v_value_512_; lean_object* v_tail_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_525_; 
v_key_511_ = lean_ctor_get(v_x_510_, 0);
v_value_512_ = lean_ctor_get(v_x_510_, 1);
v_tail_513_ = lean_ctor_get(v_x_510_, 2);
v_isSharedCheck_525_ = !lean_is_exclusive(v_x_510_);
if (v_isSharedCheck_525_ == 0)
{
v___x_515_ = v_x_510_;
v_isShared_516_ = v_isSharedCheck_525_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_tail_513_);
lean_inc(v_value_512_);
lean_inc(v_key_511_);
lean_dec(v_x_510_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_525_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
uint8_t v___x_517_; 
v___x_517_ = l_Lean_instBEqMVarId_beq(v_key_511_, v_a_508_);
if (v___x_517_ == 0)
{
lean_object* v___x_518_; lean_object* v___x_520_; 
v___x_518_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__5___redArg(v_a_508_, v_b_509_, v_tail_513_);
if (v_isShared_516_ == 0)
{
lean_ctor_set(v___x_515_, 2, v___x_518_);
v___x_520_ = v___x_515_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v_key_511_);
lean_ctor_set(v_reuseFailAlloc_521_, 1, v_value_512_);
lean_ctor_set(v_reuseFailAlloc_521_, 2, v___x_518_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
else
{
lean_object* v___x_523_; 
lean_dec(v_value_512_);
lean_dec(v_key_511_);
if (v_isShared_516_ == 0)
{
lean_ctor_set(v___x_515_, 1, v_b_509_);
lean_ctor_set(v___x_515_, 0, v_a_508_);
v___x_523_ = v___x_515_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_a_508_);
lean_ctor_set(v_reuseFailAlloc_524_, 1, v_b_509_);
lean_ctor_set(v_reuseFailAlloc_524_, 2, v_tail_513_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4_spec__5_spec__7___redArg(lean_object* v_x_526_, lean_object* v_x_527_){
_start:
{
if (lean_obj_tag(v_x_527_) == 0)
{
return v_x_526_;
}
else
{
lean_object* v_key_528_; lean_object* v_value_529_; lean_object* v_tail_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_553_; 
v_key_528_ = lean_ctor_get(v_x_527_, 0);
v_value_529_ = lean_ctor_get(v_x_527_, 1);
v_tail_530_ = lean_ctor_get(v_x_527_, 2);
v_isSharedCheck_553_ = !lean_is_exclusive(v_x_527_);
if (v_isSharedCheck_553_ == 0)
{
v___x_532_ = v_x_527_;
v_isShared_533_ = v_isSharedCheck_553_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_tail_530_);
lean_inc(v_value_529_);
lean_inc(v_key_528_);
lean_dec(v_x_527_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_553_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_534_; uint64_t v___x_535_; uint64_t v___x_536_; uint64_t v___x_537_; uint64_t v_fold_538_; uint64_t v___x_539_; uint64_t v___x_540_; uint64_t v___x_541_; size_t v___x_542_; size_t v___x_543_; size_t v___x_544_; size_t v___x_545_; size_t v___x_546_; lean_object* v___x_547_; lean_object* v___x_549_; 
v___x_534_ = lean_array_get_size(v_x_526_);
v___x_535_ = l_Lean_instHashableMVarId_hash(v_key_528_);
v___x_536_ = 32ULL;
v___x_537_ = lean_uint64_shift_right(v___x_535_, v___x_536_);
v_fold_538_ = lean_uint64_xor(v___x_535_, v___x_537_);
v___x_539_ = 16ULL;
v___x_540_ = lean_uint64_shift_right(v_fold_538_, v___x_539_);
v___x_541_ = lean_uint64_xor(v_fold_538_, v___x_540_);
v___x_542_ = lean_uint64_to_usize(v___x_541_);
v___x_543_ = lean_usize_of_nat(v___x_534_);
v___x_544_ = ((size_t)1ULL);
v___x_545_ = lean_usize_sub(v___x_543_, v___x_544_);
v___x_546_ = lean_usize_land(v___x_542_, v___x_545_);
v___x_547_ = lean_array_uget_borrowed(v_x_526_, v___x_546_);
lean_inc(v___x_547_);
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 2, v___x_547_);
v___x_549_ = v___x_532_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v_key_528_);
lean_ctor_set(v_reuseFailAlloc_552_, 1, v_value_529_);
lean_ctor_set(v_reuseFailAlloc_552_, 2, v___x_547_);
v___x_549_ = v_reuseFailAlloc_552_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
lean_object* v___x_550_; 
v___x_550_ = lean_array_uset(v_x_526_, v___x_546_, v___x_549_);
v_x_526_ = v___x_550_;
v_x_527_ = v_tail_530_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4_spec__5___redArg(lean_object* v_i_554_, lean_object* v_source_555_, lean_object* v_target_556_){
_start:
{
lean_object* v___x_557_; uint8_t v___x_558_; 
v___x_557_ = lean_array_get_size(v_source_555_);
v___x_558_ = lean_nat_dec_lt(v_i_554_, v___x_557_);
if (v___x_558_ == 0)
{
lean_dec_ref(v_source_555_);
lean_dec(v_i_554_);
return v_target_556_;
}
else
{
lean_object* v_es_559_; lean_object* v___x_560_; lean_object* v_source_561_; lean_object* v_target_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v_es_559_ = lean_array_fget(v_source_555_, v_i_554_);
v___x_560_ = lean_box(0);
v_source_561_ = lean_array_fset(v_source_555_, v_i_554_, v___x_560_);
v_target_562_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4_spec__5_spec__7___redArg(v_target_556_, v_es_559_);
v___x_563_ = lean_unsigned_to_nat(1u);
v___x_564_ = lean_nat_add(v_i_554_, v___x_563_);
lean_dec(v_i_554_);
v_i_554_ = v___x_564_;
v_source_555_ = v_source_561_;
v_target_556_ = v_target_562_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4___redArg(lean_object* v_data_566_){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v_nbuckets_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_567_ = lean_array_get_size(v_data_566_);
v___x_568_ = lean_unsigned_to_nat(2u);
v_nbuckets_569_ = lean_nat_mul(v___x_567_, v___x_568_);
v___x_570_ = lean_unsigned_to_nat(0u);
v___x_571_ = lean_box(0);
v___x_572_ = lean_mk_array(v_nbuckets_569_, v___x_571_);
v___x_573_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4_spec__5___redArg(v___x_570_, v_data_566_, v___x_572_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2___redArg(lean_object* v_m_574_, lean_object* v_a_575_, lean_object* v_b_576_){
_start:
{
lean_object* v_size_577_; lean_object* v_buckets_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_621_; 
v_size_577_ = lean_ctor_get(v_m_574_, 0);
v_buckets_578_ = lean_ctor_get(v_m_574_, 1);
v_isSharedCheck_621_ = !lean_is_exclusive(v_m_574_);
if (v_isSharedCheck_621_ == 0)
{
v___x_580_ = v_m_574_;
v_isShared_581_ = v_isSharedCheck_621_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_buckets_578_);
lean_inc(v_size_577_);
lean_dec(v_m_574_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_621_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_582_; uint64_t v___x_583_; uint64_t v___x_584_; uint64_t v___x_585_; uint64_t v_fold_586_; uint64_t v___x_587_; uint64_t v___x_588_; uint64_t v___x_589_; size_t v___x_590_; size_t v___x_591_; size_t v___x_592_; size_t v___x_593_; size_t v___x_594_; lean_object* v_bkt_595_; uint8_t v___x_596_; 
v___x_582_ = lean_array_get_size(v_buckets_578_);
v___x_583_ = l_Lean_instHashableMVarId_hash(v_a_575_);
v___x_584_ = 32ULL;
v___x_585_ = lean_uint64_shift_right(v___x_583_, v___x_584_);
v_fold_586_ = lean_uint64_xor(v___x_583_, v___x_585_);
v___x_587_ = 16ULL;
v___x_588_ = lean_uint64_shift_right(v_fold_586_, v___x_587_);
v___x_589_ = lean_uint64_xor(v_fold_586_, v___x_588_);
v___x_590_ = lean_uint64_to_usize(v___x_589_);
v___x_591_ = lean_usize_of_nat(v___x_582_);
v___x_592_ = ((size_t)1ULL);
v___x_593_ = lean_usize_sub(v___x_591_, v___x_592_);
v___x_594_ = lean_usize_land(v___x_590_, v___x_593_);
v_bkt_595_ = lean_array_uget_borrowed(v_buckets_578_, v___x_594_);
v___x_596_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3___redArg(v_a_575_, v_bkt_595_);
if (v___x_596_ == 0)
{
lean_object* v___x_597_; lean_object* v_size_x27_598_; lean_object* v___x_599_; lean_object* v_buckets_x27_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; uint8_t v___x_606_; 
v___x_597_ = lean_unsigned_to_nat(1u);
v_size_x27_598_ = lean_nat_add(v_size_577_, v___x_597_);
lean_dec(v_size_577_);
lean_inc(v_bkt_595_);
v___x_599_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_599_, 0, v_a_575_);
lean_ctor_set(v___x_599_, 1, v_b_576_);
lean_ctor_set(v___x_599_, 2, v_bkt_595_);
v_buckets_x27_600_ = lean_array_uset(v_buckets_578_, v___x_594_, v___x_599_);
v___x_601_ = lean_unsigned_to_nat(4u);
v___x_602_ = lean_nat_mul(v_size_x27_598_, v___x_601_);
v___x_603_ = lean_unsigned_to_nat(3u);
v___x_604_ = lean_nat_div(v___x_602_, v___x_603_);
lean_dec(v___x_602_);
v___x_605_ = lean_array_get_size(v_buckets_x27_600_);
v___x_606_ = lean_nat_dec_le(v___x_604_, v___x_605_);
lean_dec(v___x_604_);
if (v___x_606_ == 0)
{
lean_object* v_val_607_; lean_object* v___x_609_; 
v_val_607_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4___redArg(v_buckets_x27_600_);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 1, v_val_607_);
lean_ctor_set(v___x_580_, 0, v_size_x27_598_);
v___x_609_ = v___x_580_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_size_x27_598_);
lean_ctor_set(v_reuseFailAlloc_610_, 1, v_val_607_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
else
{
lean_object* v___x_612_; 
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 1, v_buckets_x27_600_);
lean_ctor_set(v___x_580_, 0, v_size_x27_598_);
v___x_612_ = v___x_580_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_size_x27_598_);
lean_ctor_set(v_reuseFailAlloc_613_, 1, v_buckets_x27_600_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
else
{
lean_object* v___x_614_; lean_object* v_buckets_x27_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_619_; 
lean_inc(v_bkt_595_);
v___x_614_ = lean_box(0);
v_buckets_x27_615_ = lean_array_uset(v_buckets_578_, v___x_594_, v___x_614_);
v___x_616_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__5___redArg(v_a_575_, v_b_576_, v_bkt_595_);
v___x_617_ = lean_array_uset(v_buckets_x27_615_, v___x_594_, v___x_616_);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 1, v___x_617_);
v___x_619_ = v___x_580_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_size_577_);
lean_ctor_set(v_reuseFailAlloc_620_, 1, v___x_617_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__3(lean_object* v_x_622_, lean_object* v_x_623_, lean_object* v___y_624_){
_start:
{
if (lean_obj_tag(v_x_622_) == 0)
{
lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_625_ = l_List_reverse___redArg(v_x_623_);
v___x_626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_626_, 0, v___x_625_);
lean_ctor_set(v___x_626_, 1, v___y_624_);
return v___x_626_;
}
else
{
lean_object* v_head_627_; lean_object* v_tail_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_639_; 
v_head_627_ = lean_ctor_get(v_x_622_, 0);
v_tail_628_ = lean_ctor_get(v_x_622_, 1);
v_isSharedCheck_639_ = !lean_is_exclusive(v_x_622_);
if (v_isSharedCheck_639_ == 0)
{
v___x_630_ = v_x_622_;
v_isShared_631_ = v_isSharedCheck_639_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_tail_628_);
lean_inc(v_head_627_);
lean_dec(v_x_622_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_639_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v___x_632_; lean_object* v_fst_633_; lean_object* v_snd_634_; lean_object* v___x_636_; 
v___x_632_ = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(v_head_627_, v___y_624_);
v_fst_633_ = lean_ctor_get(v___x_632_, 0);
lean_inc(v_fst_633_);
v_snd_634_ = lean_ctor_get(v___x_632_, 1);
lean_inc(v_snd_634_);
lean_dec_ref(v___x_632_);
if (v_isShared_631_ == 0)
{
lean_ctor_set(v___x_630_, 1, v_x_623_);
lean_ctor_set(v___x_630_, 0, v_fst_633_);
v___x_636_ = v___x_630_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_fst_633_);
lean_ctor_set(v_reuseFailAlloc_638_, 1, v_x_623_);
v___x_636_ = v_reuseFailAlloc_638_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
v_x_622_ = v_tail_628_;
v_x_623_ = v___x_636_;
v___y_624_ = v_snd_634_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_abstractExprMVars(lean_object* v_e_643_, lean_object* v_a_644_){
_start:
{
uint8_t v___x_645_; 
v___x_645_ = l_Lean_Expr_hasMVar(v_e_643_);
if (v___x_645_ == 0)
{
lean_object* v___x_646_; 
v___x_646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_646_, 0, v_e_643_);
lean_ctor_set(v___x_646_, 1, v_a_644_);
return v___x_646_;
}
else
{
switch(lean_obj_tag(v_e_643_))
{
case 2:
{
lean_object* v_mvarId_647_; lean_object* v_mctx_648_; lean_object* v_emap_649_; lean_object* v___x_650_; lean_object* v_userName_651_; lean_object* v_type_652_; lean_object* v_depth_653_; lean_object* v_depth_654_; uint8_t v___x_655_; 
v_mvarId_647_ = lean_ctor_get(v_e_643_, 0);
v_mctx_648_ = lean_ctor_get(v_a_644_, 2);
v_emap_649_ = lean_ctor_get(v_a_644_, 8);
lean_inc(v_mvarId_647_);
lean_inc_ref(v_mctx_648_);
v___x_650_ = l_Lean_MetavarContext_getDecl(v_mctx_648_, v_mvarId_647_);
v_userName_651_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_userName_651_);
v_type_652_ = lean_ctor_get(v___x_650_, 2);
lean_inc_ref(v_type_652_);
v_depth_653_ = lean_ctor_get(v___x_650_, 3);
lean_inc(v_depth_653_);
lean_dec_ref(v___x_650_);
v_depth_654_ = lean_ctor_get(v_mctx_648_, 0);
v___x_655_ = lean_nat_dec_eq(v_depth_653_, v_depth_654_);
lean_dec(v_depth_653_);
if (v___x_655_ == 0)
{
lean_object* v___x_656_; 
lean_dec_ref(v_type_652_);
lean_dec(v_userName_651_);
v___x_656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_656_, 0, v_e_643_);
lean_ctor_set(v___x_656_, 1, v_a_644_);
return v___x_656_;
}
else
{
lean_object* v___x_657_; 
lean_inc(v_mvarId_647_);
v___x_657_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0___redArg(v_emap_649_, v_mvarId_647_);
if (lean_obj_tag(v___x_657_) == 0)
{
lean_object* v___x_658_; lean_object* v_fst_659_; lean_object* v_snd_660_; lean_object* v___x_661_; lean_object* v_fst_662_; lean_object* v_snd_663_; lean_object* v___x_664_; lean_object* v_fst_665_; lean_object* v_snd_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_704_; 
v___x_658_ = l_Lean_instantiateMVars___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__1(v_type_652_, v_a_644_);
v_fst_659_ = lean_ctor_get(v___x_658_, 0);
lean_inc(v_fst_659_);
v_snd_660_ = lean_ctor_get(v___x_658_, 1);
lean_inc(v_snd_660_);
lean_dec_ref(v___x_658_);
v___x_661_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_fst_659_, v_snd_660_);
v_fst_662_ = lean_ctor_get(v___x_661_, 0);
lean_inc(v_fst_662_);
v_snd_663_ = lean_ctor_get(v___x_661_, 1);
lean_inc(v_snd_663_);
lean_dec_ref(v___x_661_);
v___x_664_ = l_Lean_Meta_AbstractMVars_mkFreshFVarId(v_snd_663_);
v_fst_665_ = lean_ctor_get(v___x_664_, 0);
v_snd_666_ = lean_ctor_get(v___x_664_, 1);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_704_ == 0)
{
v___x_668_ = v___x_664_;
v_isShared_669_ = v_isSharedCheck_704_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_snd_666_);
lean_inc(v_fst_665_);
lean_dec(v___x_664_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_704_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_670_; lean_object* v_userName_672_; uint8_t v___x_699_; 
lean_inc(v_fst_665_);
v___x_670_ = l_Lean_mkFVar(v_fst_665_);
v___x_699_ = l_Lean_Name_isAnonymous(v_userName_651_);
if (v___x_699_ == 0)
{
v_userName_672_ = v_userName_651_;
goto v___jp_671_;
}
else
{
lean_object* v_fvars_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
lean_dec(v_userName_651_);
v_fvars_700_ = lean_ctor_get(v_snd_666_, 5);
v___x_701_ = ((lean_object*)(l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__1));
v___x_702_ = lean_array_get_size(v_fvars_700_);
v___x_703_ = lean_name_append_index_after(v___x_701_, v___x_702_);
v_userName_672_ = v___x_703_;
goto v___jp_671_;
}
v___jp_671_:
{
lean_object* v_ngen_673_; lean_object* v_lctx_674_; lean_object* v_mctx_675_; lean_object* v_nextParamIdx_676_; lean_object* v_paramNames_677_; lean_object* v_fvars_678_; lean_object* v_mvars_679_; lean_object* v_lmap_680_; lean_object* v_emap_681_; uint8_t v_abstractLevels_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_698_; 
v_ngen_673_ = lean_ctor_get(v_snd_666_, 0);
v_lctx_674_ = lean_ctor_get(v_snd_666_, 1);
v_mctx_675_ = lean_ctor_get(v_snd_666_, 2);
v_nextParamIdx_676_ = lean_ctor_get(v_snd_666_, 3);
v_paramNames_677_ = lean_ctor_get(v_snd_666_, 4);
v_fvars_678_ = lean_ctor_get(v_snd_666_, 5);
v_mvars_679_ = lean_ctor_get(v_snd_666_, 6);
v_lmap_680_ = lean_ctor_get(v_snd_666_, 7);
v_emap_681_ = lean_ctor_get(v_snd_666_, 8);
v_abstractLevels_682_ = lean_ctor_get_uint8(v_snd_666_, sizeof(void*)*9);
v_isSharedCheck_698_ = !lean_is_exclusive(v_snd_666_);
if (v_isSharedCheck_698_ == 0)
{
v___x_684_ = v_snd_666_;
v_isShared_685_ = v_isSharedCheck_698_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_emap_681_);
lean_inc(v_lmap_680_);
lean_inc(v_mvars_679_);
lean_inc(v_fvars_678_);
lean_inc(v_paramNames_677_);
lean_inc(v_nextParamIdx_676_);
lean_inc(v_mctx_675_);
lean_inc(v_lctx_674_);
lean_inc(v_ngen_673_);
lean_dec(v_snd_666_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_698_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
uint8_t v___x_686_; uint8_t v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_693_; 
v___x_686_ = 0;
v___x_687_ = 0;
v___x_688_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_674_, v_fst_665_, v_userName_672_, v_fst_662_, v___x_686_, v___x_687_);
lean_inc_ref_n(v___x_670_, 2);
v___x_689_ = lean_array_push(v_fvars_678_, v___x_670_);
v___x_690_ = lean_array_push(v_mvars_679_, v_e_643_);
v___x_691_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2___redArg(v_emap_681_, v_mvarId_647_, v___x_670_);
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 8, v___x_691_);
lean_ctor_set(v___x_684_, 6, v___x_690_);
lean_ctor_set(v___x_684_, 5, v___x_689_);
lean_ctor_set(v___x_684_, 1, v___x_688_);
v___x_693_ = v___x_684_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_ngen_673_);
lean_ctor_set(v_reuseFailAlloc_697_, 1, v___x_688_);
lean_ctor_set(v_reuseFailAlloc_697_, 2, v_mctx_675_);
lean_ctor_set(v_reuseFailAlloc_697_, 3, v_nextParamIdx_676_);
lean_ctor_set(v_reuseFailAlloc_697_, 4, v_paramNames_677_);
lean_ctor_set(v_reuseFailAlloc_697_, 5, v___x_689_);
lean_ctor_set(v_reuseFailAlloc_697_, 6, v___x_690_);
lean_ctor_set(v_reuseFailAlloc_697_, 7, v_lmap_680_);
lean_ctor_set(v_reuseFailAlloc_697_, 8, v___x_691_);
lean_ctor_set_uint8(v_reuseFailAlloc_697_, sizeof(void*)*9, v_abstractLevels_682_);
v___x_693_ = v_reuseFailAlloc_697_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
lean_object* v___x_695_; 
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 1, v___x_693_);
lean_ctor_set(v___x_668_, 0, v___x_670_);
v___x_695_ = v___x_668_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v___x_670_);
lean_ctor_set(v_reuseFailAlloc_696_, 1, v___x_693_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
}
}
}
}
else
{
lean_object* v_val_705_; lean_object* v___x_706_; 
lean_dec_ref(v_type_652_);
lean_dec(v_userName_651_);
lean_dec(v_mvarId_647_);
lean_dec_ref(v_e_643_);
v_val_705_ = lean_ctor_get(v___x_657_, 0);
lean_inc(v_val_705_);
lean_dec_ref(v___x_657_);
v___x_706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_706_, 0, v_val_705_);
lean_ctor_set(v___x_706_, 1, v_a_644_);
return v___x_706_;
}
}
}
case 3:
{
lean_object* v_u_707_; lean_object* v___x_708_; lean_object* v_fst_709_; lean_object* v_snd_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_724_; 
v_u_707_ = lean_ctor_get(v_e_643_, 0);
lean_inc(v_u_707_);
v___x_708_ = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(v_u_707_, v_a_644_);
v_fst_709_ = lean_ctor_get(v___x_708_, 0);
v_snd_710_ = lean_ctor_get(v___x_708_, 1);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_724_ == 0)
{
v___x_712_ = v___x_708_;
v_isShared_713_ = v_isSharedCheck_724_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_snd_710_);
lean_inc(v_fst_709_);
lean_dec(v___x_708_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_724_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
size_t v___x_714_; size_t v___x_715_; uint8_t v___x_716_; 
v___x_714_ = lean_ptr_addr(v_u_707_);
v___x_715_ = lean_ptr_addr(v_fst_709_);
v___x_716_ = lean_usize_dec_eq(v___x_714_, v___x_715_);
if (v___x_716_ == 0)
{
lean_object* v___x_717_; lean_object* v___x_719_; 
lean_dec_ref(v_e_643_);
v___x_717_ = l_Lean_Expr_sort___override(v_fst_709_);
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 0, v___x_717_);
v___x_719_ = v___x_712_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v___x_717_);
lean_ctor_set(v_reuseFailAlloc_720_, 1, v_snd_710_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
else
{
lean_object* v___x_722_; 
lean_dec(v_fst_709_);
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 0, v_e_643_);
v___x_722_ = v___x_712_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_e_643_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v_snd_710_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
}
case 4:
{
lean_object* v_declName_725_; lean_object* v_us_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v_fst_729_; lean_object* v_snd_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_742_; 
v_declName_725_ = lean_ctor_get(v_e_643_, 0);
v_us_726_ = lean_ctor_get(v_e_643_, 1);
v___x_727_ = lean_box(0);
lean_inc(v_us_726_);
v___x_728_ = l_List_mapM_loop___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__3(v_us_726_, v___x_727_, v_a_644_);
v_fst_729_ = lean_ctor_get(v___x_728_, 0);
v_snd_730_ = lean_ctor_get(v___x_728_, 1);
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_742_ == 0)
{
v___x_732_ = v___x_728_;
v_isShared_733_ = v_isSharedCheck_742_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_snd_730_);
lean_inc(v_fst_729_);
lean_dec(v___x_728_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_742_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
uint8_t v___x_734_; 
v___x_734_ = l_ptrEqList___redArg(v_us_726_, v_fst_729_);
if (v___x_734_ == 0)
{
lean_object* v___x_735_; lean_object* v___x_737_; 
lean_inc(v_declName_725_);
lean_dec_ref(v_e_643_);
v___x_735_ = l_Lean_Expr_const___override(v_declName_725_, v_fst_729_);
if (v_isShared_733_ == 0)
{
lean_ctor_set(v___x_732_, 0, v___x_735_);
v___x_737_ = v___x_732_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v___x_735_);
lean_ctor_set(v_reuseFailAlloc_738_, 1, v_snd_730_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
else
{
lean_object* v___x_740_; 
lean_dec(v_fst_729_);
if (v_isShared_733_ == 0)
{
lean_ctor_set(v___x_732_, 0, v_e_643_);
v___x_740_ = v___x_732_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v_e_643_);
lean_ctor_set(v_reuseFailAlloc_741_, 1, v_snd_730_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
}
}
case 5:
{
lean_object* v_fn_743_; lean_object* v_arg_744_; lean_object* v___x_745_; lean_object* v_fst_746_; lean_object* v_snd_747_; lean_object* v___x_748_; lean_object* v_fst_749_; lean_object* v_snd_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_769_; 
v_fn_743_ = lean_ctor_get(v_e_643_, 0);
v_arg_744_ = lean_ctor_get(v_e_643_, 1);
lean_inc_ref(v_fn_743_);
v___x_745_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_fn_743_, v_a_644_);
v_fst_746_ = lean_ctor_get(v___x_745_, 0);
lean_inc(v_fst_746_);
v_snd_747_ = lean_ctor_get(v___x_745_, 1);
lean_inc(v_snd_747_);
lean_dec_ref(v___x_745_);
lean_inc_ref(v_arg_744_);
v___x_748_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_arg_744_, v_snd_747_);
v_fst_749_ = lean_ctor_get(v___x_748_, 0);
v_snd_750_ = lean_ctor_get(v___x_748_, 1);
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_769_ == 0)
{
v___x_752_ = v___x_748_;
v_isShared_753_ = v_isSharedCheck_769_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_snd_750_);
lean_inc(v_fst_749_);
lean_dec(v___x_748_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_769_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
uint8_t v___y_755_; size_t v___x_763_; size_t v___x_764_; uint8_t v___x_765_; 
v___x_763_ = lean_ptr_addr(v_fn_743_);
v___x_764_ = lean_ptr_addr(v_fst_746_);
v___x_765_ = lean_usize_dec_eq(v___x_763_, v___x_764_);
if (v___x_765_ == 0)
{
v___y_755_ = v___x_765_;
goto v___jp_754_;
}
else
{
size_t v___x_766_; size_t v___x_767_; uint8_t v___x_768_; 
v___x_766_ = lean_ptr_addr(v_arg_744_);
v___x_767_ = lean_ptr_addr(v_fst_749_);
v___x_768_ = lean_usize_dec_eq(v___x_766_, v___x_767_);
v___y_755_ = v___x_768_;
goto v___jp_754_;
}
v___jp_754_:
{
if (v___y_755_ == 0)
{
lean_object* v___x_756_; lean_object* v___x_758_; 
lean_dec_ref(v_e_643_);
v___x_756_ = l_Lean_Expr_app___override(v_fst_746_, v_fst_749_);
if (v_isShared_753_ == 0)
{
lean_ctor_set(v___x_752_, 0, v___x_756_);
v___x_758_ = v___x_752_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v___x_756_);
lean_ctor_set(v_reuseFailAlloc_759_, 1, v_snd_750_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
else
{
lean_object* v___x_761_; 
lean_dec(v_fst_749_);
lean_dec(v_fst_746_);
if (v_isShared_753_ == 0)
{
lean_ctor_set(v___x_752_, 0, v_e_643_);
v___x_761_ = v___x_752_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_e_643_);
lean_ctor_set(v_reuseFailAlloc_762_, 1, v_snd_750_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
}
}
case 6:
{
lean_object* v_binderName_770_; lean_object* v_binderType_771_; lean_object* v_body_772_; uint8_t v_binderInfo_773_; lean_object* v___x_774_; lean_object* v_fst_775_; lean_object* v_snd_776_; lean_object* v___x_777_; lean_object* v_fst_778_; lean_object* v_snd_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_803_; 
v_binderName_770_ = lean_ctor_get(v_e_643_, 0);
v_binderType_771_ = lean_ctor_get(v_e_643_, 1);
v_body_772_ = lean_ctor_get(v_e_643_, 2);
v_binderInfo_773_ = lean_ctor_get_uint8(v_e_643_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_771_);
v___x_774_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_binderType_771_, v_a_644_);
v_fst_775_ = lean_ctor_get(v___x_774_, 0);
lean_inc(v_fst_775_);
v_snd_776_ = lean_ctor_get(v___x_774_, 1);
lean_inc(v_snd_776_);
lean_dec_ref(v___x_774_);
lean_inc_ref(v_body_772_);
v___x_777_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_body_772_, v_snd_776_);
v_fst_778_ = lean_ctor_get(v___x_777_, 0);
v_snd_779_ = lean_ctor_get(v___x_777_, 1);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_777_);
if (v_isSharedCheck_803_ == 0)
{
v___x_781_ = v___x_777_;
v_isShared_782_ = v_isSharedCheck_803_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_snd_779_);
lean_inc(v_fst_778_);
lean_dec(v___x_777_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_803_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
uint8_t v___y_784_; size_t v___x_797_; size_t v___x_798_; uint8_t v___x_799_; 
v___x_797_ = lean_ptr_addr(v_binderType_771_);
v___x_798_ = lean_ptr_addr(v_fst_775_);
v___x_799_ = lean_usize_dec_eq(v___x_797_, v___x_798_);
if (v___x_799_ == 0)
{
v___y_784_ = v___x_799_;
goto v___jp_783_;
}
else
{
size_t v___x_800_; size_t v___x_801_; uint8_t v___x_802_; 
v___x_800_ = lean_ptr_addr(v_body_772_);
v___x_801_ = lean_ptr_addr(v_fst_778_);
v___x_802_ = lean_usize_dec_eq(v___x_800_, v___x_801_);
v___y_784_ = v___x_802_;
goto v___jp_783_;
}
v___jp_783_:
{
if (v___y_784_ == 0)
{
lean_object* v___x_785_; lean_object* v___x_787_; 
lean_inc(v_binderName_770_);
lean_dec_ref(v_e_643_);
v___x_785_ = l_Lean_Expr_lam___override(v_binderName_770_, v_fst_775_, v_fst_778_, v_binderInfo_773_);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 0, v___x_785_);
v___x_787_ = v___x_781_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v___x_785_);
lean_ctor_set(v_reuseFailAlloc_788_, 1, v_snd_779_);
v___x_787_ = v_reuseFailAlloc_788_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
return v___x_787_;
}
}
else
{
uint8_t v___x_789_; 
v___x_789_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_773_, v_binderInfo_773_);
if (v___x_789_ == 0)
{
lean_object* v___x_790_; lean_object* v___x_792_; 
lean_inc(v_binderName_770_);
lean_dec_ref(v_e_643_);
v___x_790_ = l_Lean_Expr_lam___override(v_binderName_770_, v_fst_775_, v_fst_778_, v_binderInfo_773_);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 0, v___x_790_);
v___x_792_ = v___x_781_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v___x_790_);
lean_ctor_set(v_reuseFailAlloc_793_, 1, v_snd_779_);
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
lean_object* v___x_795_; 
lean_dec(v_fst_778_);
lean_dec(v_fst_775_);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 0, v_e_643_);
v___x_795_ = v___x_781_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_e_643_);
lean_ctor_set(v_reuseFailAlloc_796_, 1, v_snd_779_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
}
}
}
case 7:
{
lean_object* v_binderName_804_; lean_object* v_binderType_805_; lean_object* v_body_806_; uint8_t v_binderInfo_807_; lean_object* v___x_808_; lean_object* v_fst_809_; lean_object* v_snd_810_; lean_object* v___x_811_; lean_object* v_fst_812_; lean_object* v_snd_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_837_; 
v_binderName_804_ = lean_ctor_get(v_e_643_, 0);
v_binderType_805_ = lean_ctor_get(v_e_643_, 1);
v_body_806_ = lean_ctor_get(v_e_643_, 2);
v_binderInfo_807_ = lean_ctor_get_uint8(v_e_643_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_805_);
v___x_808_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_binderType_805_, v_a_644_);
v_fst_809_ = lean_ctor_get(v___x_808_, 0);
lean_inc(v_fst_809_);
v_snd_810_ = lean_ctor_get(v___x_808_, 1);
lean_inc(v_snd_810_);
lean_dec_ref(v___x_808_);
lean_inc_ref(v_body_806_);
v___x_811_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_body_806_, v_snd_810_);
v_fst_812_ = lean_ctor_get(v___x_811_, 0);
v_snd_813_ = lean_ctor_get(v___x_811_, 1);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_837_ == 0)
{
v___x_815_ = v___x_811_;
v_isShared_816_ = v_isSharedCheck_837_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_snd_813_);
lean_inc(v_fst_812_);
lean_dec(v___x_811_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_837_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
uint8_t v___y_818_; size_t v___x_831_; size_t v___x_832_; uint8_t v___x_833_; 
v___x_831_ = lean_ptr_addr(v_binderType_805_);
v___x_832_ = lean_ptr_addr(v_fst_809_);
v___x_833_ = lean_usize_dec_eq(v___x_831_, v___x_832_);
if (v___x_833_ == 0)
{
v___y_818_ = v___x_833_;
goto v___jp_817_;
}
else
{
size_t v___x_834_; size_t v___x_835_; uint8_t v___x_836_; 
v___x_834_ = lean_ptr_addr(v_body_806_);
v___x_835_ = lean_ptr_addr(v_fst_812_);
v___x_836_ = lean_usize_dec_eq(v___x_834_, v___x_835_);
v___y_818_ = v___x_836_;
goto v___jp_817_;
}
v___jp_817_:
{
if (v___y_818_ == 0)
{
lean_object* v___x_819_; lean_object* v___x_821_; 
lean_inc(v_binderName_804_);
lean_dec_ref(v_e_643_);
v___x_819_ = l_Lean_Expr_forallE___override(v_binderName_804_, v_fst_809_, v_fst_812_, v_binderInfo_807_);
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 0, v___x_819_);
v___x_821_ = v___x_815_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_819_);
lean_ctor_set(v_reuseFailAlloc_822_, 1, v_snd_813_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
else
{
uint8_t v___x_823_; 
v___x_823_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_807_, v_binderInfo_807_);
if (v___x_823_ == 0)
{
lean_object* v___x_824_; lean_object* v___x_826_; 
lean_inc(v_binderName_804_);
lean_dec_ref(v_e_643_);
v___x_824_ = l_Lean_Expr_forallE___override(v_binderName_804_, v_fst_809_, v_fst_812_, v_binderInfo_807_);
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 0, v___x_824_);
v___x_826_ = v___x_815_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v___x_824_);
lean_ctor_set(v_reuseFailAlloc_827_, 1, v_snd_813_);
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
lean_object* v___x_829_; 
lean_dec(v_fst_812_);
lean_dec(v_fst_809_);
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 0, v_e_643_);
v___x_829_ = v___x_815_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_e_643_);
lean_ctor_set(v_reuseFailAlloc_830_, 1, v_snd_813_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
}
}
}
case 8:
{
lean_object* v_declName_838_; lean_object* v_type_839_; lean_object* v_value_840_; lean_object* v_body_841_; uint8_t v_nondep_842_; lean_object* v___x_843_; lean_object* v_fst_844_; lean_object* v_snd_845_; lean_object* v___x_846_; lean_object* v_fst_847_; lean_object* v_snd_848_; lean_object* v___x_849_; lean_object* v_fst_850_; lean_object* v_snd_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_877_; 
v_declName_838_ = lean_ctor_get(v_e_643_, 0);
v_type_839_ = lean_ctor_get(v_e_643_, 1);
v_value_840_ = lean_ctor_get(v_e_643_, 2);
v_body_841_ = lean_ctor_get(v_e_643_, 3);
v_nondep_842_ = lean_ctor_get_uint8(v_e_643_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_839_);
v___x_843_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_type_839_, v_a_644_);
v_fst_844_ = lean_ctor_get(v___x_843_, 0);
lean_inc(v_fst_844_);
v_snd_845_ = lean_ctor_get(v___x_843_, 1);
lean_inc(v_snd_845_);
lean_dec_ref(v___x_843_);
lean_inc_ref(v_value_840_);
v___x_846_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_value_840_, v_snd_845_);
v_fst_847_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_fst_847_);
v_snd_848_ = lean_ctor_get(v___x_846_, 1);
lean_inc(v_snd_848_);
lean_dec_ref(v___x_846_);
lean_inc_ref(v_body_841_);
v___x_849_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_body_841_, v_snd_848_);
v_fst_850_ = lean_ctor_get(v___x_849_, 0);
v_snd_851_ = lean_ctor_get(v___x_849_, 1);
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_877_ == 0)
{
v___x_853_ = v___x_849_;
v_isShared_854_ = v_isSharedCheck_877_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_snd_851_);
lean_inc(v_fst_850_);
lean_dec(v___x_849_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_877_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
uint8_t v___y_856_; size_t v___x_871_; size_t v___x_872_; uint8_t v___x_873_; 
v___x_871_ = lean_ptr_addr(v_type_839_);
v___x_872_ = lean_ptr_addr(v_fst_844_);
v___x_873_ = lean_usize_dec_eq(v___x_871_, v___x_872_);
if (v___x_873_ == 0)
{
v___y_856_ = v___x_873_;
goto v___jp_855_;
}
else
{
size_t v___x_874_; size_t v___x_875_; uint8_t v___x_876_; 
v___x_874_ = lean_ptr_addr(v_value_840_);
v___x_875_ = lean_ptr_addr(v_fst_847_);
v___x_876_ = lean_usize_dec_eq(v___x_874_, v___x_875_);
v___y_856_ = v___x_876_;
goto v___jp_855_;
}
v___jp_855_:
{
if (v___y_856_ == 0)
{
lean_object* v___x_857_; lean_object* v___x_859_; 
lean_inc(v_declName_838_);
lean_dec_ref(v_e_643_);
v___x_857_ = l_Lean_Expr_letE___override(v_declName_838_, v_fst_844_, v_fst_847_, v_fst_850_, v_nondep_842_);
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 0, v___x_857_);
v___x_859_ = v___x_853_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v___x_857_);
lean_ctor_set(v_reuseFailAlloc_860_, 1, v_snd_851_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
else
{
size_t v___x_861_; size_t v___x_862_; uint8_t v___x_863_; 
v___x_861_ = lean_ptr_addr(v_body_841_);
v___x_862_ = lean_ptr_addr(v_fst_850_);
v___x_863_ = lean_usize_dec_eq(v___x_861_, v___x_862_);
if (v___x_863_ == 0)
{
lean_object* v___x_864_; lean_object* v___x_866_; 
lean_inc(v_declName_838_);
lean_dec_ref(v_e_643_);
v___x_864_ = l_Lean_Expr_letE___override(v_declName_838_, v_fst_844_, v_fst_847_, v_fst_850_, v_nondep_842_);
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 0, v___x_864_);
v___x_866_ = v___x_853_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v___x_864_);
lean_ctor_set(v_reuseFailAlloc_867_, 1, v_snd_851_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
else
{
lean_object* v___x_869_; 
lean_dec(v_fst_850_);
lean_dec(v_fst_847_);
lean_dec(v_fst_844_);
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 0, v_e_643_);
v___x_869_ = v___x_853_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_e_643_);
lean_ctor_set(v_reuseFailAlloc_870_, 1, v_snd_851_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
}
}
}
}
case 10:
{
lean_object* v_data_878_; lean_object* v_expr_879_; lean_object* v___x_880_; lean_object* v_fst_881_; lean_object* v_snd_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_896_; 
v_data_878_ = lean_ctor_get(v_e_643_, 0);
v_expr_879_ = lean_ctor_get(v_e_643_, 1);
lean_inc_ref(v_expr_879_);
v___x_880_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_expr_879_, v_a_644_);
v_fst_881_ = lean_ctor_get(v___x_880_, 0);
v_snd_882_ = lean_ctor_get(v___x_880_, 1);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_896_ == 0)
{
v___x_884_ = v___x_880_;
v_isShared_885_ = v_isSharedCheck_896_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_snd_882_);
lean_inc(v_fst_881_);
lean_dec(v___x_880_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_896_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
size_t v___x_886_; size_t v___x_887_; uint8_t v___x_888_; 
v___x_886_ = lean_ptr_addr(v_expr_879_);
v___x_887_ = lean_ptr_addr(v_fst_881_);
v___x_888_ = lean_usize_dec_eq(v___x_886_, v___x_887_);
if (v___x_888_ == 0)
{
lean_object* v___x_889_; lean_object* v___x_891_; 
lean_inc(v_data_878_);
lean_dec_ref(v_e_643_);
v___x_889_ = l_Lean_Expr_mdata___override(v_data_878_, v_fst_881_);
if (v_isShared_885_ == 0)
{
lean_ctor_set(v___x_884_, 0, v___x_889_);
v___x_891_ = v___x_884_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v___x_889_);
lean_ctor_set(v_reuseFailAlloc_892_, 1, v_snd_882_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
else
{
lean_object* v___x_894_; 
lean_dec(v_fst_881_);
if (v_isShared_885_ == 0)
{
lean_ctor_set(v___x_884_, 0, v_e_643_);
v___x_894_ = v___x_884_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_e_643_);
lean_ctor_set(v_reuseFailAlloc_895_, 1, v_snd_882_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
}
case 11:
{
lean_object* v_typeName_897_; lean_object* v_idx_898_; lean_object* v_struct_899_; lean_object* v___x_900_; lean_object* v_fst_901_; lean_object* v_snd_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_916_; 
v_typeName_897_ = lean_ctor_get(v_e_643_, 0);
v_idx_898_ = lean_ctor_get(v_e_643_, 1);
v_struct_899_ = lean_ctor_get(v_e_643_, 2);
lean_inc_ref(v_struct_899_);
v___x_900_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_struct_899_, v_a_644_);
v_fst_901_ = lean_ctor_get(v___x_900_, 0);
v_snd_902_ = lean_ctor_get(v___x_900_, 1);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_900_);
if (v_isSharedCheck_916_ == 0)
{
v___x_904_ = v___x_900_;
v_isShared_905_ = v_isSharedCheck_916_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_snd_902_);
lean_inc(v_fst_901_);
lean_dec(v___x_900_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_916_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
size_t v___x_906_; size_t v___x_907_; uint8_t v___x_908_; 
v___x_906_ = lean_ptr_addr(v_struct_899_);
v___x_907_ = lean_ptr_addr(v_fst_901_);
v___x_908_ = lean_usize_dec_eq(v___x_906_, v___x_907_);
if (v___x_908_ == 0)
{
lean_object* v___x_909_; lean_object* v___x_911_; 
lean_inc(v_idx_898_);
lean_inc(v_typeName_897_);
lean_dec_ref(v_e_643_);
v___x_909_ = l_Lean_Expr_proj___override(v_typeName_897_, v_idx_898_, v_fst_901_);
if (v_isShared_905_ == 0)
{
lean_ctor_set(v___x_904_, 0, v___x_909_);
v___x_911_ = v___x_904_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v___x_909_);
lean_ctor_set(v_reuseFailAlloc_912_, 1, v_snd_902_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
else
{
lean_object* v___x_914_; 
lean_dec(v_fst_901_);
if (v_isShared_905_ == 0)
{
lean_ctor_set(v___x_904_, 0, v_e_643_);
v___x_914_ = v___x_904_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_e_643_);
lean_ctor_set(v_reuseFailAlloc_915_, 1, v_snd_902_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
default: 
{
lean_object* v___x_917_; 
v___x_917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_917_, 0, v_e_643_);
lean_ctor_set(v___x_917_, 1, v_a_644_);
return v___x_917_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0(lean_object* v_00_u03b2_918_, lean_object* v_m_919_, lean_object* v_a_920_){
_start:
{
lean_object* v___x_921_; 
v___x_921_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0___redArg(v_m_919_, v_a_920_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0___boxed(lean_object* v_00_u03b2_922_, lean_object* v_m_923_, lean_object* v_a_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0(v_00_u03b2_922_, v_m_923_, v_a_924_);
lean_dec(v_a_924_);
lean_dec_ref(v_m_923_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2(lean_object* v_00_u03b2_926_, lean_object* v_m_927_, lean_object* v_a_928_, lean_object* v_b_929_){
_start:
{
lean_object* v___x_930_; 
v___x_930_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2___redArg(v_m_927_, v_a_928_, v_b_929_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0(lean_object* v_00_u03b2_931_, lean_object* v_a_932_, lean_object* v_x_933_){
_start:
{
lean_object* v___x_934_; 
v___x_934_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0___redArg(v_a_932_, v_x_933_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0___boxed(lean_object* v_00_u03b2_935_, lean_object* v_a_936_, lean_object* v_x_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0(v_00_u03b2_935_, v_a_936_, v_x_937_);
lean_dec(v_x_937_);
lean_dec(v_a_936_);
return v_res_938_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3(lean_object* v_00_u03b2_939_, lean_object* v_a_940_, lean_object* v_x_941_){
_start:
{
uint8_t v___x_942_; 
v___x_942_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3___redArg(v_a_940_, v_x_941_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3___boxed(lean_object* v_00_u03b2_943_, lean_object* v_a_944_, lean_object* v_x_945_){
_start:
{
uint8_t v_res_946_; lean_object* v_r_947_; 
v_res_946_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3(v_00_u03b2_943_, v_a_944_, v_x_945_);
lean_dec(v_x_945_);
lean_dec(v_a_944_);
v_r_947_ = lean_box(v_res_946_);
return v_r_947_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4(lean_object* v_00_u03b2_948_, lean_object* v_data_949_){
_start:
{
lean_object* v___x_950_; 
v___x_950_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4___redArg(v_data_949_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__5(lean_object* v_00_u03b2_951_, lean_object* v_a_952_, lean_object* v_b_953_, lean_object* v_x_954_){
_start:
{
lean_object* v___x_955_; 
v___x_955_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__5___redArg(v_a_952_, v_b_953_, v_x_954_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_956_, lean_object* v_i_957_, lean_object* v_source_958_, lean_object* v_target_959_){
_start:
{
lean_object* v___x_960_; 
v___x_960_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4_spec__5___redArg(v_i_957_, v_source_958_, v_target_959_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4_spec__5_spec__7(lean_object* v_00_u03b2_961_, lean_object* v_x_962_, lean_object* v_x_963_){
_start:
{
lean_object* v___x_964_; 
v___x_964_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4_spec__5_spec__7___redArg(v_x_962_, v_x_963_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0___redArg(lean_object* v_e_965_, lean_object* v___y_966_){
_start:
{
uint8_t v___x_968_; 
v___x_968_ = l_Lean_Expr_hasMVar(v_e_965_);
if (v___x_968_ == 0)
{
lean_object* v___x_969_; 
v___x_969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_969_, 0, v_e_965_);
return v___x_969_;
}
else
{
lean_object* v___x_970_; lean_object* v_mctx_971_; lean_object* v___x_972_; lean_object* v_fst_973_; lean_object* v_snd_974_; lean_object* v___x_975_; lean_object* v_cache_976_; lean_object* v_zetaDeltaFVarIds_977_; lean_object* v_postponed_978_; lean_object* v_diag_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_988_; 
v___x_970_ = lean_st_ref_get(v___y_966_);
v_mctx_971_ = lean_ctor_get(v___x_970_, 0);
lean_inc_ref(v_mctx_971_);
lean_dec(v___x_970_);
v___x_972_ = l_Lean_instantiateMVarsCore(v_mctx_971_, v_e_965_);
v_fst_973_ = lean_ctor_get(v___x_972_, 0);
lean_inc(v_fst_973_);
v_snd_974_ = lean_ctor_get(v___x_972_, 1);
lean_inc(v_snd_974_);
lean_dec_ref(v___x_972_);
v___x_975_ = lean_st_ref_take(v___y_966_);
v_cache_976_ = lean_ctor_get(v___x_975_, 1);
v_zetaDeltaFVarIds_977_ = lean_ctor_get(v___x_975_, 2);
v_postponed_978_ = lean_ctor_get(v___x_975_, 3);
v_diag_979_ = lean_ctor_get(v___x_975_, 4);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_988_ == 0)
{
lean_object* v_unused_989_; 
v_unused_989_ = lean_ctor_get(v___x_975_, 0);
lean_dec(v_unused_989_);
v___x_981_ = v___x_975_;
v_isShared_982_ = v_isSharedCheck_988_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_diag_979_);
lean_inc(v_postponed_978_);
lean_inc(v_zetaDeltaFVarIds_977_);
lean_inc(v_cache_976_);
lean_dec(v___x_975_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_988_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_984_; 
if (v_isShared_982_ == 0)
{
lean_ctor_set(v___x_981_, 0, v_snd_974_);
v___x_984_ = v___x_981_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_snd_974_);
lean_ctor_set(v_reuseFailAlloc_987_, 1, v_cache_976_);
lean_ctor_set(v_reuseFailAlloc_987_, 2, v_zetaDeltaFVarIds_977_);
lean_ctor_set(v_reuseFailAlloc_987_, 3, v_postponed_978_);
lean_ctor_set(v_reuseFailAlloc_987_, 4, v_diag_979_);
v___x_984_ = v_reuseFailAlloc_987_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_985_ = lean_st_ref_set(v___y_966_, v___x_984_);
v___x_986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_986_, 0, v_fst_973_);
return v___x_986_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0___redArg___boxed(lean_object* v_e_990_, lean_object* v___y_991_, lean_object* v___y_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0___redArg(v_e_990_, v___y_991_);
lean_dec(v___y_991_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0(lean_object* v_e_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_){
_start:
{
lean_object* v___x_1000_; 
v___x_1000_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0___redArg(v_e_994_, v___y_996_);
return v___x_1000_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0___boxed(lean_object* v_e_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_){
_start:
{
lean_object* v_res_1007_; 
v_res_1007_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0(v_e_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
lean_dec(v___y_1003_);
lean_dec_ref(v___y_1002_);
return v_res_1007_;
}
}
static lean_object* _init_l_Lean_Meta_abstractMVars___closed__1(void){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1010_ = lean_box(0);
v___x_1011_ = lean_unsigned_to_nat(16u);
v___x_1012_ = lean_mk_array(v___x_1011_, v___x_1010_);
return v___x_1012_;
}
}
static lean_object* _init_l_Lean_Meta_abstractMVars___closed__2(void){
_start:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1013_ = lean_obj_once(&l_Lean_Meta_abstractMVars___closed__1, &l_Lean_Meta_abstractMVars___closed__1_once, _init_l_Lean_Meta_abstractMVars___closed__1);
v___x_1014_ = lean_unsigned_to_nat(0u);
v___x_1015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1014_);
lean_ctor_set(v___x_1015_, 1, v___x_1013_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractMVars(lean_object* v_e_1016_, uint8_t v_levels_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_){
_start:
{
lean_object* v___x_1023_; lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1085_; 
v___x_1023_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0___redArg(v_e_1016_, v_a_1019_);
v_a_1024_ = lean_ctor_get(v___x_1023_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1026_ = v___x_1023_;
v_isShared_1027_ = v_isSharedCheck_1085_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v___x_1023_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1085_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v_mctx_1030_; lean_object* v_lctx_1031_; lean_object* v_ngen_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v_fst_1038_; lean_object* v_snd_1039_; lean_object* v___x_1040_; lean_object* v_ngen_1041_; lean_object* v_lctx_1042_; lean_object* v_mctx_1043_; lean_object* v_paramNames_1044_; lean_object* v_fvars_1045_; lean_object* v_mvars_1046_; lean_object* v_env_1047_; lean_object* v_nextMacroScope_1048_; lean_object* v_auxDeclNGen_1049_; lean_object* v_traceState_1050_; lean_object* v_cache_1051_; lean_object* v_messages_1052_; lean_object* v_infoState_1053_; lean_object* v_snapshotTasks_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1083_; 
v___x_1028_ = lean_st_ref_get(v_a_1019_);
v___x_1029_ = lean_st_ref_get(v_a_1021_);
v_mctx_1030_ = lean_ctor_get(v___x_1028_, 0);
lean_inc_ref(v_mctx_1030_);
lean_dec(v___x_1028_);
v_lctx_1031_ = lean_ctor_get(v_a_1018_, 2);
v_ngen_1032_ = lean_ctor_get(v___x_1029_, 2);
lean_inc_ref(v_ngen_1032_);
lean_dec(v___x_1029_);
v___x_1033_ = lean_unsigned_to_nat(0u);
v___x_1034_ = ((lean_object*)(l_Lean_Meta_abstractMVars___closed__0));
v___x_1035_ = lean_obj_once(&l_Lean_Meta_abstractMVars___closed__2, &l_Lean_Meta_abstractMVars___closed__2_once, _init_l_Lean_Meta_abstractMVars___closed__2);
lean_inc_ref(v_lctx_1031_);
v___x_1036_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v___x_1036_, 0, v_ngen_1032_);
lean_ctor_set(v___x_1036_, 1, v_lctx_1031_);
lean_ctor_set(v___x_1036_, 2, v_mctx_1030_);
lean_ctor_set(v___x_1036_, 3, v___x_1033_);
lean_ctor_set(v___x_1036_, 4, v___x_1034_);
lean_ctor_set(v___x_1036_, 5, v___x_1034_);
lean_ctor_set(v___x_1036_, 6, v___x_1034_);
lean_ctor_set(v___x_1036_, 7, v___x_1035_);
lean_ctor_set(v___x_1036_, 8, v___x_1035_);
lean_ctor_set_uint8(v___x_1036_, sizeof(void*)*9, v_levels_1017_);
v___x_1037_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_a_1024_, v___x_1036_);
v_fst_1038_ = lean_ctor_get(v___x_1037_, 0);
lean_inc(v_fst_1038_);
v_snd_1039_ = lean_ctor_get(v___x_1037_, 1);
lean_inc(v_snd_1039_);
lean_dec_ref(v___x_1037_);
v___x_1040_ = lean_st_ref_take(v_a_1021_);
v_ngen_1041_ = lean_ctor_get(v_snd_1039_, 0);
lean_inc_ref(v_ngen_1041_);
v_lctx_1042_ = lean_ctor_get(v_snd_1039_, 1);
lean_inc_ref(v_lctx_1042_);
v_mctx_1043_ = lean_ctor_get(v_snd_1039_, 2);
lean_inc_ref(v_mctx_1043_);
v_paramNames_1044_ = lean_ctor_get(v_snd_1039_, 4);
lean_inc_ref(v_paramNames_1044_);
v_fvars_1045_ = lean_ctor_get(v_snd_1039_, 5);
lean_inc_ref(v_fvars_1045_);
v_mvars_1046_ = lean_ctor_get(v_snd_1039_, 6);
lean_inc_ref(v_mvars_1046_);
lean_dec(v_snd_1039_);
v_env_1047_ = lean_ctor_get(v___x_1040_, 0);
v_nextMacroScope_1048_ = lean_ctor_get(v___x_1040_, 1);
v_auxDeclNGen_1049_ = lean_ctor_get(v___x_1040_, 3);
v_traceState_1050_ = lean_ctor_get(v___x_1040_, 4);
v_cache_1051_ = lean_ctor_get(v___x_1040_, 5);
v_messages_1052_ = lean_ctor_get(v___x_1040_, 6);
v_infoState_1053_ = lean_ctor_get(v___x_1040_, 7);
v_snapshotTasks_1054_ = lean_ctor_get(v___x_1040_, 8);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_1040_);
if (v_isSharedCheck_1083_ == 0)
{
lean_object* v_unused_1084_; 
v_unused_1084_ = lean_ctor_get(v___x_1040_, 2);
lean_dec(v_unused_1084_);
v___x_1056_ = v___x_1040_;
v_isShared_1057_ = v_isSharedCheck_1083_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_snapshotTasks_1054_);
lean_inc(v_infoState_1053_);
lean_inc(v_messages_1052_);
lean_inc(v_cache_1051_);
lean_inc(v_traceState_1050_);
lean_inc(v_auxDeclNGen_1049_);
lean_inc(v_nextMacroScope_1048_);
lean_inc(v_env_1047_);
lean_dec(v___x_1040_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1083_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___x_1059_; 
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 2, v_ngen_1041_);
v___x_1059_ = v___x_1056_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_env_1047_);
lean_ctor_set(v_reuseFailAlloc_1082_, 1, v_nextMacroScope_1048_);
lean_ctor_set(v_reuseFailAlloc_1082_, 2, v_ngen_1041_);
lean_ctor_set(v_reuseFailAlloc_1082_, 3, v_auxDeclNGen_1049_);
lean_ctor_set(v_reuseFailAlloc_1082_, 4, v_traceState_1050_);
lean_ctor_set(v_reuseFailAlloc_1082_, 5, v_cache_1051_);
lean_ctor_set(v_reuseFailAlloc_1082_, 6, v_messages_1052_);
lean_ctor_set(v_reuseFailAlloc_1082_, 7, v_infoState_1053_);
lean_ctor_set(v_reuseFailAlloc_1082_, 8, v_snapshotTasks_1054_);
v___x_1059_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v_cache_1062_; lean_object* v_zetaDeltaFVarIds_1063_; lean_object* v_postponed_1064_; lean_object* v_diag_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1080_; 
v___x_1060_ = lean_st_ref_set(v_a_1021_, v___x_1059_);
v___x_1061_ = lean_st_ref_take(v_a_1019_);
v_cache_1062_ = lean_ctor_get(v___x_1061_, 1);
v_zetaDeltaFVarIds_1063_ = lean_ctor_get(v___x_1061_, 2);
v_postponed_1064_ = lean_ctor_get(v___x_1061_, 3);
v_diag_1065_ = lean_ctor_get(v___x_1061_, 4);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_1061_);
if (v_isSharedCheck_1080_ == 0)
{
lean_object* v_unused_1081_; 
v_unused_1081_ = lean_ctor_get(v___x_1061_, 0);
lean_dec(v_unused_1081_);
v___x_1067_ = v___x_1061_;
v_isShared_1068_ = v_isSharedCheck_1080_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_diag_1065_);
lean_inc(v_postponed_1064_);
lean_inc(v_zetaDeltaFVarIds_1063_);
lean_inc(v_cache_1062_);
lean_dec(v___x_1061_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1080_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1070_; 
if (v_isShared_1068_ == 0)
{
lean_ctor_set(v___x_1067_, 0, v_mctx_1043_);
v___x_1070_ = v___x_1067_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_mctx_1043_);
lean_ctor_set(v_reuseFailAlloc_1079_, 1, v_cache_1062_);
lean_ctor_set(v_reuseFailAlloc_1079_, 2, v_zetaDeltaFVarIds_1063_);
lean_ctor_set(v_reuseFailAlloc_1079_, 3, v_postponed_1064_);
lean_ctor_set(v_reuseFailAlloc_1079_, 4, v_diag_1065_);
v___x_1070_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
lean_object* v___x_1071_; uint8_t v___x_1072_; uint8_t v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1077_; 
v___x_1071_ = lean_st_ref_set(v_a_1019_, v___x_1070_);
v___x_1072_ = 1;
v___x_1073_ = 0;
v___x_1074_ = l_Lean_LocalContext_mkLambda(v_lctx_1042_, v_fvars_1045_, v_fst_1038_, v___x_1072_, v___x_1073_);
lean_dec(v_fst_1038_);
lean_dec_ref(v_fvars_1045_);
v___x_1075_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1075_, 0, v_paramNames_1044_);
lean_ctor_set(v___x_1075_, 1, v_mvars_1046_);
lean_ctor_set(v___x_1075_, 2, v___x_1074_);
if (v_isShared_1027_ == 0)
{
lean_ctor_set(v___x_1026_, 0, v___x_1075_);
v___x_1077_ = v___x_1026_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v___x_1075_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
return v___x_1077_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractMVars___boxed(lean_object* v_e_1086_, lean_object* v_levels_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_){
_start:
{
uint8_t v_levels_boxed_1093_; lean_object* v_res_1094_; 
v_levels_boxed_1093_ = lean_unbox(v_levels_1087_);
v_res_1094_ = l_Lean_Meta_abstractMVars(v_e_1086_, v_levels_boxed_1093_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_);
lean_dec(v_a_1091_);
lean_dec_ref(v_a_1090_);
lean_dec(v_a_1089_);
lean_dec_ref(v_a_1088_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_openAbstractMVarsResult_spec__0(size_t v_sz_1095_, size_t v_i_1096_, lean_object* v_bs_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
uint8_t v___x_1103_; 
v___x_1103_ = lean_usize_dec_lt(v_i_1096_, v_sz_1095_);
if (v___x_1103_ == 0)
{
lean_object* v___x_1104_; 
v___x_1104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1104_, 0, v_bs_1097_);
return v___x_1104_;
}
else
{
lean_object* v___x_1105_; 
v___x_1105_ = l_Lean_Meta_mkFreshLevelMVar(v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_);
if (lean_obj_tag(v___x_1105_) == 0)
{
lean_object* v_a_1106_; lean_object* v___x_1107_; lean_object* v_bs_x27_1108_; size_t v___x_1109_; size_t v___x_1110_; lean_object* v___x_1111_; 
v_a_1106_ = lean_ctor_get(v___x_1105_, 0);
lean_inc(v_a_1106_);
lean_dec_ref(v___x_1105_);
v___x_1107_ = lean_unsigned_to_nat(0u);
v_bs_x27_1108_ = lean_array_uset(v_bs_1097_, v_i_1096_, v___x_1107_);
v___x_1109_ = ((size_t)1ULL);
v___x_1110_ = lean_usize_add(v_i_1096_, v___x_1109_);
v___x_1111_ = lean_array_uset(v_bs_x27_1108_, v_i_1096_, v_a_1106_);
v_i_1096_ = v___x_1110_;
v_bs_1097_ = v___x_1111_;
goto _start;
}
else
{
lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1120_; 
lean_dec_ref(v_bs_1097_);
v_a_1113_ = lean_ctor_get(v___x_1105_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1115_ = v___x_1105_;
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v___x_1105_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1118_; 
if (v_isShared_1116_ == 0)
{
v___x_1118_ = v___x_1115_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_a_1113_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_openAbstractMVarsResult_spec__0___boxed(lean_object* v_sz_1121_, lean_object* v_i_1122_, lean_object* v_bs_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_){
_start:
{
size_t v_sz_boxed_1129_; size_t v_i_boxed_1130_; lean_object* v_res_1131_; 
v_sz_boxed_1129_ = lean_unbox_usize(v_sz_1121_);
lean_dec(v_sz_1121_);
v_i_boxed_1130_ = lean_unbox_usize(v_i_1122_);
lean_dec(v_i_1122_);
v_res_1131_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_openAbstractMVarsResult_spec__0(v_sz_boxed_1129_, v_i_boxed_1130_, v_bs_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_openAbstractMVarsResult(lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_){
_start:
{
lean_object* v_paramNames_1138_; lean_object* v_expr_1139_; size_t v_sz_1140_; size_t v___x_1141_; lean_object* v___x_1142_; 
v_paramNames_1138_ = lean_ctor_get(v_a_1132_, 0);
v_expr_1139_ = lean_ctor_get(v_a_1132_, 2);
v_sz_1140_ = lean_array_size(v_paramNames_1138_);
v___x_1141_ = ((size_t)0ULL);
lean_inc_ref(v_paramNames_1138_);
v___x_1142_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_openAbstractMVarsResult_spec__0(v_sz_1140_, v___x_1141_, v_paramNames_1138_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_);
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_object* v_a_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
v_a_1143_ = lean_ctor_get(v___x_1142_, 0);
lean_inc(v_a_1143_);
lean_dec_ref(v___x_1142_);
lean_inc_ref(v_paramNames_1138_);
v___x_1144_ = l_Lean_Expr_instantiateLevelParamsArray(v_expr_1139_, v_paramNames_1138_, v_a_1143_);
v___x_1145_ = l_Lean_Meta_AbstractMVarsResult_numMVars(v_a_1132_);
lean_dec_ref(v_a_1132_);
v___x_1146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1145_);
v___x_1147_ = l_Lean_Meta_lambdaMetaTelescope(v___x_1144_, v___x_1146_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_);
lean_dec_ref(v___x_1146_);
lean_dec_ref(v___x_1144_);
return v___x_1147_;
}
else
{
lean_object* v_a_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1155_; 
lean_dec_ref(v_a_1132_);
v_a_1148_ = lean_ctor_get(v___x_1142_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1150_ = v___x_1142_;
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_a_1148_);
lean_dec(v___x_1142_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1153_; 
if (v_isShared_1151_ == 0)
{
v___x_1153_ = v___x_1150_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_a_1148_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_openAbstractMVarsResult___boxed(lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = l_Lean_Meta_openAbstractMVarsResult(v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_);
lean_dec(v_a_1160_);
lean_dec_ref(v_a_1159_);
lean_dec(v_a_1158_);
lean_dec_ref(v_a_1157_);
return v_res_1162_;
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
