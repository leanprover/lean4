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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v_nbuckets_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_144_ = lean_array_get_size(v_data_143_);
v___x_145_ = lean_unsigned_to_nat(2u);
v_nbuckets_146_ = lean_nat_mul(v___x_144_, v___x_145_);
v___x_147_ = lean_unsigned_to_nat(0u);
v___x_148_ = lean_box(0);
v___x_149_ = lean_mk_array(v_nbuckets_146_, v___x_148_);
v___x_150_ = lean_array_propagate_mark(v_data_143_, v___x_149_);
v___x_151_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3_spec__4___redArg(v___x_147_, v_data_143_, v___x_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__4___redArg(lean_object* v_a_152_, lean_object* v_b_153_, lean_object* v_x_154_){
_start:
{
if (lean_obj_tag(v_x_154_) == 0)
{
lean_dec(v_b_153_);
lean_dec(v_a_152_);
return v_x_154_;
}
else
{
lean_object* v_key_155_; lean_object* v_value_156_; lean_object* v_tail_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_169_; 
v_key_155_ = lean_ctor_get(v_x_154_, 0);
v_value_156_ = lean_ctor_get(v_x_154_, 1);
v_tail_157_ = lean_ctor_get(v_x_154_, 2);
v_isSharedCheck_169_ = !lean_is_exclusive(v_x_154_);
if (v_isSharedCheck_169_ == 0)
{
v___x_159_ = v_x_154_;
v_isShared_160_ = v_isSharedCheck_169_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_tail_157_);
lean_inc(v_value_156_);
lean_inc(v_key_155_);
lean_dec(v_x_154_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_169_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
uint8_t v___x_161_; 
v___x_161_ = l_Lean_instBEqLevelMVarId_beq(v_key_155_, v_a_152_);
if (v___x_161_ == 0)
{
lean_object* v___x_162_; lean_object* v___x_164_; 
v___x_162_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__4___redArg(v_a_152_, v_b_153_, v_tail_157_);
if (v_isShared_160_ == 0)
{
lean_ctor_set(v___x_159_, 2, v___x_162_);
v___x_164_ = v___x_159_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v_key_155_);
lean_ctor_set(v_reuseFailAlloc_165_, 1, v_value_156_);
lean_ctor_set(v_reuseFailAlloc_165_, 2, v___x_162_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
else
{
lean_object* v___x_167_; 
lean_dec(v_value_156_);
lean_dec(v_key_155_);
if (v_isShared_160_ == 0)
{
lean_ctor_set(v___x_159_, 1, v_b_153_);
lean_ctor_set(v___x_159_, 0, v_a_152_);
v___x_167_ = v___x_159_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_a_152_);
lean_ctor_set(v_reuseFailAlloc_168_, 1, v_b_153_);
lean_ctor_set(v_reuseFailAlloc_168_, 2, v_tail_157_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2___redArg(lean_object* v_a_170_, lean_object* v_x_171_){
_start:
{
if (lean_obj_tag(v_x_171_) == 0)
{
uint8_t v___x_172_; 
v___x_172_ = 0;
return v___x_172_;
}
else
{
lean_object* v_key_173_; lean_object* v_tail_174_; uint8_t v___x_175_; 
v_key_173_ = lean_ctor_get(v_x_171_, 0);
v_tail_174_ = lean_ctor_get(v_x_171_, 2);
v___x_175_ = l_Lean_instBEqLevelMVarId_beq(v_key_173_, v_a_170_);
if (v___x_175_ == 0)
{
v_x_171_ = v_tail_174_;
goto _start;
}
else
{
return v___x_175_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2___redArg___boxed(lean_object* v_a_177_, lean_object* v_x_178_){
_start:
{
uint8_t v_res_179_; lean_object* v_r_180_; 
v_res_179_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2___redArg(v_a_177_, v_x_178_);
lean_dec(v_x_178_);
lean_dec(v_a_177_);
v_r_180_ = lean_box(v_res_179_);
return v_r_180_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1___redArg(lean_object* v_m_181_, lean_object* v_a_182_, lean_object* v_b_183_){
_start:
{
lean_object* v_size_184_; lean_object* v_buckets_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_228_; 
v_size_184_ = lean_ctor_get(v_m_181_, 0);
v_buckets_185_ = lean_ctor_get(v_m_181_, 1);
v_isSharedCheck_228_ = !lean_is_exclusive(v_m_181_);
if (v_isSharedCheck_228_ == 0)
{
v___x_187_ = v_m_181_;
v_isShared_188_ = v_isSharedCheck_228_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_buckets_185_);
lean_inc(v_size_184_);
lean_dec(v_m_181_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_228_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_189_; uint64_t v___x_190_; uint64_t v___x_191_; uint64_t v___x_192_; uint64_t v_fold_193_; uint64_t v___x_194_; uint64_t v___x_195_; uint64_t v___x_196_; size_t v___x_197_; size_t v___x_198_; size_t v___x_199_; size_t v___x_200_; size_t v___x_201_; lean_object* v_bkt_202_; uint8_t v___x_203_; 
v___x_189_ = lean_array_get_size(v_buckets_185_);
v___x_190_ = l_Lean_instHashableLevelMVarId_hash(v_a_182_);
v___x_191_ = 32ULL;
v___x_192_ = lean_uint64_shift_right(v___x_190_, v___x_191_);
v_fold_193_ = lean_uint64_xor(v___x_190_, v___x_192_);
v___x_194_ = 16ULL;
v___x_195_ = lean_uint64_shift_right(v_fold_193_, v___x_194_);
v___x_196_ = lean_uint64_xor(v_fold_193_, v___x_195_);
v___x_197_ = lean_uint64_to_usize(v___x_196_);
v___x_198_ = lean_usize_of_nat(v___x_189_);
v___x_199_ = ((size_t)1ULL);
v___x_200_ = lean_usize_sub(v___x_198_, v___x_199_);
v___x_201_ = lean_usize_land(v___x_197_, v___x_200_);
v_bkt_202_ = lean_array_uget_borrowed(v_buckets_185_, v___x_201_);
v___x_203_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2___redArg(v_a_182_, v_bkt_202_);
if (v___x_203_ == 0)
{
lean_object* v___x_204_; lean_object* v_size_x27_205_; lean_object* v___x_206_; lean_object* v_buckets_x27_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; uint8_t v___x_213_; 
v___x_204_ = lean_unsigned_to_nat(1u);
v_size_x27_205_ = lean_nat_add(v_size_184_, v___x_204_);
lean_dec(v_size_184_);
lean_inc(v_bkt_202_);
v___x_206_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_206_, 0, v_a_182_);
lean_ctor_set(v___x_206_, 1, v_b_183_);
lean_ctor_set(v___x_206_, 2, v_bkt_202_);
v_buckets_x27_207_ = lean_array_uset(v_buckets_185_, v___x_201_, v___x_206_);
v___x_208_ = lean_unsigned_to_nat(4u);
v___x_209_ = lean_nat_mul(v_size_x27_205_, v___x_208_);
v___x_210_ = lean_unsigned_to_nat(3u);
v___x_211_ = lean_nat_div(v___x_209_, v___x_210_);
lean_dec(v___x_209_);
v___x_212_ = lean_array_get_size(v_buckets_x27_207_);
v___x_213_ = lean_nat_dec_le(v___x_211_, v___x_212_);
lean_dec(v___x_211_);
if (v___x_213_ == 0)
{
lean_object* v_val_214_; lean_object* v___x_216_; 
v_val_214_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3___redArg(v_buckets_x27_207_);
if (v_isShared_188_ == 0)
{
lean_ctor_set(v___x_187_, 1, v_val_214_);
lean_ctor_set(v___x_187_, 0, v_size_x27_205_);
v___x_216_ = v___x_187_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v_size_x27_205_);
lean_ctor_set(v_reuseFailAlloc_217_, 1, v_val_214_);
v___x_216_ = v_reuseFailAlloc_217_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
return v___x_216_;
}
}
else
{
lean_object* v___x_219_; 
if (v_isShared_188_ == 0)
{
lean_ctor_set(v___x_187_, 1, v_buckets_x27_207_);
lean_ctor_set(v___x_187_, 0, v_size_x27_205_);
v___x_219_ = v___x_187_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v_size_x27_205_);
lean_ctor_set(v_reuseFailAlloc_220_, 1, v_buckets_x27_207_);
v___x_219_ = v_reuseFailAlloc_220_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
return v___x_219_;
}
}
}
else
{
lean_object* v___x_221_; lean_object* v_buckets_x27_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_226_; 
lean_inc(v_bkt_202_);
v___x_221_ = lean_box(0);
v_buckets_x27_222_ = lean_array_uset(v_buckets_185_, v___x_201_, v___x_221_);
v___x_223_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__4___redArg(v_a_182_, v_b_183_, v_bkt_202_);
v___x_224_ = lean_array_uset(v_buckets_x27_222_, v___x_201_, v___x_223_);
if (v_isShared_188_ == 0)
{
lean_ctor_set(v___x_187_, 1, v___x_224_);
v___x_226_ = v___x_187_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v_size_184_);
lean_ctor_set(v_reuseFailAlloc_227_, 1, v___x_224_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
return v___x_226_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0___redArg(lean_object* v_a_229_, lean_object* v_x_230_){
_start:
{
if (lean_obj_tag(v_x_230_) == 0)
{
lean_object* v___x_231_; 
v___x_231_ = lean_box(0);
return v___x_231_;
}
else
{
lean_object* v_key_232_; lean_object* v_value_233_; lean_object* v_tail_234_; uint8_t v___x_235_; 
v_key_232_ = lean_ctor_get(v_x_230_, 0);
v_value_233_ = lean_ctor_get(v_x_230_, 1);
v_tail_234_ = lean_ctor_get(v_x_230_, 2);
v___x_235_ = l_Lean_instBEqLevelMVarId_beq(v_key_232_, v_a_229_);
if (v___x_235_ == 0)
{
v_x_230_ = v_tail_234_;
goto _start;
}
else
{
lean_object* v___x_237_; 
lean_inc(v_value_233_);
v___x_237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_237_, 0, v_value_233_);
return v___x_237_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0___redArg___boxed(lean_object* v_a_238_, lean_object* v_x_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0___redArg(v_a_238_, v_x_239_);
lean_dec(v_x_239_);
lean_dec(v_a_238_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___redArg(lean_object* v_m_241_, lean_object* v_a_242_){
_start:
{
lean_object* v_buckets_243_; lean_object* v___x_244_; uint64_t v___x_245_; uint64_t v___x_246_; uint64_t v___x_247_; uint64_t v_fold_248_; uint64_t v___x_249_; uint64_t v___x_250_; uint64_t v___x_251_; size_t v___x_252_; size_t v___x_253_; size_t v___x_254_; size_t v___x_255_; size_t v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v_buckets_243_ = lean_ctor_get(v_m_241_, 1);
v___x_244_ = lean_array_get_size(v_buckets_243_);
v___x_245_ = l_Lean_instHashableLevelMVarId_hash(v_a_242_);
v___x_246_ = 32ULL;
v___x_247_ = lean_uint64_shift_right(v___x_245_, v___x_246_);
v_fold_248_ = lean_uint64_xor(v___x_245_, v___x_247_);
v___x_249_ = 16ULL;
v___x_250_ = lean_uint64_shift_right(v_fold_248_, v___x_249_);
v___x_251_ = lean_uint64_xor(v_fold_248_, v___x_250_);
v___x_252_ = lean_uint64_to_usize(v___x_251_);
v___x_253_ = lean_usize_of_nat(v___x_244_);
v___x_254_ = ((size_t)1ULL);
v___x_255_ = lean_usize_sub(v___x_253_, v___x_254_);
v___x_256_ = lean_usize_land(v___x_252_, v___x_255_);
v___x_257_ = lean_array_uget_borrowed(v_buckets_243_, v___x_256_);
v___x_258_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0___redArg(v_a_242_, v___x_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___redArg___boxed(lean_object* v_m_259_, lean_object* v_a_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___redArg(v_m_259_, v_a_260_);
lean_dec(v_a_260_);
lean_dec_ref(v_m_259_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(lean_object* v_u_265_, lean_object* v_a_266_){
_start:
{
uint8_t v_abstractLevels_267_; 
v_abstractLevels_267_ = lean_ctor_get_uint8(v_a_266_, sizeof(void*)*9);
if (v_abstractLevels_267_ == 0)
{
lean_object* v___x_268_; 
v___x_268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_268_, 0, v_u_265_);
lean_ctor_set(v___x_268_, 1, v_a_266_);
return v___x_268_;
}
else
{
lean_object* v_ngen_269_; lean_object* v_lctx_270_; lean_object* v_mctx_271_; lean_object* v_nextParamIdx_272_; lean_object* v_paramNames_273_; lean_object* v_fvars_274_; lean_object* v_mvars_275_; lean_object* v_lmap_276_; lean_object* v_emap_277_; uint8_t v___x_278_; 
v_ngen_269_ = lean_ctor_get(v_a_266_, 0);
v_lctx_270_ = lean_ctor_get(v_a_266_, 1);
v_mctx_271_ = lean_ctor_get(v_a_266_, 2);
v_nextParamIdx_272_ = lean_ctor_get(v_a_266_, 3);
v_paramNames_273_ = lean_ctor_get(v_a_266_, 4);
v_fvars_274_ = lean_ctor_get(v_a_266_, 5);
v_mvars_275_ = lean_ctor_get(v_a_266_, 6);
v_lmap_276_ = lean_ctor_get(v_a_266_, 7);
v_emap_277_ = lean_ctor_get(v_a_266_, 8);
v___x_278_ = l_Lean_Level_hasMVar(v_u_265_);
if (v___x_278_ == 0)
{
lean_object* v___x_279_; 
v___x_279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_279_, 0, v_u_265_);
lean_ctor_set(v___x_279_, 1, v_a_266_);
return v___x_279_;
}
else
{
switch(lean_obj_tag(v_u_265_))
{
case 1:
{
lean_object* v_a_280_; lean_object* v___x_281_; lean_object* v_fst_282_; lean_object* v_snd_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_297_; 
v_a_280_ = lean_ctor_get(v_u_265_, 0);
lean_inc(v_a_280_);
v___x_281_ = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(v_a_280_, v_a_266_);
v_fst_282_ = lean_ctor_get(v___x_281_, 0);
v_snd_283_ = lean_ctor_get(v___x_281_, 1);
v_isSharedCheck_297_ = !lean_is_exclusive(v___x_281_);
if (v_isSharedCheck_297_ == 0)
{
v___x_285_ = v___x_281_;
v_isShared_286_ = v_isSharedCheck_297_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_snd_283_);
lean_inc(v_fst_282_);
lean_dec(v___x_281_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_297_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
size_t v___x_287_; size_t v___x_288_; uint8_t v___x_289_; 
v___x_287_ = lean_ptr_addr(v_a_280_);
v___x_288_ = lean_ptr_addr(v_fst_282_);
v___x_289_ = lean_usize_dec_eq(v___x_287_, v___x_288_);
if (v___x_289_ == 0)
{
lean_object* v___x_290_; lean_object* v___x_292_; 
lean_dec_ref_known(v_u_265_, 1);
v___x_290_ = l_Lean_Level_succ___override(v_fst_282_);
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 0, v___x_290_);
v___x_292_ = v___x_285_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v___x_290_);
lean_ctor_set(v_reuseFailAlloc_293_, 1, v_snd_283_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
else
{
lean_object* v___x_295_; 
lean_dec(v_fst_282_);
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 0, v_u_265_);
v___x_295_ = v___x_285_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v_u_265_);
lean_ctor_set(v_reuseFailAlloc_296_, 1, v_snd_283_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
}
}
case 2:
{
lean_object* v_a_298_; lean_object* v_a_299_; lean_object* v___x_300_; lean_object* v_fst_301_; lean_object* v_snd_302_; lean_object* v___x_303_; lean_object* v_fst_304_; lean_object* v_snd_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_327_; 
v_a_298_ = lean_ctor_get(v_u_265_, 0);
v_a_299_ = lean_ctor_get(v_u_265_, 1);
lean_inc(v_a_298_);
v___x_300_ = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(v_a_298_, v_a_266_);
v_fst_301_ = lean_ctor_get(v___x_300_, 0);
lean_inc(v_fst_301_);
v_snd_302_ = lean_ctor_get(v___x_300_, 1);
lean_inc(v_snd_302_);
lean_dec_ref(v___x_300_);
lean_inc(v_a_299_);
v___x_303_ = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(v_a_299_, v_snd_302_);
v_fst_304_ = lean_ctor_get(v___x_303_, 0);
v_snd_305_ = lean_ctor_get(v___x_303_, 1);
v_isSharedCheck_327_ = !lean_is_exclusive(v___x_303_);
if (v_isSharedCheck_327_ == 0)
{
v___x_307_ = v___x_303_;
v_isShared_308_ = v_isSharedCheck_327_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_snd_305_);
lean_inc(v_fst_304_);
lean_dec(v___x_303_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_327_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
size_t v___x_309_; size_t v___x_310_; uint8_t v___x_311_; 
v___x_309_ = lean_ptr_addr(v_a_298_);
v___x_310_ = lean_ptr_addr(v_fst_301_);
v___x_311_ = lean_usize_dec_eq(v___x_309_, v___x_310_);
if (v___x_311_ == 0)
{
lean_object* v___x_312_; lean_object* v___x_314_; 
lean_dec_ref_known(v_u_265_, 2);
v___x_312_ = l_Lean_mkLevelMax_x27(v_fst_301_, v_fst_304_);
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 0, v___x_312_);
v___x_314_ = v___x_307_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v___x_312_);
lean_ctor_set(v_reuseFailAlloc_315_, 1, v_snd_305_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
else
{
size_t v___x_316_; size_t v___x_317_; uint8_t v___x_318_; 
v___x_316_ = lean_ptr_addr(v_a_299_);
v___x_317_ = lean_ptr_addr(v_fst_304_);
v___x_318_ = lean_usize_dec_eq(v___x_316_, v___x_317_);
if (v___x_318_ == 0)
{
lean_object* v___x_319_; lean_object* v___x_321_; 
lean_dec_ref_known(v_u_265_, 2);
v___x_319_ = l_Lean_mkLevelMax_x27(v_fst_301_, v_fst_304_);
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 0, v___x_319_);
v___x_321_ = v___x_307_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v___x_319_);
lean_ctor_set(v_reuseFailAlloc_322_, 1, v_snd_305_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
else
{
lean_object* v___x_323_; lean_object* v___x_325_; 
v___x_323_ = l_Lean_simpLevelMax_x27(v_fst_301_, v_fst_304_, v_u_265_);
lean_dec_ref_known(v_u_265_, 2);
lean_dec(v_fst_304_);
lean_dec(v_fst_301_);
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 0, v___x_323_);
v___x_325_ = v___x_307_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v___x_323_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v_snd_305_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
}
}
}
case 3:
{
lean_object* v_a_328_; lean_object* v_a_329_; lean_object* v___x_330_; lean_object* v_fst_331_; lean_object* v_snd_332_; lean_object* v___x_333_; lean_object* v_fst_334_; lean_object* v_snd_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_357_; 
v_a_328_ = lean_ctor_get(v_u_265_, 0);
v_a_329_ = lean_ctor_get(v_u_265_, 1);
lean_inc(v_a_328_);
v___x_330_ = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(v_a_328_, v_a_266_);
v_fst_331_ = lean_ctor_get(v___x_330_, 0);
lean_inc(v_fst_331_);
v_snd_332_ = lean_ctor_get(v___x_330_, 1);
lean_inc(v_snd_332_);
lean_dec_ref(v___x_330_);
lean_inc(v_a_329_);
v___x_333_ = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(v_a_329_, v_snd_332_);
v_fst_334_ = lean_ctor_get(v___x_333_, 0);
v_snd_335_ = lean_ctor_get(v___x_333_, 1);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_357_ == 0)
{
v___x_337_ = v___x_333_;
v_isShared_338_ = v_isSharedCheck_357_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_snd_335_);
lean_inc(v_fst_334_);
lean_dec(v___x_333_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_357_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
size_t v___x_339_; size_t v___x_340_; uint8_t v___x_341_; 
v___x_339_ = lean_ptr_addr(v_a_328_);
v___x_340_ = lean_ptr_addr(v_fst_331_);
v___x_341_ = lean_usize_dec_eq(v___x_339_, v___x_340_);
if (v___x_341_ == 0)
{
lean_object* v___x_342_; lean_object* v___x_344_; 
lean_dec_ref_known(v_u_265_, 2);
v___x_342_ = l_Lean_mkLevelIMax_x27(v_fst_331_, v_fst_334_);
if (v_isShared_338_ == 0)
{
lean_ctor_set(v___x_337_, 0, v___x_342_);
v___x_344_ = v___x_337_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v___x_342_);
lean_ctor_set(v_reuseFailAlloc_345_, 1, v_snd_335_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
else
{
size_t v___x_346_; size_t v___x_347_; uint8_t v___x_348_; 
v___x_346_ = lean_ptr_addr(v_a_329_);
v___x_347_ = lean_ptr_addr(v_fst_334_);
v___x_348_ = lean_usize_dec_eq(v___x_346_, v___x_347_);
if (v___x_348_ == 0)
{
lean_object* v___x_349_; lean_object* v___x_351_; 
lean_dec_ref_known(v_u_265_, 2);
v___x_349_ = l_Lean_mkLevelIMax_x27(v_fst_331_, v_fst_334_);
if (v_isShared_338_ == 0)
{
lean_ctor_set(v___x_337_, 0, v___x_349_);
v___x_351_ = v___x_337_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v___x_349_);
lean_ctor_set(v_reuseFailAlloc_352_, 1, v_snd_335_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
return v___x_351_;
}
}
else
{
lean_object* v___x_353_; lean_object* v___x_355_; 
v___x_353_ = l_Lean_simpLevelIMax_x27(v_fst_331_, v_fst_334_, v_u_265_);
lean_dec_ref_known(v_u_265_, 2);
if (v_isShared_338_ == 0)
{
lean_ctor_set(v___x_337_, 0, v___x_353_);
v___x_355_ = v___x_337_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v___x_353_);
lean_ctor_set(v_reuseFailAlloc_356_, 1, v_snd_335_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
}
}
}
case 5:
{
lean_object* v_a_358_; lean_object* v_depth_359_; lean_object* v___x_360_; uint8_t v___x_361_; 
v_a_358_ = lean_ctor_get(v_u_265_, 0);
v_depth_359_ = lean_ctor_get(v_mctx_271_, 0);
lean_inc(v_a_358_);
v___x_360_ = l_Lean_MetavarContext_getLevelDepth(v_mctx_271_, v_a_358_);
v___x_361_ = lean_nat_dec_eq(v___x_360_, v_depth_359_);
lean_dec(v___x_360_);
if (v___x_361_ == 0)
{
lean_object* v___x_362_; 
v___x_362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_362_, 0, v_u_265_);
lean_ctor_set(v___x_362_, 1, v_a_266_);
return v___x_362_;
}
else
{
lean_object* v___x_363_; 
lean_inc(v_a_358_);
lean_dec_ref_known(v_u_265_, 1);
v___x_363_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___redArg(v_lmap_276_, v_a_358_);
if (lean_obj_tag(v___x_363_) == 0)
{
lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_378_; 
lean_inc_ref(v_emap_277_);
lean_inc_ref(v_lmap_276_);
lean_inc_ref(v_mvars_275_);
lean_inc_ref(v_fvars_274_);
lean_inc_ref(v_paramNames_273_);
lean_inc(v_nextParamIdx_272_);
lean_inc_ref(v_mctx_271_);
lean_inc_ref(v_lctx_270_);
lean_inc_ref(v_ngen_269_);
v_isSharedCheck_378_ = !lean_is_exclusive(v_a_266_);
if (v_isSharedCheck_378_ == 0)
{
lean_object* v_unused_379_; lean_object* v_unused_380_; lean_object* v_unused_381_; lean_object* v_unused_382_; lean_object* v_unused_383_; lean_object* v_unused_384_; lean_object* v_unused_385_; lean_object* v_unused_386_; lean_object* v_unused_387_; 
v_unused_379_ = lean_ctor_get(v_a_266_, 8);
lean_dec(v_unused_379_);
v_unused_380_ = lean_ctor_get(v_a_266_, 7);
lean_dec(v_unused_380_);
v_unused_381_ = lean_ctor_get(v_a_266_, 6);
lean_dec(v_unused_381_);
v_unused_382_ = lean_ctor_get(v_a_266_, 5);
lean_dec(v_unused_382_);
v_unused_383_ = lean_ctor_get(v_a_266_, 4);
lean_dec(v_unused_383_);
v_unused_384_ = lean_ctor_get(v_a_266_, 3);
lean_dec(v_unused_384_);
v_unused_385_ = lean_ctor_get(v_a_266_, 2);
lean_dec(v_unused_385_);
v_unused_386_ = lean_ctor_get(v_a_266_, 1);
lean_dec(v_unused_386_);
v_unused_387_ = lean_ctor_get(v_a_266_, 0);
lean_dec(v_unused_387_);
v___x_365_ = v_a_266_;
v_isShared_366_ = v_isSharedCheck_378_;
goto v_resetjp_364_;
}
else
{
lean_dec(v_a_266_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_378_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_375_; 
v___x_367_ = ((lean_object*)(l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___closed__1));
lean_inc(v_nextParamIdx_272_);
v___x_368_ = l_Lean_Name_num___override(v___x_367_, v_nextParamIdx_272_);
lean_inc(v___x_368_);
v___x_369_ = l_Lean_mkLevelParam(v___x_368_);
v___x_370_ = lean_unsigned_to_nat(1u);
v___x_371_ = lean_nat_add(v_nextParamIdx_272_, v___x_370_);
lean_dec(v_nextParamIdx_272_);
v___x_372_ = lean_array_push(v_paramNames_273_, v___x_368_);
lean_inc(v___x_369_);
v___x_373_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1___redArg(v_lmap_276_, v_a_358_, v___x_369_);
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 7, v___x_373_);
lean_ctor_set(v___x_365_, 4, v___x_372_);
lean_ctor_set(v___x_365_, 3, v___x_371_);
v___x_375_ = v___x_365_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_ngen_269_);
lean_ctor_set(v_reuseFailAlloc_377_, 1, v_lctx_270_);
lean_ctor_set(v_reuseFailAlloc_377_, 2, v_mctx_271_);
lean_ctor_set(v_reuseFailAlloc_377_, 3, v___x_371_);
lean_ctor_set(v_reuseFailAlloc_377_, 4, v___x_372_);
lean_ctor_set(v_reuseFailAlloc_377_, 5, v_fvars_274_);
lean_ctor_set(v_reuseFailAlloc_377_, 6, v_mvars_275_);
lean_ctor_set(v_reuseFailAlloc_377_, 7, v___x_373_);
lean_ctor_set(v_reuseFailAlloc_377_, 8, v_emap_277_);
lean_ctor_set_uint8(v_reuseFailAlloc_377_, sizeof(void*)*9, v_abstractLevels_267_);
v___x_375_ = v_reuseFailAlloc_377_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
lean_object* v___x_376_; 
v___x_376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_376_, 0, v___x_369_);
lean_ctor_set(v___x_376_, 1, v___x_375_);
return v___x_376_;
}
}
}
else
{
lean_object* v_val_388_; lean_object* v___x_389_; 
lean_dec(v_a_358_);
v_val_388_ = lean_ctor_get(v___x_363_, 0);
lean_inc(v_val_388_);
lean_dec_ref_known(v___x_363_, 1);
v___x_389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_389_, 0, v_val_388_);
lean_ctor_set(v___x_389_, 1, v_a_266_);
return v___x_389_;
}
}
}
default: 
{
lean_object* v___x_390_; 
v___x_390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_390_, 0, v_u_265_);
lean_ctor_set(v___x_390_, 1, v_a_266_);
return v___x_390_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0(lean_object* v_00_u03b2_391_, lean_object* v_m_392_, lean_object* v_a_393_){
_start:
{
lean_object* v___x_394_; 
v___x_394_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___redArg(v_m_392_, v_a_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___boxed(lean_object* v_00_u03b2_395_, lean_object* v_m_396_, lean_object* v_a_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0(v_00_u03b2_395_, v_m_396_, v_a_397_);
lean_dec(v_a_397_);
lean_dec_ref(v_m_396_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1(lean_object* v_00_u03b2_399_, lean_object* v_m_400_, lean_object* v_a_401_, lean_object* v_b_402_){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1___redArg(v_m_400_, v_a_401_, v_b_402_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0(lean_object* v_00_u03b2_404_, lean_object* v_a_405_, lean_object* v_x_406_){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0___redArg(v_a_405_, v_x_406_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0___boxed(lean_object* v_00_u03b2_408_, lean_object* v_a_409_, lean_object* v_x_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0(v_00_u03b2_408_, v_a_409_, v_x_410_);
lean_dec(v_x_410_);
lean_dec(v_a_409_);
return v_res_411_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2(lean_object* v_00_u03b2_412_, lean_object* v_a_413_, lean_object* v_x_414_){
_start:
{
uint8_t v___x_415_; 
v___x_415_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2___redArg(v_a_413_, v_x_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2___boxed(lean_object* v_00_u03b2_416_, lean_object* v_a_417_, lean_object* v_x_418_){
_start:
{
uint8_t v_res_419_; lean_object* v_r_420_; 
v_res_419_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2(v_00_u03b2_416_, v_a_417_, v_x_418_);
lean_dec(v_x_418_);
lean_dec(v_a_417_);
v_r_420_ = lean_box(v_res_419_);
return v_r_420_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3(lean_object* v_00_u03b2_421_, lean_object* v_data_422_){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3___redArg(v_data_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__4(lean_object* v_00_u03b2_424_, lean_object* v_a_425_, lean_object* v_b_426_, lean_object* v_x_427_){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__4___redArg(v_a_425_, v_b_426_, v_x_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_429_, lean_object* v_i_430_, lean_object* v_source_431_, lean_object* v_target_432_){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3_spec__4___redArg(v_i_430_, v_source_431_, v_target_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_434_, lean_object* v_x_435_, lean_object* v_x_436_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3_spec__4_spec__5___redArg(v_x_435_, v_x_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__1(lean_object* v_e_438_, lean_object* v___y_439_){
_start:
{
uint8_t v___x_440_; 
v___x_440_ = l_Lean_Expr_hasMVar(v_e_438_);
if (v___x_440_ == 0)
{
lean_object* v___x_441_; 
v___x_441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_441_, 0, v_e_438_);
lean_ctor_set(v___x_441_, 1, v___y_439_);
return v___x_441_;
}
else
{
lean_object* v_ngen_442_; lean_object* v_lctx_443_; lean_object* v_mctx_444_; lean_object* v_nextParamIdx_445_; lean_object* v_paramNames_446_; lean_object* v_fvars_447_; lean_object* v_mvars_448_; lean_object* v_lmap_449_; lean_object* v_emap_450_; uint8_t v_abstractLevels_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_468_; 
v_ngen_442_ = lean_ctor_get(v___y_439_, 0);
v_lctx_443_ = lean_ctor_get(v___y_439_, 1);
v_mctx_444_ = lean_ctor_get(v___y_439_, 2);
v_nextParamIdx_445_ = lean_ctor_get(v___y_439_, 3);
v_paramNames_446_ = lean_ctor_get(v___y_439_, 4);
v_fvars_447_ = lean_ctor_get(v___y_439_, 5);
v_mvars_448_ = lean_ctor_get(v___y_439_, 6);
v_lmap_449_ = lean_ctor_get(v___y_439_, 7);
v_emap_450_ = lean_ctor_get(v___y_439_, 8);
v_abstractLevels_451_ = lean_ctor_get_uint8(v___y_439_, sizeof(void*)*9);
v_isSharedCheck_468_ = !lean_is_exclusive(v___y_439_);
if (v_isSharedCheck_468_ == 0)
{
v___x_453_ = v___y_439_;
v_isShared_454_ = v_isSharedCheck_468_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_emap_450_);
lean_inc(v_lmap_449_);
lean_inc(v_mvars_448_);
lean_inc(v_fvars_447_);
lean_inc(v_paramNames_446_);
lean_inc(v_nextParamIdx_445_);
lean_inc(v_mctx_444_);
lean_inc(v_lctx_443_);
lean_inc(v_ngen_442_);
lean_dec(v___y_439_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_468_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_455_; lean_object* v_fst_456_; lean_object* v_snd_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_467_; 
v___x_455_ = l_Lean_instantiateMVarsCore(v_mctx_444_, v_e_438_);
v_fst_456_ = lean_ctor_get(v___x_455_, 0);
v_snd_457_ = lean_ctor_get(v___x_455_, 1);
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_455_);
if (v_isSharedCheck_467_ == 0)
{
v___x_459_ = v___x_455_;
v_isShared_460_ = v_isSharedCheck_467_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_snd_457_);
lean_inc(v_fst_456_);
lean_dec(v___x_455_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_467_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_462_; 
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 2, v_snd_457_);
v___x_462_ = v___x_453_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_ngen_442_);
lean_ctor_set(v_reuseFailAlloc_466_, 1, v_lctx_443_);
lean_ctor_set(v_reuseFailAlloc_466_, 2, v_snd_457_);
lean_ctor_set(v_reuseFailAlloc_466_, 3, v_nextParamIdx_445_);
lean_ctor_set(v_reuseFailAlloc_466_, 4, v_paramNames_446_);
lean_ctor_set(v_reuseFailAlloc_466_, 5, v_fvars_447_);
lean_ctor_set(v_reuseFailAlloc_466_, 6, v_mvars_448_);
lean_ctor_set(v_reuseFailAlloc_466_, 7, v_lmap_449_);
lean_ctor_set(v_reuseFailAlloc_466_, 8, v_emap_450_);
lean_ctor_set_uint8(v_reuseFailAlloc_466_, sizeof(void*)*9, v_abstractLevels_451_);
v___x_462_ = v_reuseFailAlloc_466_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
lean_object* v___x_464_; 
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 1, v___x_462_);
v___x_464_ = v___x_459_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_fst_456_);
lean_ctor_set(v_reuseFailAlloc_465_, 1, v___x_462_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0___redArg(lean_object* v_a_469_, lean_object* v_x_470_){
_start:
{
if (lean_obj_tag(v_x_470_) == 0)
{
lean_object* v___x_471_; 
v___x_471_ = lean_box(0);
return v___x_471_;
}
else
{
lean_object* v_key_472_; lean_object* v_value_473_; lean_object* v_tail_474_; uint8_t v___x_475_; 
v_key_472_ = lean_ctor_get(v_x_470_, 0);
v_value_473_ = lean_ctor_get(v_x_470_, 1);
v_tail_474_ = lean_ctor_get(v_x_470_, 2);
v___x_475_ = l_Lean_instBEqMVarId_beq(v_key_472_, v_a_469_);
if (v___x_475_ == 0)
{
v_x_470_ = v_tail_474_;
goto _start;
}
else
{
lean_object* v___x_477_; 
lean_inc(v_value_473_);
v___x_477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_477_, 0, v_value_473_);
return v___x_477_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0___redArg___boxed(lean_object* v_a_478_, lean_object* v_x_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0___redArg(v_a_478_, v_x_479_);
lean_dec(v_x_479_);
lean_dec(v_a_478_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0___redArg(lean_object* v_m_481_, lean_object* v_a_482_){
_start:
{
lean_object* v_buckets_483_; lean_object* v___x_484_; uint64_t v___x_485_; uint64_t v___x_486_; uint64_t v___x_487_; uint64_t v_fold_488_; uint64_t v___x_489_; uint64_t v___x_490_; uint64_t v___x_491_; size_t v___x_492_; size_t v___x_493_; size_t v___x_494_; size_t v___x_495_; size_t v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v_buckets_483_ = lean_ctor_get(v_m_481_, 1);
v___x_484_ = lean_array_get_size(v_buckets_483_);
v___x_485_ = l_Lean_instHashableMVarId_hash(v_a_482_);
v___x_486_ = 32ULL;
v___x_487_ = lean_uint64_shift_right(v___x_485_, v___x_486_);
v_fold_488_ = lean_uint64_xor(v___x_485_, v___x_487_);
v___x_489_ = 16ULL;
v___x_490_ = lean_uint64_shift_right(v_fold_488_, v___x_489_);
v___x_491_ = lean_uint64_xor(v_fold_488_, v___x_490_);
v___x_492_ = lean_uint64_to_usize(v___x_491_);
v___x_493_ = lean_usize_of_nat(v___x_484_);
v___x_494_ = ((size_t)1ULL);
v___x_495_ = lean_usize_sub(v___x_493_, v___x_494_);
v___x_496_ = lean_usize_land(v___x_492_, v___x_495_);
v___x_497_ = lean_array_uget_borrowed(v_buckets_483_, v___x_496_);
v___x_498_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0___redArg(v_a_482_, v___x_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0___redArg___boxed(lean_object* v_m_499_, lean_object* v_a_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0___redArg(v_m_499_, v_a_500_);
lean_dec(v_a_500_);
lean_dec_ref(v_m_499_);
return v_res_501_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3___redArg(lean_object* v_a_502_, lean_object* v_x_503_){
_start:
{
if (lean_obj_tag(v_x_503_) == 0)
{
uint8_t v___x_504_; 
v___x_504_ = 0;
return v___x_504_;
}
else
{
lean_object* v_key_505_; lean_object* v_tail_506_; uint8_t v___x_507_; 
v_key_505_ = lean_ctor_get(v_x_503_, 0);
v_tail_506_ = lean_ctor_get(v_x_503_, 2);
v___x_507_ = l_Lean_instBEqMVarId_beq(v_key_505_, v_a_502_);
if (v___x_507_ == 0)
{
v_x_503_ = v_tail_506_;
goto _start;
}
else
{
return v___x_507_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3___redArg___boxed(lean_object* v_a_509_, lean_object* v_x_510_){
_start:
{
uint8_t v_res_511_; lean_object* v_r_512_; 
v_res_511_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3___redArg(v_a_509_, v_x_510_);
lean_dec(v_x_510_);
lean_dec(v_a_509_);
v_r_512_ = lean_box(v_res_511_);
return v_r_512_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__5___redArg(lean_object* v_a_513_, lean_object* v_b_514_, lean_object* v_x_515_){
_start:
{
if (lean_obj_tag(v_x_515_) == 0)
{
lean_dec(v_b_514_);
lean_dec(v_a_513_);
return v_x_515_;
}
else
{
lean_object* v_key_516_; lean_object* v_value_517_; lean_object* v_tail_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_530_; 
v_key_516_ = lean_ctor_get(v_x_515_, 0);
v_value_517_ = lean_ctor_get(v_x_515_, 1);
v_tail_518_ = lean_ctor_get(v_x_515_, 2);
v_isSharedCheck_530_ = !lean_is_exclusive(v_x_515_);
if (v_isSharedCheck_530_ == 0)
{
v___x_520_ = v_x_515_;
v_isShared_521_ = v_isSharedCheck_530_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_tail_518_);
lean_inc(v_value_517_);
lean_inc(v_key_516_);
lean_dec(v_x_515_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_530_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
uint8_t v___x_522_; 
v___x_522_ = l_Lean_instBEqMVarId_beq(v_key_516_, v_a_513_);
if (v___x_522_ == 0)
{
lean_object* v___x_523_; lean_object* v___x_525_; 
v___x_523_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__5___redArg(v_a_513_, v_b_514_, v_tail_518_);
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 2, v___x_523_);
v___x_525_ = v___x_520_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v_key_516_);
lean_ctor_set(v_reuseFailAlloc_526_, 1, v_value_517_);
lean_ctor_set(v_reuseFailAlloc_526_, 2, v___x_523_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
else
{
lean_object* v___x_528_; 
lean_dec(v_value_517_);
lean_dec(v_key_516_);
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 1, v_b_514_);
lean_ctor_set(v___x_520_, 0, v_a_513_);
v___x_528_ = v___x_520_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_a_513_);
lean_ctor_set(v_reuseFailAlloc_529_, 1, v_b_514_);
lean_ctor_set(v_reuseFailAlloc_529_, 2, v_tail_518_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4_spec__5_spec__7___redArg(lean_object* v_x_531_, lean_object* v_x_532_){
_start:
{
if (lean_obj_tag(v_x_532_) == 0)
{
return v_x_531_;
}
else
{
lean_object* v_key_533_; lean_object* v_value_534_; lean_object* v_tail_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_558_; 
v_key_533_ = lean_ctor_get(v_x_532_, 0);
v_value_534_ = lean_ctor_get(v_x_532_, 1);
v_tail_535_ = lean_ctor_get(v_x_532_, 2);
v_isSharedCheck_558_ = !lean_is_exclusive(v_x_532_);
if (v_isSharedCheck_558_ == 0)
{
v___x_537_ = v_x_532_;
v_isShared_538_ = v_isSharedCheck_558_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_tail_535_);
lean_inc(v_value_534_);
lean_inc(v_key_533_);
lean_dec(v_x_532_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_558_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_539_; uint64_t v___x_540_; uint64_t v___x_541_; uint64_t v___x_542_; uint64_t v_fold_543_; uint64_t v___x_544_; uint64_t v___x_545_; uint64_t v___x_546_; size_t v___x_547_; size_t v___x_548_; size_t v___x_549_; size_t v___x_550_; size_t v___x_551_; lean_object* v___x_552_; lean_object* v___x_554_; 
v___x_539_ = lean_array_get_size(v_x_531_);
v___x_540_ = l_Lean_instHashableMVarId_hash(v_key_533_);
v___x_541_ = 32ULL;
v___x_542_ = lean_uint64_shift_right(v___x_540_, v___x_541_);
v_fold_543_ = lean_uint64_xor(v___x_540_, v___x_542_);
v___x_544_ = 16ULL;
v___x_545_ = lean_uint64_shift_right(v_fold_543_, v___x_544_);
v___x_546_ = lean_uint64_xor(v_fold_543_, v___x_545_);
v___x_547_ = lean_uint64_to_usize(v___x_546_);
v___x_548_ = lean_usize_of_nat(v___x_539_);
v___x_549_ = ((size_t)1ULL);
v___x_550_ = lean_usize_sub(v___x_548_, v___x_549_);
v___x_551_ = lean_usize_land(v___x_547_, v___x_550_);
v___x_552_ = lean_array_uget_borrowed(v_x_531_, v___x_551_);
lean_inc(v___x_552_);
if (v_isShared_538_ == 0)
{
lean_ctor_set(v___x_537_, 2, v___x_552_);
v___x_554_ = v___x_537_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v_key_533_);
lean_ctor_set(v_reuseFailAlloc_557_, 1, v_value_534_);
lean_ctor_set(v_reuseFailAlloc_557_, 2, v___x_552_);
v___x_554_ = v_reuseFailAlloc_557_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
lean_object* v___x_555_; 
v___x_555_ = lean_array_uset(v_x_531_, v___x_551_, v___x_554_);
v_x_531_ = v___x_555_;
v_x_532_ = v_tail_535_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4_spec__5___redArg(lean_object* v_i_559_, lean_object* v_source_560_, lean_object* v_target_561_){
_start:
{
lean_object* v___x_562_; uint8_t v___x_563_; 
v___x_562_ = lean_array_get_size(v_source_560_);
v___x_563_ = lean_nat_dec_lt(v_i_559_, v___x_562_);
if (v___x_563_ == 0)
{
lean_dec_ref(v_source_560_);
lean_dec(v_i_559_);
return v_target_561_;
}
else
{
lean_object* v_es_564_; lean_object* v___x_565_; lean_object* v_source_566_; lean_object* v_target_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v_es_564_ = lean_array_fget(v_source_560_, v_i_559_);
v___x_565_ = lean_box(0);
v_source_566_ = lean_array_fset(v_source_560_, v_i_559_, v___x_565_);
v_target_567_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4_spec__5_spec__7___redArg(v_target_561_, v_es_564_);
v___x_568_ = lean_unsigned_to_nat(1u);
v___x_569_ = lean_nat_add(v_i_559_, v___x_568_);
lean_dec(v_i_559_);
v_i_559_ = v___x_569_;
v_source_560_ = v_source_566_;
v_target_561_ = v_target_567_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4___redArg(lean_object* v_data_571_){
_start:
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v_nbuckets_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_572_ = lean_array_get_size(v_data_571_);
v___x_573_ = lean_unsigned_to_nat(2u);
v_nbuckets_574_ = lean_nat_mul(v___x_572_, v___x_573_);
v___x_575_ = lean_unsigned_to_nat(0u);
v___x_576_ = lean_box(0);
v___x_577_ = lean_mk_array(v_nbuckets_574_, v___x_576_);
v___x_578_ = lean_array_propagate_mark(v_data_571_, v___x_577_);
v___x_579_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4_spec__5___redArg(v___x_575_, v_data_571_, v___x_578_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2___redArg(lean_object* v_m_580_, lean_object* v_a_581_, lean_object* v_b_582_){
_start:
{
lean_object* v_size_583_; lean_object* v_buckets_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_627_; 
v_size_583_ = lean_ctor_get(v_m_580_, 0);
v_buckets_584_ = lean_ctor_get(v_m_580_, 1);
v_isSharedCheck_627_ = !lean_is_exclusive(v_m_580_);
if (v_isSharedCheck_627_ == 0)
{
v___x_586_ = v_m_580_;
v_isShared_587_ = v_isSharedCheck_627_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_buckets_584_);
lean_inc(v_size_583_);
lean_dec(v_m_580_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_627_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_588_; uint64_t v___x_589_; uint64_t v___x_590_; uint64_t v___x_591_; uint64_t v_fold_592_; uint64_t v___x_593_; uint64_t v___x_594_; uint64_t v___x_595_; size_t v___x_596_; size_t v___x_597_; size_t v___x_598_; size_t v___x_599_; size_t v___x_600_; lean_object* v_bkt_601_; uint8_t v___x_602_; 
v___x_588_ = lean_array_get_size(v_buckets_584_);
v___x_589_ = l_Lean_instHashableMVarId_hash(v_a_581_);
v___x_590_ = 32ULL;
v___x_591_ = lean_uint64_shift_right(v___x_589_, v___x_590_);
v_fold_592_ = lean_uint64_xor(v___x_589_, v___x_591_);
v___x_593_ = 16ULL;
v___x_594_ = lean_uint64_shift_right(v_fold_592_, v___x_593_);
v___x_595_ = lean_uint64_xor(v_fold_592_, v___x_594_);
v___x_596_ = lean_uint64_to_usize(v___x_595_);
v___x_597_ = lean_usize_of_nat(v___x_588_);
v___x_598_ = ((size_t)1ULL);
v___x_599_ = lean_usize_sub(v___x_597_, v___x_598_);
v___x_600_ = lean_usize_land(v___x_596_, v___x_599_);
v_bkt_601_ = lean_array_uget_borrowed(v_buckets_584_, v___x_600_);
v___x_602_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3___redArg(v_a_581_, v_bkt_601_);
if (v___x_602_ == 0)
{
lean_object* v___x_603_; lean_object* v_size_x27_604_; lean_object* v___x_605_; lean_object* v_buckets_x27_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; uint8_t v___x_612_; 
v___x_603_ = lean_unsigned_to_nat(1u);
v_size_x27_604_ = lean_nat_add(v_size_583_, v___x_603_);
lean_dec(v_size_583_);
lean_inc(v_bkt_601_);
v___x_605_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_605_, 0, v_a_581_);
lean_ctor_set(v___x_605_, 1, v_b_582_);
lean_ctor_set(v___x_605_, 2, v_bkt_601_);
v_buckets_x27_606_ = lean_array_uset(v_buckets_584_, v___x_600_, v___x_605_);
v___x_607_ = lean_unsigned_to_nat(4u);
v___x_608_ = lean_nat_mul(v_size_x27_604_, v___x_607_);
v___x_609_ = lean_unsigned_to_nat(3u);
v___x_610_ = lean_nat_div(v___x_608_, v___x_609_);
lean_dec(v___x_608_);
v___x_611_ = lean_array_get_size(v_buckets_x27_606_);
v___x_612_ = lean_nat_dec_le(v___x_610_, v___x_611_);
lean_dec(v___x_610_);
if (v___x_612_ == 0)
{
lean_object* v_val_613_; lean_object* v___x_615_; 
v_val_613_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4___redArg(v_buckets_x27_606_);
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 1, v_val_613_);
lean_ctor_set(v___x_586_, 0, v_size_x27_604_);
v___x_615_ = v___x_586_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_size_x27_604_);
lean_ctor_set(v_reuseFailAlloc_616_, 1, v_val_613_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
else
{
lean_object* v___x_618_; 
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 1, v_buckets_x27_606_);
lean_ctor_set(v___x_586_, 0, v_size_x27_604_);
v___x_618_ = v___x_586_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_size_x27_604_);
lean_ctor_set(v_reuseFailAlloc_619_, 1, v_buckets_x27_606_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
}
else
{
lean_object* v___x_620_; lean_object* v_buckets_x27_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_625_; 
lean_inc(v_bkt_601_);
v___x_620_ = lean_box(0);
v_buckets_x27_621_ = lean_array_uset(v_buckets_584_, v___x_600_, v___x_620_);
v___x_622_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__5___redArg(v_a_581_, v_b_582_, v_bkt_601_);
v___x_623_ = lean_array_uset(v_buckets_x27_621_, v___x_600_, v___x_622_);
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 1, v___x_623_);
v___x_625_ = v___x_586_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_size_583_);
lean_ctor_set(v_reuseFailAlloc_626_, 1, v___x_623_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__3(lean_object* v_x_628_, lean_object* v_x_629_, lean_object* v___y_630_){
_start:
{
if (lean_obj_tag(v_x_628_) == 0)
{
lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_631_ = l_List_reverse___redArg(v_x_629_);
v___x_632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_632_, 0, v___x_631_);
lean_ctor_set(v___x_632_, 1, v___y_630_);
return v___x_632_;
}
else
{
lean_object* v_head_633_; lean_object* v_tail_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_645_; 
v_head_633_ = lean_ctor_get(v_x_628_, 0);
v_tail_634_ = lean_ctor_get(v_x_628_, 1);
v_isSharedCheck_645_ = !lean_is_exclusive(v_x_628_);
if (v_isSharedCheck_645_ == 0)
{
v___x_636_ = v_x_628_;
v_isShared_637_ = v_isSharedCheck_645_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_tail_634_);
lean_inc(v_head_633_);
lean_dec(v_x_628_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_645_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_638_; lean_object* v_fst_639_; lean_object* v_snd_640_; lean_object* v___x_642_; 
v___x_638_ = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(v_head_633_, v___y_630_);
v_fst_639_ = lean_ctor_get(v___x_638_, 0);
lean_inc(v_fst_639_);
v_snd_640_ = lean_ctor_get(v___x_638_, 1);
lean_inc(v_snd_640_);
lean_dec_ref(v___x_638_);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 1, v_x_629_);
lean_ctor_set(v___x_636_, 0, v_fst_639_);
v___x_642_ = v___x_636_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_fst_639_);
lean_ctor_set(v_reuseFailAlloc_644_, 1, v_x_629_);
v___x_642_ = v_reuseFailAlloc_644_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
v_x_628_ = v_tail_634_;
v_x_629_ = v___x_642_;
v___y_630_ = v_snd_640_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_abstractExprMVars(lean_object* v_e_649_, lean_object* v_a_650_){
_start:
{
uint8_t v___x_651_; 
v___x_651_ = l_Lean_Expr_hasMVar(v_e_649_);
if (v___x_651_ == 0)
{
lean_object* v___x_652_; 
v___x_652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_652_, 0, v_e_649_);
lean_ctor_set(v___x_652_, 1, v_a_650_);
return v___x_652_;
}
else
{
switch(lean_obj_tag(v_e_649_))
{
case 2:
{
lean_object* v_mvarId_653_; lean_object* v_mctx_654_; lean_object* v_emap_655_; lean_object* v___x_656_; lean_object* v_userName_657_; lean_object* v_type_658_; lean_object* v_depth_659_; lean_object* v_depth_660_; uint8_t v___x_661_; 
v_mvarId_653_ = lean_ctor_get(v_e_649_, 0);
v_mctx_654_ = lean_ctor_get(v_a_650_, 2);
v_emap_655_ = lean_ctor_get(v_a_650_, 8);
lean_inc(v_mvarId_653_);
v___x_656_ = l_Lean_MetavarContext_getDecl(v_mctx_654_, v_mvarId_653_);
v_userName_657_ = lean_ctor_get(v___x_656_, 0);
lean_inc(v_userName_657_);
v_type_658_ = lean_ctor_get(v___x_656_, 2);
lean_inc_ref(v_type_658_);
v_depth_659_ = lean_ctor_get(v___x_656_, 3);
lean_inc(v_depth_659_);
lean_dec_ref(v___x_656_);
v_depth_660_ = lean_ctor_get(v_mctx_654_, 0);
v___x_661_ = lean_nat_dec_eq(v_depth_659_, v_depth_660_);
lean_dec(v_depth_659_);
if (v___x_661_ == 0)
{
lean_object* v___x_662_; 
lean_dec_ref(v_type_658_);
lean_dec(v_userName_657_);
v___x_662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_662_, 0, v_e_649_);
lean_ctor_set(v___x_662_, 1, v_a_650_);
return v___x_662_;
}
else
{
lean_object* v___x_663_; 
lean_inc(v_mvarId_653_);
v___x_663_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0___redArg(v_emap_655_, v_mvarId_653_);
if (lean_obj_tag(v___x_663_) == 0)
{
lean_object* v___x_664_; lean_object* v_fst_665_; lean_object* v_snd_666_; lean_object* v___x_667_; lean_object* v_fst_668_; lean_object* v_snd_669_; lean_object* v___x_670_; lean_object* v_fst_671_; lean_object* v_snd_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_710_; 
v___x_664_ = l_Lean_instantiateMVars___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__1(v_type_658_, v_a_650_);
v_fst_665_ = lean_ctor_get(v___x_664_, 0);
lean_inc(v_fst_665_);
v_snd_666_ = lean_ctor_get(v___x_664_, 1);
lean_inc(v_snd_666_);
lean_dec_ref(v___x_664_);
v___x_667_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_fst_665_, v_snd_666_);
v_fst_668_ = lean_ctor_get(v___x_667_, 0);
lean_inc(v_fst_668_);
v_snd_669_ = lean_ctor_get(v___x_667_, 1);
lean_inc(v_snd_669_);
lean_dec_ref(v___x_667_);
v___x_670_ = l_Lean_Meta_AbstractMVars_mkFreshFVarId(v_snd_669_);
v_fst_671_ = lean_ctor_get(v___x_670_, 0);
v_snd_672_ = lean_ctor_get(v___x_670_, 1);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_710_ == 0)
{
v___x_674_ = v___x_670_;
v_isShared_675_ = v_isSharedCheck_710_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_snd_672_);
lean_inc(v_fst_671_);
lean_dec(v___x_670_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_710_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_676_; lean_object* v_userName_678_; uint8_t v___x_705_; 
lean_inc(v_fst_671_);
v___x_676_ = l_Lean_mkFVar(v_fst_671_);
v___x_705_ = l_Lean_Name_isAnonymous(v_userName_657_);
if (v___x_705_ == 0)
{
v_userName_678_ = v_userName_657_;
goto v___jp_677_;
}
else
{
lean_object* v_fvars_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
lean_dec(v_userName_657_);
v_fvars_706_ = lean_ctor_get(v_snd_672_, 5);
v___x_707_ = ((lean_object*)(l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__1));
v___x_708_ = lean_array_get_size(v_fvars_706_);
v___x_709_ = lean_name_append_index_after(v___x_707_, v___x_708_);
v_userName_678_ = v___x_709_;
goto v___jp_677_;
}
v___jp_677_:
{
lean_object* v_ngen_679_; lean_object* v_lctx_680_; lean_object* v_mctx_681_; lean_object* v_nextParamIdx_682_; lean_object* v_paramNames_683_; lean_object* v_fvars_684_; lean_object* v_mvars_685_; lean_object* v_lmap_686_; lean_object* v_emap_687_; uint8_t v_abstractLevels_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_704_; 
v_ngen_679_ = lean_ctor_get(v_snd_672_, 0);
v_lctx_680_ = lean_ctor_get(v_snd_672_, 1);
v_mctx_681_ = lean_ctor_get(v_snd_672_, 2);
v_nextParamIdx_682_ = lean_ctor_get(v_snd_672_, 3);
v_paramNames_683_ = lean_ctor_get(v_snd_672_, 4);
v_fvars_684_ = lean_ctor_get(v_snd_672_, 5);
v_mvars_685_ = lean_ctor_get(v_snd_672_, 6);
v_lmap_686_ = lean_ctor_get(v_snd_672_, 7);
v_emap_687_ = lean_ctor_get(v_snd_672_, 8);
v_abstractLevels_688_ = lean_ctor_get_uint8(v_snd_672_, sizeof(void*)*9);
v_isSharedCheck_704_ = !lean_is_exclusive(v_snd_672_);
if (v_isSharedCheck_704_ == 0)
{
v___x_690_ = v_snd_672_;
v_isShared_691_ = v_isSharedCheck_704_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_emap_687_);
lean_inc(v_lmap_686_);
lean_inc(v_mvars_685_);
lean_inc(v_fvars_684_);
lean_inc(v_paramNames_683_);
lean_inc(v_nextParamIdx_682_);
lean_inc(v_mctx_681_);
lean_inc(v_lctx_680_);
lean_inc(v_ngen_679_);
lean_dec(v_snd_672_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_704_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
uint8_t v___x_692_; uint8_t v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_699_; 
v___x_692_ = 0;
v___x_693_ = 0;
v___x_694_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_680_, v_fst_671_, v_userName_678_, v_fst_668_, v___x_692_, v___x_693_);
lean_inc_ref_n(v___x_676_, 2);
v___x_695_ = lean_array_push(v_fvars_684_, v___x_676_);
v___x_696_ = lean_array_push(v_mvars_685_, v_e_649_);
v___x_697_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2___redArg(v_emap_687_, v_mvarId_653_, v___x_676_);
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 8, v___x_697_);
lean_ctor_set(v___x_690_, 6, v___x_696_);
lean_ctor_set(v___x_690_, 5, v___x_695_);
lean_ctor_set(v___x_690_, 1, v___x_694_);
v___x_699_ = v___x_690_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_ngen_679_);
lean_ctor_set(v_reuseFailAlloc_703_, 1, v___x_694_);
lean_ctor_set(v_reuseFailAlloc_703_, 2, v_mctx_681_);
lean_ctor_set(v_reuseFailAlloc_703_, 3, v_nextParamIdx_682_);
lean_ctor_set(v_reuseFailAlloc_703_, 4, v_paramNames_683_);
lean_ctor_set(v_reuseFailAlloc_703_, 5, v___x_695_);
lean_ctor_set(v_reuseFailAlloc_703_, 6, v___x_696_);
lean_ctor_set(v_reuseFailAlloc_703_, 7, v_lmap_686_);
lean_ctor_set(v_reuseFailAlloc_703_, 8, v___x_697_);
lean_ctor_set_uint8(v_reuseFailAlloc_703_, sizeof(void*)*9, v_abstractLevels_688_);
v___x_699_ = v_reuseFailAlloc_703_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
lean_object* v___x_701_; 
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 1, v___x_699_);
lean_ctor_set(v___x_674_, 0, v___x_676_);
v___x_701_ = v___x_674_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v___x_676_);
lean_ctor_set(v_reuseFailAlloc_702_, 1, v___x_699_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
}
}
}
}
else
{
lean_object* v_val_711_; lean_object* v___x_712_; 
lean_dec_ref(v_type_658_);
lean_dec(v_userName_657_);
lean_dec_ref_known(v_e_649_, 1);
lean_dec(v_mvarId_653_);
v_val_711_ = lean_ctor_get(v___x_663_, 0);
lean_inc(v_val_711_);
lean_dec_ref_known(v___x_663_, 1);
v___x_712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_712_, 0, v_val_711_);
lean_ctor_set(v___x_712_, 1, v_a_650_);
return v___x_712_;
}
}
}
case 3:
{
lean_object* v_u_713_; lean_object* v___x_714_; lean_object* v_fst_715_; lean_object* v_snd_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_730_; 
v_u_713_ = lean_ctor_get(v_e_649_, 0);
lean_inc(v_u_713_);
v___x_714_ = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(v_u_713_, v_a_650_);
v_fst_715_ = lean_ctor_get(v___x_714_, 0);
v_snd_716_ = lean_ctor_get(v___x_714_, 1);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_730_ == 0)
{
v___x_718_ = v___x_714_;
v_isShared_719_ = v_isSharedCheck_730_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_snd_716_);
lean_inc(v_fst_715_);
lean_dec(v___x_714_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_730_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
size_t v___x_720_; size_t v___x_721_; uint8_t v___x_722_; 
v___x_720_ = lean_ptr_addr(v_u_713_);
v___x_721_ = lean_ptr_addr(v_fst_715_);
v___x_722_ = lean_usize_dec_eq(v___x_720_, v___x_721_);
if (v___x_722_ == 0)
{
lean_object* v___x_723_; lean_object* v___x_725_; 
lean_dec_ref_known(v_e_649_, 1);
v___x_723_ = l_Lean_Expr_sort___override(v_fst_715_);
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 0, v___x_723_);
v___x_725_ = v___x_718_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v___x_723_);
lean_ctor_set(v_reuseFailAlloc_726_, 1, v_snd_716_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
else
{
lean_object* v___x_728_; 
lean_dec(v_fst_715_);
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 0, v_e_649_);
v___x_728_ = v___x_718_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_e_649_);
lean_ctor_set(v_reuseFailAlloc_729_, 1, v_snd_716_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
}
case 4:
{
lean_object* v_declName_731_; lean_object* v_us_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v_fst_735_; lean_object* v_snd_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_748_; 
v_declName_731_ = lean_ctor_get(v_e_649_, 0);
v_us_732_ = lean_ctor_get(v_e_649_, 1);
v___x_733_ = lean_box(0);
lean_inc(v_us_732_);
v___x_734_ = l_List_mapM_loop___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__3(v_us_732_, v___x_733_, v_a_650_);
v_fst_735_ = lean_ctor_get(v___x_734_, 0);
v_snd_736_ = lean_ctor_get(v___x_734_, 1);
v_isSharedCheck_748_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_748_ == 0)
{
v___x_738_ = v___x_734_;
v_isShared_739_ = v_isSharedCheck_748_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_snd_736_);
lean_inc(v_fst_735_);
lean_dec(v___x_734_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_748_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
uint8_t v___x_740_; 
v___x_740_ = l_ptrEqList___redArg(v_us_732_, v_fst_735_);
if (v___x_740_ == 0)
{
lean_object* v___x_741_; lean_object* v___x_743_; 
lean_inc(v_declName_731_);
lean_dec_ref_known(v_e_649_, 2);
v___x_741_ = l_Lean_Expr_const___override(v_declName_731_, v_fst_735_);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 0, v___x_741_);
v___x_743_ = v___x_738_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v___x_741_);
lean_ctor_set(v_reuseFailAlloc_744_, 1, v_snd_736_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
else
{
lean_object* v___x_746_; 
lean_dec(v_fst_735_);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 0, v_e_649_);
v___x_746_ = v___x_738_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_e_649_);
lean_ctor_set(v_reuseFailAlloc_747_, 1, v_snd_736_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
}
case 5:
{
lean_object* v_fn_749_; lean_object* v_arg_750_; lean_object* v___x_751_; lean_object* v_fst_752_; lean_object* v_snd_753_; lean_object* v___x_754_; lean_object* v_fst_755_; lean_object* v_snd_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_777_; 
v_fn_749_ = lean_ctor_get(v_e_649_, 0);
v_arg_750_ = lean_ctor_get(v_e_649_, 1);
lean_inc_ref(v_fn_749_);
v___x_751_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_fn_749_, v_a_650_);
v_fst_752_ = lean_ctor_get(v___x_751_, 0);
lean_inc(v_fst_752_);
v_snd_753_ = lean_ctor_get(v___x_751_, 1);
lean_inc(v_snd_753_);
lean_dec_ref(v___x_751_);
lean_inc_ref(v_arg_750_);
v___x_754_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_arg_750_, v_snd_753_);
v_fst_755_ = lean_ctor_get(v___x_754_, 0);
v_snd_756_ = lean_ctor_get(v___x_754_, 1);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_754_);
if (v_isSharedCheck_777_ == 0)
{
v___x_758_ = v___x_754_;
v_isShared_759_ = v_isSharedCheck_777_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_snd_756_);
lean_inc(v_fst_755_);
lean_dec(v___x_754_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_777_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
size_t v___x_760_; size_t v___x_761_; uint8_t v___x_762_; 
v___x_760_ = lean_ptr_addr(v_fn_749_);
v___x_761_ = lean_ptr_addr(v_fst_752_);
v___x_762_ = lean_usize_dec_eq(v___x_760_, v___x_761_);
if (v___x_762_ == 0)
{
lean_object* v___x_763_; lean_object* v___x_765_; 
lean_dec_ref_known(v_e_649_, 2);
v___x_763_ = l_Lean_Expr_app___override(v_fst_752_, v_fst_755_);
if (v_isShared_759_ == 0)
{
lean_ctor_set(v___x_758_, 0, v___x_763_);
v___x_765_ = v___x_758_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v___x_763_);
lean_ctor_set(v_reuseFailAlloc_766_, 1, v_snd_756_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
else
{
size_t v___x_767_; size_t v___x_768_; uint8_t v___x_769_; 
v___x_767_ = lean_ptr_addr(v_arg_750_);
v___x_768_ = lean_ptr_addr(v_fst_755_);
v___x_769_ = lean_usize_dec_eq(v___x_767_, v___x_768_);
if (v___x_769_ == 0)
{
lean_object* v___x_770_; lean_object* v___x_772_; 
lean_dec_ref_known(v_e_649_, 2);
v___x_770_ = l_Lean_Expr_app___override(v_fst_752_, v_fst_755_);
if (v_isShared_759_ == 0)
{
lean_ctor_set(v___x_758_, 0, v___x_770_);
v___x_772_ = v___x_758_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v___x_770_);
lean_ctor_set(v_reuseFailAlloc_773_, 1, v_snd_756_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
else
{
lean_object* v___x_775_; 
lean_dec(v_fst_755_);
lean_dec(v_fst_752_);
if (v_isShared_759_ == 0)
{
lean_ctor_set(v___x_758_, 0, v_e_649_);
v___x_775_ = v___x_758_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_e_649_);
lean_ctor_set(v_reuseFailAlloc_776_, 1, v_snd_756_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
}
}
case 6:
{
lean_object* v_binderName_778_; lean_object* v_binderType_779_; lean_object* v_body_780_; uint8_t v_binderInfo_781_; lean_object* v___x_782_; lean_object* v_fst_783_; lean_object* v_snd_784_; lean_object* v___x_785_; lean_object* v_fst_786_; lean_object* v_snd_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_813_; 
v_binderName_778_ = lean_ctor_get(v_e_649_, 0);
v_binderType_779_ = lean_ctor_get(v_e_649_, 1);
v_body_780_ = lean_ctor_get(v_e_649_, 2);
v_binderInfo_781_ = lean_ctor_get_uint8(v_e_649_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_779_);
v___x_782_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_binderType_779_, v_a_650_);
v_fst_783_ = lean_ctor_get(v___x_782_, 0);
lean_inc(v_fst_783_);
v_snd_784_ = lean_ctor_get(v___x_782_, 1);
lean_inc(v_snd_784_);
lean_dec_ref(v___x_782_);
lean_inc_ref(v_body_780_);
v___x_785_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_body_780_, v_snd_784_);
v_fst_786_ = lean_ctor_get(v___x_785_, 0);
v_snd_787_ = lean_ctor_get(v___x_785_, 1);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_813_ == 0)
{
v___x_789_ = v___x_785_;
v_isShared_790_ = v_isSharedCheck_813_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_snd_787_);
lean_inc(v_fst_786_);
lean_dec(v___x_785_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_813_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
size_t v___x_791_; size_t v___x_792_; uint8_t v___x_793_; 
v___x_791_ = lean_ptr_addr(v_binderType_779_);
v___x_792_ = lean_ptr_addr(v_fst_783_);
v___x_793_ = lean_usize_dec_eq(v___x_791_, v___x_792_);
if (v___x_793_ == 0)
{
lean_object* v___x_794_; lean_object* v___x_796_; 
lean_inc(v_binderName_778_);
lean_dec_ref_known(v_e_649_, 3);
v___x_794_ = l_Lean_Expr_lam___override(v_binderName_778_, v_fst_783_, v_fst_786_, v_binderInfo_781_);
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 0, v___x_794_);
v___x_796_ = v___x_789_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v___x_794_);
lean_ctor_set(v_reuseFailAlloc_797_, 1, v_snd_787_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
else
{
size_t v___x_798_; size_t v___x_799_; uint8_t v___x_800_; 
v___x_798_ = lean_ptr_addr(v_body_780_);
v___x_799_ = lean_ptr_addr(v_fst_786_);
v___x_800_ = lean_usize_dec_eq(v___x_798_, v___x_799_);
if (v___x_800_ == 0)
{
lean_object* v___x_801_; lean_object* v___x_803_; 
lean_inc(v_binderName_778_);
lean_dec_ref_known(v_e_649_, 3);
v___x_801_ = l_Lean_Expr_lam___override(v_binderName_778_, v_fst_783_, v_fst_786_, v_binderInfo_781_);
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 0, v___x_801_);
v___x_803_ = v___x_789_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v___x_801_);
lean_ctor_set(v_reuseFailAlloc_804_, 1, v_snd_787_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
else
{
uint8_t v___x_805_; 
v___x_805_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_781_, v_binderInfo_781_);
if (v___x_805_ == 0)
{
lean_object* v___x_806_; lean_object* v___x_808_; 
lean_inc(v_binderName_778_);
lean_dec_ref_known(v_e_649_, 3);
v___x_806_ = l_Lean_Expr_lam___override(v_binderName_778_, v_fst_783_, v_fst_786_, v_binderInfo_781_);
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 0, v___x_806_);
v___x_808_ = v___x_789_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v___x_806_);
lean_ctor_set(v_reuseFailAlloc_809_, 1, v_snd_787_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
else
{
lean_object* v___x_811_; 
lean_dec(v_fst_786_);
lean_dec(v_fst_783_);
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 0, v_e_649_);
v___x_811_ = v___x_789_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_e_649_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v_snd_787_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
}
}
}
case 7:
{
lean_object* v_binderName_814_; lean_object* v_binderType_815_; lean_object* v_body_816_; uint8_t v_binderInfo_817_; lean_object* v___x_818_; lean_object* v_fst_819_; lean_object* v_snd_820_; lean_object* v___x_821_; lean_object* v_fst_822_; lean_object* v_snd_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_849_; 
v_binderName_814_ = lean_ctor_get(v_e_649_, 0);
v_binderType_815_ = lean_ctor_get(v_e_649_, 1);
v_body_816_ = lean_ctor_get(v_e_649_, 2);
v_binderInfo_817_ = lean_ctor_get_uint8(v_e_649_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_815_);
v___x_818_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_binderType_815_, v_a_650_);
v_fst_819_ = lean_ctor_get(v___x_818_, 0);
lean_inc(v_fst_819_);
v_snd_820_ = lean_ctor_get(v___x_818_, 1);
lean_inc(v_snd_820_);
lean_dec_ref(v___x_818_);
lean_inc_ref(v_body_816_);
v___x_821_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_body_816_, v_snd_820_);
v_fst_822_ = lean_ctor_get(v___x_821_, 0);
v_snd_823_ = lean_ctor_get(v___x_821_, 1);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_849_ == 0)
{
v___x_825_ = v___x_821_;
v_isShared_826_ = v_isSharedCheck_849_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_snd_823_);
lean_inc(v_fst_822_);
lean_dec(v___x_821_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_849_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
size_t v___x_827_; size_t v___x_828_; uint8_t v___x_829_; 
v___x_827_ = lean_ptr_addr(v_binderType_815_);
v___x_828_ = lean_ptr_addr(v_fst_819_);
v___x_829_ = lean_usize_dec_eq(v___x_827_, v___x_828_);
if (v___x_829_ == 0)
{
lean_object* v___x_830_; lean_object* v___x_832_; 
lean_inc(v_binderName_814_);
lean_dec_ref_known(v_e_649_, 3);
v___x_830_ = l_Lean_Expr_forallE___override(v_binderName_814_, v_fst_819_, v_fst_822_, v_binderInfo_817_);
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 0, v___x_830_);
v___x_832_ = v___x_825_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v___x_830_);
lean_ctor_set(v_reuseFailAlloc_833_, 1, v_snd_823_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
else
{
size_t v___x_834_; size_t v___x_835_; uint8_t v___x_836_; 
v___x_834_ = lean_ptr_addr(v_body_816_);
v___x_835_ = lean_ptr_addr(v_fst_822_);
v___x_836_ = lean_usize_dec_eq(v___x_834_, v___x_835_);
if (v___x_836_ == 0)
{
lean_object* v___x_837_; lean_object* v___x_839_; 
lean_inc(v_binderName_814_);
lean_dec_ref_known(v_e_649_, 3);
v___x_837_ = l_Lean_Expr_forallE___override(v_binderName_814_, v_fst_819_, v_fst_822_, v_binderInfo_817_);
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 0, v___x_837_);
v___x_839_ = v___x_825_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v___x_837_);
lean_ctor_set(v_reuseFailAlloc_840_, 1, v_snd_823_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
else
{
uint8_t v___x_841_; 
v___x_841_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_817_, v_binderInfo_817_);
if (v___x_841_ == 0)
{
lean_object* v___x_842_; lean_object* v___x_844_; 
lean_inc(v_binderName_814_);
lean_dec_ref_known(v_e_649_, 3);
v___x_842_ = l_Lean_Expr_forallE___override(v_binderName_814_, v_fst_819_, v_fst_822_, v_binderInfo_817_);
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 0, v___x_842_);
v___x_844_ = v___x_825_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v___x_842_);
lean_ctor_set(v_reuseFailAlloc_845_, 1, v_snd_823_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
else
{
lean_object* v___x_847_; 
lean_dec(v_fst_822_);
lean_dec(v_fst_819_);
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 0, v_e_649_);
v___x_847_ = v___x_825_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_e_649_);
lean_ctor_set(v_reuseFailAlloc_848_, 1, v_snd_823_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
}
}
}
case 8:
{
lean_object* v_declName_850_; lean_object* v_type_851_; lean_object* v_value_852_; lean_object* v_body_853_; uint8_t v_nondep_854_; lean_object* v___x_855_; lean_object* v_fst_856_; lean_object* v_snd_857_; lean_object* v___x_858_; lean_object* v_fst_859_; lean_object* v_snd_860_; lean_object* v___x_861_; lean_object* v_fst_862_; lean_object* v_snd_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_891_; 
v_declName_850_ = lean_ctor_get(v_e_649_, 0);
v_type_851_ = lean_ctor_get(v_e_649_, 1);
v_value_852_ = lean_ctor_get(v_e_649_, 2);
v_body_853_ = lean_ctor_get(v_e_649_, 3);
v_nondep_854_ = lean_ctor_get_uint8(v_e_649_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_851_);
v___x_855_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_type_851_, v_a_650_);
v_fst_856_ = lean_ctor_get(v___x_855_, 0);
lean_inc(v_fst_856_);
v_snd_857_ = lean_ctor_get(v___x_855_, 1);
lean_inc(v_snd_857_);
lean_dec_ref(v___x_855_);
lean_inc_ref(v_value_852_);
v___x_858_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_value_852_, v_snd_857_);
v_fst_859_ = lean_ctor_get(v___x_858_, 0);
lean_inc(v_fst_859_);
v_snd_860_ = lean_ctor_get(v___x_858_, 1);
lean_inc(v_snd_860_);
lean_dec_ref(v___x_858_);
lean_inc_ref(v_body_853_);
v___x_861_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_body_853_, v_snd_860_);
v_fst_862_ = lean_ctor_get(v___x_861_, 0);
v_snd_863_ = lean_ctor_get(v___x_861_, 1);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_891_ == 0)
{
v___x_865_ = v___x_861_;
v_isShared_866_ = v_isSharedCheck_891_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_snd_863_);
lean_inc(v_fst_862_);
lean_dec(v___x_861_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_891_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
size_t v___x_867_; size_t v___x_868_; uint8_t v___x_869_; 
v___x_867_ = lean_ptr_addr(v_type_851_);
v___x_868_ = lean_ptr_addr(v_fst_856_);
v___x_869_ = lean_usize_dec_eq(v___x_867_, v___x_868_);
if (v___x_869_ == 0)
{
lean_object* v___x_870_; lean_object* v___x_872_; 
lean_inc(v_declName_850_);
lean_dec_ref_known(v_e_649_, 4);
v___x_870_ = l_Lean_Expr_letE___override(v_declName_850_, v_fst_856_, v_fst_859_, v_fst_862_, v_nondep_854_);
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 0, v___x_870_);
v___x_872_ = v___x_865_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v___x_870_);
lean_ctor_set(v_reuseFailAlloc_873_, 1, v_snd_863_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
else
{
size_t v___x_874_; size_t v___x_875_; uint8_t v___x_876_; 
v___x_874_ = lean_ptr_addr(v_value_852_);
v___x_875_ = lean_ptr_addr(v_fst_859_);
v___x_876_ = lean_usize_dec_eq(v___x_874_, v___x_875_);
if (v___x_876_ == 0)
{
lean_object* v___x_877_; lean_object* v___x_879_; 
lean_inc(v_declName_850_);
lean_dec_ref_known(v_e_649_, 4);
v___x_877_ = l_Lean_Expr_letE___override(v_declName_850_, v_fst_856_, v_fst_859_, v_fst_862_, v_nondep_854_);
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 0, v___x_877_);
v___x_879_ = v___x_865_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v___x_877_);
lean_ctor_set(v_reuseFailAlloc_880_, 1, v_snd_863_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
else
{
size_t v___x_881_; size_t v___x_882_; uint8_t v___x_883_; 
v___x_881_ = lean_ptr_addr(v_body_853_);
v___x_882_ = lean_ptr_addr(v_fst_862_);
v___x_883_ = lean_usize_dec_eq(v___x_881_, v___x_882_);
if (v___x_883_ == 0)
{
lean_object* v___x_884_; lean_object* v___x_886_; 
lean_inc(v_declName_850_);
lean_dec_ref_known(v_e_649_, 4);
v___x_884_ = l_Lean_Expr_letE___override(v_declName_850_, v_fst_856_, v_fst_859_, v_fst_862_, v_nondep_854_);
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 0, v___x_884_);
v___x_886_ = v___x_865_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_884_);
lean_ctor_set(v_reuseFailAlloc_887_, 1, v_snd_863_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
else
{
lean_object* v___x_889_; 
lean_dec(v_fst_862_);
lean_dec(v_fst_859_);
lean_dec(v_fst_856_);
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 0, v_e_649_);
v___x_889_ = v___x_865_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_e_649_);
lean_ctor_set(v_reuseFailAlloc_890_, 1, v_snd_863_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
}
}
}
case 10:
{
lean_object* v_data_892_; lean_object* v_expr_893_; lean_object* v___x_894_; lean_object* v_fst_895_; lean_object* v_snd_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_910_; 
v_data_892_ = lean_ctor_get(v_e_649_, 0);
v_expr_893_ = lean_ctor_get(v_e_649_, 1);
lean_inc_ref(v_expr_893_);
v___x_894_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_expr_893_, v_a_650_);
v_fst_895_ = lean_ctor_get(v___x_894_, 0);
v_snd_896_ = lean_ctor_get(v___x_894_, 1);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_910_ == 0)
{
v___x_898_ = v___x_894_;
v_isShared_899_ = v_isSharedCheck_910_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_snd_896_);
lean_inc(v_fst_895_);
lean_dec(v___x_894_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_910_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
size_t v___x_900_; size_t v___x_901_; uint8_t v___x_902_; 
v___x_900_ = lean_ptr_addr(v_expr_893_);
v___x_901_ = lean_ptr_addr(v_fst_895_);
v___x_902_ = lean_usize_dec_eq(v___x_900_, v___x_901_);
if (v___x_902_ == 0)
{
lean_object* v___x_903_; lean_object* v___x_905_; 
lean_inc(v_data_892_);
lean_dec_ref_known(v_e_649_, 2);
v___x_903_ = l_Lean_Expr_mdata___override(v_data_892_, v_fst_895_);
if (v_isShared_899_ == 0)
{
lean_ctor_set(v___x_898_, 0, v___x_903_);
v___x_905_ = v___x_898_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v___x_903_);
lean_ctor_set(v_reuseFailAlloc_906_, 1, v_snd_896_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
else
{
lean_object* v___x_908_; 
lean_dec(v_fst_895_);
if (v_isShared_899_ == 0)
{
lean_ctor_set(v___x_898_, 0, v_e_649_);
v___x_908_ = v___x_898_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_e_649_);
lean_ctor_set(v_reuseFailAlloc_909_, 1, v_snd_896_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
}
}
case 11:
{
lean_object* v_typeName_911_; lean_object* v_idx_912_; lean_object* v_struct_913_; lean_object* v___x_914_; lean_object* v_fst_915_; lean_object* v_snd_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_930_; 
v_typeName_911_ = lean_ctor_get(v_e_649_, 0);
v_idx_912_ = lean_ctor_get(v_e_649_, 1);
v_struct_913_ = lean_ctor_get(v_e_649_, 2);
lean_inc_ref(v_struct_913_);
v___x_914_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_struct_913_, v_a_650_);
v_fst_915_ = lean_ctor_get(v___x_914_, 0);
v_snd_916_ = lean_ctor_get(v___x_914_, 1);
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_930_ == 0)
{
v___x_918_ = v___x_914_;
v_isShared_919_ = v_isSharedCheck_930_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_snd_916_);
lean_inc(v_fst_915_);
lean_dec(v___x_914_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_930_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
size_t v___x_920_; size_t v___x_921_; uint8_t v___x_922_; 
v___x_920_ = lean_ptr_addr(v_struct_913_);
v___x_921_ = lean_ptr_addr(v_fst_915_);
v___x_922_ = lean_usize_dec_eq(v___x_920_, v___x_921_);
if (v___x_922_ == 0)
{
lean_object* v___x_923_; lean_object* v___x_925_; 
lean_inc(v_idx_912_);
lean_inc(v_typeName_911_);
lean_dec_ref_known(v_e_649_, 3);
v___x_923_ = l_Lean_Expr_proj___override(v_typeName_911_, v_idx_912_, v_fst_915_);
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 0, v___x_923_);
v___x_925_ = v___x_918_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v___x_923_);
lean_ctor_set(v_reuseFailAlloc_926_, 1, v_snd_916_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
else
{
lean_object* v___x_928_; 
lean_dec(v_fst_915_);
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 0, v_e_649_);
v___x_928_ = v___x_918_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_e_649_);
lean_ctor_set(v_reuseFailAlloc_929_, 1, v_snd_916_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
}
default: 
{
lean_object* v___x_931_; 
v___x_931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_931_, 0, v_e_649_);
lean_ctor_set(v___x_931_, 1, v_a_650_);
return v___x_931_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0(lean_object* v_00_u03b2_932_, lean_object* v_m_933_, lean_object* v_a_934_){
_start:
{
lean_object* v___x_935_; 
v___x_935_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0___redArg(v_m_933_, v_a_934_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0___boxed(lean_object* v_00_u03b2_936_, lean_object* v_m_937_, lean_object* v_a_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0(v_00_u03b2_936_, v_m_937_, v_a_938_);
lean_dec(v_a_938_);
lean_dec_ref(v_m_937_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2(lean_object* v_00_u03b2_940_, lean_object* v_m_941_, lean_object* v_a_942_, lean_object* v_b_943_){
_start:
{
lean_object* v___x_944_; 
v___x_944_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2___redArg(v_m_941_, v_a_942_, v_b_943_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0(lean_object* v_00_u03b2_945_, lean_object* v_a_946_, lean_object* v_x_947_){
_start:
{
lean_object* v___x_948_; 
v___x_948_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0___redArg(v_a_946_, v_x_947_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0___boxed(lean_object* v_00_u03b2_949_, lean_object* v_a_950_, lean_object* v_x_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0(v_00_u03b2_949_, v_a_950_, v_x_951_);
lean_dec(v_x_951_);
lean_dec(v_a_950_);
return v_res_952_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3(lean_object* v_00_u03b2_953_, lean_object* v_a_954_, lean_object* v_x_955_){
_start:
{
uint8_t v___x_956_; 
v___x_956_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3___redArg(v_a_954_, v_x_955_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3___boxed(lean_object* v_00_u03b2_957_, lean_object* v_a_958_, lean_object* v_x_959_){
_start:
{
uint8_t v_res_960_; lean_object* v_r_961_; 
v_res_960_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3(v_00_u03b2_957_, v_a_958_, v_x_959_);
lean_dec(v_x_959_);
lean_dec(v_a_958_);
v_r_961_ = lean_box(v_res_960_);
return v_r_961_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4(lean_object* v_00_u03b2_962_, lean_object* v_data_963_){
_start:
{
lean_object* v___x_964_; 
v___x_964_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4___redArg(v_data_963_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__5(lean_object* v_00_u03b2_965_, lean_object* v_a_966_, lean_object* v_b_967_, lean_object* v_x_968_){
_start:
{
lean_object* v___x_969_; 
v___x_969_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__5___redArg(v_a_966_, v_b_967_, v_x_968_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_970_, lean_object* v_i_971_, lean_object* v_source_972_, lean_object* v_target_973_){
_start:
{
lean_object* v___x_974_; 
v___x_974_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4_spec__5___redArg(v_i_971_, v_source_972_, v_target_973_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4_spec__5_spec__7(lean_object* v_00_u03b2_975_, lean_object* v_x_976_, lean_object* v_x_977_){
_start:
{
lean_object* v___x_978_; 
v___x_978_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4_spec__5_spec__7___redArg(v_x_976_, v_x_977_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0___redArg(lean_object* v_e_979_, lean_object* v___y_980_){
_start:
{
uint8_t v___x_982_; 
v___x_982_ = l_Lean_Expr_hasMVar(v_e_979_);
if (v___x_982_ == 0)
{
lean_object* v___x_983_; 
v___x_983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_983_, 0, v_e_979_);
return v___x_983_;
}
else
{
lean_object* v___x_984_; lean_object* v_mctx_985_; lean_object* v___x_986_; lean_object* v_fst_987_; lean_object* v_snd_988_; lean_object* v___x_989_; lean_object* v_cache_990_; lean_object* v_zetaDeltaFVarIds_991_; lean_object* v_postponed_992_; lean_object* v_diag_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1002_; 
v___x_984_ = lean_st_ref_get(v___y_980_);
v_mctx_985_ = lean_ctor_get(v___x_984_, 0);
lean_inc_ref(v_mctx_985_);
lean_dec(v___x_984_);
v___x_986_ = l_Lean_instantiateMVarsCore(v_mctx_985_, v_e_979_);
v_fst_987_ = lean_ctor_get(v___x_986_, 0);
lean_inc(v_fst_987_);
v_snd_988_ = lean_ctor_get(v___x_986_, 1);
lean_inc(v_snd_988_);
lean_dec_ref(v___x_986_);
v___x_989_ = lean_st_ref_take(v___y_980_);
v_cache_990_ = lean_ctor_get(v___x_989_, 1);
v_zetaDeltaFVarIds_991_ = lean_ctor_get(v___x_989_, 2);
v_postponed_992_ = lean_ctor_get(v___x_989_, 3);
v_diag_993_ = lean_ctor_get(v___x_989_, 4);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_1002_ == 0)
{
lean_object* v_unused_1003_; 
v_unused_1003_ = lean_ctor_get(v___x_989_, 0);
lean_dec(v_unused_1003_);
v___x_995_ = v___x_989_;
v_isShared_996_ = v_isSharedCheck_1002_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_diag_993_);
lean_inc(v_postponed_992_);
lean_inc(v_zetaDeltaFVarIds_991_);
lean_inc(v_cache_990_);
lean_dec(v___x_989_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1002_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_998_; 
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 0, v_snd_988_);
v___x_998_ = v___x_995_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_snd_988_);
lean_ctor_set(v_reuseFailAlloc_1001_, 1, v_cache_990_);
lean_ctor_set(v_reuseFailAlloc_1001_, 2, v_zetaDeltaFVarIds_991_);
lean_ctor_set(v_reuseFailAlloc_1001_, 3, v_postponed_992_);
lean_ctor_set(v_reuseFailAlloc_1001_, 4, v_diag_993_);
v___x_998_ = v_reuseFailAlloc_1001_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_999_ = lean_st_ref_put(v___y_980_, v___x_998_);
v___x_1000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1000_, 0, v_fst_987_);
return v___x_1000_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0___redArg___boxed(lean_object* v_e_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_){
_start:
{
lean_object* v_res_1007_; 
v_res_1007_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0___redArg(v_e_1004_, v___y_1005_);
lean_dec(v___y_1005_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0(lean_object* v_e_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_){
_start:
{
lean_object* v___x_1014_; 
v___x_1014_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0___redArg(v_e_1008_, v___y_1010_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0___boxed(lean_object* v_e_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_){
_start:
{
lean_object* v_res_1021_; 
v_res_1021_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0(v_e_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
return v_res_1021_;
}
}
static lean_object* _init_l_Lean_Meta_abstractMVars___closed__1(void){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1024_ = lean_box(0);
v___x_1025_ = lean_unsigned_to_nat(16u);
v___x_1026_ = lean_mk_array(v___x_1025_, v___x_1024_);
return v___x_1026_;
}
}
static lean_object* _init_l_Lean_Meta_abstractMVars___closed__2(void){
_start:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1027_ = lean_obj_once(&l_Lean_Meta_abstractMVars___closed__1, &l_Lean_Meta_abstractMVars___closed__1_once, _init_l_Lean_Meta_abstractMVars___closed__1);
v___x_1028_ = lean_unsigned_to_nat(0u);
v___x_1029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1028_);
lean_ctor_set(v___x_1029_, 1, v___x_1027_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractMVars(lean_object* v_e_1030_, uint8_t v_levels_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_){
_start:
{
lean_object* v___x_1037_; lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1099_; 
v___x_1037_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0___redArg(v_e_1030_, v_a_1033_);
v_a_1038_ = lean_ctor_get(v___x_1037_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1037_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1040_ = v___x_1037_;
v_isShared_1041_ = v_isSharedCheck_1099_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_dec(v___x_1037_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1099_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v_mctx_1044_; lean_object* v_lctx_1045_; lean_object* v_ngen_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v_fst_1052_; lean_object* v_snd_1053_; lean_object* v___x_1054_; lean_object* v_ngen_1055_; lean_object* v_lctx_1056_; lean_object* v_mctx_1057_; lean_object* v_paramNames_1058_; lean_object* v_fvars_1059_; lean_object* v_mvars_1060_; lean_object* v_env_1061_; lean_object* v_nextMacroScope_1062_; lean_object* v_auxDeclNGen_1063_; lean_object* v_traceState_1064_; lean_object* v_cache_1065_; lean_object* v_messages_1066_; lean_object* v_infoState_1067_; lean_object* v_snapshotTasks_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1097_; 
v___x_1042_ = lean_st_ref_get(v_a_1033_);
v___x_1043_ = lean_st_ref_get(v_a_1035_);
v_mctx_1044_ = lean_ctor_get(v___x_1042_, 0);
lean_inc_ref(v_mctx_1044_);
lean_dec(v___x_1042_);
v_lctx_1045_ = lean_ctor_get(v_a_1032_, 2);
v_ngen_1046_ = lean_ctor_get(v___x_1043_, 2);
lean_inc_ref(v_ngen_1046_);
lean_dec(v___x_1043_);
v___x_1047_ = lean_unsigned_to_nat(0u);
v___x_1048_ = ((lean_object*)(l_Lean_Meta_abstractMVars___closed__0));
v___x_1049_ = lean_obj_once(&l_Lean_Meta_abstractMVars___closed__2, &l_Lean_Meta_abstractMVars___closed__2_once, _init_l_Lean_Meta_abstractMVars___closed__2);
lean_inc_ref(v_lctx_1045_);
v___x_1050_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v___x_1050_, 0, v_ngen_1046_);
lean_ctor_set(v___x_1050_, 1, v_lctx_1045_);
lean_ctor_set(v___x_1050_, 2, v_mctx_1044_);
lean_ctor_set(v___x_1050_, 3, v___x_1047_);
lean_ctor_set(v___x_1050_, 4, v___x_1048_);
lean_ctor_set(v___x_1050_, 5, v___x_1048_);
lean_ctor_set(v___x_1050_, 6, v___x_1048_);
lean_ctor_set(v___x_1050_, 7, v___x_1049_);
lean_ctor_set(v___x_1050_, 8, v___x_1049_);
lean_ctor_set_uint8(v___x_1050_, sizeof(void*)*9, v_levels_1031_);
v___x_1051_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_a_1038_, v___x_1050_);
v_fst_1052_ = lean_ctor_get(v___x_1051_, 0);
lean_inc(v_fst_1052_);
v_snd_1053_ = lean_ctor_get(v___x_1051_, 1);
lean_inc(v_snd_1053_);
lean_dec_ref(v___x_1051_);
v___x_1054_ = lean_st_ref_take(v_a_1035_);
v_ngen_1055_ = lean_ctor_get(v_snd_1053_, 0);
lean_inc_ref(v_ngen_1055_);
v_lctx_1056_ = lean_ctor_get(v_snd_1053_, 1);
lean_inc_ref(v_lctx_1056_);
v_mctx_1057_ = lean_ctor_get(v_snd_1053_, 2);
lean_inc_ref(v_mctx_1057_);
v_paramNames_1058_ = lean_ctor_get(v_snd_1053_, 4);
lean_inc_ref(v_paramNames_1058_);
v_fvars_1059_ = lean_ctor_get(v_snd_1053_, 5);
lean_inc_ref(v_fvars_1059_);
v_mvars_1060_ = lean_ctor_get(v_snd_1053_, 6);
lean_inc_ref(v_mvars_1060_);
lean_dec(v_snd_1053_);
v_env_1061_ = lean_ctor_get(v___x_1054_, 0);
v_nextMacroScope_1062_ = lean_ctor_get(v___x_1054_, 1);
v_auxDeclNGen_1063_ = lean_ctor_get(v___x_1054_, 3);
v_traceState_1064_ = lean_ctor_get(v___x_1054_, 4);
v_cache_1065_ = lean_ctor_get(v___x_1054_, 5);
v_messages_1066_ = lean_ctor_get(v___x_1054_, 6);
v_infoState_1067_ = lean_ctor_get(v___x_1054_, 7);
v_snapshotTasks_1068_ = lean_ctor_get(v___x_1054_, 8);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1054_);
if (v_isSharedCheck_1097_ == 0)
{
lean_object* v_unused_1098_; 
v_unused_1098_ = lean_ctor_get(v___x_1054_, 2);
lean_dec(v_unused_1098_);
v___x_1070_ = v___x_1054_;
v_isShared_1071_ = v_isSharedCheck_1097_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_snapshotTasks_1068_);
lean_inc(v_infoState_1067_);
lean_inc(v_messages_1066_);
lean_inc(v_cache_1065_);
lean_inc(v_traceState_1064_);
lean_inc(v_auxDeclNGen_1063_);
lean_inc(v_nextMacroScope_1062_);
lean_inc(v_env_1061_);
lean_dec(v___x_1054_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1097_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1073_; 
if (v_isShared_1071_ == 0)
{
lean_ctor_set(v___x_1070_, 2, v_ngen_1055_);
v___x_1073_ = v___x_1070_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_env_1061_);
lean_ctor_set(v_reuseFailAlloc_1096_, 1, v_nextMacroScope_1062_);
lean_ctor_set(v_reuseFailAlloc_1096_, 2, v_ngen_1055_);
lean_ctor_set(v_reuseFailAlloc_1096_, 3, v_auxDeclNGen_1063_);
lean_ctor_set(v_reuseFailAlloc_1096_, 4, v_traceState_1064_);
lean_ctor_set(v_reuseFailAlloc_1096_, 5, v_cache_1065_);
lean_ctor_set(v_reuseFailAlloc_1096_, 6, v_messages_1066_);
lean_ctor_set(v_reuseFailAlloc_1096_, 7, v_infoState_1067_);
lean_ctor_set(v_reuseFailAlloc_1096_, 8, v_snapshotTasks_1068_);
v___x_1073_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v_cache_1076_; lean_object* v_zetaDeltaFVarIds_1077_; lean_object* v_postponed_1078_; lean_object* v_diag_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1094_; 
v___x_1074_ = lean_st_ref_put(v_a_1035_, v___x_1073_);
v___x_1075_ = lean_st_ref_take(v_a_1033_);
v_cache_1076_ = lean_ctor_get(v___x_1075_, 1);
v_zetaDeltaFVarIds_1077_ = lean_ctor_get(v___x_1075_, 2);
v_postponed_1078_ = lean_ctor_get(v___x_1075_, 3);
v_diag_1079_ = lean_ctor_get(v___x_1075_, 4);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1094_ == 0)
{
lean_object* v_unused_1095_; 
v_unused_1095_ = lean_ctor_get(v___x_1075_, 0);
lean_dec(v_unused_1095_);
v___x_1081_ = v___x_1075_;
v_isShared_1082_ = v_isSharedCheck_1094_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_diag_1079_);
lean_inc(v_postponed_1078_);
lean_inc(v_zetaDeltaFVarIds_1077_);
lean_inc(v_cache_1076_);
lean_dec(v___x_1075_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1094_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1084_; 
if (v_isShared_1082_ == 0)
{
lean_ctor_set(v___x_1081_, 0, v_mctx_1057_);
v___x_1084_ = v___x_1081_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_mctx_1057_);
lean_ctor_set(v_reuseFailAlloc_1093_, 1, v_cache_1076_);
lean_ctor_set(v_reuseFailAlloc_1093_, 2, v_zetaDeltaFVarIds_1077_);
lean_ctor_set(v_reuseFailAlloc_1093_, 3, v_postponed_1078_);
lean_ctor_set(v_reuseFailAlloc_1093_, 4, v_diag_1079_);
v___x_1084_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
lean_object* v___x_1085_; uint8_t v___x_1086_; uint8_t v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1091_; 
v___x_1085_ = lean_st_ref_put(v_a_1033_, v___x_1084_);
v___x_1086_ = 1;
v___x_1087_ = 0;
v___x_1088_ = l_Lean_LocalContext_mkLambda(v_lctx_1056_, v_fvars_1059_, v_fst_1052_, v___x_1086_, v___x_1087_);
lean_dec(v_fst_1052_);
lean_dec_ref(v_fvars_1059_);
v___x_1089_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1089_, 0, v_paramNames_1058_);
lean_ctor_set(v___x_1089_, 1, v_mvars_1060_);
lean_ctor_set(v___x_1089_, 2, v___x_1088_);
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 0, v___x_1089_);
v___x_1091_ = v___x_1040_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v___x_1089_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractMVars___boxed(lean_object* v_e_1100_, lean_object* v_levels_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_){
_start:
{
uint8_t v_levels_boxed_1107_; lean_object* v_res_1108_; 
v_levels_boxed_1107_ = lean_unbox(v_levels_1101_);
v_res_1108_ = l_Lean_Meta_abstractMVars(v_e_1100_, v_levels_boxed_1107_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_);
lean_dec(v_a_1105_);
lean_dec_ref(v_a_1104_);
lean_dec(v_a_1103_);
lean_dec_ref(v_a_1102_);
return v_res_1108_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_openAbstractMVarsResult_spec__0(size_t v_sz_1109_, size_t v_i_1110_, lean_object* v_bs_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_){
_start:
{
uint8_t v___x_1117_; 
v___x_1117_ = lean_usize_dec_lt(v_i_1110_, v_sz_1109_);
if (v___x_1117_ == 0)
{
lean_object* v___x_1118_; 
v___x_1118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1118_, 0, v_bs_1111_);
return v___x_1118_;
}
else
{
lean_object* v___x_1119_; 
v___x_1119_ = l_Lean_Meta_mkFreshLevelMVar(v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_);
if (lean_obj_tag(v___x_1119_) == 0)
{
lean_object* v_a_1120_; lean_object* v___x_1121_; lean_object* v_bs_x27_1122_; size_t v___x_1123_; size_t v___x_1124_; lean_object* v___x_1125_; 
v_a_1120_ = lean_ctor_get(v___x_1119_, 0);
lean_inc(v_a_1120_);
lean_dec_ref_known(v___x_1119_, 1);
v___x_1121_ = lean_unsigned_to_nat(0u);
v_bs_x27_1122_ = lean_array_uset(v_bs_1111_, v_i_1110_, v___x_1121_);
v___x_1123_ = ((size_t)1ULL);
v___x_1124_ = lean_usize_add(v_i_1110_, v___x_1123_);
v___x_1125_ = lean_array_uset(v_bs_x27_1122_, v_i_1110_, v_a_1120_);
v_i_1110_ = v___x_1124_;
v_bs_1111_ = v___x_1125_;
goto _start;
}
else
{
lean_object* v_a_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1134_; 
lean_dec_ref(v_bs_1111_);
v_a_1127_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1129_ = v___x_1119_;
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_a_1127_);
lean_dec(v___x_1119_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1132_; 
if (v_isShared_1130_ == 0)
{
v___x_1132_ = v___x_1129_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_a_1127_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_openAbstractMVarsResult_spec__0___boxed(lean_object* v_sz_1135_, lean_object* v_i_1136_, lean_object* v_bs_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
size_t v_sz_boxed_1143_; size_t v_i_boxed_1144_; lean_object* v_res_1145_; 
v_sz_boxed_1143_ = lean_unbox_usize(v_sz_1135_);
lean_dec(v_sz_1135_);
v_i_boxed_1144_ = lean_unbox_usize(v_i_1136_);
lean_dec(v_i_1136_);
v_res_1145_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_openAbstractMVarsResult_spec__0(v_sz_boxed_1143_, v_i_boxed_1144_, v_bs_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
lean_dec(v___y_1139_);
lean_dec_ref(v___y_1138_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_openAbstractMVarsResult(lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_){
_start:
{
lean_object* v_paramNames_1152_; lean_object* v_expr_1153_; size_t v_sz_1154_; size_t v___x_1155_; lean_object* v___x_1156_; 
v_paramNames_1152_ = lean_ctor_get(v_a_1146_, 0);
v_expr_1153_ = lean_ctor_get(v_a_1146_, 2);
v_sz_1154_ = lean_array_size(v_paramNames_1152_);
v___x_1155_ = ((size_t)0ULL);
lean_inc_ref(v_paramNames_1152_);
v___x_1156_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_openAbstractMVarsResult_spec__0(v_sz_1154_, v___x_1155_, v_paramNames_1152_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_);
if (lean_obj_tag(v___x_1156_) == 0)
{
lean_object* v_a_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; 
v_a_1157_ = lean_ctor_get(v___x_1156_, 0);
lean_inc(v_a_1157_);
lean_dec_ref_known(v___x_1156_, 1);
lean_inc_ref(v_paramNames_1152_);
v___x_1158_ = l_Lean_Expr_instantiateLevelParamsArray(v_expr_1153_, v_paramNames_1152_, v_a_1157_);
v___x_1159_ = l_Lean_Meta_AbstractMVarsResult_numMVars(v_a_1146_);
lean_dec_ref(v_a_1146_);
v___x_1160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1159_);
v___x_1161_ = l_Lean_Meta_lambdaMetaTelescope(v___x_1158_, v___x_1160_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_);
lean_dec_ref_known(v___x_1160_, 1);
lean_dec_ref(v___x_1158_);
return v___x_1161_;
}
else
{
lean_object* v_a_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1169_; 
lean_dec_ref(v_a_1146_);
v_a_1162_ = lean_ctor_get(v___x_1156_, 0);
v_isSharedCheck_1169_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_1164_ = v___x_1156_;
v_isShared_1165_ = v_isSharedCheck_1169_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_a_1162_);
lean_dec(v___x_1156_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1169_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1167_; 
if (v_isShared_1165_ == 0)
{
v___x_1167_ = v___x_1164_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v_a_1162_);
v___x_1167_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
return v___x_1167_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_openAbstractMVarsResult___boxed(lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_){
_start:
{
lean_object* v_res_1176_; 
v_res_1176_ = l_Lean_Meta_openAbstractMVarsResult(v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_);
lean_dec(v_a_1174_);
lean_dec_ref(v_a_1173_);
lean_dec(v_a_1172_);
lean_dec_ref(v_a_1171_);
return v_res_1176_;
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
