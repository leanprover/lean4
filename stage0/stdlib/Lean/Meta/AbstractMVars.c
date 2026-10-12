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
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2___redArg(lean_object* v_a_170_, lean_object* v_x_171_){
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
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_170_ = stack[0].m_obj;
lean_object* v_x_171_ = stack[1].m_obj;
uint8_t v_res_177_;
v_res_177_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2___redArg(v_a_170_, v_x_171_);
stack->m_num = v_res_177_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2___redArg___boxed(lean_object* v_a_178_, lean_object* v_x_179_){
_start:
{
uint8_t v_res_180_; lean_object* v_r_181_; 
v_res_180_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2___redArg(v_a_178_, v_x_179_);
lean_dec(v_x_179_);
lean_dec(v_a_178_);
v_r_181_ = lean_box(v_res_180_);
return v_r_181_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1___redArg(lean_object* v_m_182_, lean_object* v_a_183_, lean_object* v_b_184_){
_start:
{
lean_object* v_size_185_; lean_object* v_buckets_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_229_; 
v_size_185_ = lean_ctor_get(v_m_182_, 0);
v_buckets_186_ = lean_ctor_get(v_m_182_, 1);
v_isSharedCheck_229_ = !lean_is_exclusive(v_m_182_);
if (v_isSharedCheck_229_ == 0)
{
v___x_188_ = v_m_182_;
v_isShared_189_ = v_isSharedCheck_229_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_buckets_186_);
lean_inc(v_size_185_);
lean_dec(v_m_182_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_229_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_190_; uint64_t v___x_191_; uint64_t v___x_192_; uint64_t v___x_193_; uint64_t v_fold_194_; uint64_t v___x_195_; uint64_t v___x_196_; uint64_t v___x_197_; size_t v___x_198_; size_t v___x_199_; size_t v___x_200_; size_t v___x_201_; size_t v___x_202_; lean_object* v_bkt_203_; uint8_t v___x_204_; 
v___x_190_ = lean_array_get_size(v_buckets_186_);
v___x_191_ = l_Lean_instHashableLevelMVarId_hash(v_a_183_);
v___x_192_ = 32ULL;
v___x_193_ = lean_uint64_shift_right(v___x_191_, v___x_192_);
v_fold_194_ = lean_uint64_xor(v___x_191_, v___x_193_);
v___x_195_ = 16ULL;
v___x_196_ = lean_uint64_shift_right(v_fold_194_, v___x_195_);
v___x_197_ = lean_uint64_xor(v_fold_194_, v___x_196_);
v___x_198_ = lean_uint64_to_usize(v___x_197_);
v___x_199_ = lean_usize_of_nat(v___x_190_);
v___x_200_ = ((size_t)1ULL);
v___x_201_ = lean_usize_sub(v___x_199_, v___x_200_);
v___x_202_ = lean_usize_land(v___x_198_, v___x_201_);
v_bkt_203_ = lean_array_uget_borrowed(v_buckets_186_, v___x_202_);
v___x_204_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2___redArg(v_a_183_, v_bkt_203_);
if (v___x_204_ == 0)
{
lean_object* v___x_205_; lean_object* v_size_x27_206_; lean_object* v___x_207_; lean_object* v_buckets_x27_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; uint8_t v___x_214_; 
v___x_205_ = lean_unsigned_to_nat(1u);
v_size_x27_206_ = lean_nat_add(v_size_185_, v___x_205_);
lean_dec(v_size_185_);
lean_inc(v_bkt_203_);
v___x_207_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_207_, 0, v_a_183_);
lean_ctor_set(v___x_207_, 1, v_b_184_);
lean_ctor_set(v___x_207_, 2, v_bkt_203_);
v_buckets_x27_208_ = lean_array_uset(v_buckets_186_, v___x_202_, v___x_207_);
v___x_209_ = lean_unsigned_to_nat(4u);
v___x_210_ = lean_nat_mul(v_size_x27_206_, v___x_209_);
v___x_211_ = lean_unsigned_to_nat(3u);
v___x_212_ = lean_nat_div(v___x_210_, v___x_211_);
lean_dec(v___x_210_);
v___x_213_ = lean_array_get_size(v_buckets_x27_208_);
v___x_214_ = lean_nat_dec_le(v___x_212_, v___x_213_);
lean_dec(v___x_212_);
if (v___x_214_ == 0)
{
lean_object* v_val_215_; lean_object* v___x_217_; 
v_val_215_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3___redArg(v_buckets_x27_208_);
if (v_isShared_189_ == 0)
{
lean_ctor_set(v___x_188_, 1, v_val_215_);
lean_ctor_set(v___x_188_, 0, v_size_x27_206_);
v___x_217_ = v___x_188_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v_size_x27_206_);
lean_ctor_set(v_reuseFailAlloc_218_, 1, v_val_215_);
v___x_217_ = v_reuseFailAlloc_218_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
return v___x_217_;
}
}
else
{
lean_object* v___x_220_; 
if (v_isShared_189_ == 0)
{
lean_ctor_set(v___x_188_, 1, v_buckets_x27_208_);
lean_ctor_set(v___x_188_, 0, v_size_x27_206_);
v___x_220_ = v___x_188_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v_size_x27_206_);
lean_ctor_set(v_reuseFailAlloc_221_, 1, v_buckets_x27_208_);
v___x_220_ = v_reuseFailAlloc_221_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
return v___x_220_;
}
}
}
else
{
lean_object* v___x_222_; lean_object* v_buckets_x27_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_227_; 
lean_inc(v_bkt_203_);
v___x_222_ = lean_box(0);
v_buckets_x27_223_ = lean_array_uset(v_buckets_186_, v___x_202_, v___x_222_);
v___x_224_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__4___redArg(v_a_183_, v_b_184_, v_bkt_203_);
v___x_225_ = lean_array_uset(v_buckets_x27_223_, v___x_202_, v___x_224_);
if (v_isShared_189_ == 0)
{
lean_ctor_set(v___x_188_, 1, v___x_225_);
v___x_227_ = v___x_188_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v_size_185_);
lean_ctor_set(v_reuseFailAlloc_228_, 1, v___x_225_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
return v___x_227_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0___redArg(lean_object* v_a_230_, lean_object* v_x_231_){
_start:
{
if (lean_obj_tag(v_x_231_) == 0)
{
lean_object* v___x_232_; 
v___x_232_ = lean_box(0);
return v___x_232_;
}
else
{
lean_object* v_key_233_; lean_object* v_value_234_; lean_object* v_tail_235_; uint8_t v___x_236_; 
v_key_233_ = lean_ctor_get(v_x_231_, 0);
v_value_234_ = lean_ctor_get(v_x_231_, 1);
v_tail_235_ = lean_ctor_get(v_x_231_, 2);
v___x_236_ = l_Lean_instBEqLevelMVarId_beq(v_key_233_, v_a_230_);
if (v___x_236_ == 0)
{
v_x_231_ = v_tail_235_;
goto _start;
}
else
{
lean_object* v___x_238_; 
lean_inc(v_value_234_);
v___x_238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_238_, 0, v_value_234_);
return v___x_238_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0___redArg___boxed(lean_object* v_a_239_, lean_object* v_x_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0___redArg(v_a_239_, v_x_240_);
lean_dec(v_x_240_);
lean_dec(v_a_239_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___redArg(lean_object* v_m_242_, lean_object* v_a_243_){
_start:
{
lean_object* v_buckets_244_; lean_object* v___x_245_; uint64_t v___x_246_; uint64_t v___x_247_; uint64_t v___x_248_; uint64_t v_fold_249_; uint64_t v___x_250_; uint64_t v___x_251_; uint64_t v___x_252_; size_t v___x_253_; size_t v___x_254_; size_t v___x_255_; size_t v___x_256_; size_t v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v_buckets_244_ = lean_ctor_get(v_m_242_, 1);
v___x_245_ = lean_array_get_size(v_buckets_244_);
v___x_246_ = l_Lean_instHashableLevelMVarId_hash(v_a_243_);
v___x_247_ = 32ULL;
v___x_248_ = lean_uint64_shift_right(v___x_246_, v___x_247_);
v_fold_249_ = lean_uint64_xor(v___x_246_, v___x_248_);
v___x_250_ = 16ULL;
v___x_251_ = lean_uint64_shift_right(v_fold_249_, v___x_250_);
v___x_252_ = lean_uint64_xor(v_fold_249_, v___x_251_);
v___x_253_ = lean_uint64_to_usize(v___x_252_);
v___x_254_ = lean_usize_of_nat(v___x_245_);
v___x_255_ = ((size_t)1ULL);
v___x_256_ = lean_usize_sub(v___x_254_, v___x_255_);
v___x_257_ = lean_usize_land(v___x_253_, v___x_256_);
v___x_258_ = lean_array_uget_borrowed(v_buckets_244_, v___x_257_);
v___x_259_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0___redArg(v_a_243_, v___x_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___redArg___boxed(lean_object* v_m_260_, lean_object* v_a_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___redArg(v_m_260_, v_a_261_);
lean_dec(v_a_261_);
lean_dec_ref(v_m_260_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(lean_object* v_u_266_, lean_object* v_a_267_){
_start:
{
uint8_t v_abstractLevels_268_; 
v_abstractLevels_268_ = lean_ctor_get_uint8(v_a_267_, sizeof(void*)*9);
if (v_abstractLevels_268_ == 0)
{
lean_object* v___x_269_; 
v___x_269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_269_, 0, v_u_266_);
lean_ctor_set(v___x_269_, 1, v_a_267_);
return v___x_269_;
}
else
{
lean_object* v_ngen_270_; lean_object* v_lctx_271_; lean_object* v_mctx_272_; lean_object* v_nextParamIdx_273_; lean_object* v_paramNames_274_; lean_object* v_fvars_275_; lean_object* v_mvars_276_; lean_object* v_lmap_277_; lean_object* v_emap_278_; uint8_t v___x_279_; 
v_ngen_270_ = lean_ctor_get(v_a_267_, 0);
v_lctx_271_ = lean_ctor_get(v_a_267_, 1);
v_mctx_272_ = lean_ctor_get(v_a_267_, 2);
v_nextParamIdx_273_ = lean_ctor_get(v_a_267_, 3);
v_paramNames_274_ = lean_ctor_get(v_a_267_, 4);
v_fvars_275_ = lean_ctor_get(v_a_267_, 5);
v_mvars_276_ = lean_ctor_get(v_a_267_, 6);
v_lmap_277_ = lean_ctor_get(v_a_267_, 7);
v_emap_278_ = lean_ctor_get(v_a_267_, 8);
v___x_279_ = l_Lean_Level_hasMVar(v_u_266_);
if (v___x_279_ == 0)
{
lean_object* v___x_280_; 
v___x_280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_280_, 0, v_u_266_);
lean_ctor_set(v___x_280_, 1, v_a_267_);
return v___x_280_;
}
else
{
switch(lean_obj_tag(v_u_266_))
{
case 1:
{
lean_object* v_a_281_; lean_object* v___x_282_; lean_object* v_fst_283_; lean_object* v_snd_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_298_; 
v_a_281_ = lean_ctor_get(v_u_266_, 0);
lean_inc(v_a_281_);
v___x_282_ = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(v_a_281_, v_a_267_);
v_fst_283_ = lean_ctor_get(v___x_282_, 0);
v_snd_284_ = lean_ctor_get(v___x_282_, 1);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_298_ == 0)
{
v___x_286_ = v___x_282_;
v_isShared_287_ = v_isSharedCheck_298_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_snd_284_);
lean_inc(v_fst_283_);
lean_dec(v___x_282_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_298_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
size_t v___x_288_; size_t v___x_289_; uint8_t v___x_290_; 
v___x_288_ = lean_ptr_addr(v_a_281_);
v___x_289_ = lean_ptr_addr(v_fst_283_);
v___x_290_ = lean_usize_dec_eq(v___x_288_, v___x_289_);
if (v___x_290_ == 0)
{
lean_object* v___x_291_; lean_object* v___x_293_; 
lean_dec_ref_known(v_u_266_, 1);
v___x_291_ = l_Lean_Level_succ___override(v_fst_283_);
if (v_isShared_287_ == 0)
{
lean_ctor_set(v___x_286_, 0, v___x_291_);
v___x_293_ = v___x_286_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v___x_291_);
lean_ctor_set(v_reuseFailAlloc_294_, 1, v_snd_284_);
v___x_293_ = v_reuseFailAlloc_294_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
return v___x_293_;
}
}
else
{
lean_object* v___x_296_; 
lean_dec(v_fst_283_);
if (v_isShared_287_ == 0)
{
lean_ctor_set(v___x_286_, 0, v_u_266_);
v___x_296_ = v___x_286_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_u_266_);
lean_ctor_set(v_reuseFailAlloc_297_, 1, v_snd_284_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
}
}
case 2:
{
lean_object* v_a_299_; lean_object* v_a_300_; lean_object* v___x_301_; lean_object* v_fst_302_; lean_object* v_snd_303_; lean_object* v___x_304_; lean_object* v_fst_305_; lean_object* v_snd_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_328_; 
v_a_299_ = lean_ctor_get(v_u_266_, 0);
v_a_300_ = lean_ctor_get(v_u_266_, 1);
lean_inc(v_a_299_);
v___x_301_ = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(v_a_299_, v_a_267_);
v_fst_302_ = lean_ctor_get(v___x_301_, 0);
lean_inc(v_fst_302_);
v_snd_303_ = lean_ctor_get(v___x_301_, 1);
lean_inc(v_snd_303_);
lean_dec_ref(v___x_301_);
lean_inc(v_a_300_);
v___x_304_ = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(v_a_300_, v_snd_303_);
v_fst_305_ = lean_ctor_get(v___x_304_, 0);
v_snd_306_ = lean_ctor_get(v___x_304_, 1);
v_isSharedCheck_328_ = !lean_is_exclusive(v___x_304_);
if (v_isSharedCheck_328_ == 0)
{
v___x_308_ = v___x_304_;
v_isShared_309_ = v_isSharedCheck_328_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_snd_306_);
lean_inc(v_fst_305_);
lean_dec(v___x_304_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_328_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
size_t v___x_310_; size_t v___x_311_; uint8_t v___x_312_; 
v___x_310_ = lean_ptr_addr(v_a_299_);
v___x_311_ = lean_ptr_addr(v_fst_302_);
v___x_312_ = lean_usize_dec_eq(v___x_310_, v___x_311_);
if (v___x_312_ == 0)
{
lean_object* v___x_313_; lean_object* v___x_315_; 
lean_dec_ref_known(v_u_266_, 2);
v___x_313_ = l_Lean_mkLevelMax_x27(v_fst_302_, v_fst_305_);
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 0, v___x_313_);
v___x_315_ = v___x_308_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v___x_313_);
lean_ctor_set(v_reuseFailAlloc_316_, 1, v_snd_306_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
else
{
size_t v___x_317_; size_t v___x_318_; uint8_t v___x_319_; 
v___x_317_ = lean_ptr_addr(v_a_300_);
v___x_318_ = lean_ptr_addr(v_fst_305_);
v___x_319_ = lean_usize_dec_eq(v___x_317_, v___x_318_);
if (v___x_319_ == 0)
{
lean_object* v___x_320_; lean_object* v___x_322_; 
lean_dec_ref_known(v_u_266_, 2);
v___x_320_ = l_Lean_mkLevelMax_x27(v_fst_302_, v_fst_305_);
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 0, v___x_320_);
v___x_322_ = v___x_308_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v___x_320_);
lean_ctor_set(v_reuseFailAlloc_323_, 1, v_snd_306_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
else
{
lean_object* v___x_324_; lean_object* v___x_326_; 
v___x_324_ = l_Lean_simpLevelMax_x27(v_fst_302_, v_fst_305_, v_u_266_);
lean_dec_ref_known(v_u_266_, 2);
lean_dec(v_fst_305_);
lean_dec(v_fst_302_);
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 0, v___x_324_);
v___x_326_ = v___x_308_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v___x_324_);
lean_ctor_set(v_reuseFailAlloc_327_, 1, v_snd_306_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
}
}
}
case 3:
{
lean_object* v_a_329_; lean_object* v_a_330_; lean_object* v___x_331_; lean_object* v_fst_332_; lean_object* v_snd_333_; lean_object* v___x_334_; lean_object* v_fst_335_; lean_object* v_snd_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_358_; 
v_a_329_ = lean_ctor_get(v_u_266_, 0);
v_a_330_ = lean_ctor_get(v_u_266_, 1);
lean_inc(v_a_329_);
v___x_331_ = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(v_a_329_, v_a_267_);
v_fst_332_ = lean_ctor_get(v___x_331_, 0);
lean_inc(v_fst_332_);
v_snd_333_ = lean_ctor_get(v___x_331_, 1);
lean_inc(v_snd_333_);
lean_dec_ref(v___x_331_);
lean_inc(v_a_330_);
v___x_334_ = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(v_a_330_, v_snd_333_);
v_fst_335_ = lean_ctor_get(v___x_334_, 0);
v_snd_336_ = lean_ctor_get(v___x_334_, 1);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_334_);
if (v_isSharedCheck_358_ == 0)
{
v___x_338_ = v___x_334_;
v_isShared_339_ = v_isSharedCheck_358_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_snd_336_);
lean_inc(v_fst_335_);
lean_dec(v___x_334_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_358_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
size_t v___x_340_; size_t v___x_341_; uint8_t v___x_342_; 
v___x_340_ = lean_ptr_addr(v_a_329_);
v___x_341_ = lean_ptr_addr(v_fst_332_);
v___x_342_ = lean_usize_dec_eq(v___x_340_, v___x_341_);
if (v___x_342_ == 0)
{
lean_object* v___x_343_; lean_object* v___x_345_; 
lean_dec_ref_known(v_u_266_, 2);
v___x_343_ = l_Lean_mkLevelIMax_x27(v_fst_332_, v_fst_335_);
if (v_isShared_339_ == 0)
{
lean_ctor_set(v___x_338_, 0, v___x_343_);
v___x_345_ = v___x_338_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v___x_343_);
lean_ctor_set(v_reuseFailAlloc_346_, 1, v_snd_336_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
else
{
size_t v___x_347_; size_t v___x_348_; uint8_t v___x_349_; 
v___x_347_ = lean_ptr_addr(v_a_330_);
v___x_348_ = lean_ptr_addr(v_fst_335_);
v___x_349_ = lean_usize_dec_eq(v___x_347_, v___x_348_);
if (v___x_349_ == 0)
{
lean_object* v___x_350_; lean_object* v___x_352_; 
lean_dec_ref_known(v_u_266_, 2);
v___x_350_ = l_Lean_mkLevelIMax_x27(v_fst_332_, v_fst_335_);
if (v_isShared_339_ == 0)
{
lean_ctor_set(v___x_338_, 0, v___x_350_);
v___x_352_ = v___x_338_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v___x_350_);
lean_ctor_set(v_reuseFailAlloc_353_, 1, v_snd_336_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
else
{
lean_object* v___x_354_; lean_object* v___x_356_; 
v___x_354_ = l_Lean_simpLevelIMax_x27(v_fst_332_, v_fst_335_, v_u_266_);
lean_dec_ref_known(v_u_266_, 2);
if (v_isShared_339_ == 0)
{
lean_ctor_set(v___x_338_, 0, v___x_354_);
v___x_356_ = v___x_338_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v___x_354_);
lean_ctor_set(v_reuseFailAlloc_357_, 1, v_snd_336_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
}
}
case 5:
{
lean_object* v_a_359_; lean_object* v_depth_360_; lean_object* v___x_361_; uint8_t v___x_362_; 
v_a_359_ = lean_ctor_get(v_u_266_, 0);
v_depth_360_ = lean_ctor_get(v_mctx_272_, 0);
lean_inc(v_a_359_);
v___x_361_ = l_Lean_MetavarContext_getLevelDepth(v_mctx_272_, v_a_359_);
v___x_362_ = lean_nat_dec_eq(v___x_361_, v_depth_360_);
lean_dec(v___x_361_);
if (v___x_362_ == 0)
{
lean_object* v___x_363_; 
v___x_363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_363_, 0, v_u_266_);
lean_ctor_set(v___x_363_, 1, v_a_267_);
return v___x_363_;
}
else
{
lean_object* v___x_364_; 
lean_inc(v_a_359_);
lean_dec_ref_known(v_u_266_, 1);
v___x_364_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___redArg(v_lmap_277_, v_a_359_);
if (lean_obj_tag(v___x_364_) == 0)
{
lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_379_; 
lean_inc_ref(v_emap_278_);
lean_inc_ref(v_lmap_277_);
lean_inc_ref(v_mvars_276_);
lean_inc_ref(v_fvars_275_);
lean_inc_ref(v_paramNames_274_);
lean_inc(v_nextParamIdx_273_);
lean_inc_ref(v_mctx_272_);
lean_inc_ref(v_lctx_271_);
lean_inc_ref(v_ngen_270_);
v_isSharedCheck_379_ = !lean_is_exclusive(v_a_267_);
if (v_isSharedCheck_379_ == 0)
{
lean_object* v_unused_380_; lean_object* v_unused_381_; lean_object* v_unused_382_; lean_object* v_unused_383_; lean_object* v_unused_384_; lean_object* v_unused_385_; lean_object* v_unused_386_; lean_object* v_unused_387_; lean_object* v_unused_388_; 
v_unused_380_ = lean_ctor_get(v_a_267_, 8);
lean_dec(v_unused_380_);
v_unused_381_ = lean_ctor_get(v_a_267_, 7);
lean_dec(v_unused_381_);
v_unused_382_ = lean_ctor_get(v_a_267_, 6);
lean_dec(v_unused_382_);
v_unused_383_ = lean_ctor_get(v_a_267_, 5);
lean_dec(v_unused_383_);
v_unused_384_ = lean_ctor_get(v_a_267_, 4);
lean_dec(v_unused_384_);
v_unused_385_ = lean_ctor_get(v_a_267_, 3);
lean_dec(v_unused_385_);
v_unused_386_ = lean_ctor_get(v_a_267_, 2);
lean_dec(v_unused_386_);
v_unused_387_ = lean_ctor_get(v_a_267_, 1);
lean_dec(v_unused_387_);
v_unused_388_ = lean_ctor_get(v_a_267_, 0);
lean_dec(v_unused_388_);
v___x_366_ = v_a_267_;
v_isShared_367_ = v_isSharedCheck_379_;
goto v_resetjp_365_;
}
else
{
lean_dec(v_a_267_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_379_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_376_; 
v___x_368_ = ((lean_object*)(l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___closed__1));
lean_inc(v_nextParamIdx_273_);
v___x_369_ = l_Lean_Name_num___override(v___x_368_, v_nextParamIdx_273_);
lean_inc(v___x_369_);
v___x_370_ = l_Lean_mkLevelParam(v___x_369_);
v___x_371_ = lean_unsigned_to_nat(1u);
v___x_372_ = lean_nat_add(v_nextParamIdx_273_, v___x_371_);
lean_dec(v_nextParamIdx_273_);
v___x_373_ = lean_array_push(v_paramNames_274_, v___x_369_);
lean_inc(v___x_370_);
v___x_374_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1___redArg(v_lmap_277_, v_a_359_, v___x_370_);
if (v_isShared_367_ == 0)
{
lean_ctor_set(v___x_366_, 7, v___x_374_);
lean_ctor_set(v___x_366_, 4, v___x_373_);
lean_ctor_set(v___x_366_, 3, v___x_372_);
v___x_376_ = v___x_366_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_ngen_270_);
lean_ctor_set(v_reuseFailAlloc_378_, 1, v_lctx_271_);
lean_ctor_set(v_reuseFailAlloc_378_, 2, v_mctx_272_);
lean_ctor_set(v_reuseFailAlloc_378_, 3, v___x_372_);
lean_ctor_set(v_reuseFailAlloc_378_, 4, v___x_373_);
lean_ctor_set(v_reuseFailAlloc_378_, 5, v_fvars_275_);
lean_ctor_set(v_reuseFailAlloc_378_, 6, v_mvars_276_);
lean_ctor_set(v_reuseFailAlloc_378_, 7, v___x_374_);
lean_ctor_set(v_reuseFailAlloc_378_, 8, v_emap_278_);
lean_ctor_set_uint8(v_reuseFailAlloc_378_, sizeof(void*)*9, v_abstractLevels_268_);
v___x_376_ = v_reuseFailAlloc_378_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
lean_object* v___x_377_; 
v___x_377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_377_, 0, v___x_370_);
lean_ctor_set(v___x_377_, 1, v___x_376_);
return v___x_377_;
}
}
}
else
{
lean_object* v_val_389_; lean_object* v___x_390_; 
lean_dec(v_a_359_);
v_val_389_ = lean_ctor_get(v___x_364_, 0);
lean_inc(v_val_389_);
lean_dec_ref_known(v___x_364_, 1);
v___x_390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_390_, 0, v_val_389_);
lean_ctor_set(v___x_390_, 1, v_a_267_);
return v___x_390_;
}
}
}
default: 
{
lean_object* v___x_391_; 
v___x_391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_391_, 0, v_u_266_);
lean_ctor_set(v___x_391_, 1, v_a_267_);
return v___x_391_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0(lean_object* v_00_u03b2_392_, lean_object* v_m_393_, lean_object* v_a_394_){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___redArg(v_m_393_, v_a_394_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0___boxed(lean_object* v_00_u03b2_396_, lean_object* v_m_397_, lean_object* v_a_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0(v_00_u03b2_396_, v_m_397_, v_a_398_);
lean_dec(v_a_398_);
lean_dec_ref(v_m_397_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1(lean_object* v_00_u03b2_400_, lean_object* v_m_401_, lean_object* v_a_402_, lean_object* v_b_403_){
_start:
{
lean_object* v___x_404_; 
v___x_404_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1___redArg(v_m_401_, v_a_402_, v_b_403_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0(lean_object* v_00_u03b2_405_, lean_object* v_a_406_, lean_object* v_x_407_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0___redArg(v_a_406_, v_x_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0___boxed(lean_object* v_00_u03b2_409_, lean_object* v_a_410_, lean_object* v_x_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__0_spec__0(v_00_u03b2_409_, v_a_410_, v_x_411_);
lean_dec(v_x_411_);
lean_dec(v_a_410_);
return v_res_412_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2(lean_object* v_00_u03b2_413_, lean_object* v_a_414_, lean_object* v_x_415_){
_start:
{
uint8_t v___x_416_; 
v___x_416_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2___redArg(v_a_414_, v_x_415_);
return v___x_416_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_414_ = stack[1].m_obj;
lean_object* v_x_415_ = stack[2].m_obj;
uint8_t v_res_417_;
v_res_417_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2(lean_box(0), v_a_414_, v_x_415_);
stack->m_num = v_res_417_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2___boxed(lean_object* v_00_u03b2_418_, lean_object* v_a_419_, lean_object* v_x_420_){
_start:
{
uint8_t v_res_421_; lean_object* v_r_422_; 
v_res_421_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__2(v_00_u03b2_418_, v_a_419_, v_x_420_);
lean_dec(v_x_420_);
lean_dec(v_a_419_);
v_r_422_ = lean_box(v_res_421_);
return v_r_422_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3(lean_object* v_00_u03b2_423_, lean_object* v_data_424_){
_start:
{
lean_object* v___x_425_; 
v___x_425_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3___redArg(v_data_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__4(lean_object* v_00_u03b2_426_, lean_object* v_a_427_, lean_object* v_b_428_, lean_object* v_x_429_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__4___redArg(v_a_427_, v_b_428_, v_x_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_431_, lean_object* v_i_432_, lean_object* v_source_433_, lean_object* v_target_434_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3_spec__4___redArg(v_i_432_, v_source_433_, v_target_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_436_, lean_object* v_x_437_, lean_object* v_x_438_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars_spec__1_spec__3_spec__4_spec__5___redArg(v_x_437_, v_x_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__1(lean_object* v_e_440_, lean_object* v___y_441_){
_start:
{
uint8_t v___x_442_; 
v___x_442_ = l_Lean_Expr_hasMVar(v_e_440_);
if (v___x_442_ == 0)
{
lean_object* v___x_443_; 
v___x_443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_443_, 0, v_e_440_);
lean_ctor_set(v___x_443_, 1, v___y_441_);
return v___x_443_;
}
else
{
lean_object* v_ngen_444_; lean_object* v_lctx_445_; lean_object* v_mctx_446_; lean_object* v_nextParamIdx_447_; lean_object* v_paramNames_448_; lean_object* v_fvars_449_; lean_object* v_mvars_450_; lean_object* v_lmap_451_; lean_object* v_emap_452_; uint8_t v_abstractLevels_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_470_; 
v_ngen_444_ = lean_ctor_get(v___y_441_, 0);
v_lctx_445_ = lean_ctor_get(v___y_441_, 1);
v_mctx_446_ = lean_ctor_get(v___y_441_, 2);
v_nextParamIdx_447_ = lean_ctor_get(v___y_441_, 3);
v_paramNames_448_ = lean_ctor_get(v___y_441_, 4);
v_fvars_449_ = lean_ctor_get(v___y_441_, 5);
v_mvars_450_ = lean_ctor_get(v___y_441_, 6);
v_lmap_451_ = lean_ctor_get(v___y_441_, 7);
v_emap_452_ = lean_ctor_get(v___y_441_, 8);
v_abstractLevels_453_ = lean_ctor_get_uint8(v___y_441_, sizeof(void*)*9);
v_isSharedCheck_470_ = !lean_is_exclusive(v___y_441_);
if (v_isSharedCheck_470_ == 0)
{
v___x_455_ = v___y_441_;
v_isShared_456_ = v_isSharedCheck_470_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_emap_452_);
lean_inc(v_lmap_451_);
lean_inc(v_mvars_450_);
lean_inc(v_fvars_449_);
lean_inc(v_paramNames_448_);
lean_inc(v_nextParamIdx_447_);
lean_inc(v_mctx_446_);
lean_inc(v_lctx_445_);
lean_inc(v_ngen_444_);
lean_dec(v___y_441_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_470_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_457_; lean_object* v_fst_458_; lean_object* v_snd_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_469_; 
v___x_457_ = l_Lean_instantiateMVarsCore(v_mctx_446_, v_e_440_);
v_fst_458_ = lean_ctor_get(v___x_457_, 0);
v_snd_459_ = lean_ctor_get(v___x_457_, 1);
v_isSharedCheck_469_ = !lean_is_exclusive(v___x_457_);
if (v_isSharedCheck_469_ == 0)
{
v___x_461_ = v___x_457_;
v_isShared_462_ = v_isSharedCheck_469_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_snd_459_);
lean_inc(v_fst_458_);
lean_dec(v___x_457_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_469_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_464_; 
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 2, v_snd_459_);
v___x_464_ = v___x_455_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_ngen_444_);
lean_ctor_set(v_reuseFailAlloc_468_, 1, v_lctx_445_);
lean_ctor_set(v_reuseFailAlloc_468_, 2, v_snd_459_);
lean_ctor_set(v_reuseFailAlloc_468_, 3, v_nextParamIdx_447_);
lean_ctor_set(v_reuseFailAlloc_468_, 4, v_paramNames_448_);
lean_ctor_set(v_reuseFailAlloc_468_, 5, v_fvars_449_);
lean_ctor_set(v_reuseFailAlloc_468_, 6, v_mvars_450_);
lean_ctor_set(v_reuseFailAlloc_468_, 7, v_lmap_451_);
lean_ctor_set(v_reuseFailAlloc_468_, 8, v_emap_452_);
lean_ctor_set_uint8(v_reuseFailAlloc_468_, sizeof(void*)*9, v_abstractLevels_453_);
v___x_464_ = v_reuseFailAlloc_468_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
lean_object* v___x_466_; 
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 1, v___x_464_);
v___x_466_ = v___x_461_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_fst_458_);
lean_ctor_set(v_reuseFailAlloc_467_, 1, v___x_464_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0___redArg(lean_object* v_a_471_, lean_object* v_x_472_){
_start:
{
if (lean_obj_tag(v_x_472_) == 0)
{
lean_object* v___x_473_; 
v___x_473_ = lean_box(0);
return v___x_473_;
}
else
{
lean_object* v_key_474_; lean_object* v_value_475_; lean_object* v_tail_476_; uint8_t v___x_477_; 
v_key_474_ = lean_ctor_get(v_x_472_, 0);
v_value_475_ = lean_ctor_get(v_x_472_, 1);
v_tail_476_ = lean_ctor_get(v_x_472_, 2);
v___x_477_ = l_Lean_instBEqMVarId_beq(v_key_474_, v_a_471_);
if (v___x_477_ == 0)
{
v_x_472_ = v_tail_476_;
goto _start;
}
else
{
lean_object* v___x_479_; 
lean_inc(v_value_475_);
v___x_479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_479_, 0, v_value_475_);
return v___x_479_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0___redArg___boxed(lean_object* v_a_480_, lean_object* v_x_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0___redArg(v_a_480_, v_x_481_);
lean_dec(v_x_481_);
lean_dec(v_a_480_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0___redArg(lean_object* v_m_483_, lean_object* v_a_484_){
_start:
{
lean_object* v_buckets_485_; lean_object* v___x_486_; uint64_t v___x_487_; uint64_t v___x_488_; uint64_t v___x_489_; uint64_t v_fold_490_; uint64_t v___x_491_; uint64_t v___x_492_; uint64_t v___x_493_; size_t v___x_494_; size_t v___x_495_; size_t v___x_496_; size_t v___x_497_; size_t v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v_buckets_485_ = lean_ctor_get(v_m_483_, 1);
v___x_486_ = lean_array_get_size(v_buckets_485_);
v___x_487_ = l_Lean_instHashableMVarId_hash(v_a_484_);
v___x_488_ = 32ULL;
v___x_489_ = lean_uint64_shift_right(v___x_487_, v___x_488_);
v_fold_490_ = lean_uint64_xor(v___x_487_, v___x_489_);
v___x_491_ = 16ULL;
v___x_492_ = lean_uint64_shift_right(v_fold_490_, v___x_491_);
v___x_493_ = lean_uint64_xor(v_fold_490_, v___x_492_);
v___x_494_ = lean_uint64_to_usize(v___x_493_);
v___x_495_ = lean_usize_of_nat(v___x_486_);
v___x_496_ = ((size_t)1ULL);
v___x_497_ = lean_usize_sub(v___x_495_, v___x_496_);
v___x_498_ = lean_usize_land(v___x_494_, v___x_497_);
v___x_499_ = lean_array_uget_borrowed(v_buckets_485_, v___x_498_);
v___x_500_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0___redArg(v_a_484_, v___x_499_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0___redArg___boxed(lean_object* v_m_501_, lean_object* v_a_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0___redArg(v_m_501_, v_a_502_);
lean_dec(v_a_502_);
lean_dec_ref(v_m_501_);
return v_res_503_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3___redArg(lean_object* v_a_504_, lean_object* v_x_505_){
_start:
{
if (lean_obj_tag(v_x_505_) == 0)
{
uint8_t v___x_506_; 
v___x_506_ = 0;
return v___x_506_;
}
else
{
lean_object* v_key_507_; lean_object* v_tail_508_; uint8_t v___x_509_; 
v_key_507_ = lean_ctor_get(v_x_505_, 0);
v_tail_508_ = lean_ctor_get(v_x_505_, 2);
v___x_509_ = l_Lean_instBEqMVarId_beq(v_key_507_, v_a_504_);
if (v___x_509_ == 0)
{
v_x_505_ = v_tail_508_;
goto _start;
}
else
{
return v___x_509_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_504_ = stack[0].m_obj;
lean_object* v_x_505_ = stack[1].m_obj;
uint8_t v_res_511_;
v_res_511_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3___redArg(v_a_504_, v_x_505_);
stack->m_num = v_res_511_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3___redArg___boxed(lean_object* v_a_512_, lean_object* v_x_513_){
_start:
{
uint8_t v_res_514_; lean_object* v_r_515_; 
v_res_514_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3___redArg(v_a_512_, v_x_513_);
lean_dec(v_x_513_);
lean_dec(v_a_512_);
v_r_515_ = lean_box(v_res_514_);
return v_r_515_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__5___redArg(lean_object* v_a_516_, lean_object* v_b_517_, lean_object* v_x_518_){
_start:
{
if (lean_obj_tag(v_x_518_) == 0)
{
lean_dec(v_b_517_);
lean_dec(v_a_516_);
return v_x_518_;
}
else
{
lean_object* v_key_519_; lean_object* v_value_520_; lean_object* v_tail_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_533_; 
v_key_519_ = lean_ctor_get(v_x_518_, 0);
v_value_520_ = lean_ctor_get(v_x_518_, 1);
v_tail_521_ = lean_ctor_get(v_x_518_, 2);
v_isSharedCheck_533_ = !lean_is_exclusive(v_x_518_);
if (v_isSharedCheck_533_ == 0)
{
v___x_523_ = v_x_518_;
v_isShared_524_ = v_isSharedCheck_533_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_tail_521_);
lean_inc(v_value_520_);
lean_inc(v_key_519_);
lean_dec(v_x_518_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_533_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
uint8_t v___x_525_; 
v___x_525_ = l_Lean_instBEqMVarId_beq(v_key_519_, v_a_516_);
if (v___x_525_ == 0)
{
lean_object* v___x_526_; lean_object* v___x_528_; 
v___x_526_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__5___redArg(v_a_516_, v_b_517_, v_tail_521_);
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 2, v___x_526_);
v___x_528_ = v___x_523_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_key_519_);
lean_ctor_set(v_reuseFailAlloc_529_, 1, v_value_520_);
lean_ctor_set(v_reuseFailAlloc_529_, 2, v___x_526_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
else
{
lean_object* v___x_531_; 
lean_dec(v_value_520_);
lean_dec(v_key_519_);
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 1, v_b_517_);
lean_ctor_set(v___x_523_, 0, v_a_516_);
v___x_531_ = v___x_523_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v_a_516_);
lean_ctor_set(v_reuseFailAlloc_532_, 1, v_b_517_);
lean_ctor_set(v_reuseFailAlloc_532_, 2, v_tail_521_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4_spec__5_spec__7___redArg(lean_object* v_x_534_, lean_object* v_x_535_){
_start:
{
if (lean_obj_tag(v_x_535_) == 0)
{
return v_x_534_;
}
else
{
lean_object* v_key_536_; lean_object* v_value_537_; lean_object* v_tail_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_561_; 
v_key_536_ = lean_ctor_get(v_x_535_, 0);
v_value_537_ = lean_ctor_get(v_x_535_, 1);
v_tail_538_ = lean_ctor_get(v_x_535_, 2);
v_isSharedCheck_561_ = !lean_is_exclusive(v_x_535_);
if (v_isSharedCheck_561_ == 0)
{
v___x_540_ = v_x_535_;
v_isShared_541_ = v_isSharedCheck_561_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_tail_538_);
lean_inc(v_value_537_);
lean_inc(v_key_536_);
lean_dec(v_x_535_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_561_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_542_; uint64_t v___x_543_; uint64_t v___x_544_; uint64_t v___x_545_; uint64_t v_fold_546_; uint64_t v___x_547_; uint64_t v___x_548_; uint64_t v___x_549_; size_t v___x_550_; size_t v___x_551_; size_t v___x_552_; size_t v___x_553_; size_t v___x_554_; lean_object* v___x_555_; lean_object* v___x_557_; 
v___x_542_ = lean_array_get_size(v_x_534_);
v___x_543_ = l_Lean_instHashableMVarId_hash(v_key_536_);
v___x_544_ = 32ULL;
v___x_545_ = lean_uint64_shift_right(v___x_543_, v___x_544_);
v_fold_546_ = lean_uint64_xor(v___x_543_, v___x_545_);
v___x_547_ = 16ULL;
v___x_548_ = lean_uint64_shift_right(v_fold_546_, v___x_547_);
v___x_549_ = lean_uint64_xor(v_fold_546_, v___x_548_);
v___x_550_ = lean_uint64_to_usize(v___x_549_);
v___x_551_ = lean_usize_of_nat(v___x_542_);
v___x_552_ = ((size_t)1ULL);
v___x_553_ = lean_usize_sub(v___x_551_, v___x_552_);
v___x_554_ = lean_usize_land(v___x_550_, v___x_553_);
v___x_555_ = lean_array_uget_borrowed(v_x_534_, v___x_554_);
lean_inc(v___x_555_);
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 2, v___x_555_);
v___x_557_ = v___x_540_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_key_536_);
lean_ctor_set(v_reuseFailAlloc_560_, 1, v_value_537_);
lean_ctor_set(v_reuseFailAlloc_560_, 2, v___x_555_);
v___x_557_ = v_reuseFailAlloc_560_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
lean_object* v___x_558_; 
v___x_558_ = lean_array_uset(v_x_534_, v___x_554_, v___x_557_);
v_x_534_ = v___x_558_;
v_x_535_ = v_tail_538_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4_spec__5___redArg(lean_object* v_i_562_, lean_object* v_source_563_, lean_object* v_target_564_){
_start:
{
lean_object* v___x_565_; uint8_t v___x_566_; 
v___x_565_ = lean_array_get_size(v_source_563_);
v___x_566_ = lean_nat_dec_lt(v_i_562_, v___x_565_);
if (v___x_566_ == 0)
{
lean_dec_ref(v_source_563_);
lean_dec(v_i_562_);
return v_target_564_;
}
else
{
lean_object* v_es_567_; lean_object* v___x_568_; lean_object* v_source_569_; lean_object* v_target_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v_es_567_ = lean_array_fget(v_source_563_, v_i_562_);
v___x_568_ = lean_box(0);
v_source_569_ = lean_array_fset(v_source_563_, v_i_562_, v___x_568_);
v_target_570_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4_spec__5_spec__7___redArg(v_target_564_, v_es_567_);
v___x_571_ = lean_unsigned_to_nat(1u);
v___x_572_ = lean_nat_add(v_i_562_, v___x_571_);
lean_dec(v_i_562_);
v_i_562_ = v___x_572_;
v_source_563_ = v_source_569_;
v_target_564_ = v_target_570_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4___redArg(lean_object* v_data_574_){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v_nbuckets_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_575_ = lean_array_get_size(v_data_574_);
v___x_576_ = lean_unsigned_to_nat(2u);
v_nbuckets_577_ = lean_nat_mul(v___x_575_, v___x_576_);
v___x_578_ = lean_unsigned_to_nat(0u);
v___x_579_ = lean_box(0);
v___x_580_ = lean_mk_array(v_nbuckets_577_, v___x_579_);
v___x_581_ = lean_array_propagate_mark(v_data_574_, v___x_580_);
v___x_582_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4_spec__5___redArg(v___x_578_, v_data_574_, v___x_581_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2___redArg(lean_object* v_m_583_, lean_object* v_a_584_, lean_object* v_b_585_){
_start:
{
lean_object* v_size_586_; lean_object* v_buckets_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_630_; 
v_size_586_ = lean_ctor_get(v_m_583_, 0);
v_buckets_587_ = lean_ctor_get(v_m_583_, 1);
v_isSharedCheck_630_ = !lean_is_exclusive(v_m_583_);
if (v_isSharedCheck_630_ == 0)
{
v___x_589_ = v_m_583_;
v_isShared_590_ = v_isSharedCheck_630_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_buckets_587_);
lean_inc(v_size_586_);
lean_dec(v_m_583_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_630_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___x_591_; uint64_t v___x_592_; uint64_t v___x_593_; uint64_t v___x_594_; uint64_t v_fold_595_; uint64_t v___x_596_; uint64_t v___x_597_; uint64_t v___x_598_; size_t v___x_599_; size_t v___x_600_; size_t v___x_601_; size_t v___x_602_; size_t v___x_603_; lean_object* v_bkt_604_; uint8_t v___x_605_; 
v___x_591_ = lean_array_get_size(v_buckets_587_);
v___x_592_ = l_Lean_instHashableMVarId_hash(v_a_584_);
v___x_593_ = 32ULL;
v___x_594_ = lean_uint64_shift_right(v___x_592_, v___x_593_);
v_fold_595_ = lean_uint64_xor(v___x_592_, v___x_594_);
v___x_596_ = 16ULL;
v___x_597_ = lean_uint64_shift_right(v_fold_595_, v___x_596_);
v___x_598_ = lean_uint64_xor(v_fold_595_, v___x_597_);
v___x_599_ = lean_uint64_to_usize(v___x_598_);
v___x_600_ = lean_usize_of_nat(v___x_591_);
v___x_601_ = ((size_t)1ULL);
v___x_602_ = lean_usize_sub(v___x_600_, v___x_601_);
v___x_603_ = lean_usize_land(v___x_599_, v___x_602_);
v_bkt_604_ = lean_array_uget_borrowed(v_buckets_587_, v___x_603_);
v___x_605_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3___redArg(v_a_584_, v_bkt_604_);
if (v___x_605_ == 0)
{
lean_object* v___x_606_; lean_object* v_size_x27_607_; lean_object* v___x_608_; lean_object* v_buckets_x27_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; uint8_t v___x_615_; 
v___x_606_ = lean_unsigned_to_nat(1u);
v_size_x27_607_ = lean_nat_add(v_size_586_, v___x_606_);
lean_dec(v_size_586_);
lean_inc(v_bkt_604_);
v___x_608_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_608_, 0, v_a_584_);
lean_ctor_set(v___x_608_, 1, v_b_585_);
lean_ctor_set(v___x_608_, 2, v_bkt_604_);
v_buckets_x27_609_ = lean_array_uset(v_buckets_587_, v___x_603_, v___x_608_);
v___x_610_ = lean_unsigned_to_nat(4u);
v___x_611_ = lean_nat_mul(v_size_x27_607_, v___x_610_);
v___x_612_ = lean_unsigned_to_nat(3u);
v___x_613_ = lean_nat_div(v___x_611_, v___x_612_);
lean_dec(v___x_611_);
v___x_614_ = lean_array_get_size(v_buckets_x27_609_);
v___x_615_ = lean_nat_dec_le(v___x_613_, v___x_614_);
lean_dec(v___x_613_);
if (v___x_615_ == 0)
{
lean_object* v_val_616_; lean_object* v___x_618_; 
v_val_616_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4___redArg(v_buckets_x27_609_);
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 1, v_val_616_);
lean_ctor_set(v___x_589_, 0, v_size_x27_607_);
v___x_618_ = v___x_589_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_size_x27_607_);
lean_ctor_set(v_reuseFailAlloc_619_, 1, v_val_616_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
else
{
lean_object* v___x_621_; 
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 1, v_buckets_x27_609_);
lean_ctor_set(v___x_589_, 0, v_size_x27_607_);
v___x_621_ = v___x_589_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_size_x27_607_);
lean_ctor_set(v_reuseFailAlloc_622_, 1, v_buckets_x27_609_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
else
{
lean_object* v___x_623_; lean_object* v_buckets_x27_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_628_; 
lean_inc(v_bkt_604_);
v___x_623_ = lean_box(0);
v_buckets_x27_624_ = lean_array_uset(v_buckets_587_, v___x_603_, v___x_623_);
v___x_625_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__5___redArg(v_a_584_, v_b_585_, v_bkt_604_);
v___x_626_ = lean_array_uset(v_buckets_x27_624_, v___x_603_, v___x_625_);
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 1, v___x_626_);
v___x_628_ = v___x_589_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_size_586_);
lean_ctor_set(v_reuseFailAlloc_629_, 1, v___x_626_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__3(lean_object* v_x_631_, lean_object* v_x_632_, lean_object* v___y_633_){
_start:
{
if (lean_obj_tag(v_x_631_) == 0)
{
lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_634_ = l_List_reverse___redArg(v_x_632_);
v___x_635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_635_, 0, v___x_634_);
lean_ctor_set(v___x_635_, 1, v___y_633_);
return v___x_635_;
}
else
{
lean_object* v_head_636_; lean_object* v_tail_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_648_; 
v_head_636_ = lean_ctor_get(v_x_631_, 0);
v_tail_637_ = lean_ctor_get(v_x_631_, 1);
v_isSharedCheck_648_ = !lean_is_exclusive(v_x_631_);
if (v_isSharedCheck_648_ == 0)
{
v___x_639_ = v_x_631_;
v_isShared_640_ = v_isSharedCheck_648_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_tail_637_);
lean_inc(v_head_636_);
lean_dec(v_x_631_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_648_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_641_; lean_object* v_fst_642_; lean_object* v_snd_643_; lean_object* v___x_645_; 
v___x_641_ = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(v_head_636_, v___y_633_);
v_fst_642_ = lean_ctor_get(v___x_641_, 0);
lean_inc(v_fst_642_);
v_snd_643_ = lean_ctor_get(v___x_641_, 1);
lean_inc(v_snd_643_);
lean_dec_ref(v___x_641_);
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 1, v_x_632_);
lean_ctor_set(v___x_639_, 0, v_fst_642_);
v___x_645_ = v___x_639_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_fst_642_);
lean_ctor_set(v_reuseFailAlloc_647_, 1, v_x_632_);
v___x_645_ = v_reuseFailAlloc_647_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
v_x_631_ = v_tail_637_;
v_x_632_ = v___x_645_;
v___y_633_ = v_snd_643_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_abstractExprMVars(lean_object* v_e_652_, lean_object* v_a_653_){
_start:
{
uint8_t v___x_654_; 
v___x_654_ = l_Lean_Expr_hasMVar(v_e_652_);
if (v___x_654_ == 0)
{
lean_object* v___x_655_; 
v___x_655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_655_, 0, v_e_652_);
lean_ctor_set(v___x_655_, 1, v_a_653_);
return v___x_655_;
}
else
{
switch(lean_obj_tag(v_e_652_))
{
case 2:
{
lean_object* v_mvarId_656_; lean_object* v_mctx_657_; lean_object* v_emap_658_; lean_object* v___x_659_; lean_object* v_userName_660_; lean_object* v_type_661_; lean_object* v_depth_662_; lean_object* v_depth_663_; uint8_t v___x_664_; 
v_mvarId_656_ = lean_ctor_get(v_e_652_, 0);
v_mctx_657_ = lean_ctor_get(v_a_653_, 2);
v_emap_658_ = lean_ctor_get(v_a_653_, 8);
lean_inc(v_mvarId_656_);
v___x_659_ = l_Lean_MetavarContext_getDecl(v_mctx_657_, v_mvarId_656_);
v_userName_660_ = lean_ctor_get(v___x_659_, 0);
lean_inc(v_userName_660_);
v_type_661_ = lean_ctor_get(v___x_659_, 2);
lean_inc_ref(v_type_661_);
v_depth_662_ = lean_ctor_get(v___x_659_, 3);
lean_inc(v_depth_662_);
lean_dec_ref(v___x_659_);
v_depth_663_ = lean_ctor_get(v_mctx_657_, 0);
v___x_664_ = lean_nat_dec_eq(v_depth_662_, v_depth_663_);
lean_dec(v_depth_662_);
if (v___x_664_ == 0)
{
lean_object* v___x_665_; 
lean_dec_ref(v_type_661_);
lean_dec(v_userName_660_);
v___x_665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_665_, 0, v_e_652_);
lean_ctor_set(v___x_665_, 1, v_a_653_);
return v___x_665_;
}
else
{
lean_object* v___x_666_; 
lean_inc(v_mvarId_656_);
v___x_666_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0___redArg(v_emap_658_, v_mvarId_656_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_object* v___x_667_; lean_object* v_fst_668_; lean_object* v_snd_669_; lean_object* v___x_670_; lean_object* v_fst_671_; lean_object* v_snd_672_; lean_object* v___x_673_; lean_object* v_fst_674_; lean_object* v_snd_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_713_; 
v___x_667_ = l_Lean_instantiateMVars___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__1(v_type_661_, v_a_653_);
v_fst_668_ = lean_ctor_get(v___x_667_, 0);
lean_inc(v_fst_668_);
v_snd_669_ = lean_ctor_get(v___x_667_, 1);
lean_inc(v_snd_669_);
lean_dec_ref(v___x_667_);
v___x_670_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_fst_668_, v_snd_669_);
v_fst_671_ = lean_ctor_get(v___x_670_, 0);
lean_inc(v_fst_671_);
v_snd_672_ = lean_ctor_get(v___x_670_, 1);
lean_inc(v_snd_672_);
lean_dec_ref(v___x_670_);
v___x_673_ = l_Lean_Meta_AbstractMVars_mkFreshFVarId(v_snd_672_);
v_fst_674_ = lean_ctor_get(v___x_673_, 0);
v_snd_675_ = lean_ctor_get(v___x_673_, 1);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_713_ == 0)
{
v___x_677_ = v___x_673_;
v_isShared_678_ = v_isSharedCheck_713_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_snd_675_);
lean_inc(v_fst_674_);
lean_dec(v___x_673_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_713_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_679_; lean_object* v_userName_681_; uint8_t v___x_708_; 
lean_inc(v_fst_674_);
v___x_679_ = l_Lean_mkFVar(v_fst_674_);
v___x_708_ = l_Lean_Name_isAnonymous(v_userName_660_);
if (v___x_708_ == 0)
{
v_userName_681_ = v_userName_660_;
goto v___jp_680_;
}
else
{
lean_object* v_fvars_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
lean_dec(v_userName_660_);
v_fvars_709_ = lean_ctor_get(v_snd_675_, 5);
v___x_710_ = ((lean_object*)(l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__1));
v___x_711_ = lean_array_get_size(v_fvars_709_);
v___x_712_ = lean_name_append_index_after(v___x_710_, v___x_711_);
v_userName_681_ = v___x_712_;
goto v___jp_680_;
}
v___jp_680_:
{
lean_object* v_ngen_682_; lean_object* v_lctx_683_; lean_object* v_mctx_684_; lean_object* v_nextParamIdx_685_; lean_object* v_paramNames_686_; lean_object* v_fvars_687_; lean_object* v_mvars_688_; lean_object* v_lmap_689_; lean_object* v_emap_690_; uint8_t v_abstractLevels_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_707_; 
v_ngen_682_ = lean_ctor_get(v_snd_675_, 0);
v_lctx_683_ = lean_ctor_get(v_snd_675_, 1);
v_mctx_684_ = lean_ctor_get(v_snd_675_, 2);
v_nextParamIdx_685_ = lean_ctor_get(v_snd_675_, 3);
v_paramNames_686_ = lean_ctor_get(v_snd_675_, 4);
v_fvars_687_ = lean_ctor_get(v_snd_675_, 5);
v_mvars_688_ = lean_ctor_get(v_snd_675_, 6);
v_lmap_689_ = lean_ctor_get(v_snd_675_, 7);
v_emap_690_ = lean_ctor_get(v_snd_675_, 8);
v_abstractLevels_691_ = lean_ctor_get_uint8(v_snd_675_, sizeof(void*)*9);
v_isSharedCheck_707_ = !lean_is_exclusive(v_snd_675_);
if (v_isSharedCheck_707_ == 0)
{
v___x_693_ = v_snd_675_;
v_isShared_694_ = v_isSharedCheck_707_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_emap_690_);
lean_inc(v_lmap_689_);
lean_inc(v_mvars_688_);
lean_inc(v_fvars_687_);
lean_inc(v_paramNames_686_);
lean_inc(v_nextParamIdx_685_);
lean_inc(v_mctx_684_);
lean_inc(v_lctx_683_);
lean_inc(v_ngen_682_);
lean_dec(v_snd_675_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_707_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
uint8_t v___x_695_; uint8_t v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_702_; 
v___x_695_ = 0;
v___x_696_ = 0;
v___x_697_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_683_, v_fst_674_, v_userName_681_, v_fst_671_, v___x_695_, v___x_696_);
lean_inc_ref_n(v___x_679_, 2);
v___x_698_ = lean_array_push(v_fvars_687_, v___x_679_);
v___x_699_ = lean_array_push(v_mvars_688_, v_e_652_);
v___x_700_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2___redArg(v_emap_690_, v_mvarId_656_, v___x_679_);
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 8, v___x_700_);
lean_ctor_set(v___x_693_, 6, v___x_699_);
lean_ctor_set(v___x_693_, 5, v___x_698_);
lean_ctor_set(v___x_693_, 1, v___x_697_);
v___x_702_ = v___x_693_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_ngen_682_);
lean_ctor_set(v_reuseFailAlloc_706_, 1, v___x_697_);
lean_ctor_set(v_reuseFailAlloc_706_, 2, v_mctx_684_);
lean_ctor_set(v_reuseFailAlloc_706_, 3, v_nextParamIdx_685_);
lean_ctor_set(v_reuseFailAlloc_706_, 4, v_paramNames_686_);
lean_ctor_set(v_reuseFailAlloc_706_, 5, v___x_698_);
lean_ctor_set(v_reuseFailAlloc_706_, 6, v___x_699_);
lean_ctor_set(v_reuseFailAlloc_706_, 7, v_lmap_689_);
lean_ctor_set(v_reuseFailAlloc_706_, 8, v___x_700_);
lean_ctor_set_uint8(v_reuseFailAlloc_706_, sizeof(void*)*9, v_abstractLevels_691_);
v___x_702_ = v_reuseFailAlloc_706_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
lean_object* v___x_704_; 
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 1, v___x_702_);
lean_ctor_set(v___x_677_, 0, v___x_679_);
v___x_704_ = v___x_677_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_679_);
lean_ctor_set(v_reuseFailAlloc_705_, 1, v___x_702_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
}
}
}
else
{
lean_object* v_val_714_; lean_object* v___x_715_; 
lean_dec_ref(v_type_661_);
lean_dec(v_userName_660_);
lean_dec(v_mvarId_656_);
lean_dec_ref_known(v_e_652_, 1);
v_val_714_ = lean_ctor_get(v___x_666_, 0);
lean_inc(v_val_714_);
lean_dec_ref_known(v___x_666_, 1);
v___x_715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_715_, 0, v_val_714_);
lean_ctor_set(v___x_715_, 1, v_a_653_);
return v___x_715_;
}
}
}
case 3:
{
lean_object* v_u_716_; lean_object* v___x_717_; lean_object* v_fst_718_; lean_object* v_snd_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_733_; 
v_u_716_ = lean_ctor_get(v_e_652_, 0);
lean_inc(v_u_716_);
v___x_717_ = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(v_u_716_, v_a_653_);
v_fst_718_ = lean_ctor_get(v___x_717_, 0);
v_snd_719_ = lean_ctor_get(v___x_717_, 1);
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_733_ == 0)
{
v___x_721_ = v___x_717_;
v_isShared_722_ = v_isSharedCheck_733_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_snd_719_);
lean_inc(v_fst_718_);
lean_dec(v___x_717_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_733_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
size_t v___x_723_; size_t v___x_724_; uint8_t v___x_725_; 
v___x_723_ = lean_ptr_addr(v_u_716_);
v___x_724_ = lean_ptr_addr(v_fst_718_);
v___x_725_ = lean_usize_dec_eq(v___x_723_, v___x_724_);
if (v___x_725_ == 0)
{
lean_object* v___x_726_; lean_object* v___x_728_; 
lean_dec_ref_known(v_e_652_, 1);
v___x_726_ = l_Lean_Expr_sort___override(v_fst_718_);
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 0, v___x_726_);
v___x_728_ = v___x_721_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v___x_726_);
lean_ctor_set(v_reuseFailAlloc_729_, 1, v_snd_719_);
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
lean_object* v___x_731_; 
lean_dec(v_fst_718_);
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 0, v_e_652_);
v___x_731_ = v___x_721_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_e_652_);
lean_ctor_set(v_reuseFailAlloc_732_, 1, v_snd_719_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
}
}
case 4:
{
lean_object* v_declName_734_; lean_object* v_us_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v_fst_738_; lean_object* v_snd_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_751_; 
v_declName_734_ = lean_ctor_get(v_e_652_, 0);
v_us_735_ = lean_ctor_get(v_e_652_, 1);
v___x_736_ = lean_box(0);
lean_inc(v_us_735_);
v___x_737_ = l_List_mapM_loop___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__3(v_us_735_, v___x_736_, v_a_653_);
v_fst_738_ = lean_ctor_get(v___x_737_, 0);
v_snd_739_ = lean_ctor_get(v___x_737_, 1);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_751_ == 0)
{
v___x_741_ = v___x_737_;
v_isShared_742_ = v_isSharedCheck_751_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_snd_739_);
lean_inc(v_fst_738_);
lean_dec(v___x_737_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_751_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
uint8_t v___x_743_; 
v___x_743_ = l_ptrEqList___redArg(v_us_735_, v_fst_738_);
if (v___x_743_ == 0)
{
lean_object* v___x_744_; lean_object* v___x_746_; 
lean_inc(v_declName_734_);
lean_dec_ref_known(v_e_652_, 2);
v___x_744_ = l_Lean_Expr_const___override(v_declName_734_, v_fst_738_);
if (v_isShared_742_ == 0)
{
lean_ctor_set(v___x_741_, 0, v___x_744_);
v___x_746_ = v___x_741_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v___x_744_);
lean_ctor_set(v_reuseFailAlloc_747_, 1, v_snd_739_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
else
{
lean_object* v___x_749_; 
lean_dec(v_fst_738_);
if (v_isShared_742_ == 0)
{
lean_ctor_set(v___x_741_, 0, v_e_652_);
v___x_749_ = v___x_741_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_e_652_);
lean_ctor_set(v_reuseFailAlloc_750_, 1, v_snd_739_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
}
case 5:
{
lean_object* v_fn_752_; lean_object* v_arg_753_; lean_object* v___x_754_; lean_object* v_fst_755_; lean_object* v_snd_756_; lean_object* v___x_757_; lean_object* v_fst_758_; lean_object* v_snd_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_780_; 
v_fn_752_ = lean_ctor_get(v_e_652_, 0);
v_arg_753_ = lean_ctor_get(v_e_652_, 1);
lean_inc_ref(v_fn_752_);
v___x_754_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_fn_752_, v_a_653_);
v_fst_755_ = lean_ctor_get(v___x_754_, 0);
lean_inc(v_fst_755_);
v_snd_756_ = lean_ctor_get(v___x_754_, 1);
lean_inc(v_snd_756_);
lean_dec_ref(v___x_754_);
lean_inc_ref(v_arg_753_);
v___x_757_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_arg_753_, v_snd_756_);
v_fst_758_ = lean_ctor_get(v___x_757_, 0);
v_snd_759_ = lean_ctor_get(v___x_757_, 1);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_757_);
if (v_isSharedCheck_780_ == 0)
{
v___x_761_ = v___x_757_;
v_isShared_762_ = v_isSharedCheck_780_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_snd_759_);
lean_inc(v_fst_758_);
lean_dec(v___x_757_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_780_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
size_t v___x_763_; size_t v___x_764_; uint8_t v___x_765_; 
v___x_763_ = lean_ptr_addr(v_fn_752_);
v___x_764_ = lean_ptr_addr(v_fst_755_);
v___x_765_ = lean_usize_dec_eq(v___x_763_, v___x_764_);
if (v___x_765_ == 0)
{
lean_object* v___x_766_; lean_object* v___x_768_; 
lean_dec_ref_known(v_e_652_, 2);
v___x_766_ = l_Lean_Expr_app___override(v_fst_755_, v_fst_758_);
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 0, v___x_766_);
v___x_768_ = v___x_761_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_766_);
lean_ctor_set(v_reuseFailAlloc_769_, 1, v_snd_759_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
else
{
size_t v___x_770_; size_t v___x_771_; uint8_t v___x_772_; 
v___x_770_ = lean_ptr_addr(v_arg_753_);
v___x_771_ = lean_ptr_addr(v_fst_758_);
v___x_772_ = lean_usize_dec_eq(v___x_770_, v___x_771_);
if (v___x_772_ == 0)
{
lean_object* v___x_773_; lean_object* v___x_775_; 
lean_dec_ref_known(v_e_652_, 2);
v___x_773_ = l_Lean_Expr_app___override(v_fst_755_, v_fst_758_);
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 0, v___x_773_);
v___x_775_ = v___x_761_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_773_);
lean_ctor_set(v_reuseFailAlloc_776_, 1, v_snd_759_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
else
{
lean_object* v___x_778_; 
lean_dec(v_fst_758_);
lean_dec(v_fst_755_);
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 0, v_e_652_);
v___x_778_ = v___x_761_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_e_652_);
lean_ctor_set(v_reuseFailAlloc_779_, 1, v_snd_759_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
}
}
case 6:
{
lean_object* v_binderName_781_; lean_object* v_binderType_782_; lean_object* v_body_783_; uint8_t v_binderInfo_784_; lean_object* v___x_785_; lean_object* v_fst_786_; lean_object* v_snd_787_; lean_object* v___x_788_; lean_object* v_fst_789_; lean_object* v_snd_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_816_; 
v_binderName_781_ = lean_ctor_get(v_e_652_, 0);
v_binderType_782_ = lean_ctor_get(v_e_652_, 1);
v_body_783_ = lean_ctor_get(v_e_652_, 2);
v_binderInfo_784_ = lean_ctor_get_uint8(v_e_652_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_782_);
v___x_785_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_binderType_782_, v_a_653_);
v_fst_786_ = lean_ctor_get(v___x_785_, 0);
lean_inc(v_fst_786_);
v_snd_787_ = lean_ctor_get(v___x_785_, 1);
lean_inc(v_snd_787_);
lean_dec_ref(v___x_785_);
lean_inc_ref(v_body_783_);
v___x_788_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_body_783_, v_snd_787_);
v_fst_789_ = lean_ctor_get(v___x_788_, 0);
v_snd_790_ = lean_ctor_get(v___x_788_, 1);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_816_ == 0)
{
v___x_792_ = v___x_788_;
v_isShared_793_ = v_isSharedCheck_816_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_snd_790_);
lean_inc(v_fst_789_);
lean_dec(v___x_788_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_816_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
size_t v___x_794_; size_t v___x_795_; uint8_t v___x_796_; 
v___x_794_ = lean_ptr_addr(v_binderType_782_);
v___x_795_ = lean_ptr_addr(v_fst_786_);
v___x_796_ = lean_usize_dec_eq(v___x_794_, v___x_795_);
if (v___x_796_ == 0)
{
lean_object* v___x_797_; lean_object* v___x_799_; 
lean_inc(v_binderName_781_);
lean_dec_ref_known(v_e_652_, 3);
v___x_797_ = l_Lean_Expr_lam___override(v_binderName_781_, v_fst_786_, v_fst_789_, v_binderInfo_784_);
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 0, v___x_797_);
v___x_799_ = v___x_792_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v___x_797_);
lean_ctor_set(v_reuseFailAlloc_800_, 1, v_snd_790_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
else
{
size_t v___x_801_; size_t v___x_802_; uint8_t v___x_803_; 
v___x_801_ = lean_ptr_addr(v_body_783_);
v___x_802_ = lean_ptr_addr(v_fst_789_);
v___x_803_ = lean_usize_dec_eq(v___x_801_, v___x_802_);
if (v___x_803_ == 0)
{
lean_object* v___x_804_; lean_object* v___x_806_; 
lean_inc(v_binderName_781_);
lean_dec_ref_known(v_e_652_, 3);
v___x_804_ = l_Lean_Expr_lam___override(v_binderName_781_, v_fst_786_, v_fst_789_, v_binderInfo_784_);
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 0, v___x_804_);
v___x_806_ = v___x_792_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v___x_804_);
lean_ctor_set(v_reuseFailAlloc_807_, 1, v_snd_790_);
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
uint8_t v___x_808_; 
v___x_808_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_784_, v_binderInfo_784_);
if (v___x_808_ == 0)
{
lean_object* v___x_809_; lean_object* v___x_811_; 
lean_inc(v_binderName_781_);
lean_dec_ref_known(v_e_652_, 3);
v___x_809_ = l_Lean_Expr_lam___override(v_binderName_781_, v_fst_786_, v_fst_789_, v_binderInfo_784_);
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 0, v___x_809_);
v___x_811_ = v___x_792_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v___x_809_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v_snd_790_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
else
{
lean_object* v___x_814_; 
lean_dec(v_fst_789_);
lean_dec(v_fst_786_);
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 0, v_e_652_);
v___x_814_ = v___x_792_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_e_652_);
lean_ctor_set(v_reuseFailAlloc_815_, 1, v_snd_790_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
}
}
}
}
case 7:
{
lean_object* v_binderName_817_; lean_object* v_binderType_818_; lean_object* v_body_819_; uint8_t v_binderInfo_820_; lean_object* v___x_821_; lean_object* v_fst_822_; lean_object* v_snd_823_; lean_object* v___x_824_; lean_object* v_fst_825_; lean_object* v_snd_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_852_; 
v_binderName_817_ = lean_ctor_get(v_e_652_, 0);
v_binderType_818_ = lean_ctor_get(v_e_652_, 1);
v_body_819_ = lean_ctor_get(v_e_652_, 2);
v_binderInfo_820_ = lean_ctor_get_uint8(v_e_652_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_818_);
v___x_821_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_binderType_818_, v_a_653_);
v_fst_822_ = lean_ctor_get(v___x_821_, 0);
lean_inc(v_fst_822_);
v_snd_823_ = lean_ctor_get(v___x_821_, 1);
lean_inc(v_snd_823_);
lean_dec_ref(v___x_821_);
lean_inc_ref(v_body_819_);
v___x_824_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_body_819_, v_snd_823_);
v_fst_825_ = lean_ctor_get(v___x_824_, 0);
v_snd_826_ = lean_ctor_get(v___x_824_, 1);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_824_);
if (v_isSharedCheck_852_ == 0)
{
v___x_828_ = v___x_824_;
v_isShared_829_ = v_isSharedCheck_852_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_snd_826_);
lean_inc(v_fst_825_);
lean_dec(v___x_824_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_852_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
size_t v___x_830_; size_t v___x_831_; uint8_t v___x_832_; 
v___x_830_ = lean_ptr_addr(v_binderType_818_);
v___x_831_ = lean_ptr_addr(v_fst_822_);
v___x_832_ = lean_usize_dec_eq(v___x_830_, v___x_831_);
if (v___x_832_ == 0)
{
lean_object* v___x_833_; lean_object* v___x_835_; 
lean_inc(v_binderName_817_);
lean_dec_ref_known(v_e_652_, 3);
v___x_833_ = l_Lean_Expr_forallE___override(v_binderName_817_, v_fst_822_, v_fst_825_, v_binderInfo_820_);
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 0, v___x_833_);
v___x_835_ = v___x_828_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v___x_833_);
lean_ctor_set(v_reuseFailAlloc_836_, 1, v_snd_826_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
else
{
size_t v___x_837_; size_t v___x_838_; uint8_t v___x_839_; 
v___x_837_ = lean_ptr_addr(v_body_819_);
v___x_838_ = lean_ptr_addr(v_fst_825_);
v___x_839_ = lean_usize_dec_eq(v___x_837_, v___x_838_);
if (v___x_839_ == 0)
{
lean_object* v___x_840_; lean_object* v___x_842_; 
lean_inc(v_binderName_817_);
lean_dec_ref_known(v_e_652_, 3);
v___x_840_ = l_Lean_Expr_forallE___override(v_binderName_817_, v_fst_822_, v_fst_825_, v_binderInfo_820_);
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 0, v___x_840_);
v___x_842_ = v___x_828_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v___x_840_);
lean_ctor_set(v_reuseFailAlloc_843_, 1, v_snd_826_);
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
uint8_t v___x_844_; 
v___x_844_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_820_, v_binderInfo_820_);
if (v___x_844_ == 0)
{
lean_object* v___x_845_; lean_object* v___x_847_; 
lean_inc(v_binderName_817_);
lean_dec_ref_known(v_e_652_, 3);
v___x_845_ = l_Lean_Expr_forallE___override(v_binderName_817_, v_fst_822_, v_fst_825_, v_binderInfo_820_);
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 0, v___x_845_);
v___x_847_ = v___x_828_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v___x_845_);
lean_ctor_set(v_reuseFailAlloc_848_, 1, v_snd_826_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
else
{
lean_object* v___x_850_; 
lean_dec(v_fst_825_);
lean_dec(v_fst_822_);
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 0, v_e_652_);
v___x_850_ = v___x_828_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_e_652_);
lean_ctor_set(v_reuseFailAlloc_851_, 1, v_snd_826_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
}
}
}
case 8:
{
lean_object* v_declName_853_; lean_object* v_type_854_; lean_object* v_value_855_; lean_object* v_body_856_; uint8_t v_nondep_857_; lean_object* v___x_858_; lean_object* v_fst_859_; lean_object* v_snd_860_; lean_object* v___x_861_; lean_object* v_fst_862_; lean_object* v_snd_863_; lean_object* v___x_864_; lean_object* v_fst_865_; lean_object* v_snd_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_894_; 
v_declName_853_ = lean_ctor_get(v_e_652_, 0);
v_type_854_ = lean_ctor_get(v_e_652_, 1);
v_value_855_ = lean_ctor_get(v_e_652_, 2);
v_body_856_ = lean_ctor_get(v_e_652_, 3);
v_nondep_857_ = lean_ctor_get_uint8(v_e_652_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_854_);
v___x_858_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_type_854_, v_a_653_);
v_fst_859_ = lean_ctor_get(v___x_858_, 0);
lean_inc(v_fst_859_);
v_snd_860_ = lean_ctor_get(v___x_858_, 1);
lean_inc(v_snd_860_);
lean_dec_ref(v___x_858_);
lean_inc_ref(v_value_855_);
v___x_861_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_value_855_, v_snd_860_);
v_fst_862_ = lean_ctor_get(v___x_861_, 0);
lean_inc(v_fst_862_);
v_snd_863_ = lean_ctor_get(v___x_861_, 1);
lean_inc(v_snd_863_);
lean_dec_ref(v___x_861_);
lean_inc_ref(v_body_856_);
v___x_864_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_body_856_, v_snd_863_);
v_fst_865_ = lean_ctor_get(v___x_864_, 0);
v_snd_866_ = lean_ctor_get(v___x_864_, 1);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_894_ == 0)
{
v___x_868_ = v___x_864_;
v_isShared_869_ = v_isSharedCheck_894_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_snd_866_);
lean_inc(v_fst_865_);
lean_dec(v___x_864_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_894_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
size_t v___x_870_; size_t v___x_871_; uint8_t v___x_872_; 
v___x_870_ = lean_ptr_addr(v_type_854_);
v___x_871_ = lean_ptr_addr(v_fst_859_);
v___x_872_ = lean_usize_dec_eq(v___x_870_, v___x_871_);
if (v___x_872_ == 0)
{
lean_object* v___x_873_; lean_object* v___x_875_; 
lean_inc(v_declName_853_);
lean_dec_ref_known(v_e_652_, 4);
v___x_873_ = l_Lean_Expr_letE___override(v_declName_853_, v_fst_859_, v_fst_862_, v_fst_865_, v_nondep_857_);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 0, v___x_873_);
v___x_875_ = v___x_868_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v___x_873_);
lean_ctor_set(v_reuseFailAlloc_876_, 1, v_snd_866_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
else
{
size_t v___x_877_; size_t v___x_878_; uint8_t v___x_879_; 
v___x_877_ = lean_ptr_addr(v_value_855_);
v___x_878_ = lean_ptr_addr(v_fst_862_);
v___x_879_ = lean_usize_dec_eq(v___x_877_, v___x_878_);
if (v___x_879_ == 0)
{
lean_object* v___x_880_; lean_object* v___x_882_; 
lean_inc(v_declName_853_);
lean_dec_ref_known(v_e_652_, 4);
v___x_880_ = l_Lean_Expr_letE___override(v_declName_853_, v_fst_859_, v_fst_862_, v_fst_865_, v_nondep_857_);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 0, v___x_880_);
v___x_882_ = v___x_868_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v___x_880_);
lean_ctor_set(v_reuseFailAlloc_883_, 1, v_snd_866_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
else
{
size_t v___x_884_; size_t v___x_885_; uint8_t v___x_886_; 
v___x_884_ = lean_ptr_addr(v_body_856_);
v___x_885_ = lean_ptr_addr(v_fst_865_);
v___x_886_ = lean_usize_dec_eq(v___x_884_, v___x_885_);
if (v___x_886_ == 0)
{
lean_object* v___x_887_; lean_object* v___x_889_; 
lean_inc(v_declName_853_);
lean_dec_ref_known(v_e_652_, 4);
v___x_887_ = l_Lean_Expr_letE___override(v_declName_853_, v_fst_859_, v_fst_862_, v_fst_865_, v_nondep_857_);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 0, v___x_887_);
v___x_889_ = v___x_868_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v___x_887_);
lean_ctor_set(v_reuseFailAlloc_890_, 1, v_snd_866_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
else
{
lean_object* v___x_892_; 
lean_dec(v_fst_865_);
lean_dec(v_fst_862_);
lean_dec(v_fst_859_);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 0, v_e_652_);
v___x_892_ = v___x_868_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_e_652_);
lean_ctor_set(v_reuseFailAlloc_893_, 1, v_snd_866_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
}
}
}
}
case 10:
{
lean_object* v_data_895_; lean_object* v_expr_896_; lean_object* v___x_897_; lean_object* v_fst_898_; lean_object* v_snd_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_913_; 
v_data_895_ = lean_ctor_get(v_e_652_, 0);
v_expr_896_ = lean_ctor_get(v_e_652_, 1);
lean_inc_ref(v_expr_896_);
v___x_897_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_expr_896_, v_a_653_);
v_fst_898_ = lean_ctor_get(v___x_897_, 0);
v_snd_899_ = lean_ctor_get(v___x_897_, 1);
v_isSharedCheck_913_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_913_ == 0)
{
v___x_901_ = v___x_897_;
v_isShared_902_ = v_isSharedCheck_913_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_snd_899_);
lean_inc(v_fst_898_);
lean_dec(v___x_897_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_913_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
size_t v___x_903_; size_t v___x_904_; uint8_t v___x_905_; 
v___x_903_ = lean_ptr_addr(v_expr_896_);
v___x_904_ = lean_ptr_addr(v_fst_898_);
v___x_905_ = lean_usize_dec_eq(v___x_903_, v___x_904_);
if (v___x_905_ == 0)
{
lean_object* v___x_906_; lean_object* v___x_908_; 
lean_inc(v_data_895_);
lean_dec_ref_known(v_e_652_, 2);
v___x_906_ = l_Lean_Expr_mdata___override(v_data_895_, v_fst_898_);
if (v_isShared_902_ == 0)
{
lean_ctor_set(v___x_901_, 0, v___x_906_);
v___x_908_ = v___x_901_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v___x_906_);
lean_ctor_set(v_reuseFailAlloc_909_, 1, v_snd_899_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
else
{
lean_object* v___x_911_; 
lean_dec(v_fst_898_);
if (v_isShared_902_ == 0)
{
lean_ctor_set(v___x_901_, 0, v_e_652_);
v___x_911_ = v___x_901_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_e_652_);
lean_ctor_set(v_reuseFailAlloc_912_, 1, v_snd_899_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
}
}
case 11:
{
lean_object* v_typeName_914_; lean_object* v_idx_915_; lean_object* v_struct_916_; lean_object* v___x_917_; lean_object* v_fst_918_; lean_object* v_snd_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_933_; 
v_typeName_914_ = lean_ctor_get(v_e_652_, 0);
v_idx_915_ = lean_ctor_get(v_e_652_, 1);
v_struct_916_ = lean_ctor_get(v_e_652_, 2);
lean_inc_ref(v_struct_916_);
v___x_917_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_struct_916_, v_a_653_);
v_fst_918_ = lean_ctor_get(v___x_917_, 0);
v_snd_919_ = lean_ctor_get(v___x_917_, 1);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_917_);
if (v_isSharedCheck_933_ == 0)
{
v___x_921_ = v___x_917_;
v_isShared_922_ = v_isSharedCheck_933_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_snd_919_);
lean_inc(v_fst_918_);
lean_dec(v___x_917_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_933_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
size_t v___x_923_; size_t v___x_924_; uint8_t v___x_925_; 
v___x_923_ = lean_ptr_addr(v_struct_916_);
v___x_924_ = lean_ptr_addr(v_fst_918_);
v___x_925_ = lean_usize_dec_eq(v___x_923_, v___x_924_);
if (v___x_925_ == 0)
{
lean_object* v___x_926_; lean_object* v___x_928_; 
lean_inc(v_idx_915_);
lean_inc(v_typeName_914_);
lean_dec_ref_known(v_e_652_, 3);
v___x_926_ = l_Lean_Expr_proj___override(v_typeName_914_, v_idx_915_, v_fst_918_);
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 0, v___x_926_);
v___x_928_ = v___x_921_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v___x_926_);
lean_ctor_set(v_reuseFailAlloc_929_, 1, v_snd_919_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
else
{
lean_object* v___x_931_; 
lean_dec(v_fst_918_);
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 0, v_e_652_);
v___x_931_ = v___x_921_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_e_652_);
lean_ctor_set(v_reuseFailAlloc_932_, 1, v_snd_919_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
}
default: 
{
lean_object* v___x_934_; 
v___x_934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_934_, 0, v_e_652_);
lean_ctor_set(v___x_934_, 1, v_a_653_);
return v___x_934_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0(lean_object* v_00_u03b2_935_, lean_object* v_m_936_, lean_object* v_a_937_){
_start:
{
lean_object* v___x_938_; 
v___x_938_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0___redArg(v_m_936_, v_a_937_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0___boxed(lean_object* v_00_u03b2_939_, lean_object* v_m_940_, lean_object* v_a_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0(v_00_u03b2_939_, v_m_940_, v_a_941_);
lean_dec(v_a_941_);
lean_dec_ref(v_m_940_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2(lean_object* v_00_u03b2_943_, lean_object* v_m_944_, lean_object* v_a_945_, lean_object* v_b_946_){
_start:
{
lean_object* v___x_947_; 
v___x_947_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2___redArg(v_m_944_, v_a_945_, v_b_946_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0(lean_object* v_00_u03b2_948_, lean_object* v_a_949_, lean_object* v_x_950_){
_start:
{
lean_object* v___x_951_; 
v___x_951_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0___redArg(v_a_949_, v_x_950_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0___boxed(lean_object* v_00_u03b2_952_, lean_object* v_a_953_, lean_object* v_x_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__0_spec__0(v_00_u03b2_952_, v_a_953_, v_x_954_);
lean_dec(v_x_954_);
lean_dec(v_a_953_);
return v_res_955_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3(lean_object* v_00_u03b2_956_, lean_object* v_a_957_, lean_object* v_x_958_){
_start:
{
uint8_t v___x_959_; 
v___x_959_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3___redArg(v_a_957_, v_x_958_);
return v___x_959_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_957_ = stack[1].m_obj;
lean_object* v_x_958_ = stack[2].m_obj;
uint8_t v_res_960_;
v_res_960_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3(lean_box(0), v_a_957_, v_x_958_);
stack->m_num = v_res_960_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3___boxed(lean_object* v_00_u03b2_961_, lean_object* v_a_962_, lean_object* v_x_963_){
_start:
{
uint8_t v_res_964_; lean_object* v_r_965_; 
v_res_964_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__3(v_00_u03b2_961_, v_a_962_, v_x_963_);
lean_dec(v_x_963_);
lean_dec(v_a_962_);
v_r_965_ = lean_box(v_res_964_);
return v_r_965_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4(lean_object* v_00_u03b2_966_, lean_object* v_data_967_){
_start:
{
lean_object* v___x_968_; 
v___x_968_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4___redArg(v_data_967_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__5(lean_object* v_00_u03b2_969_, lean_object* v_a_970_, lean_object* v_b_971_, lean_object* v_x_972_){
_start:
{
lean_object* v___x_973_; 
v___x_973_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__5___redArg(v_a_970_, v_b_971_, v_x_972_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_974_, lean_object* v_i_975_, lean_object* v_source_976_, lean_object* v_target_977_){
_start:
{
lean_object* v___x_978_; 
v___x_978_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4_spec__5___redArg(v_i_975_, v_source_976_, v_target_977_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4_spec__5_spec__7(lean_object* v_00_u03b2_979_, lean_object* v_x_980_, lean_object* v_x_981_){
_start:
{
lean_object* v___x_982_; 
v___x_982_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AbstractMVars_abstractExprMVars_spec__2_spec__4_spec__5_spec__7___redArg(v_x_980_, v_x_981_);
return v___x_982_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0___redArg(lean_object* v_e_983_, lean_object* v___y_984_){
_start:
{
uint8_t v___x_986_; 
v___x_986_ = l_Lean_Expr_hasMVar(v_e_983_);
if (v___x_986_ == 0)
{
lean_object* v___x_987_; 
v___x_987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_987_, 0, v_e_983_);
return v___x_987_;
}
else
{
lean_object* v___x_988_; lean_object* v_mctx_989_; lean_object* v___x_990_; lean_object* v_fst_991_; lean_object* v_snd_992_; lean_object* v___x_993_; lean_object* v_cache_994_; lean_object* v_zetaDeltaFVarIds_995_; lean_object* v_postponed_996_; lean_object* v_diag_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1006_; 
v___x_988_ = lean_st_ref_get(v___y_984_);
v_mctx_989_ = lean_ctor_get(v___x_988_, 0);
lean_inc_ref(v_mctx_989_);
lean_dec(v___x_988_);
v___x_990_ = l_Lean_instantiateMVarsCore(v_mctx_989_, v_e_983_);
v_fst_991_ = lean_ctor_get(v___x_990_, 0);
lean_inc(v_fst_991_);
v_snd_992_ = lean_ctor_get(v___x_990_, 1);
lean_inc(v_snd_992_);
lean_dec_ref(v___x_990_);
v___x_993_ = lean_st_ref_take(v___y_984_);
v_cache_994_ = lean_ctor_get(v___x_993_, 1);
v_zetaDeltaFVarIds_995_ = lean_ctor_get(v___x_993_, 2);
v_postponed_996_ = lean_ctor_get(v___x_993_, 3);
v_diag_997_ = lean_ctor_get(v___x_993_, 4);
v_isSharedCheck_1006_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1006_ == 0)
{
lean_object* v_unused_1007_; 
v_unused_1007_ = lean_ctor_get(v___x_993_, 0);
lean_dec(v_unused_1007_);
v___x_999_ = v___x_993_;
v_isShared_1000_ = v_isSharedCheck_1006_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_diag_997_);
lean_inc(v_postponed_996_);
lean_inc(v_zetaDeltaFVarIds_995_);
lean_inc(v_cache_994_);
lean_dec(v___x_993_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1006_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1002_; 
if (v_isShared_1000_ == 0)
{
lean_ctor_set(v___x_999_, 0, v_snd_992_);
v___x_1002_ = v___x_999_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v_snd_992_);
lean_ctor_set(v_reuseFailAlloc_1005_, 1, v_cache_994_);
lean_ctor_set(v_reuseFailAlloc_1005_, 2, v_zetaDeltaFVarIds_995_);
lean_ctor_set(v_reuseFailAlloc_1005_, 3, v_postponed_996_);
lean_ctor_set(v_reuseFailAlloc_1005_, 4, v_diag_997_);
v___x_1002_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1003_ = lean_st_ref_put(v___y_984_, v___x_1002_);
v___x_1004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1004_, 0, v_fst_991_);
return v___x_1004_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_983_ = stack[0].m_obj;
lean_object* v___y_984_ = stack[1].m_obj;
lean_object* v_res_1008_;
v_res_1008_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0___redArg(v_e_983_, v___y_984_);
stack->m_obj
 = v_res_1008_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0___redArg___boxed(lean_object* v_e_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0___redArg(v_e_1009_, v___y_1010_);
lean_dec(v___y_1010_);
return v_res_1012_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0(lean_object* v_e_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_){
_start:
{
lean_object* v___x_1019_; 
v___x_1019_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0___redArg(v_e_1013_, v___y_1015_);
return v___x_1019_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1013_ = stack[0].m_obj;
lean_object* v___y_1014_ = stack[1].m_obj;
lean_object* v___y_1015_ = stack[2].m_obj;
lean_object* v___y_1016_ = stack[3].m_obj;
lean_object* v___y_1017_ = stack[4].m_obj;
lean_object* v_res_1020_;
v_res_1020_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0(v_e_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_);
stack->m_obj
 = v_res_1020_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0___boxed(lean_object* v_e_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_){
_start:
{
lean_object* v_res_1027_; 
v_res_1027_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0(v_e_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_);
lean_dec(v___y_1025_);
lean_dec_ref(v___y_1024_);
lean_dec(v___y_1023_);
lean_dec_ref(v___y_1022_);
return v_res_1027_;
}
}
static lean_object* _init_l_Lean_Meta_abstractMVars___closed__1(void){
_start:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1030_ = lean_box(0);
v___x_1031_ = lean_unsigned_to_nat(16u);
v___x_1032_ = lean_mk_array(v___x_1031_, v___x_1030_);
return v___x_1032_;
}
}
static lean_object* _init_l_Lean_Meta_abstractMVars___closed__2(void){
_start:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1033_ = lean_obj_once(&l_Lean_Meta_abstractMVars___closed__1, &l_Lean_Meta_abstractMVars___closed__1_once, _init_l_Lean_Meta_abstractMVars___closed__1);
v___x_1034_ = lean_unsigned_to_nat(0u);
v___x_1035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1034_);
lean_ctor_set(v___x_1035_, 1, v___x_1033_);
return v___x_1035_;
}
}
lean_object* l_Lean_Meta_abstractMVars(lean_object* v_e_1036_, uint8_t v_levels_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_){
_start:
{
lean_object* v___x_1043_; lean_object* v_a_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1106_; 
v___x_1043_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractMVars_spec__0___redArg(v_e_1036_, v_a_1039_);
v_a_1044_ = lean_ctor_get(v___x_1043_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1046_ = v___x_1043_;
v_isShared_1047_ = v_isSharedCheck_1106_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_a_1044_);
lean_dec(v___x_1043_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1106_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1048_; lean_object* v_mctx_1049_; lean_object* v_lctx_1050_; lean_object* v___x_1051_; lean_object* v_ngen_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v_snd_1058_; lean_object* v_fst_1059_; lean_object* v_ngen_1060_; lean_object* v_lctx_1061_; lean_object* v_mctx_1062_; lean_object* v_paramNames_1063_; lean_object* v_fvars_1064_; lean_object* v_mvars_1065_; lean_object* v___x_1066_; lean_object* v_env_1067_; lean_object* v_nextMacroScope_1068_; lean_object* v_auxDeclNGen_1069_; lean_object* v_traceState_1070_; lean_object* v_cache_1071_; lean_object* v_recordedDeps_1072_; lean_object* v_messages_1073_; lean_object* v_infoState_1074_; lean_object* v_snapshotTasks_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1104_; 
v___x_1048_ = lean_st_ref_get(v_a_1039_);
v_mctx_1049_ = lean_ctor_get(v___x_1048_, 0);
lean_inc_ref(v_mctx_1049_);
lean_dec(v___x_1048_);
v_lctx_1050_ = lean_ctor_get(v_a_1038_, 2);
v___x_1051_ = lean_st_ref_get(v_a_1041_);
v_ngen_1052_ = lean_ctor_get(v___x_1051_, 2);
lean_inc_ref(v_ngen_1052_);
lean_dec(v___x_1051_);
v___x_1053_ = lean_unsigned_to_nat(0u);
v___x_1054_ = ((lean_object*)(l_Lean_Meta_abstractMVars___closed__0));
v___x_1055_ = lean_obj_once(&l_Lean_Meta_abstractMVars___closed__2, &l_Lean_Meta_abstractMVars___closed__2_once, _init_l_Lean_Meta_abstractMVars___closed__2);
lean_inc_ref(v_lctx_1050_);
v___x_1056_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v___x_1056_, 0, v_ngen_1052_);
lean_ctor_set(v___x_1056_, 1, v_lctx_1050_);
lean_ctor_set(v___x_1056_, 2, v_mctx_1049_);
lean_ctor_set(v___x_1056_, 3, v___x_1053_);
lean_ctor_set(v___x_1056_, 4, v___x_1054_);
lean_ctor_set(v___x_1056_, 5, v___x_1054_);
lean_ctor_set(v___x_1056_, 6, v___x_1054_);
lean_ctor_set(v___x_1056_, 7, v___x_1055_);
lean_ctor_set(v___x_1056_, 8, v___x_1055_);
lean_ctor_set_uint8(v___x_1056_, sizeof(void*)*9, v_levels_1037_);
v___x_1057_ = l_Lean_Meta_AbstractMVars_abstractExprMVars(v_a_1044_, v___x_1056_);
v_snd_1058_ = lean_ctor_get(v___x_1057_, 1);
lean_inc(v_snd_1058_);
v_fst_1059_ = lean_ctor_get(v___x_1057_, 0);
lean_inc(v_fst_1059_);
lean_dec_ref(v___x_1057_);
v_ngen_1060_ = lean_ctor_get(v_snd_1058_, 0);
lean_inc_ref(v_ngen_1060_);
v_lctx_1061_ = lean_ctor_get(v_snd_1058_, 1);
lean_inc_ref(v_lctx_1061_);
v_mctx_1062_ = lean_ctor_get(v_snd_1058_, 2);
lean_inc_ref(v_mctx_1062_);
v_paramNames_1063_ = lean_ctor_get(v_snd_1058_, 4);
lean_inc_ref(v_paramNames_1063_);
v_fvars_1064_ = lean_ctor_get(v_snd_1058_, 5);
lean_inc_ref(v_fvars_1064_);
v_mvars_1065_ = lean_ctor_get(v_snd_1058_, 6);
lean_inc_ref(v_mvars_1065_);
lean_dec(v_snd_1058_);
v___x_1066_ = lean_st_ref_take(v_a_1041_);
v_env_1067_ = lean_ctor_get(v___x_1066_, 0);
v_nextMacroScope_1068_ = lean_ctor_get(v___x_1066_, 1);
v_auxDeclNGen_1069_ = lean_ctor_get(v___x_1066_, 3);
v_traceState_1070_ = lean_ctor_get(v___x_1066_, 4);
v_cache_1071_ = lean_ctor_get(v___x_1066_, 5);
v_recordedDeps_1072_ = lean_ctor_get(v___x_1066_, 6);
v_messages_1073_ = lean_ctor_get(v___x_1066_, 7);
v_infoState_1074_ = lean_ctor_get(v___x_1066_, 8);
v_snapshotTasks_1075_ = lean_ctor_get(v___x_1066_, 9);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1104_ == 0)
{
lean_object* v_unused_1105_; 
v_unused_1105_ = lean_ctor_get(v___x_1066_, 2);
lean_dec(v_unused_1105_);
v___x_1077_ = v___x_1066_;
v_isShared_1078_ = v_isSharedCheck_1104_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_snapshotTasks_1075_);
lean_inc(v_infoState_1074_);
lean_inc(v_messages_1073_);
lean_inc(v_recordedDeps_1072_);
lean_inc(v_cache_1071_);
lean_inc(v_traceState_1070_);
lean_inc(v_auxDeclNGen_1069_);
lean_inc(v_nextMacroScope_1068_);
lean_inc(v_env_1067_);
lean_dec(v___x_1066_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1104_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1080_; 
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 2, v_ngen_1060_);
v___x_1080_ = v___x_1077_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_env_1067_);
lean_ctor_set(v_reuseFailAlloc_1103_, 1, v_nextMacroScope_1068_);
lean_ctor_set(v_reuseFailAlloc_1103_, 2, v_ngen_1060_);
lean_ctor_set(v_reuseFailAlloc_1103_, 3, v_auxDeclNGen_1069_);
lean_ctor_set(v_reuseFailAlloc_1103_, 4, v_traceState_1070_);
lean_ctor_set(v_reuseFailAlloc_1103_, 5, v_cache_1071_);
lean_ctor_set(v_reuseFailAlloc_1103_, 6, v_recordedDeps_1072_);
lean_ctor_set(v_reuseFailAlloc_1103_, 7, v_messages_1073_);
lean_ctor_set(v_reuseFailAlloc_1103_, 8, v_infoState_1074_);
lean_ctor_set(v_reuseFailAlloc_1103_, 9, v_snapshotTasks_1075_);
v___x_1080_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v_cache_1083_; lean_object* v_zetaDeltaFVarIds_1084_; lean_object* v_postponed_1085_; lean_object* v_diag_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1101_; 
v___x_1081_ = lean_st_ref_put(v_a_1041_, v___x_1080_);
v___x_1082_ = lean_st_ref_take(v_a_1039_);
v_cache_1083_ = lean_ctor_get(v___x_1082_, 1);
v_zetaDeltaFVarIds_1084_ = lean_ctor_get(v___x_1082_, 2);
v_postponed_1085_ = lean_ctor_get(v___x_1082_, 3);
v_diag_1086_ = lean_ctor_get(v___x_1082_, 4);
v_isSharedCheck_1101_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1101_ == 0)
{
lean_object* v_unused_1102_; 
v_unused_1102_ = lean_ctor_get(v___x_1082_, 0);
lean_dec(v_unused_1102_);
v___x_1088_ = v___x_1082_;
v_isShared_1089_ = v_isSharedCheck_1101_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_diag_1086_);
lean_inc(v_postponed_1085_);
lean_inc(v_zetaDeltaFVarIds_1084_);
lean_inc(v_cache_1083_);
lean_dec(v___x_1082_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1101_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1091_; 
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 0, v_mctx_1062_);
v___x_1091_ = v___x_1088_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_mctx_1062_);
lean_ctor_set(v_reuseFailAlloc_1100_, 1, v_cache_1083_);
lean_ctor_set(v_reuseFailAlloc_1100_, 2, v_zetaDeltaFVarIds_1084_);
lean_ctor_set(v_reuseFailAlloc_1100_, 3, v_postponed_1085_);
lean_ctor_set(v_reuseFailAlloc_1100_, 4, v_diag_1086_);
v___x_1091_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
lean_object* v___x_1092_; uint8_t v___x_1093_; uint8_t v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1098_; 
v___x_1092_ = lean_st_ref_put(v_a_1039_, v___x_1091_);
v___x_1093_ = 1;
v___x_1094_ = 0;
v___x_1095_ = l_Lean_LocalContext_mkLambda(v_lctx_1061_, v_fvars_1064_, v_fst_1059_, v___x_1093_, v___x_1094_);
lean_dec(v_fst_1059_);
lean_dec_ref(v_fvars_1064_);
v___x_1096_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1096_, 0, v_paramNames_1063_);
lean_ctor_set(v___x_1096_, 1, v_mvars_1065_);
lean_ctor_set(v___x_1096_, 2, v___x_1095_);
if (v_isShared_1047_ == 0)
{
lean_ctor_set(v___x_1046_, 0, v___x_1096_);
v___x_1098_ = v___x_1046_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v___x_1096_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_abstractMVars_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1036_ = stack[0].m_obj;
uint8_t v_levels_1037_ = stack[1].m_num;
lean_object* v_a_1038_ = stack[2].m_obj;
lean_object* v_a_1039_ = stack[3].m_obj;
lean_object* v_a_1040_ = stack[4].m_obj;
lean_object* v_a_1041_ = stack[5].m_obj;
lean_object* v_res_1107_;
v_res_1107_ = l_Lean_Meta_abstractMVars(v_e_1036_, v_levels_1037_, v_a_1038_, v_a_1039_, v_a_1040_, v_a_1041_);
stack->m_obj
 = v_res_1107_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractMVars___boxed(lean_object* v_e_1108_, lean_object* v_levels_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_){
_start:
{
uint8_t v_levels_boxed_1115_; lean_object* v_res_1116_; 
v_levels_boxed_1115_ = lean_unbox(v_levels_1109_);
v_res_1116_ = l_Lean_Meta_abstractMVars(v_e_1108_, v_levels_boxed_1115_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_);
lean_dec(v_a_1113_);
lean_dec_ref(v_a_1112_);
lean_dec(v_a_1111_);
lean_dec_ref(v_a_1110_);
return v_res_1116_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_openAbstractMVarsResult_spec__0(size_t v_sz_1117_, size_t v_i_1118_, lean_object* v_bs_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_){
_start:
{
uint8_t v___x_1125_; 
v___x_1125_ = lean_usize_dec_lt(v_i_1118_, v_sz_1117_);
if (v___x_1125_ == 0)
{
lean_object* v___x_1126_; 
v___x_1126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1126_, 0, v_bs_1119_);
return v___x_1126_;
}
else
{
lean_object* v___x_1127_; lean_object* v_bs_x27_1128_; lean_object* v___x_1129_; 
v___x_1127_ = lean_unsigned_to_nat(0u);
v_bs_x27_1128_ = lean_array_uset(v_bs_1119_, v_i_1118_, v___x_1127_);
v___x_1129_ = l_Lean_Meta_mkFreshLevelMVar(v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
if (lean_obj_tag(v___x_1129_) == 0)
{
lean_object* v_a_1130_; size_t v___x_1131_; size_t v___x_1132_; lean_object* v___x_1133_; 
v_a_1130_ = lean_ctor_get(v___x_1129_, 0);
lean_inc(v_a_1130_);
lean_dec_ref_known(v___x_1129_, 1);
v___x_1131_ = ((size_t)1ULL);
v___x_1132_ = lean_usize_add(v_i_1118_, v___x_1131_);
v___x_1133_ = lean_array_uset(v_bs_x27_1128_, v_i_1118_, v_a_1130_);
v_i_1118_ = v___x_1132_;
v_bs_1119_ = v___x_1133_;
goto _start;
}
else
{
lean_object* v_a_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1142_; 
lean_dec_ref(v_bs_x27_1128_);
v_a_1135_ = lean_ctor_get(v___x_1129_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1129_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1137_ = v___x_1129_;
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_dec(v___x_1129_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1140_; 
if (v_isShared_1138_ == 0)
{
v___x_1140_ = v___x_1137_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_a_1135_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_openAbstractMVarsResult_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1117_ = stack[0].m_num;
size_t v_i_1118_ = stack[1].m_num;
lean_object* v_bs_1119_ = stack[2].m_obj;
lean_object* v___y_1120_ = stack[3].m_obj;
lean_object* v___y_1121_ = stack[4].m_obj;
lean_object* v___y_1122_ = stack[5].m_obj;
lean_object* v___y_1123_ = stack[6].m_obj;
lean_object* v_res_1143_;
v_res_1143_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_openAbstractMVarsResult_spec__0(v_sz_1117_, v_i_1118_, v_bs_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
stack->m_obj
 = v_res_1143_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_openAbstractMVarsResult_spec__0___boxed(lean_object* v_sz_1144_, lean_object* v_i_1145_, lean_object* v_bs_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_){
_start:
{
size_t v_sz_boxed_1152_; size_t v_i_boxed_1153_; lean_object* v_res_1154_; 
v_sz_boxed_1152_ = lean_unbox_usize(v_sz_1144_);
lean_dec(v_sz_1144_);
v_i_boxed_1153_ = lean_unbox_usize(v_i_1145_);
lean_dec(v_i_1145_);
v_res_1154_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_openAbstractMVarsResult_spec__0(v_sz_boxed_1152_, v_i_boxed_1153_, v_bs_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_);
lean_dec(v___y_1150_);
lean_dec_ref(v___y_1149_);
lean_dec(v___y_1148_);
lean_dec_ref(v___y_1147_);
return v_res_1154_;
}
}
lean_object* l_Lean_Meta_openAbstractMVarsResult(lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_){
_start:
{
lean_object* v_paramNames_1161_; lean_object* v_expr_1162_; size_t v_sz_1163_; size_t v___x_1164_; lean_object* v___x_1165_; 
v_paramNames_1161_ = lean_ctor_get(v_a_1155_, 0);
v_expr_1162_ = lean_ctor_get(v_a_1155_, 2);
v_sz_1163_ = lean_array_size(v_paramNames_1161_);
v___x_1164_ = ((size_t)0ULL);
lean_inc_ref(v_paramNames_1161_);
v___x_1165_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_openAbstractMVarsResult_spec__0(v_sz_1163_, v___x_1164_, v_paramNames_1161_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_);
if (lean_obj_tag(v___x_1165_) == 0)
{
lean_object* v_a_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
v_a_1166_ = lean_ctor_get(v___x_1165_, 0);
lean_inc(v_a_1166_);
lean_dec_ref_known(v___x_1165_, 1);
lean_inc_ref(v_paramNames_1161_);
v___x_1167_ = l_Lean_Expr_instantiateLevelParamsArray(v_expr_1162_, v_paramNames_1161_, v_a_1166_);
v___x_1168_ = l_Lean_Meta_AbstractMVarsResult_numMVars(v_a_1155_);
lean_dec_ref(v_a_1155_);
v___x_1169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1168_);
v___x_1170_ = l_Lean_Meta_lambdaMetaTelescope(v___x_1167_, v___x_1169_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_);
lean_dec_ref_known(v___x_1169_, 1);
lean_dec_ref(v___x_1167_);
return v___x_1170_;
}
else
{
lean_object* v_a_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1178_; 
lean_dec_ref(v_a_1155_);
v_a_1171_ = lean_ctor_get(v___x_1165_, 0);
v_isSharedCheck_1178_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1173_ = v___x_1165_;
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_a_1171_);
lean_dec(v___x_1165_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v___x_1176_; 
if (v_isShared_1174_ == 0)
{
v___x_1176_ = v___x_1173_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_a_1171_);
v___x_1176_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
return v___x_1176_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_openAbstractMVarsResult_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1155_ = stack[0].m_obj;
lean_object* v_a_1156_ = stack[1].m_obj;
lean_object* v_a_1157_ = stack[2].m_obj;
lean_object* v_a_1158_ = stack[3].m_obj;
lean_object* v_a_1159_ = stack[4].m_obj;
lean_object* v_res_1179_;
v_res_1179_ = l_Lean_Meta_openAbstractMVarsResult(v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_);
stack->m_obj
 = v_res_1179_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_openAbstractMVarsResult___boxed(lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l_Lean_Meta_openAbstractMVarsResult(v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_);
lean_dec(v_a_1184_);
lean_dec_ref(v_a_1183_);
lean_dec(v_a_1182_);
lean_dec_ref(v_a_1181_);
return v_res_1186_;
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
