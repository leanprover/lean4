// Lean compiler output
// Module: Lean.Meta.Sym.ReplaceS
// Imports: public import Lean.Meta.Sym.AlphaShareBuilder import Init.Omega
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
lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash___boxed(lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_instDecidableEqNat___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_hashPtrExpr_unsafe__1___boxed(lean_object*);
lean_object* l_UInt64_ofNat___boxed(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_instHashableProd___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1___boxed(lean_object*, lean_object*);
lean_object* l_instBEqProd___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM;
lean_object* l_StateT_lift(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift___redArg___lam__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_hashPtrExpr_unsafe__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__1_value;
static const lean_closure_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt64_ofNat___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__2_value;
static const lean_closure_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instHashableProd___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__1_value),((lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__2_value)} };
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__4;
static lean_once_cell_t l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__5;
static const lean_closure_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__6 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__6_value;
static const lean_closure_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__5 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__5_value;
static const lean_closure_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__4 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__4_value;
static const lean_closure_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__3_value;
static const lean_closure_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__2_value;
static const lean_closure_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__1_value;
static const lean_closure_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__0_value),((lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__1_value)}};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__7 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__7_value),((lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__2_value),((lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__3_value),((lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__4_value),((lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__5_value)}};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__8 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__8_value),((lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__6_value)}};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__9 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__9_value;
static const lean_closure_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_bind, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__9_value)} };
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__18 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__18_value;
static const lean_closure_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_instMonad___redArg___lam__9, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__9_value)} };
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__13 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__13_value;
static const lean_closure_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_instMonad___redArg___lam__7, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__9_value)} };
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__12 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__12_value;
static const lean_closure_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_instMonad___redArg___lam__4, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__9_value)} };
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11_value;
static const lean_closure_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_pure, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__9_value)} };
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__16 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__16_value;
static const lean_closure_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_instMonad___redArg___lam__1, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__9_value)} };
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__10 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__10_value;
static const lean_closure_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_map, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__9_value)} };
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__14 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__14_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__14_value),((lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__10_value)}};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__15 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__15_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__15_value),((lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__16_value),((lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11_value),((lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__12_value),((lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__13_value)}};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__17 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__17_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__17_value),((lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__18_value)}};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__19 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__19_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20;
static lean_once_cell_t l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__29;
static lean_once_cell_t l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__24;
static lean_once_cell_t l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__23;
static lean_once_cell_t l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__22;
static lean_once_cell_t l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__27;
static lean_once_cell_t l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__21;
static lean_once_cell_t l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__25;
static lean_once_cell_t l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__26;
static lean_once_cell_t l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__28;
static lean_once_cell_t l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__30;
static lean_once_cell_t l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__31;
static lean_once_cell_t l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__32;
static const lean_string_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__35 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__35_value;
static const lean_string_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "_private.Lean.Meta.Sym.ReplaceS.0.Lean.Meta.Sym.visit"};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__34 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__34_value;
static const lean_string_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Meta.Sym.ReplaceS"};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__33 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__33_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__36;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild_match__4_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild_match__4_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Sym_replaceS_x27___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_replaceS_x27___closed__0;
static lean_once_cell_t l_Lean_Meta_Sym_replaceS_x27___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_replaceS_x27___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_replaceS_x27(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_replaceS_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Sym_replaceS___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_replaceS___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_replaceS___redArg___closed__0_value;
static const lean_closure_object l_Lean_Meta_Sym_replaceS___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_replaceS___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_replaceS___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Sym_replaceS___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_replaceS___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_replaceS___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_replaceS___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_replaceS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_replaceS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(lean_object* v_a_1_, lean_object* v_x_2_){
_start:
{
if (lean_obj_tag(v_x_2_) == 0)
{
uint8_t v___x_3_; 
v___x_3_ = 0;
return v___x_3_;
}
else
{
lean_object* v_key_4_; lean_object* v_tail_5_; uint8_t v___y_7_; lean_object* v_fst_9_; lean_object* v_snd_10_; lean_object* v_fst_11_; lean_object* v_snd_12_; uint8_t v___x_13_; 
v_key_4_ = lean_ctor_get(v_x_2_, 0);
v_tail_5_ = lean_ctor_get(v_x_2_, 2);
v_fst_9_ = lean_ctor_get(v_key_4_, 0);
v_snd_10_ = lean_ctor_get(v_key_4_, 1);
v_fst_11_ = lean_ctor_get(v_a_1_, 0);
v_snd_12_ = lean_ctor_get(v_a_1_, 1);
v___x_13_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_9_, v_fst_11_);
if (v___x_13_ == 0)
{
v___y_7_ = v___x_13_;
goto v___jp_6_;
}
else
{
uint8_t v___x_14_; 
v___x_14_ = lean_nat_dec_eq(v_snd_10_, v_snd_12_);
v___y_7_ = v___x_14_;
goto v___jp_6_;
}
v___jp_6_:
{
if (v___y_7_ == 0)
{
v_x_2_ = v_tail_5_;
goto _start;
}
else
{
return v___y_7_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg___boxed(lean_object* v_a_15_, lean_object* v_x_16_){
_start:
{
uint8_t v_res_17_; lean_object* v_r_18_; 
v_res_17_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_a_15_, v_x_16_);
lean_dec(v_x_16_);
lean_dec_ref(v_a_15_);
v_r_18_ = lean_box(v_res_17_);
return v_r_18_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_19_, lean_object* v_x_20_){
_start:
{
if (lean_obj_tag(v_x_20_) == 0)
{
return v_x_19_;
}
else
{
lean_object* v_key_21_; lean_object* v_value_22_; lean_object* v_tail_23_; lean_object* v___x_25_; uint8_t v_isShared_26_; uint8_t v_isSharedCheck_50_; 
v_key_21_ = lean_ctor_get(v_x_20_, 0);
v_value_22_ = lean_ctor_get(v_x_20_, 1);
v_tail_23_ = lean_ctor_get(v_x_20_, 2);
v_isSharedCheck_50_ = !lean_is_exclusive(v_x_20_);
if (v_isSharedCheck_50_ == 0)
{
v___x_25_ = v_x_20_;
v_isShared_26_ = v_isSharedCheck_50_;
goto v_resetjp_24_;
}
else
{
lean_inc(v_tail_23_);
lean_inc(v_value_22_);
lean_inc(v_key_21_);
lean_dec(v_x_20_);
v___x_25_ = lean_box(0);
v_isShared_26_ = v_isSharedCheck_50_;
goto v_resetjp_24_;
}
v_resetjp_24_:
{
lean_object* v_fst_27_; lean_object* v_snd_28_; lean_object* v___x_29_; uint64_t v___x_30_; uint64_t v___x_31_; uint64_t v___x_32_; uint64_t v___x_33_; uint64_t v___x_34_; uint64_t v_fold_35_; uint64_t v___x_36_; uint64_t v___x_37_; uint64_t v___x_38_; size_t v___x_39_; size_t v___x_40_; size_t v___x_41_; size_t v___x_42_; size_t v___x_43_; lean_object* v___x_44_; lean_object* v___x_46_; 
v_fst_27_ = lean_ctor_get(v_key_21_, 0);
v_snd_28_ = lean_ctor_get(v_key_21_, 1);
v___x_29_ = lean_array_get_size(v_x_19_);
v___x_30_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_27_);
v___x_31_ = lean_uint64_of_nat(v_snd_28_);
v___x_32_ = lean_uint64_mix_hash(v___x_30_, v___x_31_);
v___x_33_ = 32ULL;
v___x_34_ = lean_uint64_shift_right(v___x_32_, v___x_33_);
v_fold_35_ = lean_uint64_xor(v___x_32_, v___x_34_);
v___x_36_ = 16ULL;
v___x_37_ = lean_uint64_shift_right(v_fold_35_, v___x_36_);
v___x_38_ = lean_uint64_xor(v_fold_35_, v___x_37_);
v___x_39_ = lean_uint64_to_usize(v___x_38_);
v___x_40_ = lean_usize_of_nat(v___x_29_);
v___x_41_ = ((size_t)1ULL);
v___x_42_ = lean_usize_sub(v___x_40_, v___x_41_);
v___x_43_ = lean_usize_land(v___x_39_, v___x_42_);
v___x_44_ = lean_array_uget_borrowed(v_x_19_, v___x_43_);
lean_inc(v___x_44_);
if (v_isShared_26_ == 0)
{
lean_ctor_set(v___x_25_, 2, v___x_44_);
v___x_46_ = v___x_25_;
goto v_reusejp_45_;
}
else
{
lean_object* v_reuseFailAlloc_49_; 
v_reuseFailAlloc_49_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_49_, 0, v_key_21_);
lean_ctor_set(v_reuseFailAlloc_49_, 1, v_value_22_);
lean_ctor_set(v_reuseFailAlloc_49_, 2, v___x_44_);
v___x_46_ = v_reuseFailAlloc_49_;
goto v_reusejp_45_;
}
v_reusejp_45_:
{
lean_object* v___x_47_; 
v___x_47_ = lean_array_uset(v_x_19_, v___x_43_, v___x_46_);
v_x_19_ = v___x_47_;
v_x_20_ = v_tail_23_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2___redArg(lean_object* v_i_51_, lean_object* v_source_52_, lean_object* v_target_53_){
_start:
{
lean_object* v___x_54_; uint8_t v___x_55_; 
v___x_54_ = lean_array_get_size(v_source_52_);
v___x_55_ = lean_nat_dec_lt(v_i_51_, v___x_54_);
if (v___x_55_ == 0)
{
lean_dec_ref(v_source_52_);
lean_dec(v_i_51_);
return v_target_53_;
}
else
{
lean_object* v_es_56_; lean_object* v___x_57_; lean_object* v_source_58_; lean_object* v_target_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v_es_56_ = lean_array_fget(v_source_52_, v_i_51_);
v___x_57_ = lean_box(0);
v_source_58_ = lean_array_fset(v_source_52_, v_i_51_, v___x_57_);
v_target_59_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3___redArg(v_target_53_, v_es_56_);
v___x_60_ = lean_unsigned_to_nat(1u);
v___x_61_ = lean_nat_add(v_i_51_, v___x_60_);
lean_dec(v_i_51_);
v_i_51_ = v___x_61_;
v_source_52_ = v_source_58_;
v_target_53_ = v_target_59_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1___redArg(lean_object* v_data_63_){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v_nbuckets_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_64_ = lean_array_get_size(v_data_63_);
v___x_65_ = lean_unsigned_to_nat(2u);
v_nbuckets_66_ = lean_nat_mul(v___x_64_, v___x_65_);
v___x_67_ = lean_unsigned_to_nat(0u);
v___x_68_ = lean_box(0);
v___x_69_ = lean_mk_array(v_nbuckets_66_, v___x_68_);
v___x_70_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2___redArg(v___x_67_, v_data_63_, v___x_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(lean_object* v_a_71_, lean_object* v_b_72_, lean_object* v_x_73_){
_start:
{
if (lean_obj_tag(v_x_73_) == 0)
{
lean_dec(v_b_72_);
lean_dec_ref(v_a_71_);
return v_x_73_;
}
else
{
lean_object* v_key_74_; lean_object* v_value_75_; lean_object* v_tail_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_95_; 
v_key_74_ = lean_ctor_get(v_x_73_, 0);
v_value_75_ = lean_ctor_get(v_x_73_, 1);
v_tail_76_ = lean_ctor_get(v_x_73_, 2);
v_isSharedCheck_95_ = !lean_is_exclusive(v_x_73_);
if (v_isSharedCheck_95_ == 0)
{
v___x_78_ = v_x_73_;
v_isShared_79_ = v_isSharedCheck_95_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_tail_76_);
lean_inc(v_value_75_);
lean_inc(v_key_74_);
lean_dec(v_x_73_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_95_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
uint8_t v___y_81_; lean_object* v_fst_89_; lean_object* v_snd_90_; lean_object* v_fst_91_; lean_object* v_snd_92_; uint8_t v___x_93_; 
v_fst_89_ = lean_ctor_get(v_key_74_, 0);
v_snd_90_ = lean_ctor_get(v_key_74_, 1);
v_fst_91_ = lean_ctor_get(v_a_71_, 0);
v_snd_92_ = lean_ctor_get(v_a_71_, 1);
v___x_93_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_89_, v_fst_91_);
if (v___x_93_ == 0)
{
v___y_81_ = v___x_93_;
goto v___jp_80_;
}
else
{
uint8_t v___x_94_; 
v___x_94_ = lean_nat_dec_eq(v_snd_90_, v_snd_92_);
v___y_81_ = v___x_94_;
goto v___jp_80_;
}
v___jp_80_:
{
if (v___y_81_ == 0)
{
lean_object* v___x_82_; lean_object* v___x_84_; 
v___x_82_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(v_a_71_, v_b_72_, v_tail_76_);
if (v_isShared_79_ == 0)
{
lean_ctor_set(v___x_78_, 2, v___x_82_);
v___x_84_ = v___x_78_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v_key_74_);
lean_ctor_set(v_reuseFailAlloc_85_, 1, v_value_75_);
lean_ctor_set(v_reuseFailAlloc_85_, 2, v___x_82_);
v___x_84_ = v_reuseFailAlloc_85_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
return v___x_84_;
}
}
else
{
lean_object* v___x_87_; 
lean_dec(v_value_75_);
lean_dec(v_key_74_);
if (v_isShared_79_ == 0)
{
lean_ctor_set(v___x_78_, 1, v_b_72_);
lean_ctor_set(v___x_78_, 0, v_a_71_);
v___x_87_ = v___x_78_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v_a_71_);
lean_ctor_set(v_reuseFailAlloc_88_, 1, v_b_72_);
lean_ctor_set(v_reuseFailAlloc_88_, 2, v_tail_76_);
v___x_87_ = v_reuseFailAlloc_88_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
return v___x_87_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0___redArg(lean_object* v_m_96_, lean_object* v_a_97_, lean_object* v_b_98_){
_start:
{
lean_object* v_size_99_; lean_object* v_buckets_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_147_; 
v_size_99_ = lean_ctor_get(v_m_96_, 0);
v_buckets_100_ = lean_ctor_get(v_m_96_, 1);
v_isSharedCheck_147_ = !lean_is_exclusive(v_m_96_);
if (v_isSharedCheck_147_ == 0)
{
v___x_102_ = v_m_96_;
v_isShared_103_ = v_isSharedCheck_147_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_buckets_100_);
lean_inc(v_size_99_);
lean_dec(v_m_96_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_147_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v_fst_104_; lean_object* v_snd_105_; lean_object* v___x_106_; uint64_t v___x_107_; uint64_t v___x_108_; uint64_t v___x_109_; uint64_t v___x_110_; uint64_t v___x_111_; uint64_t v_fold_112_; uint64_t v___x_113_; uint64_t v___x_114_; uint64_t v___x_115_; size_t v___x_116_; size_t v___x_117_; size_t v___x_118_; size_t v___x_119_; size_t v___x_120_; lean_object* v_bkt_121_; uint8_t v___x_122_; 
v_fst_104_ = lean_ctor_get(v_a_97_, 0);
v_snd_105_ = lean_ctor_get(v_a_97_, 1);
v___x_106_ = lean_array_get_size(v_buckets_100_);
v___x_107_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_104_);
v___x_108_ = lean_uint64_of_nat(v_snd_105_);
v___x_109_ = lean_uint64_mix_hash(v___x_107_, v___x_108_);
v___x_110_ = 32ULL;
v___x_111_ = lean_uint64_shift_right(v___x_109_, v___x_110_);
v_fold_112_ = lean_uint64_xor(v___x_109_, v___x_111_);
v___x_113_ = 16ULL;
v___x_114_ = lean_uint64_shift_right(v_fold_112_, v___x_113_);
v___x_115_ = lean_uint64_xor(v_fold_112_, v___x_114_);
v___x_116_ = lean_uint64_to_usize(v___x_115_);
v___x_117_ = lean_usize_of_nat(v___x_106_);
v___x_118_ = ((size_t)1ULL);
v___x_119_ = lean_usize_sub(v___x_117_, v___x_118_);
v___x_120_ = lean_usize_land(v___x_116_, v___x_119_);
v_bkt_121_ = lean_array_uget_borrowed(v_buckets_100_, v___x_120_);
v___x_122_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_a_97_, v_bkt_121_);
if (v___x_122_ == 0)
{
lean_object* v___x_123_; lean_object* v_size_x27_124_; lean_object* v___x_125_; lean_object* v_buckets_x27_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; uint8_t v___x_132_; 
v___x_123_ = lean_unsigned_to_nat(1u);
v_size_x27_124_ = lean_nat_add(v_size_99_, v___x_123_);
lean_dec(v_size_99_);
lean_inc(v_bkt_121_);
v___x_125_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_125_, 0, v_a_97_);
lean_ctor_set(v___x_125_, 1, v_b_98_);
lean_ctor_set(v___x_125_, 2, v_bkt_121_);
v_buckets_x27_126_ = lean_array_uset(v_buckets_100_, v___x_120_, v___x_125_);
v___x_127_ = lean_unsigned_to_nat(4u);
v___x_128_ = lean_nat_mul(v_size_x27_124_, v___x_127_);
v___x_129_ = lean_unsigned_to_nat(3u);
v___x_130_ = lean_nat_div(v___x_128_, v___x_129_);
lean_dec(v___x_128_);
v___x_131_ = lean_array_get_size(v_buckets_x27_126_);
v___x_132_ = lean_nat_dec_le(v___x_130_, v___x_131_);
lean_dec(v___x_130_);
if (v___x_132_ == 0)
{
lean_object* v_val_133_; lean_object* v___x_135_; 
v_val_133_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1___redArg(v_buckets_x27_126_);
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 1, v_val_133_);
lean_ctor_set(v___x_102_, 0, v_size_x27_124_);
v___x_135_ = v___x_102_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v_size_x27_124_);
lean_ctor_set(v_reuseFailAlloc_136_, 1, v_val_133_);
v___x_135_ = v_reuseFailAlloc_136_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
return v___x_135_;
}
}
else
{
lean_object* v___x_138_; 
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 1, v_buckets_x27_126_);
lean_ctor_set(v___x_102_, 0, v_size_x27_124_);
v___x_138_ = v___x_102_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v_size_x27_124_);
lean_ctor_set(v_reuseFailAlloc_139_, 1, v_buckets_x27_126_);
v___x_138_ = v_reuseFailAlloc_139_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
return v___x_138_;
}
}
}
else
{
lean_object* v___x_140_; lean_object* v_buckets_x27_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_145_; 
lean_inc(v_bkt_121_);
v___x_140_ = lean_box(0);
v_buckets_x27_141_ = lean_array_uset(v_buckets_100_, v___x_120_, v___x_140_);
v___x_142_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(v_a_97_, v_b_98_, v_bkt_121_);
v___x_143_ = lean_array_uset(v_buckets_x27_141_, v___x_120_, v___x_142_);
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 1, v___x_143_);
v___x_145_ = v___x_102_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_size_99_);
lean_ctor_set(v_reuseFailAlloc_146_, 1, v___x_143_);
v___x_145_ = v_reuseFailAlloc_146_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
return v___x_145_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(lean_object* v_key_148_, lean_object* v_r_149_, lean_object* v_a_150_, lean_object* v_a_151_){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
lean_inc_ref(v_r_149_);
v___x_152_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_150_, v_key_148_, v_r_149_);
v___x_153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_153_, 0, v_r_149_);
lean_ctor_set(v___x_153_, 1, v___x_152_);
v___x_154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_154_, 0, v___x_153_);
lean_ctor_set(v___x_154_, 1, v_a_151_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(lean_object* v_key_155_, lean_object* v_r_156_, lean_object* v_a_157_, uint8_t v_a_158_, lean_object* v_a_159_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(v_key_155_, v_r_156_, v_a_157_, v_a_159_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___boxed(lean_object* v_key_161_, lean_object* v_r_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_){
_start:
{
uint8_t v_a_boxed_166_; lean_object* v_res_167_; 
v_a_boxed_166_ = lean_unbox(v_a_164_);
v_res_167_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_161_, v_r_162_, v_a_163_, v_a_boxed_166_, v_a_165_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0(lean_object* v_00_u03b2_168_, lean_object* v_m_169_, lean_object* v_a_170_, lean_object* v_b_171_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0___redArg(v_m_169_, v_a_170_, v_b_171_);
return v___x_172_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0(lean_object* v_00_u03b2_173_, lean_object* v_a_174_, lean_object* v_x_175_){
_start:
{
uint8_t v___x_176_; 
v___x_176_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_a_174_, v_x_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0___boxed(lean_object* v_00_u03b2_177_, lean_object* v_a_178_, lean_object* v_x_179_){
_start:
{
uint8_t v_res_180_; lean_object* v_r_181_; 
v_res_180_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0(v_00_u03b2_177_, v_a_178_, v_x_179_);
lean_dec(v_x_179_);
lean_dec_ref(v_a_178_);
v_r_181_ = lean_box(v_res_180_);
return v_r_181_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1(lean_object* v_00_u03b2_182_, lean_object* v_data_183_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1___redArg(v_data_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__2(lean_object* v_00_u03b2_185_, lean_object* v_a_186_, lean_object* v_b_187_, lean_object* v_x_188_){
_start:
{
lean_object* v___x_189_; 
v___x_189_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(v_a_186_, v_b_187_, v_x_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_190_, lean_object* v_i_191_, lean_object* v_source_192_, lean_object* v_target_193_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2___redArg(v_i_191_, v_source_192_, v_target_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_195_, lean_object* v_x_196_, lean_object* v_x_197_){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3___redArg(v_x_196_, v_x_197_);
return v___x_198_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__4(void){
_start:
{
lean_object* v___x_205_; lean_object* v___f_206_; 
v___x_205_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___f_206_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_206_, 0, v___x_205_);
return v___f_206_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__5(void){
_start:
{
lean_object* v___f_207_; lean_object* v___f_208_; lean_object* v___f_209_; 
v___f_207_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__4, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__4_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__4);
v___f_208_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__0));
v___f_209_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_209_, 0, v___f_208_);
lean_closure_set(v___f_209_, 1, v___f_207_);
return v___f_209_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20(void){
_start:
{
lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_255_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__19));
v___x_256_ = l_ReaderT_instMonad___redArg(v___x_255_);
return v___x_256_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__29(void){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_257_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20);
v___x_258_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_258_, 0, lean_box(0));
lean_closure_set(v___x_258_, 1, lean_box(0));
lean_closure_set(v___x_258_, 2, v___x_257_);
return v___x_258_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__24(void){
_start:
{
lean_object* v___x_259_; lean_object* v___f_260_; 
v___x_259_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20);
v___f_260_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_260_, 0, v___x_259_);
return v___f_260_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__23(void){
_start:
{
lean_object* v___x_261_; lean_object* v___f_262_; 
v___x_261_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20);
v___f_262_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_262_, 0, v___x_261_);
return v___f_262_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__22(void){
_start:
{
lean_object* v___x_263_; lean_object* v___f_264_; 
v___x_263_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20);
v___f_264_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_264_, 0, v___x_263_);
return v___f_264_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__27(void){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_265_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20);
v___x_266_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_266_, 0, lean_box(0));
lean_closure_set(v___x_266_, 1, lean_box(0));
lean_closure_set(v___x_266_, 2, v___x_265_);
return v___x_266_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__21(void){
_start:
{
lean_object* v___x_267_; lean_object* v___f_268_; 
v___x_267_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20);
v___f_268_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_268_, 0, v___x_267_);
return v___f_268_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__25(void){
_start:
{
lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_269_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20);
v___x_270_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_270_, 0, lean_box(0));
lean_closure_set(v___x_270_, 1, lean_box(0));
lean_closure_set(v___x_270_, 2, v___x_269_);
return v___x_270_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__26(void){
_start:
{
lean_object* v___f_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___f_271_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__21, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__21_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__21);
v___x_272_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__25, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__25_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__25);
v___x_273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_273_, 0, v___x_272_);
lean_ctor_set(v___x_273_, 1, v___f_271_);
return v___x_273_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__28(void){
_start:
{
lean_object* v___f_274_; lean_object* v___f_275_; lean_object* v___f_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v___f_274_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__24, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__24_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__24);
v___f_275_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__23, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__23_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__23);
v___f_276_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__22, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__22_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__22);
v___x_277_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__27, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__27_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__27);
v___x_278_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__26, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__26_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__26);
v___x_279_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
lean_ctor_set(v___x_279_, 1, v___x_277_);
lean_ctor_set(v___x_279_, 2, v___f_276_);
lean_ctor_set(v___x_279_, 3, v___f_275_);
lean_ctor_set(v___x_279_, 4, v___f_274_);
return v___x_279_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__30(void){
_start:
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_280_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__29, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__29_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__29);
v___x_281_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__28, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__28_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__28);
v___x_282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_282_, 0, v___x_281_);
lean_ctor_set(v___x_282_, 1, v___x_280_);
return v___x_282_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__31(void){
_start:
{
lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_283_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20);
v___x_284_ = lean_alloc_closure((void*)(l_StateT_lift), 6, 3);
lean_closure_set(v___x_284_, 0, lean_box(0));
lean_closure_set(v___x_284_, 1, lean_box(0));
lean_closure_set(v___x_284_, 2, v___x_283_);
return v___x_284_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__32(void){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_285_ = l_Lean_instInhabitedExpr;
v___x_286_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__30, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__30_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__30);
v___x_287_ = l_instInhabitedOfMonad___redArg(v___x_286_, v___x_285_);
return v___x_287_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__36(void){
_start:
{
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_291_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__35));
v___x_292_ = lean_unsigned_to_nat(67u);
v___x_293_ = lean_unsigned_to_nat(35u);
v___x_294_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__34));
v___x_295_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__33));
v___x_296_ = l_mkPanicMessageWithDecl(v___x_295_, v___x_294_, v___x_293_, v___x_292_, v___x_291_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit(lean_object* v_e_297_, lean_object* v_offset_298_, lean_object* v_fn_299_, lean_object* v_a_300_, uint8_t v_a_301_, lean_object* v_a_302_){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v_share1_306_; lean_object* v_assertShared_307_; lean_object* v_isDebugEnabled_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_529_; 
v___x_303_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20);
v___x_304_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__30, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__30_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__30);
v___x_305_ = l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM;
v_share1_306_ = lean_ctor_get(v___x_305_, 0);
v_assertShared_307_ = lean_ctor_get(v___x_305_, 1);
v_isDebugEnabled_308_ = lean_ctor_get(v___x_305_, 2);
v_isSharedCheck_529_ = !lean_is_exclusive(v___x_305_);
if (v_isSharedCheck_529_ == 0)
{
v___x_310_ = v___x_305_;
v_isShared_311_ = v_isSharedCheck_529_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_isDebugEnabled_308_);
lean_inc(v_assertShared_307_);
lean_inc(v_share1_306_);
lean_dec(v___x_305_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_529_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_312_; lean_object* v___f_313_; lean_object* v___f_314_; lean_object* v___x_315_; lean_object* v___x_317_; 
v___x_312_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__31, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__31_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__31);
v___f_313_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_313_, 0, v_share1_306_);
lean_closure_set(v___f_313_, 1, v___x_312_);
v___f_314_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift___redArg___lam__1), 3, 2);
lean_closure_set(v___f_314_, 0, v_assertShared_307_);
lean_closure_set(v___f_314_, 1, v___x_312_);
v___x_315_ = lean_alloc_closure((void*)(l_StateT_lift), 6, 5);
lean_closure_set(v___x_315_, 0, lean_box(0));
lean_closure_set(v___x_315_, 1, lean_box(0));
lean_closure_set(v___x_315_, 2, v___x_303_);
lean_closure_set(v___x_315_, 3, lean_box(0));
lean_closure_set(v___x_315_, 4, v_isDebugEnabled_308_);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 2, v___x_315_);
lean_ctor_set(v___x_310_, 1, v___f_314_);
lean_ctor_set(v___x_310_, 0, v___f_313_);
v___x_317_ = v___x_310_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v___f_313_);
lean_ctor_set(v_reuseFailAlloc_528_, 1, v___f_314_);
lean_ctor_set(v_reuseFailAlloc_528_, 2, v___x_315_);
v___x_317_ = v_reuseFailAlloc_528_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
switch(lean_obj_tag(v_e_297_))
{
case 5:
{
lean_object* v_fn_318_; lean_object* v_arg_319_; lean_object* v___x_320_; lean_object* v_fst_321_; lean_object* v_snd_322_; lean_object* v_fst_323_; lean_object* v_snd_324_; lean_object* v___x_325_; lean_object* v_fst_326_; lean_object* v_snd_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_350_; 
v_fn_318_ = lean_ctor_get(v_e_297_, 0);
v_arg_319_ = lean_ctor_get(v_e_297_, 1);
lean_inc_ref(v_fn_299_);
lean_inc(v_offset_298_);
lean_inc_ref(v_fn_318_);
v___x_320_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_fn_318_, v_offset_298_, v_fn_299_, v_a_300_, v_a_301_, v_a_302_);
v_fst_321_ = lean_ctor_get(v___x_320_, 0);
lean_inc(v_fst_321_);
v_snd_322_ = lean_ctor_get(v___x_320_, 1);
lean_inc(v_snd_322_);
lean_dec_ref(v___x_320_);
v_fst_323_ = lean_ctor_get(v_fst_321_, 0);
lean_inc(v_fst_323_);
v_snd_324_ = lean_ctor_get(v_fst_321_, 1);
lean_inc(v_snd_324_);
lean_dec(v_fst_321_);
lean_inc_ref(v_arg_319_);
v___x_325_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_arg_319_, v_offset_298_, v_fn_299_, v_snd_324_, v_a_301_, v_snd_322_);
v_fst_326_ = lean_ctor_get(v___x_325_, 0);
v_snd_327_ = lean_ctor_get(v___x_325_, 1);
v_isSharedCheck_350_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_350_ == 0)
{
v___x_329_ = v___x_325_;
v_isShared_330_ = v_isSharedCheck_350_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_snd_327_);
lean_inc(v_fst_326_);
lean_dec(v___x_325_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_350_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v_fst_331_; lean_object* v_snd_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_349_; 
v_fst_331_ = lean_ctor_get(v_fst_326_, 0);
v_snd_332_ = lean_ctor_get(v_fst_326_, 1);
v_isSharedCheck_349_ = !lean_is_exclusive(v_fst_326_);
if (v_isSharedCheck_349_ == 0)
{
v___x_334_ = v_fst_326_;
v_isShared_335_ = v_isSharedCheck_349_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_snd_332_);
lean_inc(v_fst_331_);
lean_dec(v_fst_326_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_349_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
uint8_t v___y_337_; uint8_t v___x_347_; 
v___x_347_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_318_, v_fst_323_);
if (v___x_347_ == 0)
{
v___y_337_ = v___x_347_;
goto v___jp_336_;
}
else
{
uint8_t v___x_348_; 
v___x_348_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_319_, v_fst_331_);
v___y_337_ = v___x_348_;
goto v___jp_336_;
}
v___jp_336_:
{
if (v___y_337_ == 0)
{
lean_object* v___x_10643__overap_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
lean_del_object(v___x_334_);
lean_del_object(v___x_329_);
lean_dec_ref(v_e_297_);
v___x_10643__overap_338_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v___x_317_, v___x_304_, v_fst_323_, v_fst_331_);
v___x_339_ = lean_box(v_a_301_);
v___x_340_ = lean_apply_3(v___x_10643__overap_338_, v_snd_332_, v___x_339_, v_snd_327_);
return v___x_340_;
}
else
{
lean_object* v___x_342_; 
lean_dec(v_fst_331_);
lean_dec(v_fst_323_);
lean_dec_ref(v___x_317_);
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 0, v_e_297_);
v___x_342_ = v___x_334_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v_e_297_);
lean_ctor_set(v_reuseFailAlloc_346_, 1, v_snd_332_);
v___x_342_ = v_reuseFailAlloc_346_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
lean_object* v___x_344_; 
if (v_isShared_330_ == 0)
{
lean_ctor_set(v___x_329_, 0, v___x_342_);
v___x_344_ = v___x_329_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v___x_342_);
lean_ctor_set(v_reuseFailAlloc_345_, 1, v_snd_327_);
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
}
}
case 6:
{
lean_object* v_binderName_351_; lean_object* v_binderType_352_; lean_object* v_body_353_; uint8_t v_binderInfo_354_; lean_object* v___x_355_; lean_object* v_fst_356_; lean_object* v_snd_357_; lean_object* v_fst_358_; lean_object* v_snd_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v_fst_363_; lean_object* v_snd_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_387_; 
v_binderName_351_ = lean_ctor_get(v_e_297_, 0);
v_binderType_352_ = lean_ctor_get(v_e_297_, 1);
v_body_353_ = lean_ctor_get(v_e_297_, 2);
v_binderInfo_354_ = lean_ctor_get_uint8(v_e_297_, sizeof(void*)*3 + 8);
lean_inc_ref(v_fn_299_);
lean_inc(v_offset_298_);
lean_inc_ref(v_binderType_352_);
v___x_355_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_binderType_352_, v_offset_298_, v_fn_299_, v_a_300_, v_a_301_, v_a_302_);
v_fst_356_ = lean_ctor_get(v___x_355_, 0);
lean_inc(v_fst_356_);
v_snd_357_ = lean_ctor_get(v___x_355_, 1);
lean_inc(v_snd_357_);
lean_dec_ref(v___x_355_);
v_fst_358_ = lean_ctor_get(v_fst_356_, 0);
lean_inc(v_fst_358_);
v_snd_359_ = lean_ctor_get(v_fst_356_, 1);
lean_inc(v_snd_359_);
lean_dec(v_fst_356_);
v___x_360_ = lean_unsigned_to_nat(1u);
v___x_361_ = lean_nat_add(v_offset_298_, v___x_360_);
lean_dec(v_offset_298_);
lean_inc_ref(v_body_353_);
v___x_362_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_body_353_, v___x_361_, v_fn_299_, v_snd_359_, v_a_301_, v_snd_357_);
v_fst_363_ = lean_ctor_get(v___x_362_, 0);
v_snd_364_ = lean_ctor_get(v___x_362_, 1);
v_isSharedCheck_387_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_387_ == 0)
{
v___x_366_ = v___x_362_;
v_isShared_367_ = v_isSharedCheck_387_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_snd_364_);
lean_inc(v_fst_363_);
lean_dec(v___x_362_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_387_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v_fst_368_; lean_object* v_snd_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_386_; 
v_fst_368_ = lean_ctor_get(v_fst_363_, 0);
v_snd_369_ = lean_ctor_get(v_fst_363_, 1);
v_isSharedCheck_386_ = !lean_is_exclusive(v_fst_363_);
if (v_isSharedCheck_386_ == 0)
{
v___x_371_ = v_fst_363_;
v_isShared_372_ = v_isSharedCheck_386_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_snd_369_);
lean_inc(v_fst_368_);
lean_dec(v_fst_363_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_386_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
uint8_t v___y_374_; uint8_t v___x_384_; 
v___x_384_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_352_, v_fst_358_);
if (v___x_384_ == 0)
{
v___y_374_ = v___x_384_;
goto v___jp_373_;
}
else
{
uint8_t v___x_385_; 
v___x_385_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_353_, v_fst_368_);
v___y_374_ = v___x_385_;
goto v___jp_373_;
}
v___jp_373_:
{
if (v___y_374_ == 0)
{
lean_object* v___x_10804__overap_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
lean_inc(v_binderName_351_);
lean_del_object(v___x_371_);
lean_del_object(v___x_366_);
lean_dec_ref(v_e_297_);
v___x_10804__overap_375_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v___x_317_, v___x_304_, v_binderName_351_, v_binderInfo_354_, v_fst_358_, v_fst_368_);
v___x_376_ = lean_box(v_a_301_);
v___x_377_ = lean_apply_3(v___x_10804__overap_375_, v_snd_369_, v___x_376_, v_snd_364_);
return v___x_377_;
}
else
{
lean_object* v___x_379_; 
lean_dec(v_fst_368_);
lean_dec(v_fst_358_);
lean_dec_ref(v___x_317_);
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 0, v_e_297_);
v___x_379_ = v___x_371_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_e_297_);
lean_ctor_set(v_reuseFailAlloc_383_, 1, v_snd_369_);
v___x_379_ = v_reuseFailAlloc_383_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
lean_object* v___x_381_; 
if (v_isShared_367_ == 0)
{
lean_ctor_set(v___x_366_, 0, v___x_379_);
v___x_381_ = v___x_366_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v___x_379_);
lean_ctor_set(v_reuseFailAlloc_382_, 1, v_snd_364_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
}
}
}
}
}
case 7:
{
lean_object* v_binderName_388_; lean_object* v_binderType_389_; lean_object* v_body_390_; uint8_t v_binderInfo_391_; lean_object* v___x_392_; lean_object* v_fst_393_; lean_object* v_snd_394_; lean_object* v_fst_395_; lean_object* v_snd_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v_fst_400_; lean_object* v_snd_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_424_; 
v_binderName_388_ = lean_ctor_get(v_e_297_, 0);
v_binderType_389_ = lean_ctor_get(v_e_297_, 1);
v_body_390_ = lean_ctor_get(v_e_297_, 2);
v_binderInfo_391_ = lean_ctor_get_uint8(v_e_297_, sizeof(void*)*3 + 8);
lean_inc_ref(v_fn_299_);
lean_inc(v_offset_298_);
lean_inc_ref(v_binderType_389_);
v___x_392_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_binderType_389_, v_offset_298_, v_fn_299_, v_a_300_, v_a_301_, v_a_302_);
v_fst_393_ = lean_ctor_get(v___x_392_, 0);
lean_inc(v_fst_393_);
v_snd_394_ = lean_ctor_get(v___x_392_, 1);
lean_inc(v_snd_394_);
lean_dec_ref(v___x_392_);
v_fst_395_ = lean_ctor_get(v_fst_393_, 0);
lean_inc(v_fst_395_);
v_snd_396_ = lean_ctor_get(v_fst_393_, 1);
lean_inc(v_snd_396_);
lean_dec(v_fst_393_);
v___x_397_ = lean_unsigned_to_nat(1u);
v___x_398_ = lean_nat_add(v_offset_298_, v___x_397_);
lean_dec(v_offset_298_);
lean_inc_ref(v_body_390_);
v___x_399_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_body_390_, v___x_398_, v_fn_299_, v_snd_396_, v_a_301_, v_snd_394_);
v_fst_400_ = lean_ctor_get(v___x_399_, 0);
v_snd_401_ = lean_ctor_get(v___x_399_, 1);
v_isSharedCheck_424_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_424_ == 0)
{
v___x_403_ = v___x_399_;
v_isShared_404_ = v_isSharedCheck_424_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_snd_401_);
lean_inc(v_fst_400_);
lean_dec(v___x_399_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_424_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v_fst_405_; lean_object* v_snd_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_423_; 
v_fst_405_ = lean_ctor_get(v_fst_400_, 0);
v_snd_406_ = lean_ctor_get(v_fst_400_, 1);
v_isSharedCheck_423_ = !lean_is_exclusive(v_fst_400_);
if (v_isSharedCheck_423_ == 0)
{
v___x_408_ = v_fst_400_;
v_isShared_409_ = v_isSharedCheck_423_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_snd_406_);
lean_inc(v_fst_405_);
lean_dec(v_fst_400_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_423_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
uint8_t v___y_411_; uint8_t v___x_421_; 
v___x_421_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_389_, v_fst_395_);
if (v___x_421_ == 0)
{
v___y_411_ = v___x_421_;
goto v___jp_410_;
}
else
{
uint8_t v___x_422_; 
v___x_422_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_390_, v_fst_405_);
v___y_411_ = v___x_422_;
goto v___jp_410_;
}
v___jp_410_:
{
if (v___y_411_ == 0)
{
lean_object* v___x_10969__overap_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
lean_inc(v_binderName_388_);
lean_del_object(v___x_408_);
lean_del_object(v___x_403_);
lean_dec_ref(v_e_297_);
v___x_10969__overap_412_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v___x_317_, v___x_304_, v_binderName_388_, v_binderInfo_391_, v_fst_395_, v_fst_405_);
v___x_413_ = lean_box(v_a_301_);
v___x_414_ = lean_apply_3(v___x_10969__overap_412_, v_snd_406_, v___x_413_, v_snd_401_);
return v___x_414_;
}
else
{
lean_object* v___x_416_; 
lean_dec(v_fst_405_);
lean_dec(v_fst_395_);
lean_dec_ref(v___x_317_);
if (v_isShared_409_ == 0)
{
lean_ctor_set(v___x_408_, 0, v_e_297_);
v___x_416_ = v___x_408_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_e_297_);
lean_ctor_set(v_reuseFailAlloc_420_, 1, v_snd_406_);
v___x_416_ = v_reuseFailAlloc_420_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
lean_object* v___x_418_; 
if (v_isShared_404_ == 0)
{
lean_ctor_set(v___x_403_, 0, v___x_416_);
v___x_418_ = v___x_403_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v___x_416_);
lean_ctor_set(v_reuseFailAlloc_419_, 1, v_snd_401_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
}
}
}
}
case 8:
{
lean_object* v_declName_425_; lean_object* v_type_426_; lean_object* v_value_427_; lean_object* v_body_428_; uint8_t v_nondep_429_; lean_object* v___x_430_; lean_object* v_fst_431_; lean_object* v_snd_432_; lean_object* v_fst_433_; lean_object* v_snd_434_; lean_object* v___x_435_; lean_object* v_fst_436_; lean_object* v_snd_437_; lean_object* v_fst_438_; lean_object* v_snd_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v_fst_443_; lean_object* v_snd_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_471_; 
v_declName_425_ = lean_ctor_get(v_e_297_, 0);
v_type_426_ = lean_ctor_get(v_e_297_, 1);
v_value_427_ = lean_ctor_get(v_e_297_, 2);
v_body_428_ = lean_ctor_get(v_e_297_, 3);
v_nondep_429_ = lean_ctor_get_uint8(v_e_297_, sizeof(void*)*4 + 8);
lean_inc_ref(v_fn_299_);
lean_inc(v_offset_298_);
lean_inc_ref(v_type_426_);
v___x_430_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_type_426_, v_offset_298_, v_fn_299_, v_a_300_, v_a_301_, v_a_302_);
v_fst_431_ = lean_ctor_get(v___x_430_, 0);
lean_inc(v_fst_431_);
v_snd_432_ = lean_ctor_get(v___x_430_, 1);
lean_inc(v_snd_432_);
lean_dec_ref(v___x_430_);
v_fst_433_ = lean_ctor_get(v_fst_431_, 0);
lean_inc(v_fst_433_);
v_snd_434_ = lean_ctor_get(v_fst_431_, 1);
lean_inc(v_snd_434_);
lean_dec(v_fst_431_);
lean_inc_ref(v_fn_299_);
lean_inc(v_offset_298_);
lean_inc_ref(v_value_427_);
v___x_435_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_value_427_, v_offset_298_, v_fn_299_, v_snd_434_, v_a_301_, v_snd_432_);
v_fst_436_ = lean_ctor_get(v___x_435_, 0);
lean_inc(v_fst_436_);
v_snd_437_ = lean_ctor_get(v___x_435_, 1);
lean_inc(v_snd_437_);
lean_dec_ref(v___x_435_);
v_fst_438_ = lean_ctor_get(v_fst_436_, 0);
lean_inc(v_fst_438_);
v_snd_439_ = lean_ctor_get(v_fst_436_, 1);
lean_inc(v_snd_439_);
lean_dec(v_fst_436_);
v___x_440_ = lean_unsigned_to_nat(1u);
v___x_441_ = lean_nat_add(v_offset_298_, v___x_440_);
lean_dec(v_offset_298_);
lean_inc_ref(v_body_428_);
v___x_442_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_body_428_, v___x_441_, v_fn_299_, v_snd_439_, v_a_301_, v_snd_437_);
v_fst_443_ = lean_ctor_get(v___x_442_, 0);
v_snd_444_ = lean_ctor_get(v___x_442_, 1);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_471_ == 0)
{
v___x_446_ = v___x_442_;
v_isShared_447_ = v_isSharedCheck_471_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_snd_444_);
lean_inc(v_fst_443_);
lean_dec(v___x_442_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_471_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v_fst_448_; lean_object* v_snd_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_470_; 
v_fst_448_ = lean_ctor_get(v_fst_443_, 0);
v_snd_449_ = lean_ctor_get(v_fst_443_, 1);
v_isSharedCheck_470_ = !lean_is_exclusive(v_fst_443_);
if (v_isSharedCheck_470_ == 0)
{
v___x_451_ = v_fst_443_;
v_isShared_452_ = v_isSharedCheck_470_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_snd_449_);
lean_inc(v_fst_448_);
lean_dec(v_fst_443_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_470_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
uint8_t v___y_454_; uint8_t v___x_468_; 
v___x_468_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_type_426_, v_fst_433_);
if (v___x_468_ == 0)
{
v___y_454_ = v___x_468_;
goto v___jp_453_;
}
else
{
uint8_t v___x_469_; 
v___x_469_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_value_427_, v_fst_438_);
v___y_454_ = v___x_469_;
goto v___jp_453_;
}
v___jp_453_:
{
if (v___y_454_ == 0)
{
lean_object* v___x_11156__overap_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
lean_inc(v_declName_425_);
lean_del_object(v___x_451_);
lean_del_object(v___x_446_);
lean_dec_ref(v_e_297_);
v___x_11156__overap_455_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v___x_317_, v___x_304_, v_declName_425_, v_fst_433_, v_fst_438_, v_fst_448_, v_nondep_429_);
v___x_456_ = lean_box(v_a_301_);
v___x_457_ = lean_apply_3(v___x_11156__overap_455_, v_snd_449_, v___x_456_, v_snd_444_);
return v___x_457_;
}
else
{
uint8_t v___x_458_; 
v___x_458_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_428_, v_fst_448_);
if (v___x_458_ == 0)
{
lean_object* v___x_11158__overap_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
lean_inc(v_declName_425_);
lean_del_object(v___x_451_);
lean_del_object(v___x_446_);
lean_dec_ref(v_e_297_);
v___x_11158__overap_459_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v___x_317_, v___x_304_, v_declName_425_, v_fst_433_, v_fst_438_, v_fst_448_, v_nondep_429_);
v___x_460_ = lean_box(v_a_301_);
v___x_461_ = lean_apply_3(v___x_11158__overap_459_, v_snd_449_, v___x_460_, v_snd_444_);
return v___x_461_;
}
else
{
lean_object* v___x_463_; 
lean_dec(v_fst_448_);
lean_dec(v_fst_438_);
lean_dec(v_fst_433_);
lean_dec_ref(v___x_317_);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 0, v_e_297_);
v___x_463_ = v___x_451_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_e_297_);
lean_ctor_set(v_reuseFailAlloc_467_, 1, v_snd_449_);
v___x_463_ = v_reuseFailAlloc_467_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
lean_object* v___x_465_; 
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 0, v___x_463_);
v___x_465_ = v___x_446_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v___x_463_);
lean_ctor_set(v_reuseFailAlloc_466_, 1, v_snd_444_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
}
}
}
}
}
}
case 10:
{
lean_object* v_data_472_; lean_object* v_expr_473_; lean_object* v___x_474_; lean_object* v_fst_475_; lean_object* v_snd_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_496_; 
v_data_472_ = lean_ctor_get(v_e_297_, 0);
v_expr_473_ = lean_ctor_get(v_e_297_, 1);
lean_inc_ref(v_expr_473_);
v___x_474_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_expr_473_, v_offset_298_, v_fn_299_, v_a_300_, v_a_301_, v_a_302_);
v_fst_475_ = lean_ctor_get(v___x_474_, 0);
v_snd_476_ = lean_ctor_get(v___x_474_, 1);
v_isSharedCheck_496_ = !lean_is_exclusive(v___x_474_);
if (v_isSharedCheck_496_ == 0)
{
v___x_478_ = v___x_474_;
v_isShared_479_ = v_isSharedCheck_496_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_snd_476_);
lean_inc(v_fst_475_);
lean_dec(v___x_474_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_496_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v_fst_480_; lean_object* v_snd_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_495_; 
v_fst_480_ = lean_ctor_get(v_fst_475_, 0);
v_snd_481_ = lean_ctor_get(v_fst_475_, 1);
v_isSharedCheck_495_ = !lean_is_exclusive(v_fst_475_);
if (v_isSharedCheck_495_ == 0)
{
v___x_483_ = v_fst_475_;
v_isShared_484_ = v_isSharedCheck_495_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_snd_481_);
lean_inc(v_fst_480_);
lean_dec(v_fst_475_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_495_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
uint8_t v___x_485_; 
v___x_485_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_expr_473_, v_fst_480_);
if (v___x_485_ == 0)
{
lean_object* v___x_11315__overap_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
lean_inc(v_data_472_);
lean_del_object(v___x_483_);
lean_del_object(v___x_478_);
lean_dec_ref(v_e_297_);
v___x_11315__overap_486_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg(v___x_317_, v___x_304_, v_data_472_, v_fst_480_);
v___x_487_ = lean_box(v_a_301_);
v___x_488_ = lean_apply_3(v___x_11315__overap_486_, v_snd_481_, v___x_487_, v_snd_476_);
return v___x_488_;
}
else
{
lean_object* v___x_490_; 
lean_dec(v_fst_480_);
lean_dec_ref(v___x_317_);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 0, v_e_297_);
v___x_490_ = v___x_483_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_e_297_);
lean_ctor_set(v_reuseFailAlloc_494_, 1, v_snd_481_);
v___x_490_ = v_reuseFailAlloc_494_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
lean_object* v___x_492_; 
if (v_isShared_479_ == 0)
{
lean_ctor_set(v___x_478_, 0, v___x_490_);
v___x_492_ = v___x_478_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v___x_490_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v_snd_476_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
}
}
}
}
case 11:
{
lean_object* v_typeName_497_; lean_object* v_idx_498_; lean_object* v_struct_499_; lean_object* v___x_500_; lean_object* v_fst_501_; lean_object* v_snd_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_522_; 
v_typeName_497_ = lean_ctor_get(v_e_297_, 0);
v_idx_498_ = lean_ctor_get(v_e_297_, 1);
v_struct_499_ = lean_ctor_get(v_e_297_, 2);
lean_inc_ref(v_struct_499_);
v___x_500_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_struct_499_, v_offset_298_, v_fn_299_, v_a_300_, v_a_301_, v_a_302_);
v_fst_501_ = lean_ctor_get(v___x_500_, 0);
v_snd_502_ = lean_ctor_get(v___x_500_, 1);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_522_ == 0)
{
v___x_504_ = v___x_500_;
v_isShared_505_ = v_isSharedCheck_522_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_snd_502_);
lean_inc(v_fst_501_);
lean_dec(v___x_500_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_522_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v_fst_506_; lean_object* v_snd_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_521_; 
v_fst_506_ = lean_ctor_get(v_fst_501_, 0);
v_snd_507_ = lean_ctor_get(v_fst_501_, 1);
v_isSharedCheck_521_ = !lean_is_exclusive(v_fst_501_);
if (v_isSharedCheck_521_ == 0)
{
v___x_509_ = v_fst_501_;
v_isShared_510_ = v_isSharedCheck_521_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_snd_507_);
lean_inc(v_fst_506_);
lean_dec(v_fst_501_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_521_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
uint8_t v___x_511_; 
v___x_511_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_499_, v_fst_506_);
if (v___x_511_ == 0)
{
lean_object* v___x_11427__overap_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
lean_inc(v_idx_498_);
lean_inc(v_typeName_497_);
lean_del_object(v___x_509_);
lean_del_object(v___x_504_);
lean_dec_ref(v_e_297_);
v___x_11427__overap_512_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg(v___x_317_, v___x_304_, v_typeName_497_, v_idx_498_, v_fst_506_);
v___x_513_ = lean_box(v_a_301_);
v___x_514_ = lean_apply_3(v___x_11427__overap_512_, v_snd_507_, v___x_513_, v_snd_502_);
return v___x_514_;
}
else
{
lean_object* v___x_516_; 
lean_dec(v_fst_506_);
lean_dec_ref(v___x_317_);
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 0, v_e_297_);
v___x_516_ = v___x_509_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v_e_297_);
lean_ctor_set(v_reuseFailAlloc_520_, 1, v_snd_507_);
v___x_516_ = v_reuseFailAlloc_520_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
lean_object* v___x_518_; 
if (v_isShared_505_ == 0)
{
lean_ctor_set(v___x_504_, 0, v___x_516_);
v___x_518_ = v___x_504_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v___x_516_);
lean_ctor_set(v_reuseFailAlloc_519_, 1, v_snd_502_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_10529__overap_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
lean_dec_ref(v___x_317_);
lean_dec_ref(v_fn_299_);
lean_dec(v_offset_298_);
lean_dec_ref(v_e_297_);
v___x_523_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__32, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__32_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__32);
v___x_524_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__36, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__36_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__36);
v___x_10529__overap_525_ = l_panic___redArg(v___x_523_, v___x_524_);
v___x_526_ = lean_box(v_a_301_);
v___x_527_ = lean_apply_3(v___x_10529__overap_525_, v_a_300_, v___x_526_, v_a_302_);
return v___x_527_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(lean_object* v_e_530_, lean_object* v_offset_531_, lean_object* v_f_532_, lean_object* v_a_533_, uint8_t v_a_534_, lean_object* v_a_535_){
_start:
{
lean_object* v___f_536_; lean_object* v_key_537_; lean_object* v___f_538_; lean_object* v___x_539_; 
v___f_536_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__3));
lean_inc(v_offset_531_);
lean_inc_ref(v_e_530_);
v_key_537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_537_, 0, v_e_530_);
lean_ctor_set(v_key_537_, 1, v_offset_531_);
v___f_538_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__5, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__5_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__5);
lean_inc_ref(v_key_537_);
v___x_539_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_538_, v___f_536_, v_a_533_, v_key_537_);
if (lean_obj_tag(v___x_539_) == 1)
{
lean_object* v_val_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
lean_dec_ref(v_key_537_);
lean_dec_ref(v_f_532_);
lean_dec(v_offset_531_);
lean_dec_ref(v_e_530_);
v_val_540_ = lean_ctor_get(v___x_539_, 0);
lean_inc(v_val_540_);
lean_dec_ref(v___x_539_);
v___x_541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_541_, 0, v_val_540_);
lean_ctor_set(v___x_541_, 1, v_a_533_);
v___x_542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
lean_ctor_set(v___x_542_, 1, v_a_535_);
return v___x_542_;
}
else
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v_fst_545_; 
lean_dec(v___x_539_);
v___x_543_ = lean_box(v_a_534_);
lean_inc_ref(v_f_532_);
lean_inc(v_offset_531_);
lean_inc_ref(v_e_530_);
v___x_544_ = lean_apply_4(v_f_532_, v_e_530_, v_offset_531_, v___x_543_, v_a_535_);
v_fst_545_ = lean_ctor_get(v___x_544_, 0);
lean_inc(v_fst_545_);
if (lean_obj_tag(v_fst_545_) == 1)
{
lean_object* v_snd_546_; lean_object* v_val_547_; lean_object* v___x_548_; 
lean_dec_ref(v_f_532_);
lean_dec(v_offset_531_);
lean_dec_ref(v_e_530_);
v_snd_546_ = lean_ctor_get(v___x_544_, 1);
lean_inc(v_snd_546_);
lean_dec_ref(v___x_544_);
v_val_547_ = lean_ctor_get(v_fst_545_, 0);
lean_inc(v_val_547_);
lean_dec_ref(v_fst_545_);
v___x_548_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(v_key_537_, v_val_547_, v_a_533_, v_snd_546_);
return v___x_548_;
}
else
{
lean_dec(v_fst_545_);
switch(lean_obj_tag(v_e_530_))
{
case 9:
{
lean_object* v_snd_549_; lean_object* v___x_550_; 
lean_dec_ref(v_f_532_);
lean_dec(v_offset_531_);
v_snd_549_ = lean_ctor_get(v___x_544_, 1);
lean_inc(v_snd_549_);
lean_dec_ref(v___x_544_);
v___x_550_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(v_key_537_, v_e_530_, v_a_533_, v_snd_549_);
return v___x_550_;
}
case 2:
{
lean_object* v_snd_551_; lean_object* v___x_552_; 
lean_dec_ref(v_f_532_);
lean_dec(v_offset_531_);
v_snd_551_ = lean_ctor_get(v___x_544_, 1);
lean_inc(v_snd_551_);
lean_dec_ref(v___x_544_);
v___x_552_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(v_key_537_, v_e_530_, v_a_533_, v_snd_551_);
return v___x_552_;
}
case 0:
{
lean_object* v_snd_553_; lean_object* v___x_554_; 
lean_dec_ref(v_f_532_);
lean_dec(v_offset_531_);
v_snd_553_ = lean_ctor_get(v___x_544_, 1);
lean_inc(v_snd_553_);
lean_dec_ref(v___x_544_);
v___x_554_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(v_key_537_, v_e_530_, v_a_533_, v_snd_553_);
return v___x_554_;
}
case 1:
{
lean_object* v_snd_555_; lean_object* v___x_556_; 
lean_dec_ref(v_f_532_);
lean_dec(v_offset_531_);
v_snd_555_ = lean_ctor_get(v___x_544_, 1);
lean_inc(v_snd_555_);
lean_dec_ref(v___x_544_);
v___x_556_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(v_key_537_, v_e_530_, v_a_533_, v_snd_555_);
return v___x_556_;
}
case 4:
{
lean_object* v_snd_557_; lean_object* v___x_558_; 
lean_dec_ref(v_f_532_);
lean_dec(v_offset_531_);
v_snd_557_ = lean_ctor_get(v___x_544_, 1);
lean_inc(v_snd_557_);
lean_dec_ref(v___x_544_);
v___x_558_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(v_key_537_, v_e_530_, v_a_533_, v_snd_557_);
return v___x_558_;
}
case 3:
{
lean_object* v_snd_559_; lean_object* v___x_560_; 
lean_dec_ref(v_f_532_);
lean_dec(v_offset_531_);
v_snd_559_ = lean_ctor_get(v___x_544_, 1);
lean_inc(v_snd_559_);
lean_dec_ref(v___x_544_);
v___x_560_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(v_key_537_, v_e_530_, v_a_533_, v_snd_559_);
return v___x_560_;
}
default: 
{
lean_object* v_snd_561_; lean_object* v___x_562_; lean_object* v_fst_563_; lean_object* v_snd_564_; lean_object* v_fst_565_; lean_object* v_snd_566_; lean_object* v___x_567_; 
v_snd_561_ = lean_ctor_get(v___x_544_, 1);
lean_inc(v_snd_561_);
lean_dec_ref(v___x_544_);
v___x_562_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit(v_e_530_, v_offset_531_, v_f_532_, v_a_533_, v_a_534_, v_snd_561_);
v_fst_563_ = lean_ctor_get(v___x_562_, 0);
lean_inc(v_fst_563_);
v_snd_564_ = lean_ctor_get(v___x_562_, 1);
lean_inc(v_snd_564_);
lean_dec_ref(v___x_562_);
v_fst_565_ = lean_ctor_get(v_fst_563_, 0);
lean_inc(v_fst_565_);
v_snd_566_ = lean_ctor_get(v_fst_563_, 1);
lean_inc(v_snd_566_);
lean_dec(v_fst_563_);
v___x_567_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(v_key_537_, v_fst_565_, v_snd_566_, v_snd_564_);
return v___x_567_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___boxed(lean_object* v_e_568_, lean_object* v_offset_569_, lean_object* v_f_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_){
_start:
{
uint8_t v_a_boxed_574_; lean_object* v_res_575_; 
v_a_boxed_574_ = lean_unbox(v_a_572_);
v_res_575_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_e_568_, v_offset_569_, v_f_570_, v_a_571_, v_a_boxed_574_, v_a_573_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___boxed(lean_object* v_e_576_, lean_object* v_offset_577_, lean_object* v_fn_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_){
_start:
{
uint8_t v_a_boxed_582_; lean_object* v_res_583_; 
v_a_boxed_582_ = lean_unbox(v_a_580_);
v_res_583_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit(v_e_576_, v_offset_577_, v_fn_578_, v_a_579_, v_a_boxed_582_, v_a_581_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild_match__4_splitter___redArg(lean_object* v_____do__lift_584_, lean_object* v_h__1_585_, lean_object* v_h__2_586_){
_start:
{
if (lean_obj_tag(v_____do__lift_584_) == 1)
{
lean_object* v_val_587_; lean_object* v___x_588_; 
lean_dec(v_h__2_586_);
v_val_587_ = lean_ctor_get(v_____do__lift_584_, 0);
lean_inc(v_val_587_);
lean_dec_ref(v_____do__lift_584_);
v___x_588_ = lean_apply_1(v_h__1_585_, v_val_587_);
return v___x_588_;
}
else
{
lean_object* v___x_589_; 
lean_dec(v_h__1_585_);
v___x_589_ = lean_apply_2(v_h__2_586_, v_____do__lift_584_, lean_box(0));
return v___x_589_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild_match__4_splitter(lean_object* v_motive_590_, lean_object* v_____do__lift_591_, lean_object* v_h__1_592_, lean_object* v_h__2_593_){
_start:
{
if (lean_obj_tag(v_____do__lift_591_) == 1)
{
lean_object* v_val_594_; lean_object* v___x_595_; 
lean_dec(v_h__2_593_);
v_val_594_ = lean_ctor_get(v_____do__lift_591_, 0);
lean_inc(v_val_594_);
lean_dec_ref(v_____do__lift_591_);
v___x_595_ = lean_apply_1(v_h__1_592_, v_val_594_);
return v___x_595_;
}
else
{
lean_object* v___x_596_; 
lean_dec(v_h__1_592_);
v___x_596_ = lean_apply_2(v_h__2_593_, v_____do__lift_591_, lean_box(0));
return v___x_596_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild_match__1_splitter___redArg(lean_object* v_e_597_, lean_object* v_h__1_598_, lean_object* v_h__2_599_, lean_object* v_h__3_600_, lean_object* v_h__4_601_, lean_object* v_h__5_602_, lean_object* v_h__6_603_, lean_object* v_h__7_604_){
_start:
{
switch(lean_obj_tag(v_e_597_))
{
case 9:
{
lean_object* v_a_605_; lean_object* v___x_606_; 
lean_dec(v_h__7_604_);
lean_dec(v_h__6_603_);
lean_dec(v_h__5_602_);
lean_dec(v_h__4_601_);
lean_dec(v_h__3_600_);
lean_dec(v_h__2_599_);
v_a_605_ = lean_ctor_get(v_e_597_, 0);
lean_inc_ref(v_a_605_);
lean_dec_ref(v_e_597_);
v___x_606_ = lean_apply_1(v_h__1_598_, v_a_605_);
return v___x_606_;
}
case 2:
{
lean_object* v_mvarId_607_; lean_object* v___x_608_; 
lean_dec(v_h__7_604_);
lean_dec(v_h__6_603_);
lean_dec(v_h__5_602_);
lean_dec(v_h__4_601_);
lean_dec(v_h__3_600_);
lean_dec(v_h__1_598_);
v_mvarId_607_ = lean_ctor_get(v_e_597_, 0);
lean_inc(v_mvarId_607_);
lean_dec_ref(v_e_597_);
v___x_608_ = lean_apply_1(v_h__2_599_, v_mvarId_607_);
return v___x_608_;
}
case 0:
{
lean_object* v_deBruijnIndex_609_; lean_object* v___x_610_; 
lean_dec(v_h__7_604_);
lean_dec(v_h__6_603_);
lean_dec(v_h__5_602_);
lean_dec(v_h__4_601_);
lean_dec(v_h__2_599_);
lean_dec(v_h__1_598_);
v_deBruijnIndex_609_ = lean_ctor_get(v_e_597_, 0);
lean_inc(v_deBruijnIndex_609_);
lean_dec_ref(v_e_597_);
v___x_610_ = lean_apply_1(v_h__3_600_, v_deBruijnIndex_609_);
return v___x_610_;
}
case 1:
{
lean_object* v_fvarId_611_; lean_object* v___x_612_; 
lean_dec(v_h__7_604_);
lean_dec(v_h__6_603_);
lean_dec(v_h__5_602_);
lean_dec(v_h__3_600_);
lean_dec(v_h__2_599_);
lean_dec(v_h__1_598_);
v_fvarId_611_ = lean_ctor_get(v_e_597_, 0);
lean_inc(v_fvarId_611_);
lean_dec_ref(v_e_597_);
v___x_612_ = lean_apply_1(v_h__4_601_, v_fvarId_611_);
return v___x_612_;
}
case 4:
{
lean_object* v_declName_613_; lean_object* v_us_614_; lean_object* v___x_615_; 
lean_dec(v_h__7_604_);
lean_dec(v_h__6_603_);
lean_dec(v_h__4_601_);
lean_dec(v_h__3_600_);
lean_dec(v_h__2_599_);
lean_dec(v_h__1_598_);
v_declName_613_ = lean_ctor_get(v_e_597_, 0);
lean_inc(v_declName_613_);
v_us_614_ = lean_ctor_get(v_e_597_, 1);
lean_inc(v_us_614_);
lean_dec_ref(v_e_597_);
v___x_615_ = lean_apply_2(v_h__5_602_, v_declName_613_, v_us_614_);
return v___x_615_;
}
case 3:
{
lean_object* v_u_616_; lean_object* v___x_617_; 
lean_dec(v_h__7_604_);
lean_dec(v_h__5_602_);
lean_dec(v_h__4_601_);
lean_dec(v_h__3_600_);
lean_dec(v_h__2_599_);
lean_dec(v_h__1_598_);
v_u_616_ = lean_ctor_get(v_e_597_, 0);
lean_inc(v_u_616_);
lean_dec_ref(v_e_597_);
v___x_617_ = lean_apply_1(v_h__6_603_, v_u_616_);
return v___x_617_;
}
default: 
{
lean_object* v___x_618_; 
lean_dec(v_h__6_603_);
lean_dec(v_h__5_602_);
lean_dec(v_h__4_601_);
lean_dec(v_h__3_600_);
lean_dec(v_h__2_599_);
lean_dec(v_h__1_598_);
v___x_618_ = lean_apply_7(v_h__7_604_, v_e_597_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_618_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild_match__1_splitter(lean_object* v_motive_619_, lean_object* v_e_620_, lean_object* v_h__1_621_, lean_object* v_h__2_622_, lean_object* v_h__3_623_, lean_object* v_h__4_624_, lean_object* v_h__5_625_, lean_object* v_h__6_626_, lean_object* v_h__7_627_){
_start:
{
switch(lean_obj_tag(v_e_620_))
{
case 9:
{
lean_object* v_a_628_; lean_object* v___x_629_; 
lean_dec(v_h__7_627_);
lean_dec(v_h__6_626_);
lean_dec(v_h__5_625_);
lean_dec(v_h__4_624_);
lean_dec(v_h__3_623_);
lean_dec(v_h__2_622_);
v_a_628_ = lean_ctor_get(v_e_620_, 0);
lean_inc_ref(v_a_628_);
lean_dec_ref(v_e_620_);
v___x_629_ = lean_apply_1(v_h__1_621_, v_a_628_);
return v___x_629_;
}
case 2:
{
lean_object* v_mvarId_630_; lean_object* v___x_631_; 
lean_dec(v_h__7_627_);
lean_dec(v_h__6_626_);
lean_dec(v_h__5_625_);
lean_dec(v_h__4_624_);
lean_dec(v_h__3_623_);
lean_dec(v_h__1_621_);
v_mvarId_630_ = lean_ctor_get(v_e_620_, 0);
lean_inc(v_mvarId_630_);
lean_dec_ref(v_e_620_);
v___x_631_ = lean_apply_1(v_h__2_622_, v_mvarId_630_);
return v___x_631_;
}
case 0:
{
lean_object* v_deBruijnIndex_632_; lean_object* v___x_633_; 
lean_dec(v_h__7_627_);
lean_dec(v_h__6_626_);
lean_dec(v_h__5_625_);
lean_dec(v_h__4_624_);
lean_dec(v_h__2_622_);
lean_dec(v_h__1_621_);
v_deBruijnIndex_632_ = lean_ctor_get(v_e_620_, 0);
lean_inc(v_deBruijnIndex_632_);
lean_dec_ref(v_e_620_);
v___x_633_ = lean_apply_1(v_h__3_623_, v_deBruijnIndex_632_);
return v___x_633_;
}
case 1:
{
lean_object* v_fvarId_634_; lean_object* v___x_635_; 
lean_dec(v_h__7_627_);
lean_dec(v_h__6_626_);
lean_dec(v_h__5_625_);
lean_dec(v_h__3_623_);
lean_dec(v_h__2_622_);
lean_dec(v_h__1_621_);
v_fvarId_634_ = lean_ctor_get(v_e_620_, 0);
lean_inc(v_fvarId_634_);
lean_dec_ref(v_e_620_);
v___x_635_ = lean_apply_1(v_h__4_624_, v_fvarId_634_);
return v___x_635_;
}
case 4:
{
lean_object* v_declName_636_; lean_object* v_us_637_; lean_object* v___x_638_; 
lean_dec(v_h__7_627_);
lean_dec(v_h__6_626_);
lean_dec(v_h__4_624_);
lean_dec(v_h__3_623_);
lean_dec(v_h__2_622_);
lean_dec(v_h__1_621_);
v_declName_636_ = lean_ctor_get(v_e_620_, 0);
lean_inc(v_declName_636_);
v_us_637_ = lean_ctor_get(v_e_620_, 1);
lean_inc(v_us_637_);
lean_dec_ref(v_e_620_);
v___x_638_ = lean_apply_2(v_h__5_625_, v_declName_636_, v_us_637_);
return v___x_638_;
}
case 3:
{
lean_object* v_u_639_; lean_object* v___x_640_; 
lean_dec(v_h__7_627_);
lean_dec(v_h__5_625_);
lean_dec(v_h__4_624_);
lean_dec(v_h__3_623_);
lean_dec(v_h__2_622_);
lean_dec(v_h__1_621_);
v_u_639_ = lean_ctor_get(v_e_620_, 0);
lean_inc(v_u_639_);
lean_dec_ref(v_e_620_);
v___x_640_ = lean_apply_1(v_h__6_626_, v_u_639_);
return v___x_640_;
}
default: 
{
lean_object* v___x_641_; 
lean_dec(v_h__6_626_);
lean_dec(v_h__5_625_);
lean_dec(v_h__4_624_);
lean_dec(v_h__3_623_);
lean_dec(v_h__2_622_);
lean_dec(v_h__1_621_);
v___x_641_ = lean_apply_7(v_h__7_627_, v_e_620_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_641_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit_match__1_splitter___redArg(lean_object* v_e_642_, lean_object* v_h__1_643_, lean_object* v_h__2_644_, lean_object* v_h__3_645_, lean_object* v_h__4_646_, lean_object* v_h__5_647_, lean_object* v_h__6_648_, lean_object* v_h__7_649_, lean_object* v_h__8_650_, lean_object* v_h__9_651_, lean_object* v_h__10_652_, lean_object* v_h__11_653_, lean_object* v_h__12_654_){
_start:
{
switch(lean_obj_tag(v_e_642_))
{
case 0:
{
lean_object* v_deBruijnIndex_655_; lean_object* v___x_656_; 
lean_dec(v_h__12_654_);
lean_dec(v_h__11_653_);
lean_dec(v_h__10_652_);
lean_dec(v_h__9_651_);
lean_dec(v_h__8_650_);
lean_dec(v_h__7_649_);
lean_dec(v_h__6_648_);
lean_dec(v_h__5_647_);
lean_dec(v_h__4_646_);
lean_dec(v_h__2_644_);
lean_dec(v_h__1_643_);
v_deBruijnIndex_655_ = lean_ctor_get(v_e_642_, 0);
lean_inc(v_deBruijnIndex_655_);
lean_dec_ref(v_e_642_);
v___x_656_ = lean_apply_1(v_h__3_645_, v_deBruijnIndex_655_);
return v___x_656_;
}
case 1:
{
lean_object* v_fvarId_657_; lean_object* v___x_658_; 
lean_dec(v_h__12_654_);
lean_dec(v_h__11_653_);
lean_dec(v_h__10_652_);
lean_dec(v_h__9_651_);
lean_dec(v_h__8_650_);
lean_dec(v_h__7_649_);
lean_dec(v_h__6_648_);
lean_dec(v_h__5_647_);
lean_dec(v_h__3_645_);
lean_dec(v_h__2_644_);
lean_dec(v_h__1_643_);
v_fvarId_657_ = lean_ctor_get(v_e_642_, 0);
lean_inc(v_fvarId_657_);
lean_dec_ref(v_e_642_);
v___x_658_ = lean_apply_1(v_h__4_646_, v_fvarId_657_);
return v___x_658_;
}
case 2:
{
lean_object* v_mvarId_659_; lean_object* v___x_660_; 
lean_dec(v_h__12_654_);
lean_dec(v_h__11_653_);
lean_dec(v_h__10_652_);
lean_dec(v_h__9_651_);
lean_dec(v_h__8_650_);
lean_dec(v_h__7_649_);
lean_dec(v_h__6_648_);
lean_dec(v_h__5_647_);
lean_dec(v_h__4_646_);
lean_dec(v_h__3_645_);
lean_dec(v_h__1_643_);
v_mvarId_659_ = lean_ctor_get(v_e_642_, 0);
lean_inc(v_mvarId_659_);
lean_dec_ref(v_e_642_);
v___x_660_ = lean_apply_1(v_h__2_644_, v_mvarId_659_);
return v___x_660_;
}
case 3:
{
lean_object* v_u_661_; lean_object* v___x_662_; 
lean_dec(v_h__12_654_);
lean_dec(v_h__11_653_);
lean_dec(v_h__10_652_);
lean_dec(v_h__9_651_);
lean_dec(v_h__8_650_);
lean_dec(v_h__7_649_);
lean_dec(v_h__5_647_);
lean_dec(v_h__4_646_);
lean_dec(v_h__3_645_);
lean_dec(v_h__2_644_);
lean_dec(v_h__1_643_);
v_u_661_ = lean_ctor_get(v_e_642_, 0);
lean_inc(v_u_661_);
lean_dec_ref(v_e_642_);
v___x_662_ = lean_apply_1(v_h__6_648_, v_u_661_);
return v___x_662_;
}
case 4:
{
lean_object* v_declName_663_; lean_object* v_us_664_; lean_object* v___x_665_; 
lean_dec(v_h__12_654_);
lean_dec(v_h__11_653_);
lean_dec(v_h__10_652_);
lean_dec(v_h__9_651_);
lean_dec(v_h__8_650_);
lean_dec(v_h__7_649_);
lean_dec(v_h__6_648_);
lean_dec(v_h__4_646_);
lean_dec(v_h__3_645_);
lean_dec(v_h__2_644_);
lean_dec(v_h__1_643_);
v_declName_663_ = lean_ctor_get(v_e_642_, 0);
lean_inc(v_declName_663_);
v_us_664_ = lean_ctor_get(v_e_642_, 1);
lean_inc(v_us_664_);
lean_dec_ref(v_e_642_);
v___x_665_ = lean_apply_2(v_h__5_647_, v_declName_663_, v_us_664_);
return v___x_665_;
}
case 5:
{
lean_object* v_fn_666_; lean_object* v_arg_667_; lean_object* v___x_668_; 
lean_dec(v_h__12_654_);
lean_dec(v_h__11_653_);
lean_dec(v_h__10_652_);
lean_dec(v_h__9_651_);
lean_dec(v_h__8_650_);
lean_dec(v_h__6_648_);
lean_dec(v_h__5_647_);
lean_dec(v_h__4_646_);
lean_dec(v_h__3_645_);
lean_dec(v_h__2_644_);
lean_dec(v_h__1_643_);
v_fn_666_ = lean_ctor_get(v_e_642_, 0);
lean_inc_ref(v_fn_666_);
v_arg_667_ = lean_ctor_get(v_e_642_, 1);
lean_inc_ref(v_arg_667_);
lean_dec_ref(v_e_642_);
v___x_668_ = lean_apply_2(v_h__7_649_, v_fn_666_, v_arg_667_);
return v___x_668_;
}
case 6:
{
lean_object* v_binderName_669_; lean_object* v_binderType_670_; lean_object* v_body_671_; uint8_t v_binderInfo_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
lean_dec(v_h__12_654_);
lean_dec(v_h__10_652_);
lean_dec(v_h__9_651_);
lean_dec(v_h__8_650_);
lean_dec(v_h__7_649_);
lean_dec(v_h__6_648_);
lean_dec(v_h__5_647_);
lean_dec(v_h__4_646_);
lean_dec(v_h__3_645_);
lean_dec(v_h__2_644_);
lean_dec(v_h__1_643_);
v_binderName_669_ = lean_ctor_get(v_e_642_, 0);
lean_inc(v_binderName_669_);
v_binderType_670_ = lean_ctor_get(v_e_642_, 1);
lean_inc_ref(v_binderType_670_);
v_body_671_ = lean_ctor_get(v_e_642_, 2);
lean_inc_ref(v_body_671_);
v_binderInfo_672_ = lean_ctor_get_uint8(v_e_642_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_642_);
v___x_673_ = lean_box(v_binderInfo_672_);
v___x_674_ = lean_apply_4(v_h__11_653_, v_binderName_669_, v_binderType_670_, v_body_671_, v___x_673_);
return v___x_674_;
}
case 7:
{
lean_object* v_binderName_675_; lean_object* v_binderType_676_; lean_object* v_body_677_; uint8_t v_binderInfo_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
lean_dec(v_h__12_654_);
lean_dec(v_h__11_653_);
lean_dec(v_h__9_651_);
lean_dec(v_h__8_650_);
lean_dec(v_h__7_649_);
lean_dec(v_h__6_648_);
lean_dec(v_h__5_647_);
lean_dec(v_h__4_646_);
lean_dec(v_h__3_645_);
lean_dec(v_h__2_644_);
lean_dec(v_h__1_643_);
v_binderName_675_ = lean_ctor_get(v_e_642_, 0);
lean_inc(v_binderName_675_);
v_binderType_676_ = lean_ctor_get(v_e_642_, 1);
lean_inc_ref(v_binderType_676_);
v_body_677_ = lean_ctor_get(v_e_642_, 2);
lean_inc_ref(v_body_677_);
v_binderInfo_678_ = lean_ctor_get_uint8(v_e_642_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_642_);
v___x_679_ = lean_box(v_binderInfo_678_);
v___x_680_ = lean_apply_4(v_h__10_652_, v_binderName_675_, v_binderType_676_, v_body_677_, v___x_679_);
return v___x_680_;
}
case 8:
{
lean_object* v_declName_681_; lean_object* v_type_682_; lean_object* v_value_683_; lean_object* v_body_684_; uint8_t v_nondep_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
lean_dec(v_h__11_653_);
lean_dec(v_h__10_652_);
lean_dec(v_h__9_651_);
lean_dec(v_h__8_650_);
lean_dec(v_h__7_649_);
lean_dec(v_h__6_648_);
lean_dec(v_h__5_647_);
lean_dec(v_h__4_646_);
lean_dec(v_h__3_645_);
lean_dec(v_h__2_644_);
lean_dec(v_h__1_643_);
v_declName_681_ = lean_ctor_get(v_e_642_, 0);
lean_inc(v_declName_681_);
v_type_682_ = lean_ctor_get(v_e_642_, 1);
lean_inc_ref(v_type_682_);
v_value_683_ = lean_ctor_get(v_e_642_, 2);
lean_inc_ref(v_value_683_);
v_body_684_ = lean_ctor_get(v_e_642_, 3);
lean_inc_ref(v_body_684_);
v_nondep_685_ = lean_ctor_get_uint8(v_e_642_, sizeof(void*)*4 + 8);
lean_dec_ref(v_e_642_);
v___x_686_ = lean_box(v_nondep_685_);
v___x_687_ = lean_apply_5(v_h__12_654_, v_declName_681_, v_type_682_, v_value_683_, v_body_684_, v___x_686_);
return v___x_687_;
}
case 9:
{
lean_object* v_a_688_; lean_object* v___x_689_; 
lean_dec(v_h__12_654_);
lean_dec(v_h__11_653_);
lean_dec(v_h__10_652_);
lean_dec(v_h__9_651_);
lean_dec(v_h__8_650_);
lean_dec(v_h__7_649_);
lean_dec(v_h__6_648_);
lean_dec(v_h__5_647_);
lean_dec(v_h__4_646_);
lean_dec(v_h__3_645_);
lean_dec(v_h__2_644_);
v_a_688_ = lean_ctor_get(v_e_642_, 0);
lean_inc_ref(v_a_688_);
lean_dec_ref(v_e_642_);
v___x_689_ = lean_apply_1(v_h__1_643_, v_a_688_);
return v___x_689_;
}
case 10:
{
lean_object* v_data_690_; lean_object* v_expr_691_; lean_object* v___x_692_; 
lean_dec(v_h__12_654_);
lean_dec(v_h__11_653_);
lean_dec(v_h__10_652_);
lean_dec(v_h__9_651_);
lean_dec(v_h__7_649_);
lean_dec(v_h__6_648_);
lean_dec(v_h__5_647_);
lean_dec(v_h__4_646_);
lean_dec(v_h__3_645_);
lean_dec(v_h__2_644_);
lean_dec(v_h__1_643_);
v_data_690_ = lean_ctor_get(v_e_642_, 0);
lean_inc(v_data_690_);
v_expr_691_ = lean_ctor_get(v_e_642_, 1);
lean_inc_ref(v_expr_691_);
lean_dec_ref(v_e_642_);
v___x_692_ = lean_apply_2(v_h__8_650_, v_data_690_, v_expr_691_);
return v___x_692_;
}
default: 
{
lean_object* v_typeName_693_; lean_object* v_idx_694_; lean_object* v_struct_695_; lean_object* v___x_696_; 
lean_dec(v_h__12_654_);
lean_dec(v_h__11_653_);
lean_dec(v_h__10_652_);
lean_dec(v_h__8_650_);
lean_dec(v_h__7_649_);
lean_dec(v_h__6_648_);
lean_dec(v_h__5_647_);
lean_dec(v_h__4_646_);
lean_dec(v_h__3_645_);
lean_dec(v_h__2_644_);
lean_dec(v_h__1_643_);
v_typeName_693_ = lean_ctor_get(v_e_642_, 0);
lean_inc(v_typeName_693_);
v_idx_694_ = lean_ctor_get(v_e_642_, 1);
lean_inc(v_idx_694_);
v_struct_695_ = lean_ctor_get(v_e_642_, 2);
lean_inc_ref(v_struct_695_);
lean_dec_ref(v_e_642_);
v___x_696_ = lean_apply_3(v_h__9_651_, v_typeName_693_, v_idx_694_, v_struct_695_);
return v___x_696_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit_match__1_splitter(lean_object* v_motive_697_, lean_object* v_e_698_, lean_object* v_h__1_699_, lean_object* v_h__2_700_, lean_object* v_h__3_701_, lean_object* v_h__4_702_, lean_object* v_h__5_703_, lean_object* v_h__6_704_, lean_object* v_h__7_705_, lean_object* v_h__8_706_, lean_object* v_h__9_707_, lean_object* v_h__10_708_, lean_object* v_h__11_709_, lean_object* v_h__12_710_){
_start:
{
switch(lean_obj_tag(v_e_698_))
{
case 0:
{
lean_object* v_deBruijnIndex_711_; lean_object* v___x_712_; 
lean_dec(v_h__12_710_);
lean_dec(v_h__11_709_);
lean_dec(v_h__10_708_);
lean_dec(v_h__9_707_);
lean_dec(v_h__8_706_);
lean_dec(v_h__7_705_);
lean_dec(v_h__6_704_);
lean_dec(v_h__5_703_);
lean_dec(v_h__4_702_);
lean_dec(v_h__2_700_);
lean_dec(v_h__1_699_);
v_deBruijnIndex_711_ = lean_ctor_get(v_e_698_, 0);
lean_inc(v_deBruijnIndex_711_);
lean_dec_ref(v_e_698_);
v___x_712_ = lean_apply_1(v_h__3_701_, v_deBruijnIndex_711_);
return v___x_712_;
}
case 1:
{
lean_object* v_fvarId_713_; lean_object* v___x_714_; 
lean_dec(v_h__12_710_);
lean_dec(v_h__11_709_);
lean_dec(v_h__10_708_);
lean_dec(v_h__9_707_);
lean_dec(v_h__8_706_);
lean_dec(v_h__7_705_);
lean_dec(v_h__6_704_);
lean_dec(v_h__5_703_);
lean_dec(v_h__3_701_);
lean_dec(v_h__2_700_);
lean_dec(v_h__1_699_);
v_fvarId_713_ = lean_ctor_get(v_e_698_, 0);
lean_inc(v_fvarId_713_);
lean_dec_ref(v_e_698_);
v___x_714_ = lean_apply_1(v_h__4_702_, v_fvarId_713_);
return v___x_714_;
}
case 2:
{
lean_object* v_mvarId_715_; lean_object* v___x_716_; 
lean_dec(v_h__12_710_);
lean_dec(v_h__11_709_);
lean_dec(v_h__10_708_);
lean_dec(v_h__9_707_);
lean_dec(v_h__8_706_);
lean_dec(v_h__7_705_);
lean_dec(v_h__6_704_);
lean_dec(v_h__5_703_);
lean_dec(v_h__4_702_);
lean_dec(v_h__3_701_);
lean_dec(v_h__1_699_);
v_mvarId_715_ = lean_ctor_get(v_e_698_, 0);
lean_inc(v_mvarId_715_);
lean_dec_ref(v_e_698_);
v___x_716_ = lean_apply_1(v_h__2_700_, v_mvarId_715_);
return v___x_716_;
}
case 3:
{
lean_object* v_u_717_; lean_object* v___x_718_; 
lean_dec(v_h__12_710_);
lean_dec(v_h__11_709_);
lean_dec(v_h__10_708_);
lean_dec(v_h__9_707_);
lean_dec(v_h__8_706_);
lean_dec(v_h__7_705_);
lean_dec(v_h__5_703_);
lean_dec(v_h__4_702_);
lean_dec(v_h__3_701_);
lean_dec(v_h__2_700_);
lean_dec(v_h__1_699_);
v_u_717_ = lean_ctor_get(v_e_698_, 0);
lean_inc(v_u_717_);
lean_dec_ref(v_e_698_);
v___x_718_ = lean_apply_1(v_h__6_704_, v_u_717_);
return v___x_718_;
}
case 4:
{
lean_object* v_declName_719_; lean_object* v_us_720_; lean_object* v___x_721_; 
lean_dec(v_h__12_710_);
lean_dec(v_h__11_709_);
lean_dec(v_h__10_708_);
lean_dec(v_h__9_707_);
lean_dec(v_h__8_706_);
lean_dec(v_h__7_705_);
lean_dec(v_h__6_704_);
lean_dec(v_h__4_702_);
lean_dec(v_h__3_701_);
lean_dec(v_h__2_700_);
lean_dec(v_h__1_699_);
v_declName_719_ = lean_ctor_get(v_e_698_, 0);
lean_inc(v_declName_719_);
v_us_720_ = lean_ctor_get(v_e_698_, 1);
lean_inc(v_us_720_);
lean_dec_ref(v_e_698_);
v___x_721_ = lean_apply_2(v_h__5_703_, v_declName_719_, v_us_720_);
return v___x_721_;
}
case 5:
{
lean_object* v_fn_722_; lean_object* v_arg_723_; lean_object* v___x_724_; 
lean_dec(v_h__12_710_);
lean_dec(v_h__11_709_);
lean_dec(v_h__10_708_);
lean_dec(v_h__9_707_);
lean_dec(v_h__8_706_);
lean_dec(v_h__6_704_);
lean_dec(v_h__5_703_);
lean_dec(v_h__4_702_);
lean_dec(v_h__3_701_);
lean_dec(v_h__2_700_);
lean_dec(v_h__1_699_);
v_fn_722_ = lean_ctor_get(v_e_698_, 0);
lean_inc_ref(v_fn_722_);
v_arg_723_ = lean_ctor_get(v_e_698_, 1);
lean_inc_ref(v_arg_723_);
lean_dec_ref(v_e_698_);
v___x_724_ = lean_apply_2(v_h__7_705_, v_fn_722_, v_arg_723_);
return v___x_724_;
}
case 6:
{
lean_object* v_binderName_725_; lean_object* v_binderType_726_; lean_object* v_body_727_; uint8_t v_binderInfo_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
lean_dec(v_h__12_710_);
lean_dec(v_h__10_708_);
lean_dec(v_h__9_707_);
lean_dec(v_h__8_706_);
lean_dec(v_h__7_705_);
lean_dec(v_h__6_704_);
lean_dec(v_h__5_703_);
lean_dec(v_h__4_702_);
lean_dec(v_h__3_701_);
lean_dec(v_h__2_700_);
lean_dec(v_h__1_699_);
v_binderName_725_ = lean_ctor_get(v_e_698_, 0);
lean_inc(v_binderName_725_);
v_binderType_726_ = lean_ctor_get(v_e_698_, 1);
lean_inc_ref(v_binderType_726_);
v_body_727_ = lean_ctor_get(v_e_698_, 2);
lean_inc_ref(v_body_727_);
v_binderInfo_728_ = lean_ctor_get_uint8(v_e_698_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_698_);
v___x_729_ = lean_box(v_binderInfo_728_);
v___x_730_ = lean_apply_4(v_h__11_709_, v_binderName_725_, v_binderType_726_, v_body_727_, v___x_729_);
return v___x_730_;
}
case 7:
{
lean_object* v_binderName_731_; lean_object* v_binderType_732_; lean_object* v_body_733_; uint8_t v_binderInfo_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
lean_dec(v_h__12_710_);
lean_dec(v_h__11_709_);
lean_dec(v_h__9_707_);
lean_dec(v_h__8_706_);
lean_dec(v_h__7_705_);
lean_dec(v_h__6_704_);
lean_dec(v_h__5_703_);
lean_dec(v_h__4_702_);
lean_dec(v_h__3_701_);
lean_dec(v_h__2_700_);
lean_dec(v_h__1_699_);
v_binderName_731_ = lean_ctor_get(v_e_698_, 0);
lean_inc(v_binderName_731_);
v_binderType_732_ = lean_ctor_get(v_e_698_, 1);
lean_inc_ref(v_binderType_732_);
v_body_733_ = lean_ctor_get(v_e_698_, 2);
lean_inc_ref(v_body_733_);
v_binderInfo_734_ = lean_ctor_get_uint8(v_e_698_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_698_);
v___x_735_ = lean_box(v_binderInfo_734_);
v___x_736_ = lean_apply_4(v_h__10_708_, v_binderName_731_, v_binderType_732_, v_body_733_, v___x_735_);
return v___x_736_;
}
case 8:
{
lean_object* v_declName_737_; lean_object* v_type_738_; lean_object* v_value_739_; lean_object* v_body_740_; uint8_t v_nondep_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
lean_dec(v_h__11_709_);
lean_dec(v_h__10_708_);
lean_dec(v_h__9_707_);
lean_dec(v_h__8_706_);
lean_dec(v_h__7_705_);
lean_dec(v_h__6_704_);
lean_dec(v_h__5_703_);
lean_dec(v_h__4_702_);
lean_dec(v_h__3_701_);
lean_dec(v_h__2_700_);
lean_dec(v_h__1_699_);
v_declName_737_ = lean_ctor_get(v_e_698_, 0);
lean_inc(v_declName_737_);
v_type_738_ = lean_ctor_get(v_e_698_, 1);
lean_inc_ref(v_type_738_);
v_value_739_ = lean_ctor_get(v_e_698_, 2);
lean_inc_ref(v_value_739_);
v_body_740_ = lean_ctor_get(v_e_698_, 3);
lean_inc_ref(v_body_740_);
v_nondep_741_ = lean_ctor_get_uint8(v_e_698_, sizeof(void*)*4 + 8);
lean_dec_ref(v_e_698_);
v___x_742_ = lean_box(v_nondep_741_);
v___x_743_ = lean_apply_5(v_h__12_710_, v_declName_737_, v_type_738_, v_value_739_, v_body_740_, v___x_742_);
return v___x_743_;
}
case 9:
{
lean_object* v_a_744_; lean_object* v___x_745_; 
lean_dec(v_h__12_710_);
lean_dec(v_h__11_709_);
lean_dec(v_h__10_708_);
lean_dec(v_h__9_707_);
lean_dec(v_h__8_706_);
lean_dec(v_h__7_705_);
lean_dec(v_h__6_704_);
lean_dec(v_h__5_703_);
lean_dec(v_h__4_702_);
lean_dec(v_h__3_701_);
lean_dec(v_h__2_700_);
v_a_744_ = lean_ctor_get(v_e_698_, 0);
lean_inc_ref(v_a_744_);
lean_dec_ref(v_e_698_);
v___x_745_ = lean_apply_1(v_h__1_699_, v_a_744_);
return v___x_745_;
}
case 10:
{
lean_object* v_data_746_; lean_object* v_expr_747_; lean_object* v___x_748_; 
lean_dec(v_h__12_710_);
lean_dec(v_h__11_709_);
lean_dec(v_h__10_708_);
lean_dec(v_h__9_707_);
lean_dec(v_h__7_705_);
lean_dec(v_h__6_704_);
lean_dec(v_h__5_703_);
lean_dec(v_h__4_702_);
lean_dec(v_h__3_701_);
lean_dec(v_h__2_700_);
lean_dec(v_h__1_699_);
v_data_746_ = lean_ctor_get(v_e_698_, 0);
lean_inc(v_data_746_);
v_expr_747_ = lean_ctor_get(v_e_698_, 1);
lean_inc_ref(v_expr_747_);
lean_dec_ref(v_e_698_);
v___x_748_ = lean_apply_2(v_h__8_706_, v_data_746_, v_expr_747_);
return v___x_748_;
}
default: 
{
lean_object* v_typeName_749_; lean_object* v_idx_750_; lean_object* v_struct_751_; lean_object* v___x_752_; 
lean_dec(v_h__12_710_);
lean_dec(v_h__11_709_);
lean_dec(v_h__10_708_);
lean_dec(v_h__8_706_);
lean_dec(v_h__7_705_);
lean_dec(v_h__6_704_);
lean_dec(v_h__5_703_);
lean_dec(v_h__4_702_);
lean_dec(v_h__3_701_);
lean_dec(v_h__2_700_);
lean_dec(v_h__1_699_);
v_typeName_749_ = lean_ctor_get(v_e_698_, 0);
lean_inc(v_typeName_749_);
v_idx_750_ = lean_ctor_get(v_e_698_, 1);
lean_inc(v_idx_750_);
v_struct_751_ = lean_ctor_get(v_e_698_, 2);
lean_inc_ref(v_struct_751_);
lean_dec_ref(v_e_698_);
v___x_752_ = lean_apply_3(v_h__9_707_, v_typeName_749_, v_idx_750_, v_struct_751_);
return v___x_752_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Sym_replaceS_x27___closed__0(void){
_start:
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_753_ = lean_box(0);
v___x_754_ = lean_unsigned_to_nat(16u);
v___x_755_ = lean_mk_array(v___x_754_, v___x_753_);
return v___x_755_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_replaceS_x27___closed__1(void){
_start:
{
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_756_ = lean_obj_once(&l_Lean_Meta_Sym_replaceS_x27___closed__0, &l_Lean_Meta_Sym_replaceS_x27___closed__0_once, _init_l_Lean_Meta_Sym_replaceS_x27___closed__0);
v___x_757_ = lean_unsigned_to_nat(0u);
v___x_758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_758_, 0, v___x_757_);
lean_ctor_set(v___x_758_, 1, v___x_756_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_replaceS_x27(lean_object* v_e_759_, lean_object* v_f_760_, uint8_t v_a_761_, lean_object* v_a_762_){
_start:
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v_fst_766_; 
v___x_763_ = lean_unsigned_to_nat(0u);
v___x_764_ = lean_box(v_a_761_);
lean_inc_ref(v_f_760_);
lean_inc_ref(v_e_759_);
v___x_765_ = lean_apply_4(v_f_760_, v_e_759_, v___x_763_, v___x_764_, v_a_762_);
v_fst_766_ = lean_ctor_get(v___x_765_, 0);
lean_inc(v_fst_766_);
if (lean_obj_tag(v_fst_766_) == 1)
{
lean_object* v_snd_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_775_; 
lean_dec_ref(v_f_760_);
lean_dec_ref(v_e_759_);
v_snd_767_ = lean_ctor_get(v___x_765_, 1);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_775_ == 0)
{
lean_object* v_unused_776_; 
v_unused_776_ = lean_ctor_get(v___x_765_, 0);
lean_dec(v_unused_776_);
v___x_769_ = v___x_765_;
v_isShared_770_ = v_isSharedCheck_775_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_snd_767_);
lean_dec(v___x_765_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_775_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v_val_771_; lean_object* v___x_773_; 
v_val_771_ = lean_ctor_get(v_fst_766_, 0);
lean_inc(v_val_771_);
lean_dec_ref(v_fst_766_);
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 0, v_val_771_);
v___x_773_ = v___x_769_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_val_771_);
lean_ctor_set(v_reuseFailAlloc_774_, 1, v_snd_767_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
else
{
lean_dec(v_fst_766_);
switch(lean_obj_tag(v_e_759_))
{
case 9:
{
lean_object* v_snd_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_784_; 
lean_dec_ref(v_f_760_);
v_snd_777_ = lean_ctor_get(v___x_765_, 1);
v_isSharedCheck_784_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_784_ == 0)
{
lean_object* v_unused_785_; 
v_unused_785_ = lean_ctor_get(v___x_765_, 0);
lean_dec(v_unused_785_);
v___x_779_ = v___x_765_;
v_isShared_780_ = v_isSharedCheck_784_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_snd_777_);
lean_dec(v___x_765_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_784_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_782_; 
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 0, v_e_759_);
v___x_782_ = v___x_779_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v_e_759_);
lean_ctor_set(v_reuseFailAlloc_783_, 1, v_snd_777_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
}
case 2:
{
lean_object* v_snd_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_793_; 
lean_dec_ref(v_f_760_);
v_snd_786_ = lean_ctor_get(v___x_765_, 1);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_793_ == 0)
{
lean_object* v_unused_794_; 
v_unused_794_ = lean_ctor_get(v___x_765_, 0);
lean_dec(v_unused_794_);
v___x_788_ = v___x_765_;
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_snd_786_);
lean_dec(v___x_765_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_791_; 
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 0, v_e_759_);
v___x_791_ = v___x_788_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_e_759_);
lean_ctor_set(v_reuseFailAlloc_792_, 1, v_snd_786_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
case 0:
{
lean_object* v_snd_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_802_; 
lean_dec_ref(v_f_760_);
v_snd_795_ = lean_ctor_get(v___x_765_, 1);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_802_ == 0)
{
lean_object* v_unused_803_; 
v_unused_803_ = lean_ctor_get(v___x_765_, 0);
lean_dec(v_unused_803_);
v___x_797_ = v___x_765_;
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_snd_795_);
lean_dec(v___x_765_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_800_; 
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 0, v_e_759_);
v___x_800_ = v___x_797_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_e_759_);
lean_ctor_set(v_reuseFailAlloc_801_, 1, v_snd_795_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
case 1:
{
lean_object* v_snd_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_811_; 
lean_dec_ref(v_f_760_);
v_snd_804_ = lean_ctor_get(v___x_765_, 1);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_811_ == 0)
{
lean_object* v_unused_812_; 
v_unused_812_ = lean_ctor_get(v___x_765_, 0);
lean_dec(v_unused_812_);
v___x_806_ = v___x_765_;
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_snd_804_);
lean_dec(v___x_765_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_809_; 
if (v_isShared_807_ == 0)
{
lean_ctor_set(v___x_806_, 0, v_e_759_);
v___x_809_ = v___x_806_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_e_759_);
lean_ctor_set(v_reuseFailAlloc_810_, 1, v_snd_804_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
}
case 4:
{
lean_object* v_snd_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_820_; 
lean_dec_ref(v_f_760_);
v_snd_813_ = lean_ctor_get(v___x_765_, 1);
v_isSharedCheck_820_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_820_ == 0)
{
lean_object* v_unused_821_; 
v_unused_821_ = lean_ctor_get(v___x_765_, 0);
lean_dec(v_unused_821_);
v___x_815_ = v___x_765_;
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_snd_813_);
lean_dec(v___x_765_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_818_; 
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 0, v_e_759_);
v___x_818_ = v___x_815_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_e_759_);
lean_ctor_set(v_reuseFailAlloc_819_, 1, v_snd_813_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
}
case 3:
{
lean_object* v_snd_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_829_; 
lean_dec_ref(v_f_760_);
v_snd_822_ = lean_ctor_get(v___x_765_, 1);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_829_ == 0)
{
lean_object* v_unused_830_; 
v_unused_830_ = lean_ctor_get(v___x_765_, 0);
lean_dec(v_unused_830_);
v___x_824_ = v___x_765_;
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_snd_822_);
lean_dec(v___x_765_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_827_; 
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 0, v_e_759_);
v___x_827_ = v___x_824_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_e_759_);
lean_ctor_set(v_reuseFailAlloc_828_, 1, v_snd_822_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
}
default: 
{
lean_object* v_snd_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v_fst_834_; lean_object* v_snd_835_; lean_object* v_fst_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_843_; 
v_snd_831_ = lean_ctor_get(v___x_765_, 1);
lean_inc(v_snd_831_);
lean_dec_ref(v___x_765_);
v___x_832_ = lean_obj_once(&l_Lean_Meta_Sym_replaceS_x27___closed__1, &l_Lean_Meta_Sym_replaceS_x27___closed__1_once, _init_l_Lean_Meta_Sym_replaceS_x27___closed__1);
v___x_833_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit(v_e_759_, v___x_763_, v_f_760_, v___x_832_, v_a_761_, v_snd_831_);
v_fst_834_ = lean_ctor_get(v___x_833_, 0);
lean_inc(v_fst_834_);
v_snd_835_ = lean_ctor_get(v___x_833_, 1);
lean_inc(v_snd_835_);
lean_dec_ref(v___x_833_);
v_fst_836_ = lean_ctor_get(v_fst_834_, 0);
v_isSharedCheck_843_ = !lean_is_exclusive(v_fst_834_);
if (v_isSharedCheck_843_ == 0)
{
lean_object* v_unused_844_; 
v_unused_844_ = lean_ctor_get(v_fst_834_, 1);
lean_dec(v_unused_844_);
v___x_838_ = v_fst_834_;
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_fst_836_);
lean_dec(v_fst_834_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_841_; 
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 1, v_snd_835_);
v___x_841_ = v___x_838_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_fst_836_);
lean_ctor_set(v_reuseFailAlloc_842_, 1, v_snd_835_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_replaceS_x27___boxed(lean_object* v_e_845_, lean_object* v_f_846_, lean_object* v_a_847_, lean_object* v_a_848_){
_start:
{
uint8_t v_a_boxed_849_; lean_object* v_res_850_; 
v_a_boxed_849_ = lean_unbox(v_a_847_);
v_res_850_ = l_Lean_Meta_Sym_replaceS_x27(v_e_845_, v_f_846_, v_a_boxed_849_, v_a_848_);
return v_res_850_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_replaceS___redArg___closed__2(void){
_start:
{
lean_object* v___f_853_; lean_object* v___f_854_; lean_object* v___x_855_; 
v___f_853_ = ((lean_object*)(l_Lean_Meta_Sym_replaceS___redArg___closed__1));
v___f_854_ = ((lean_object*)(l_Lean_Meta_Sym_replaceS___redArg___closed__0));
v___x_855_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___f_854_, v___f_853_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_replaceS___redArg(lean_object* v_e_856_, lean_object* v_f_857_, lean_object* v_a_858_){
_start:
{
lean_object* v___x_860_; lean_object* v_share_861_; lean_object* v_maxFVar_862_; lean_object* v_proofInstInfo_863_; lean_object* v_inferType_864_; lean_object* v_getLevel_865_; lean_object* v_congrInfo_866_; lean_object* v_defEqI_867_; uint8_t v_debug_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_918_; 
v___x_860_ = lean_st_ref_take(v_a_858_);
v_share_861_ = lean_ctor_get(v___x_860_, 0);
v_maxFVar_862_ = lean_ctor_get(v___x_860_, 1);
v_proofInstInfo_863_ = lean_ctor_get(v___x_860_, 2);
v_inferType_864_ = lean_ctor_get(v___x_860_, 3);
v_getLevel_865_ = lean_ctor_get(v___x_860_, 4);
v_congrInfo_866_ = lean_ctor_get(v___x_860_, 5);
v_defEqI_867_ = lean_ctor_get(v___x_860_, 6);
v_debug_868_ = lean_ctor_get_uint8(v___x_860_, sizeof(void*)*7);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_918_ == 0)
{
v___x_870_ = v___x_860_;
v_isShared_871_ = v_isSharedCheck_918_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_defEqI_867_);
lean_inc(v_congrInfo_866_);
lean_inc(v_getLevel_865_);
lean_inc(v_inferType_864_);
lean_inc(v_proofInstInfo_863_);
lean_inc(v_maxFVar_862_);
lean_inc(v_share_861_);
lean_dec(v___x_860_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_918_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_872_; lean_object* v___x_874_; 
v___x_872_ = lean_obj_once(&l_Lean_Meta_Sym_replaceS___redArg___closed__2, &l_Lean_Meta_Sym_replaceS___redArg___closed__2_once, _init_l_Lean_Meta_Sym_replaceS___redArg___closed__2);
if (v_isShared_871_ == 0)
{
lean_ctor_set(v___x_870_, 0, v___x_872_);
v___x_874_ = v___x_870_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v___x_872_);
lean_ctor_set(v_reuseFailAlloc_917_, 1, v_maxFVar_862_);
lean_ctor_set(v_reuseFailAlloc_917_, 2, v_proofInstInfo_863_);
lean_ctor_set(v_reuseFailAlloc_917_, 3, v_inferType_864_);
lean_ctor_set(v_reuseFailAlloc_917_, 4, v_getLevel_865_);
lean_ctor_set(v_reuseFailAlloc_917_, 5, v_congrInfo_866_);
lean_ctor_set(v_reuseFailAlloc_917_, 6, v_defEqI_867_);
lean_ctor_set_uint8(v_reuseFailAlloc_917_, sizeof(void*)*7, v_debug_868_);
v___x_874_ = v_reuseFailAlloc_917_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v_fst_878_; lean_object* v_snd_879_; uint8_t v_debug_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v_fst_902_; 
v___x_875_ = lean_st_ref_set(v_a_858_, v___x_874_);
v___x_876_ = lean_st_ref_get(v_a_858_);
v_debug_898_ = lean_ctor_get_uint8(v___x_876_, sizeof(void*)*7);
lean_dec(v___x_876_);
v___x_899_ = lean_unsigned_to_nat(0u);
v___x_900_ = lean_box(v_debug_898_);
lean_inc_ref(v_f_857_);
lean_inc_ref(v_e_856_);
v___x_901_ = lean_apply_4(v_f_857_, v_e_856_, v___x_899_, v___x_900_, v_share_861_);
v_fst_902_ = lean_ctor_get(v___x_901_, 0);
lean_inc(v_fst_902_);
if (lean_obj_tag(v_fst_902_) == 1)
{
lean_object* v_snd_903_; lean_object* v_val_904_; 
lean_dec_ref(v_f_857_);
lean_dec_ref(v_e_856_);
v_snd_903_ = lean_ctor_get(v___x_901_, 1);
lean_inc(v_snd_903_);
lean_dec_ref(v___x_901_);
v_val_904_ = lean_ctor_get(v_fst_902_, 0);
lean_inc(v_val_904_);
lean_dec_ref(v_fst_902_);
v_fst_878_ = v_val_904_;
v_snd_879_ = v_snd_903_;
goto v___jp_877_;
}
else
{
lean_dec(v_fst_902_);
switch(lean_obj_tag(v_e_856_))
{
case 9:
{
lean_object* v_snd_905_; 
lean_dec_ref(v_f_857_);
v_snd_905_ = lean_ctor_get(v___x_901_, 1);
lean_inc(v_snd_905_);
lean_dec_ref(v___x_901_);
v_fst_878_ = v_e_856_;
v_snd_879_ = v_snd_905_;
goto v___jp_877_;
}
case 2:
{
lean_object* v_snd_906_; 
lean_dec_ref(v_f_857_);
v_snd_906_ = lean_ctor_get(v___x_901_, 1);
lean_inc(v_snd_906_);
lean_dec_ref(v___x_901_);
v_fst_878_ = v_e_856_;
v_snd_879_ = v_snd_906_;
goto v___jp_877_;
}
case 0:
{
lean_object* v_snd_907_; 
lean_dec_ref(v_f_857_);
v_snd_907_ = lean_ctor_get(v___x_901_, 1);
lean_inc(v_snd_907_);
lean_dec_ref(v___x_901_);
v_fst_878_ = v_e_856_;
v_snd_879_ = v_snd_907_;
goto v___jp_877_;
}
case 1:
{
lean_object* v_snd_908_; 
lean_dec_ref(v_f_857_);
v_snd_908_ = lean_ctor_get(v___x_901_, 1);
lean_inc(v_snd_908_);
lean_dec_ref(v___x_901_);
v_fst_878_ = v_e_856_;
v_snd_879_ = v_snd_908_;
goto v___jp_877_;
}
case 4:
{
lean_object* v_snd_909_; 
lean_dec_ref(v_f_857_);
v_snd_909_ = lean_ctor_get(v___x_901_, 1);
lean_inc(v_snd_909_);
lean_dec_ref(v___x_901_);
v_fst_878_ = v_e_856_;
v_snd_879_ = v_snd_909_;
goto v___jp_877_;
}
case 3:
{
lean_object* v_snd_910_; 
lean_dec_ref(v_f_857_);
v_snd_910_ = lean_ctor_get(v___x_901_, 1);
lean_inc(v_snd_910_);
lean_dec_ref(v___x_901_);
v_fst_878_ = v_e_856_;
v_snd_879_ = v_snd_910_;
goto v___jp_877_;
}
default: 
{
lean_object* v_snd_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v_fst_914_; lean_object* v_snd_915_; lean_object* v_fst_916_; 
v_snd_911_ = lean_ctor_get(v___x_901_, 1);
lean_inc(v_snd_911_);
lean_dec_ref(v___x_901_);
v___x_912_ = lean_obj_once(&l_Lean_Meta_Sym_replaceS_x27___closed__1, &l_Lean_Meta_Sym_replaceS_x27___closed__1_once, _init_l_Lean_Meta_Sym_replaceS_x27___closed__1);
v___x_913_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit(v_e_856_, v___x_899_, v_f_857_, v___x_912_, v_debug_898_, v_snd_911_);
v_fst_914_ = lean_ctor_get(v___x_913_, 0);
lean_inc(v_fst_914_);
v_snd_915_ = lean_ctor_get(v___x_913_, 1);
lean_inc(v_snd_915_);
lean_dec_ref(v___x_913_);
v_fst_916_ = lean_ctor_get(v_fst_914_, 0);
lean_inc(v_fst_916_);
lean_dec(v_fst_914_);
v_fst_878_ = v_fst_916_;
v_snd_879_ = v_snd_915_;
goto v___jp_877_;
}
}
}
v___jp_877_:
{
lean_object* v___x_880_; lean_object* v_maxFVar_881_; lean_object* v_proofInstInfo_882_; lean_object* v_inferType_883_; lean_object* v_getLevel_884_; lean_object* v_congrInfo_885_; lean_object* v_defEqI_886_; uint8_t v_debug_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_896_; 
v___x_880_ = lean_st_ref_take(v_a_858_);
v_maxFVar_881_ = lean_ctor_get(v___x_880_, 1);
v_proofInstInfo_882_ = lean_ctor_get(v___x_880_, 2);
v_inferType_883_ = lean_ctor_get(v___x_880_, 3);
v_getLevel_884_ = lean_ctor_get(v___x_880_, 4);
v_congrInfo_885_ = lean_ctor_get(v___x_880_, 5);
v_defEqI_886_ = lean_ctor_get(v___x_880_, 6);
v_debug_887_ = lean_ctor_get_uint8(v___x_880_, sizeof(void*)*7);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_896_ == 0)
{
lean_object* v_unused_897_; 
v_unused_897_ = lean_ctor_get(v___x_880_, 0);
lean_dec(v_unused_897_);
v___x_889_ = v___x_880_;
v_isShared_890_ = v_isSharedCheck_896_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_defEqI_886_);
lean_inc(v_congrInfo_885_);
lean_inc(v_getLevel_884_);
lean_inc(v_inferType_883_);
lean_inc(v_proofInstInfo_882_);
lean_inc(v_maxFVar_881_);
lean_dec(v___x_880_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_896_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_892_; 
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 0, v_snd_879_);
v___x_892_ = v___x_889_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_snd_879_);
lean_ctor_set(v_reuseFailAlloc_895_, 1, v_maxFVar_881_);
lean_ctor_set(v_reuseFailAlloc_895_, 2, v_proofInstInfo_882_);
lean_ctor_set(v_reuseFailAlloc_895_, 3, v_inferType_883_);
lean_ctor_set(v_reuseFailAlloc_895_, 4, v_getLevel_884_);
lean_ctor_set(v_reuseFailAlloc_895_, 5, v_congrInfo_885_);
lean_ctor_set(v_reuseFailAlloc_895_, 6, v_defEqI_886_);
lean_ctor_set_uint8(v_reuseFailAlloc_895_, sizeof(void*)*7, v_debug_887_);
v___x_892_ = v_reuseFailAlloc_895_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_893_ = lean_st_ref_set(v_a_858_, v___x_892_);
v___x_894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_894_, 0, v_fst_878_);
return v___x_894_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_replaceS___redArg___boxed(lean_object* v_e_919_, lean_object* v_f_920_, lean_object* v_a_921_, lean_object* v_a_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_Lean_Meta_Sym_replaceS___redArg(v_e_919_, v_f_920_, v_a_921_);
lean_dec(v_a_921_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_replaceS(lean_object* v_e_924_, lean_object* v_f_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_){
_start:
{
lean_object* v___x_933_; lean_object* v_share_934_; lean_object* v_maxFVar_935_; lean_object* v_proofInstInfo_936_; lean_object* v_inferType_937_; lean_object* v_getLevel_938_; lean_object* v_congrInfo_939_; lean_object* v_defEqI_940_; uint8_t v_debug_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_991_; 
v___x_933_ = lean_st_ref_take(v_a_927_);
v_share_934_ = lean_ctor_get(v___x_933_, 0);
v_maxFVar_935_ = lean_ctor_get(v___x_933_, 1);
v_proofInstInfo_936_ = lean_ctor_get(v___x_933_, 2);
v_inferType_937_ = lean_ctor_get(v___x_933_, 3);
v_getLevel_938_ = lean_ctor_get(v___x_933_, 4);
v_congrInfo_939_ = lean_ctor_get(v___x_933_, 5);
v_defEqI_940_ = lean_ctor_get(v___x_933_, 6);
v_debug_941_ = lean_ctor_get_uint8(v___x_933_, sizeof(void*)*7);
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_991_ == 0)
{
v___x_943_ = v___x_933_;
v_isShared_944_ = v_isSharedCheck_991_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_defEqI_940_);
lean_inc(v_congrInfo_939_);
lean_inc(v_getLevel_938_);
lean_inc(v_inferType_937_);
lean_inc(v_proofInstInfo_936_);
lean_inc(v_maxFVar_935_);
lean_inc(v_share_934_);
lean_dec(v___x_933_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_991_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_945_; lean_object* v___x_947_; 
v___x_945_ = lean_obj_once(&l_Lean_Meta_Sym_replaceS___redArg___closed__2, &l_Lean_Meta_Sym_replaceS___redArg___closed__2_once, _init_l_Lean_Meta_Sym_replaceS___redArg___closed__2);
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 0, v___x_945_);
v___x_947_ = v___x_943_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v___x_945_);
lean_ctor_set(v_reuseFailAlloc_990_, 1, v_maxFVar_935_);
lean_ctor_set(v_reuseFailAlloc_990_, 2, v_proofInstInfo_936_);
lean_ctor_set(v_reuseFailAlloc_990_, 3, v_inferType_937_);
lean_ctor_set(v_reuseFailAlloc_990_, 4, v_getLevel_938_);
lean_ctor_set(v_reuseFailAlloc_990_, 5, v_congrInfo_939_);
lean_ctor_set(v_reuseFailAlloc_990_, 6, v_defEqI_940_);
lean_ctor_set_uint8(v_reuseFailAlloc_990_, sizeof(void*)*7, v_debug_941_);
v___x_947_ = v_reuseFailAlloc_990_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v_fst_951_; lean_object* v_snd_952_; uint8_t v_debug_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v_fst_975_; 
v___x_948_ = lean_st_ref_set(v_a_927_, v___x_947_);
v___x_949_ = lean_st_ref_get(v_a_927_);
v_debug_971_ = lean_ctor_get_uint8(v___x_949_, sizeof(void*)*7);
lean_dec(v___x_949_);
v___x_972_ = lean_unsigned_to_nat(0u);
v___x_973_ = lean_box(v_debug_971_);
lean_inc_ref(v_f_925_);
lean_inc_ref(v_e_924_);
v___x_974_ = lean_apply_4(v_f_925_, v_e_924_, v___x_972_, v___x_973_, v_share_934_);
v_fst_975_ = lean_ctor_get(v___x_974_, 0);
lean_inc(v_fst_975_);
if (lean_obj_tag(v_fst_975_) == 1)
{
lean_object* v_snd_976_; lean_object* v_val_977_; 
lean_dec_ref(v_f_925_);
lean_dec_ref(v_e_924_);
v_snd_976_ = lean_ctor_get(v___x_974_, 1);
lean_inc(v_snd_976_);
lean_dec_ref(v___x_974_);
v_val_977_ = lean_ctor_get(v_fst_975_, 0);
lean_inc(v_val_977_);
lean_dec_ref(v_fst_975_);
v_fst_951_ = v_val_977_;
v_snd_952_ = v_snd_976_;
goto v___jp_950_;
}
else
{
lean_dec(v_fst_975_);
switch(lean_obj_tag(v_e_924_))
{
case 9:
{
lean_object* v_snd_978_; 
lean_dec_ref(v_f_925_);
v_snd_978_ = lean_ctor_get(v___x_974_, 1);
lean_inc(v_snd_978_);
lean_dec_ref(v___x_974_);
v_fst_951_ = v_e_924_;
v_snd_952_ = v_snd_978_;
goto v___jp_950_;
}
case 2:
{
lean_object* v_snd_979_; 
lean_dec_ref(v_f_925_);
v_snd_979_ = lean_ctor_get(v___x_974_, 1);
lean_inc(v_snd_979_);
lean_dec_ref(v___x_974_);
v_fst_951_ = v_e_924_;
v_snd_952_ = v_snd_979_;
goto v___jp_950_;
}
case 0:
{
lean_object* v_snd_980_; 
lean_dec_ref(v_f_925_);
v_snd_980_ = lean_ctor_get(v___x_974_, 1);
lean_inc(v_snd_980_);
lean_dec_ref(v___x_974_);
v_fst_951_ = v_e_924_;
v_snd_952_ = v_snd_980_;
goto v___jp_950_;
}
case 1:
{
lean_object* v_snd_981_; 
lean_dec_ref(v_f_925_);
v_snd_981_ = lean_ctor_get(v___x_974_, 1);
lean_inc(v_snd_981_);
lean_dec_ref(v___x_974_);
v_fst_951_ = v_e_924_;
v_snd_952_ = v_snd_981_;
goto v___jp_950_;
}
case 4:
{
lean_object* v_snd_982_; 
lean_dec_ref(v_f_925_);
v_snd_982_ = lean_ctor_get(v___x_974_, 1);
lean_inc(v_snd_982_);
lean_dec_ref(v___x_974_);
v_fst_951_ = v_e_924_;
v_snd_952_ = v_snd_982_;
goto v___jp_950_;
}
case 3:
{
lean_object* v_snd_983_; 
lean_dec_ref(v_f_925_);
v_snd_983_ = lean_ctor_get(v___x_974_, 1);
lean_inc(v_snd_983_);
lean_dec_ref(v___x_974_);
v_fst_951_ = v_e_924_;
v_snd_952_ = v_snd_983_;
goto v___jp_950_;
}
default: 
{
lean_object* v_snd_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v_fst_987_; lean_object* v_snd_988_; lean_object* v_fst_989_; 
v_snd_984_ = lean_ctor_get(v___x_974_, 1);
lean_inc(v_snd_984_);
lean_dec_ref(v___x_974_);
v___x_985_ = lean_obj_once(&l_Lean_Meta_Sym_replaceS_x27___closed__1, &l_Lean_Meta_Sym_replaceS_x27___closed__1_once, _init_l_Lean_Meta_Sym_replaceS_x27___closed__1);
v___x_986_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit(v_e_924_, v___x_972_, v_f_925_, v___x_985_, v_debug_971_, v_snd_984_);
v_fst_987_ = lean_ctor_get(v___x_986_, 0);
lean_inc(v_fst_987_);
v_snd_988_ = lean_ctor_get(v___x_986_, 1);
lean_inc(v_snd_988_);
lean_dec_ref(v___x_986_);
v_fst_989_ = lean_ctor_get(v_fst_987_, 0);
lean_inc(v_fst_989_);
lean_dec(v_fst_987_);
v_fst_951_ = v_fst_989_;
v_snd_952_ = v_snd_988_;
goto v___jp_950_;
}
}
}
v___jp_950_:
{
lean_object* v___x_953_; lean_object* v_maxFVar_954_; lean_object* v_proofInstInfo_955_; lean_object* v_inferType_956_; lean_object* v_getLevel_957_; lean_object* v_congrInfo_958_; lean_object* v_defEqI_959_; uint8_t v_debug_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_969_; 
v___x_953_ = lean_st_ref_take(v_a_927_);
v_maxFVar_954_ = lean_ctor_get(v___x_953_, 1);
v_proofInstInfo_955_ = lean_ctor_get(v___x_953_, 2);
v_inferType_956_ = lean_ctor_get(v___x_953_, 3);
v_getLevel_957_ = lean_ctor_get(v___x_953_, 4);
v_congrInfo_958_ = lean_ctor_get(v___x_953_, 5);
v_defEqI_959_ = lean_ctor_get(v___x_953_, 6);
v_debug_960_ = lean_ctor_get_uint8(v___x_953_, sizeof(void*)*7);
v_isSharedCheck_969_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_969_ == 0)
{
lean_object* v_unused_970_; 
v_unused_970_ = lean_ctor_get(v___x_953_, 0);
lean_dec(v_unused_970_);
v___x_962_ = v___x_953_;
v_isShared_963_ = v_isSharedCheck_969_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_defEqI_959_);
lean_inc(v_congrInfo_958_);
lean_inc(v_getLevel_957_);
lean_inc(v_inferType_956_);
lean_inc(v_proofInstInfo_955_);
lean_inc(v_maxFVar_954_);
lean_dec(v___x_953_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_969_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___x_965_; 
if (v_isShared_963_ == 0)
{
lean_ctor_set(v___x_962_, 0, v_snd_952_);
v___x_965_ = v___x_962_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v_snd_952_);
lean_ctor_set(v_reuseFailAlloc_968_, 1, v_maxFVar_954_);
lean_ctor_set(v_reuseFailAlloc_968_, 2, v_proofInstInfo_955_);
lean_ctor_set(v_reuseFailAlloc_968_, 3, v_inferType_956_);
lean_ctor_set(v_reuseFailAlloc_968_, 4, v_getLevel_957_);
lean_ctor_set(v_reuseFailAlloc_968_, 5, v_congrInfo_958_);
lean_ctor_set(v_reuseFailAlloc_968_, 6, v_defEqI_959_);
lean_ctor_set_uint8(v_reuseFailAlloc_968_, sizeof(void*)*7, v_debug_960_);
v___x_965_ = v_reuseFailAlloc_968_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_966_ = lean_st_ref_set(v_a_927_, v___x_965_);
v___x_967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_967_, 0, v_fst_951_);
return v___x_967_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_replaceS___boxed(lean_object* v_e_992_, lean_object* v_f_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l_Lean_Meta_Sym_replaceS(v_e_992_, v_f_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_, v_a_998_, v_a_999_);
lean_dec(v_a_999_);
lean_dec_ref(v_a_998_);
lean_dec(v_a_997_);
lean_dec_ref(v_a_996_);
lean_dec(v_a_995_);
lean_dec_ref(v_a_994_);
return v_res_1001_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_ReplaceS(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_ReplaceS(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_ReplaceS(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_ReplaceS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_ReplaceS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_ReplaceS(builtin);
}
#ifdef __cplusplus
}
#endif
