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
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v_share1_306_; lean_object* v_assertShared_307_; lean_object* v_isDebugEnabled_308_; lean_object* v___x_309_; lean_object* v___f_310_; lean_object* v___f_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_303_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20);
v___x_304_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__30, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__30_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__30);
v___x_305_ = l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM;
v_share1_306_ = lean_ctor_get(v___x_305_, 0);
v_assertShared_307_ = lean_ctor_get(v___x_305_, 1);
v_isDebugEnabled_308_ = lean_ctor_get(v___x_305_, 2);
v___x_309_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__31, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__31_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__31);
lean_inc(v_share1_306_);
v___f_310_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_310_, 0, v_share1_306_);
lean_closure_set(v___f_310_, 1, v___x_309_);
lean_inc(v_assertShared_307_);
v___f_311_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift___redArg___lam__1), 3, 2);
lean_closure_set(v___f_311_, 0, v_assertShared_307_);
lean_closure_set(v___f_311_, 1, v___x_309_);
lean_inc(v_isDebugEnabled_308_);
v___x_312_ = lean_alloc_closure((void*)(l_StateT_lift), 6, 5);
lean_closure_set(v___x_312_, 0, lean_box(0));
lean_closure_set(v___x_312_, 1, lean_box(0));
lean_closure_set(v___x_312_, 2, v___x_303_);
lean_closure_set(v___x_312_, 3, lean_box(0));
lean_closure_set(v___x_312_, 4, v_isDebugEnabled_308_);
v___x_313_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_313_, 0, v___f_310_);
lean_ctor_set(v___x_313_, 1, v___f_311_);
lean_ctor_set(v___x_313_, 2, v___x_312_);
switch(lean_obj_tag(v_e_297_))
{
case 5:
{
lean_object* v_fn_314_; lean_object* v_arg_315_; lean_object* v___x_316_; lean_object* v_fst_317_; lean_object* v_snd_318_; lean_object* v_fst_319_; lean_object* v_snd_320_; lean_object* v___x_321_; lean_object* v_fst_322_; lean_object* v_snd_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_346_; 
v_fn_314_ = lean_ctor_get(v_e_297_, 0);
v_arg_315_ = lean_ctor_get(v_e_297_, 1);
lean_inc_ref(v_fn_299_);
lean_inc(v_offset_298_);
lean_inc_ref(v_fn_314_);
v___x_316_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_fn_314_, v_offset_298_, v_fn_299_, v_a_300_, v_a_301_, v_a_302_);
v_fst_317_ = lean_ctor_get(v___x_316_, 0);
lean_inc(v_fst_317_);
v_snd_318_ = lean_ctor_get(v___x_316_, 1);
lean_inc(v_snd_318_);
lean_dec_ref(v___x_316_);
v_fst_319_ = lean_ctor_get(v_fst_317_, 0);
lean_inc(v_fst_319_);
v_snd_320_ = lean_ctor_get(v_fst_317_, 1);
lean_inc(v_snd_320_);
lean_dec(v_fst_317_);
lean_inc_ref(v_arg_315_);
v___x_321_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_arg_315_, v_offset_298_, v_fn_299_, v_snd_320_, v_a_301_, v_snd_318_);
v_fst_322_ = lean_ctor_get(v___x_321_, 0);
v_snd_323_ = lean_ctor_get(v___x_321_, 1);
v_isSharedCheck_346_ = !lean_is_exclusive(v___x_321_);
if (v_isSharedCheck_346_ == 0)
{
v___x_325_ = v___x_321_;
v_isShared_326_ = v_isSharedCheck_346_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_snd_323_);
lean_inc(v_fst_322_);
lean_dec(v___x_321_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_346_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v_fst_327_; lean_object* v_snd_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_345_; 
v_fst_327_ = lean_ctor_get(v_fst_322_, 0);
v_snd_328_ = lean_ctor_get(v_fst_322_, 1);
v_isSharedCheck_345_ = !lean_is_exclusive(v_fst_322_);
if (v_isSharedCheck_345_ == 0)
{
v___x_330_ = v_fst_322_;
v_isShared_331_ = v_isSharedCheck_345_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_snd_328_);
lean_inc(v_fst_327_);
lean_dec(v_fst_322_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_345_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
uint8_t v___y_333_; uint8_t v___x_343_; 
v___x_343_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_314_, v_fst_319_);
if (v___x_343_ == 0)
{
v___y_333_ = v___x_343_;
goto v___jp_332_;
}
else
{
uint8_t v___x_344_; 
v___x_344_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_315_, v_fst_327_);
v___y_333_ = v___x_344_;
goto v___jp_332_;
}
v___jp_332_:
{
if (v___y_333_ == 0)
{
lean_object* v___x_10643__overap_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
lean_del_object(v___x_330_);
lean_del_object(v___x_325_);
lean_dec_ref(v_e_297_);
v___x_10643__overap_334_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v___x_313_, v___x_304_, v_fst_319_, v_fst_327_);
v___x_335_ = lean_box(v_a_301_);
v___x_336_ = lean_apply_3(v___x_10643__overap_334_, v_snd_328_, v___x_335_, v_snd_323_);
return v___x_336_;
}
else
{
lean_object* v___x_338_; 
lean_dec(v_fst_327_);
lean_dec(v_fst_319_);
lean_dec_ref(v___x_313_);
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 0, v_e_297_);
v___x_338_ = v___x_330_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v_e_297_);
lean_ctor_set(v_reuseFailAlloc_342_, 1, v_snd_328_);
v___x_338_ = v_reuseFailAlloc_342_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
lean_object* v___x_340_; 
if (v_isShared_326_ == 0)
{
lean_ctor_set(v___x_325_, 0, v___x_338_);
v___x_340_ = v___x_325_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v___x_338_);
lean_ctor_set(v_reuseFailAlloc_341_, 1, v_snd_323_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
return v___x_340_;
}
}
}
}
}
}
}
case 6:
{
lean_object* v_binderName_347_; lean_object* v_binderType_348_; lean_object* v_body_349_; uint8_t v_binderInfo_350_; lean_object* v___x_351_; lean_object* v_fst_352_; lean_object* v_snd_353_; lean_object* v_fst_354_; lean_object* v_snd_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v_fst_359_; lean_object* v_snd_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_383_; 
v_binderName_347_ = lean_ctor_get(v_e_297_, 0);
v_binderType_348_ = lean_ctor_get(v_e_297_, 1);
v_body_349_ = lean_ctor_get(v_e_297_, 2);
v_binderInfo_350_ = lean_ctor_get_uint8(v_e_297_, sizeof(void*)*3 + 8);
lean_inc_ref(v_fn_299_);
lean_inc(v_offset_298_);
lean_inc_ref(v_binderType_348_);
v___x_351_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_binderType_348_, v_offset_298_, v_fn_299_, v_a_300_, v_a_301_, v_a_302_);
v_fst_352_ = lean_ctor_get(v___x_351_, 0);
lean_inc(v_fst_352_);
v_snd_353_ = lean_ctor_get(v___x_351_, 1);
lean_inc(v_snd_353_);
lean_dec_ref(v___x_351_);
v_fst_354_ = lean_ctor_get(v_fst_352_, 0);
lean_inc(v_fst_354_);
v_snd_355_ = lean_ctor_get(v_fst_352_, 1);
lean_inc(v_snd_355_);
lean_dec(v_fst_352_);
v___x_356_ = lean_unsigned_to_nat(1u);
v___x_357_ = lean_nat_add(v_offset_298_, v___x_356_);
lean_dec(v_offset_298_);
lean_inc_ref(v_body_349_);
v___x_358_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_body_349_, v___x_357_, v_fn_299_, v_snd_355_, v_a_301_, v_snd_353_);
v_fst_359_ = lean_ctor_get(v___x_358_, 0);
v_snd_360_ = lean_ctor_get(v___x_358_, 1);
v_isSharedCheck_383_ = !lean_is_exclusive(v___x_358_);
if (v_isSharedCheck_383_ == 0)
{
v___x_362_ = v___x_358_;
v_isShared_363_ = v_isSharedCheck_383_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_snd_360_);
lean_inc(v_fst_359_);
lean_dec(v___x_358_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_383_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v_fst_364_; lean_object* v_snd_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_382_; 
v_fst_364_ = lean_ctor_get(v_fst_359_, 0);
v_snd_365_ = lean_ctor_get(v_fst_359_, 1);
v_isSharedCheck_382_ = !lean_is_exclusive(v_fst_359_);
if (v_isSharedCheck_382_ == 0)
{
v___x_367_ = v_fst_359_;
v_isShared_368_ = v_isSharedCheck_382_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_snd_365_);
lean_inc(v_fst_364_);
lean_dec(v_fst_359_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_382_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
uint8_t v___y_370_; uint8_t v___x_380_; 
v___x_380_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_348_, v_fst_354_);
if (v___x_380_ == 0)
{
v___y_370_ = v___x_380_;
goto v___jp_369_;
}
else
{
uint8_t v___x_381_; 
v___x_381_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_349_, v_fst_364_);
v___y_370_ = v___x_381_;
goto v___jp_369_;
}
v___jp_369_:
{
if (v___y_370_ == 0)
{
lean_object* v___x_10804__overap_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
lean_inc(v_binderName_347_);
lean_del_object(v___x_367_);
lean_del_object(v___x_362_);
lean_dec_ref(v_e_297_);
v___x_10804__overap_371_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v___x_313_, v___x_304_, v_binderName_347_, v_binderInfo_350_, v_fst_354_, v_fst_364_);
v___x_372_ = lean_box(v_a_301_);
v___x_373_ = lean_apply_3(v___x_10804__overap_371_, v_snd_365_, v___x_372_, v_snd_360_);
return v___x_373_;
}
else
{
lean_object* v___x_375_; 
lean_dec(v_fst_364_);
lean_dec(v_fst_354_);
lean_dec_ref(v___x_313_);
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 0, v_e_297_);
v___x_375_ = v___x_367_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_e_297_);
lean_ctor_set(v_reuseFailAlloc_379_, 1, v_snd_365_);
v___x_375_ = v_reuseFailAlloc_379_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
lean_object* v___x_377_; 
if (v_isShared_363_ == 0)
{
lean_ctor_set(v___x_362_, 0, v___x_375_);
v___x_377_ = v___x_362_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v___x_375_);
lean_ctor_set(v_reuseFailAlloc_378_, 1, v_snd_360_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
}
}
}
}
}
case 7:
{
lean_object* v_binderName_384_; lean_object* v_binderType_385_; lean_object* v_body_386_; uint8_t v_binderInfo_387_; lean_object* v___x_388_; lean_object* v_fst_389_; lean_object* v_snd_390_; lean_object* v_fst_391_; lean_object* v_snd_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v_fst_396_; lean_object* v_snd_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_420_; 
v_binderName_384_ = lean_ctor_get(v_e_297_, 0);
v_binderType_385_ = lean_ctor_get(v_e_297_, 1);
v_body_386_ = lean_ctor_get(v_e_297_, 2);
v_binderInfo_387_ = lean_ctor_get_uint8(v_e_297_, sizeof(void*)*3 + 8);
lean_inc_ref(v_fn_299_);
lean_inc(v_offset_298_);
lean_inc_ref(v_binderType_385_);
v___x_388_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_binderType_385_, v_offset_298_, v_fn_299_, v_a_300_, v_a_301_, v_a_302_);
v_fst_389_ = lean_ctor_get(v___x_388_, 0);
lean_inc(v_fst_389_);
v_snd_390_ = lean_ctor_get(v___x_388_, 1);
lean_inc(v_snd_390_);
lean_dec_ref(v___x_388_);
v_fst_391_ = lean_ctor_get(v_fst_389_, 0);
lean_inc(v_fst_391_);
v_snd_392_ = lean_ctor_get(v_fst_389_, 1);
lean_inc(v_snd_392_);
lean_dec(v_fst_389_);
v___x_393_ = lean_unsigned_to_nat(1u);
v___x_394_ = lean_nat_add(v_offset_298_, v___x_393_);
lean_dec(v_offset_298_);
lean_inc_ref(v_body_386_);
v___x_395_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_body_386_, v___x_394_, v_fn_299_, v_snd_392_, v_a_301_, v_snd_390_);
v_fst_396_ = lean_ctor_get(v___x_395_, 0);
v_snd_397_ = lean_ctor_get(v___x_395_, 1);
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_395_);
if (v_isSharedCheck_420_ == 0)
{
v___x_399_ = v___x_395_;
v_isShared_400_ = v_isSharedCheck_420_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_snd_397_);
lean_inc(v_fst_396_);
lean_dec(v___x_395_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_420_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v_fst_401_; lean_object* v_snd_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_419_; 
v_fst_401_ = lean_ctor_get(v_fst_396_, 0);
v_snd_402_ = lean_ctor_get(v_fst_396_, 1);
v_isSharedCheck_419_ = !lean_is_exclusive(v_fst_396_);
if (v_isSharedCheck_419_ == 0)
{
v___x_404_ = v_fst_396_;
v_isShared_405_ = v_isSharedCheck_419_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_snd_402_);
lean_inc(v_fst_401_);
lean_dec(v_fst_396_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_419_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
uint8_t v___y_407_; uint8_t v___x_417_; 
v___x_417_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_385_, v_fst_391_);
if (v___x_417_ == 0)
{
v___y_407_ = v___x_417_;
goto v___jp_406_;
}
else
{
uint8_t v___x_418_; 
v___x_418_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_386_, v_fst_401_);
v___y_407_ = v___x_418_;
goto v___jp_406_;
}
v___jp_406_:
{
if (v___y_407_ == 0)
{
lean_object* v___x_10969__overap_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
lean_inc(v_binderName_384_);
lean_del_object(v___x_404_);
lean_del_object(v___x_399_);
lean_dec_ref(v_e_297_);
v___x_10969__overap_408_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v___x_313_, v___x_304_, v_binderName_384_, v_binderInfo_387_, v_fst_391_, v_fst_401_);
v___x_409_ = lean_box(v_a_301_);
v___x_410_ = lean_apply_3(v___x_10969__overap_408_, v_snd_402_, v___x_409_, v_snd_397_);
return v___x_410_;
}
else
{
lean_object* v___x_412_; 
lean_dec(v_fst_401_);
lean_dec(v_fst_391_);
lean_dec_ref(v___x_313_);
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 0, v_e_297_);
v___x_412_ = v___x_404_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v_e_297_);
lean_ctor_set(v_reuseFailAlloc_416_, 1, v_snd_402_);
v___x_412_ = v_reuseFailAlloc_416_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
lean_object* v___x_414_; 
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 0, v___x_412_);
v___x_414_ = v___x_399_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v___x_412_);
lean_ctor_set(v_reuseFailAlloc_415_, 1, v_snd_397_);
v___x_414_ = v_reuseFailAlloc_415_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
return v___x_414_;
}
}
}
}
}
}
}
case 8:
{
lean_object* v_declName_421_; lean_object* v_type_422_; lean_object* v_value_423_; lean_object* v_body_424_; uint8_t v_nondep_425_; lean_object* v___x_426_; lean_object* v_fst_427_; lean_object* v_snd_428_; lean_object* v_fst_429_; lean_object* v_snd_430_; lean_object* v___x_431_; lean_object* v_fst_432_; lean_object* v_snd_433_; lean_object* v_fst_434_; lean_object* v_snd_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v_fst_439_; lean_object* v_snd_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_467_; 
v_declName_421_ = lean_ctor_get(v_e_297_, 0);
v_type_422_ = lean_ctor_get(v_e_297_, 1);
v_value_423_ = lean_ctor_get(v_e_297_, 2);
v_body_424_ = lean_ctor_get(v_e_297_, 3);
v_nondep_425_ = lean_ctor_get_uint8(v_e_297_, sizeof(void*)*4 + 8);
lean_inc_ref_n(v_fn_299_, 2);
lean_inc_n(v_offset_298_, 2);
lean_inc_ref(v_type_422_);
v___x_426_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_type_422_, v_offset_298_, v_fn_299_, v_a_300_, v_a_301_, v_a_302_);
v_fst_427_ = lean_ctor_get(v___x_426_, 0);
lean_inc(v_fst_427_);
v_snd_428_ = lean_ctor_get(v___x_426_, 1);
lean_inc(v_snd_428_);
lean_dec_ref(v___x_426_);
v_fst_429_ = lean_ctor_get(v_fst_427_, 0);
lean_inc(v_fst_429_);
v_snd_430_ = lean_ctor_get(v_fst_427_, 1);
lean_inc(v_snd_430_);
lean_dec(v_fst_427_);
lean_inc_ref(v_value_423_);
v___x_431_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_value_423_, v_offset_298_, v_fn_299_, v_snd_430_, v_a_301_, v_snd_428_);
v_fst_432_ = lean_ctor_get(v___x_431_, 0);
lean_inc(v_fst_432_);
v_snd_433_ = lean_ctor_get(v___x_431_, 1);
lean_inc(v_snd_433_);
lean_dec_ref(v___x_431_);
v_fst_434_ = lean_ctor_get(v_fst_432_, 0);
lean_inc(v_fst_434_);
v_snd_435_ = lean_ctor_get(v_fst_432_, 1);
lean_inc(v_snd_435_);
lean_dec(v_fst_432_);
v___x_436_ = lean_unsigned_to_nat(1u);
v___x_437_ = lean_nat_add(v_offset_298_, v___x_436_);
lean_dec(v_offset_298_);
lean_inc_ref(v_body_424_);
v___x_438_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_body_424_, v___x_437_, v_fn_299_, v_snd_435_, v_a_301_, v_snd_433_);
v_fst_439_ = lean_ctor_get(v___x_438_, 0);
v_snd_440_ = lean_ctor_get(v___x_438_, 1);
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_467_ == 0)
{
v___x_442_ = v___x_438_;
v_isShared_443_ = v_isSharedCheck_467_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_snd_440_);
lean_inc(v_fst_439_);
lean_dec(v___x_438_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_467_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v_fst_444_; lean_object* v_snd_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_466_; 
v_fst_444_ = lean_ctor_get(v_fst_439_, 0);
v_snd_445_ = lean_ctor_get(v_fst_439_, 1);
v_isSharedCheck_466_ = !lean_is_exclusive(v_fst_439_);
if (v_isSharedCheck_466_ == 0)
{
v___x_447_ = v_fst_439_;
v_isShared_448_ = v_isSharedCheck_466_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_snd_445_);
lean_inc(v_fst_444_);
lean_dec(v_fst_439_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_466_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
uint8_t v___y_450_; uint8_t v___x_464_; 
v___x_464_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_type_422_, v_fst_429_);
if (v___x_464_ == 0)
{
v___y_450_ = v___x_464_;
goto v___jp_449_;
}
else
{
uint8_t v___x_465_; 
v___x_465_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_value_423_, v_fst_434_);
v___y_450_ = v___x_465_;
goto v___jp_449_;
}
v___jp_449_:
{
if (v___y_450_ == 0)
{
lean_object* v___x_11156__overap_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
lean_inc(v_declName_421_);
lean_del_object(v___x_447_);
lean_del_object(v___x_442_);
lean_dec_ref(v_e_297_);
v___x_11156__overap_451_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v___x_313_, v___x_304_, v_declName_421_, v_fst_429_, v_fst_434_, v_fst_444_, v_nondep_425_);
v___x_452_ = lean_box(v_a_301_);
v___x_453_ = lean_apply_3(v___x_11156__overap_451_, v_snd_445_, v___x_452_, v_snd_440_);
return v___x_453_;
}
else
{
uint8_t v___x_454_; 
v___x_454_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_424_, v_fst_444_);
if (v___x_454_ == 0)
{
lean_object* v___x_11158__overap_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
lean_inc(v_declName_421_);
lean_del_object(v___x_447_);
lean_del_object(v___x_442_);
lean_dec_ref(v_e_297_);
v___x_11158__overap_455_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v___x_313_, v___x_304_, v_declName_421_, v_fst_429_, v_fst_434_, v_fst_444_, v_nondep_425_);
v___x_456_ = lean_box(v_a_301_);
v___x_457_ = lean_apply_3(v___x_11158__overap_455_, v_snd_445_, v___x_456_, v_snd_440_);
return v___x_457_;
}
else
{
lean_object* v___x_459_; 
lean_dec(v_fst_444_);
lean_dec(v_fst_434_);
lean_dec(v_fst_429_);
lean_dec_ref(v___x_313_);
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 0, v_e_297_);
v___x_459_ = v___x_447_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_e_297_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v_snd_445_);
v___x_459_ = v_reuseFailAlloc_463_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
lean_object* v___x_461_; 
if (v_isShared_443_ == 0)
{
lean_ctor_set(v___x_442_, 0, v___x_459_);
v___x_461_ = v___x_442_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v___x_459_);
lean_ctor_set(v_reuseFailAlloc_462_, 1, v_snd_440_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
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
lean_object* v_data_468_; lean_object* v_expr_469_; lean_object* v___x_470_; lean_object* v_fst_471_; lean_object* v_snd_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_492_; 
v_data_468_ = lean_ctor_get(v_e_297_, 0);
v_expr_469_ = lean_ctor_get(v_e_297_, 1);
lean_inc_ref(v_expr_469_);
v___x_470_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_expr_469_, v_offset_298_, v_fn_299_, v_a_300_, v_a_301_, v_a_302_);
v_fst_471_ = lean_ctor_get(v___x_470_, 0);
v_snd_472_ = lean_ctor_get(v___x_470_, 1);
v_isSharedCheck_492_ = !lean_is_exclusive(v___x_470_);
if (v_isSharedCheck_492_ == 0)
{
v___x_474_ = v___x_470_;
v_isShared_475_ = v_isSharedCheck_492_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_snd_472_);
lean_inc(v_fst_471_);
lean_dec(v___x_470_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_492_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v_fst_476_; lean_object* v_snd_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_491_; 
v_fst_476_ = lean_ctor_get(v_fst_471_, 0);
v_snd_477_ = lean_ctor_get(v_fst_471_, 1);
v_isSharedCheck_491_ = !lean_is_exclusive(v_fst_471_);
if (v_isSharedCheck_491_ == 0)
{
v___x_479_ = v_fst_471_;
v_isShared_480_ = v_isSharedCheck_491_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_snd_477_);
lean_inc(v_fst_476_);
lean_dec(v_fst_471_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_491_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
uint8_t v___x_481_; 
v___x_481_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_expr_469_, v_fst_476_);
if (v___x_481_ == 0)
{
lean_object* v___x_11315__overap_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
lean_inc(v_data_468_);
lean_del_object(v___x_479_);
lean_del_object(v___x_474_);
lean_dec_ref(v_e_297_);
v___x_11315__overap_482_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg(v___x_313_, v___x_304_, v_data_468_, v_fst_476_);
v___x_483_ = lean_box(v_a_301_);
v___x_484_ = lean_apply_3(v___x_11315__overap_482_, v_snd_477_, v___x_483_, v_snd_472_);
return v___x_484_;
}
else
{
lean_object* v___x_486_; 
lean_dec(v_fst_476_);
lean_dec_ref(v___x_313_);
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 0, v_e_297_);
v___x_486_ = v___x_479_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v_e_297_);
lean_ctor_set(v_reuseFailAlloc_490_, 1, v_snd_477_);
v___x_486_ = v_reuseFailAlloc_490_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
lean_object* v___x_488_; 
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 0, v___x_486_);
v___x_488_ = v___x_474_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v___x_486_);
lean_ctor_set(v_reuseFailAlloc_489_, 1, v_snd_472_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
}
}
}
}
case 11:
{
lean_object* v_typeName_493_; lean_object* v_idx_494_; lean_object* v_struct_495_; lean_object* v___x_496_; lean_object* v_fst_497_; lean_object* v_snd_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_518_; 
v_typeName_493_ = lean_ctor_get(v_e_297_, 0);
v_idx_494_ = lean_ctor_get(v_e_297_, 1);
v_struct_495_ = lean_ctor_get(v_e_297_, 2);
lean_inc_ref(v_struct_495_);
v___x_496_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_struct_495_, v_offset_298_, v_fn_299_, v_a_300_, v_a_301_, v_a_302_);
v_fst_497_ = lean_ctor_get(v___x_496_, 0);
v_snd_498_ = lean_ctor_get(v___x_496_, 1);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_518_ == 0)
{
v___x_500_ = v___x_496_;
v_isShared_501_ = v_isSharedCheck_518_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_snd_498_);
lean_inc(v_fst_497_);
lean_dec(v___x_496_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_518_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v_fst_502_; lean_object* v_snd_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_517_; 
v_fst_502_ = lean_ctor_get(v_fst_497_, 0);
v_snd_503_ = lean_ctor_get(v_fst_497_, 1);
v_isSharedCheck_517_ = !lean_is_exclusive(v_fst_497_);
if (v_isSharedCheck_517_ == 0)
{
v___x_505_ = v_fst_497_;
v_isShared_506_ = v_isSharedCheck_517_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_snd_503_);
lean_inc(v_fst_502_);
lean_dec(v_fst_497_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_517_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
uint8_t v___x_507_; 
v___x_507_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_495_, v_fst_502_);
if (v___x_507_ == 0)
{
lean_object* v___x_11427__overap_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
lean_inc(v_idx_494_);
lean_inc(v_typeName_493_);
lean_del_object(v___x_505_);
lean_del_object(v___x_500_);
lean_dec_ref(v_e_297_);
v___x_11427__overap_508_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg(v___x_313_, v___x_304_, v_typeName_493_, v_idx_494_, v_fst_502_);
v___x_509_ = lean_box(v_a_301_);
v___x_510_ = lean_apply_3(v___x_11427__overap_508_, v_snd_503_, v___x_509_, v_snd_498_);
return v___x_510_;
}
else
{
lean_object* v___x_512_; 
lean_dec(v_fst_502_);
lean_dec_ref(v___x_313_);
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 0, v_e_297_);
v___x_512_ = v___x_505_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_e_297_);
lean_ctor_set(v_reuseFailAlloc_516_, 1, v_snd_503_);
v___x_512_ = v_reuseFailAlloc_516_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
lean_object* v___x_514_; 
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 0, v___x_512_);
v___x_514_ = v___x_500_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v___x_512_);
lean_ctor_set(v_reuseFailAlloc_515_, 1, v_snd_498_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_10529__overap_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
lean_dec_ref(v___x_313_);
lean_dec_ref(v_fn_299_);
lean_dec(v_offset_298_);
lean_dec_ref(v_e_297_);
v___x_519_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__32, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__32_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__32);
v___x_520_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__36, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__36_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__36);
v___x_10529__overap_521_ = l_panic___redArg(v___x_519_, v___x_520_);
v___x_522_ = lean_box(v_a_301_);
v___x_523_ = lean_apply_3(v___x_10529__overap_521_, v_a_300_, v___x_522_, v_a_302_);
return v___x_523_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(lean_object* v_e_524_, lean_object* v_offset_525_, lean_object* v_f_526_, lean_object* v_a_527_, uint8_t v_a_528_, lean_object* v_a_529_){
_start:
{
lean_object* v___f_530_; lean_object* v_key_531_; lean_object* v___f_532_; lean_object* v___x_533_; 
v___f_530_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__3));
lean_inc(v_offset_525_);
lean_inc_ref(v_e_524_);
v_key_531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_531_, 0, v_e_524_);
lean_ctor_set(v_key_531_, 1, v_offset_525_);
v___f_532_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__5, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__5_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__5);
lean_inc_ref(v_key_531_);
v___x_533_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_532_, v___f_530_, v_a_527_, v_key_531_);
if (lean_obj_tag(v___x_533_) == 1)
{
lean_object* v_val_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
lean_dec_ref(v_key_531_);
lean_dec_ref(v_f_526_);
lean_dec(v_offset_525_);
lean_dec_ref(v_e_524_);
v_val_534_ = lean_ctor_get(v___x_533_, 0);
lean_inc(v_val_534_);
lean_dec_ref(v___x_533_);
v___x_535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_535_, 0, v_val_534_);
lean_ctor_set(v___x_535_, 1, v_a_527_);
v___x_536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_536_, 0, v___x_535_);
lean_ctor_set(v___x_536_, 1, v_a_529_);
return v___x_536_;
}
else
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v_fst_539_; 
lean_dec(v___x_533_);
v___x_537_ = lean_box(v_a_528_);
lean_inc_ref(v_f_526_);
lean_inc(v_offset_525_);
lean_inc_ref(v_e_524_);
v___x_538_ = lean_apply_4(v_f_526_, v_e_524_, v_offset_525_, v___x_537_, v_a_529_);
v_fst_539_ = lean_ctor_get(v___x_538_, 0);
lean_inc(v_fst_539_);
if (lean_obj_tag(v_fst_539_) == 1)
{
lean_object* v_snd_540_; lean_object* v_val_541_; lean_object* v___x_542_; 
lean_dec_ref(v_f_526_);
lean_dec(v_offset_525_);
lean_dec_ref(v_e_524_);
v_snd_540_ = lean_ctor_get(v___x_538_, 1);
lean_inc(v_snd_540_);
lean_dec_ref(v___x_538_);
v_val_541_ = lean_ctor_get(v_fst_539_, 0);
lean_inc(v_val_541_);
lean_dec_ref(v_fst_539_);
v___x_542_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(v_key_531_, v_val_541_, v_a_527_, v_snd_540_);
return v___x_542_;
}
else
{
lean_dec(v_fst_539_);
switch(lean_obj_tag(v_e_524_))
{
case 9:
{
lean_object* v_snd_543_; lean_object* v___x_544_; 
lean_dec_ref(v_f_526_);
lean_dec(v_offset_525_);
v_snd_543_ = lean_ctor_get(v___x_538_, 1);
lean_inc(v_snd_543_);
lean_dec_ref(v___x_538_);
v___x_544_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(v_key_531_, v_e_524_, v_a_527_, v_snd_543_);
return v___x_544_;
}
case 2:
{
lean_object* v_snd_545_; lean_object* v___x_546_; 
lean_dec_ref(v_f_526_);
lean_dec(v_offset_525_);
v_snd_545_ = lean_ctor_get(v___x_538_, 1);
lean_inc(v_snd_545_);
lean_dec_ref(v___x_538_);
v___x_546_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(v_key_531_, v_e_524_, v_a_527_, v_snd_545_);
return v___x_546_;
}
case 0:
{
lean_object* v_snd_547_; lean_object* v___x_548_; 
lean_dec_ref(v_f_526_);
lean_dec(v_offset_525_);
v_snd_547_ = lean_ctor_get(v___x_538_, 1);
lean_inc(v_snd_547_);
lean_dec_ref(v___x_538_);
v___x_548_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(v_key_531_, v_e_524_, v_a_527_, v_snd_547_);
return v___x_548_;
}
case 1:
{
lean_object* v_snd_549_; lean_object* v___x_550_; 
lean_dec_ref(v_f_526_);
lean_dec(v_offset_525_);
v_snd_549_ = lean_ctor_get(v___x_538_, 1);
lean_inc(v_snd_549_);
lean_dec_ref(v___x_538_);
v___x_550_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(v_key_531_, v_e_524_, v_a_527_, v_snd_549_);
return v___x_550_;
}
case 4:
{
lean_object* v_snd_551_; lean_object* v___x_552_; 
lean_dec_ref(v_f_526_);
lean_dec(v_offset_525_);
v_snd_551_ = lean_ctor_get(v___x_538_, 1);
lean_inc(v_snd_551_);
lean_dec_ref(v___x_538_);
v___x_552_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(v_key_531_, v_e_524_, v_a_527_, v_snd_551_);
return v___x_552_;
}
case 3:
{
lean_object* v_snd_553_; lean_object* v___x_554_; 
lean_dec_ref(v_f_526_);
lean_dec(v_offset_525_);
v_snd_553_ = lean_ctor_get(v___x_538_, 1);
lean_inc(v_snd_553_);
lean_dec_ref(v___x_538_);
v___x_554_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(v_key_531_, v_e_524_, v_a_527_, v_snd_553_);
return v___x_554_;
}
default: 
{
lean_object* v_snd_555_; lean_object* v___x_556_; lean_object* v_fst_557_; lean_object* v_snd_558_; lean_object* v_fst_559_; lean_object* v_snd_560_; lean_object* v___x_561_; 
v_snd_555_ = lean_ctor_get(v___x_538_, 1);
lean_inc(v_snd_555_);
lean_dec_ref(v___x_538_);
v___x_556_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit(v_e_524_, v_offset_525_, v_f_526_, v_a_527_, v_a_528_, v_snd_555_);
v_fst_557_ = lean_ctor_get(v___x_556_, 0);
lean_inc(v_fst_557_);
v_snd_558_ = lean_ctor_get(v___x_556_, 1);
lean_inc(v_snd_558_);
lean_dec_ref(v___x_556_);
v_fst_559_ = lean_ctor_get(v_fst_557_, 0);
lean_inc(v_fst_559_);
v_snd_560_ = lean_ctor_get(v_fst_557_, 1);
lean_inc(v_snd_560_);
lean_dec(v_fst_557_);
v___x_561_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(v_key_531_, v_fst_559_, v_snd_560_, v_snd_558_);
return v___x_561_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___boxed(lean_object* v_e_562_, lean_object* v_offset_563_, lean_object* v_f_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_){
_start:
{
uint8_t v_a_boxed_568_; lean_object* v_res_569_; 
v_a_boxed_568_ = lean_unbox(v_a_566_);
v_res_569_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_e_562_, v_offset_563_, v_f_564_, v_a_565_, v_a_boxed_568_, v_a_567_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___boxed(lean_object* v_e_570_, lean_object* v_offset_571_, lean_object* v_fn_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_){
_start:
{
uint8_t v_a_boxed_576_; lean_object* v_res_577_; 
v_a_boxed_576_ = lean_unbox(v_a_574_);
v_res_577_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit(v_e_570_, v_offset_571_, v_fn_572_, v_a_573_, v_a_boxed_576_, v_a_575_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild_match__4_splitter___redArg(lean_object* v_____do__lift_578_, lean_object* v_h__1_579_, lean_object* v_h__2_580_){
_start:
{
if (lean_obj_tag(v_____do__lift_578_) == 1)
{
lean_object* v_val_581_; lean_object* v___x_582_; 
lean_dec(v_h__2_580_);
v_val_581_ = lean_ctor_get(v_____do__lift_578_, 0);
lean_inc(v_val_581_);
lean_dec_ref(v_____do__lift_578_);
v___x_582_ = lean_apply_1(v_h__1_579_, v_val_581_);
return v___x_582_;
}
else
{
lean_object* v___x_583_; 
lean_dec(v_h__1_579_);
v___x_583_ = lean_apply_2(v_h__2_580_, v_____do__lift_578_, lean_box(0));
return v___x_583_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild_match__4_splitter(lean_object* v_motive_584_, lean_object* v_____do__lift_585_, lean_object* v_h__1_586_, lean_object* v_h__2_587_){
_start:
{
if (lean_obj_tag(v_____do__lift_585_) == 1)
{
lean_object* v_val_588_; lean_object* v___x_589_; 
lean_dec(v_h__2_587_);
v_val_588_ = lean_ctor_get(v_____do__lift_585_, 0);
lean_inc(v_val_588_);
lean_dec_ref(v_____do__lift_585_);
v___x_589_ = lean_apply_1(v_h__1_586_, v_val_588_);
return v___x_589_;
}
else
{
lean_object* v___x_590_; 
lean_dec(v_h__1_586_);
v___x_590_ = lean_apply_2(v_h__2_587_, v_____do__lift_585_, lean_box(0));
return v___x_590_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild_match__1_splitter___redArg(lean_object* v_e_591_, lean_object* v_h__1_592_, lean_object* v_h__2_593_, lean_object* v_h__3_594_, lean_object* v_h__4_595_, lean_object* v_h__5_596_, lean_object* v_h__6_597_, lean_object* v_h__7_598_){
_start:
{
switch(lean_obj_tag(v_e_591_))
{
case 9:
{
lean_object* v_a_599_; lean_object* v___x_600_; 
lean_dec(v_h__7_598_);
lean_dec(v_h__6_597_);
lean_dec(v_h__5_596_);
lean_dec(v_h__4_595_);
lean_dec(v_h__3_594_);
lean_dec(v_h__2_593_);
v_a_599_ = lean_ctor_get(v_e_591_, 0);
lean_inc_ref(v_a_599_);
lean_dec_ref(v_e_591_);
v___x_600_ = lean_apply_1(v_h__1_592_, v_a_599_);
return v___x_600_;
}
case 2:
{
lean_object* v_mvarId_601_; lean_object* v___x_602_; 
lean_dec(v_h__7_598_);
lean_dec(v_h__6_597_);
lean_dec(v_h__5_596_);
lean_dec(v_h__4_595_);
lean_dec(v_h__3_594_);
lean_dec(v_h__1_592_);
v_mvarId_601_ = lean_ctor_get(v_e_591_, 0);
lean_inc(v_mvarId_601_);
lean_dec_ref(v_e_591_);
v___x_602_ = lean_apply_1(v_h__2_593_, v_mvarId_601_);
return v___x_602_;
}
case 0:
{
lean_object* v_deBruijnIndex_603_; lean_object* v___x_604_; 
lean_dec(v_h__7_598_);
lean_dec(v_h__6_597_);
lean_dec(v_h__5_596_);
lean_dec(v_h__4_595_);
lean_dec(v_h__2_593_);
lean_dec(v_h__1_592_);
v_deBruijnIndex_603_ = lean_ctor_get(v_e_591_, 0);
lean_inc(v_deBruijnIndex_603_);
lean_dec_ref(v_e_591_);
v___x_604_ = lean_apply_1(v_h__3_594_, v_deBruijnIndex_603_);
return v___x_604_;
}
case 1:
{
lean_object* v_fvarId_605_; lean_object* v___x_606_; 
lean_dec(v_h__7_598_);
lean_dec(v_h__6_597_);
lean_dec(v_h__5_596_);
lean_dec(v_h__3_594_);
lean_dec(v_h__2_593_);
lean_dec(v_h__1_592_);
v_fvarId_605_ = lean_ctor_get(v_e_591_, 0);
lean_inc(v_fvarId_605_);
lean_dec_ref(v_e_591_);
v___x_606_ = lean_apply_1(v_h__4_595_, v_fvarId_605_);
return v___x_606_;
}
case 4:
{
lean_object* v_declName_607_; lean_object* v_us_608_; lean_object* v___x_609_; 
lean_dec(v_h__7_598_);
lean_dec(v_h__6_597_);
lean_dec(v_h__4_595_);
lean_dec(v_h__3_594_);
lean_dec(v_h__2_593_);
lean_dec(v_h__1_592_);
v_declName_607_ = lean_ctor_get(v_e_591_, 0);
lean_inc(v_declName_607_);
v_us_608_ = lean_ctor_get(v_e_591_, 1);
lean_inc(v_us_608_);
lean_dec_ref(v_e_591_);
v___x_609_ = lean_apply_2(v_h__5_596_, v_declName_607_, v_us_608_);
return v___x_609_;
}
case 3:
{
lean_object* v_u_610_; lean_object* v___x_611_; 
lean_dec(v_h__7_598_);
lean_dec(v_h__5_596_);
lean_dec(v_h__4_595_);
lean_dec(v_h__3_594_);
lean_dec(v_h__2_593_);
lean_dec(v_h__1_592_);
v_u_610_ = lean_ctor_get(v_e_591_, 0);
lean_inc(v_u_610_);
lean_dec_ref(v_e_591_);
v___x_611_ = lean_apply_1(v_h__6_597_, v_u_610_);
return v___x_611_;
}
default: 
{
lean_object* v___x_612_; 
lean_dec(v_h__6_597_);
lean_dec(v_h__5_596_);
lean_dec(v_h__4_595_);
lean_dec(v_h__3_594_);
lean_dec(v_h__2_593_);
lean_dec(v_h__1_592_);
v___x_612_ = lean_apply_7(v_h__7_598_, v_e_591_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_612_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild_match__1_splitter(lean_object* v_motive_613_, lean_object* v_e_614_, lean_object* v_h__1_615_, lean_object* v_h__2_616_, lean_object* v_h__3_617_, lean_object* v_h__4_618_, lean_object* v_h__5_619_, lean_object* v_h__6_620_, lean_object* v_h__7_621_){
_start:
{
switch(lean_obj_tag(v_e_614_))
{
case 9:
{
lean_object* v_a_622_; lean_object* v___x_623_; 
lean_dec(v_h__7_621_);
lean_dec(v_h__6_620_);
lean_dec(v_h__5_619_);
lean_dec(v_h__4_618_);
lean_dec(v_h__3_617_);
lean_dec(v_h__2_616_);
v_a_622_ = lean_ctor_get(v_e_614_, 0);
lean_inc_ref(v_a_622_);
lean_dec_ref(v_e_614_);
v___x_623_ = lean_apply_1(v_h__1_615_, v_a_622_);
return v___x_623_;
}
case 2:
{
lean_object* v_mvarId_624_; lean_object* v___x_625_; 
lean_dec(v_h__7_621_);
lean_dec(v_h__6_620_);
lean_dec(v_h__5_619_);
lean_dec(v_h__4_618_);
lean_dec(v_h__3_617_);
lean_dec(v_h__1_615_);
v_mvarId_624_ = lean_ctor_get(v_e_614_, 0);
lean_inc(v_mvarId_624_);
lean_dec_ref(v_e_614_);
v___x_625_ = lean_apply_1(v_h__2_616_, v_mvarId_624_);
return v___x_625_;
}
case 0:
{
lean_object* v_deBruijnIndex_626_; lean_object* v___x_627_; 
lean_dec(v_h__7_621_);
lean_dec(v_h__6_620_);
lean_dec(v_h__5_619_);
lean_dec(v_h__4_618_);
lean_dec(v_h__2_616_);
lean_dec(v_h__1_615_);
v_deBruijnIndex_626_ = lean_ctor_get(v_e_614_, 0);
lean_inc(v_deBruijnIndex_626_);
lean_dec_ref(v_e_614_);
v___x_627_ = lean_apply_1(v_h__3_617_, v_deBruijnIndex_626_);
return v___x_627_;
}
case 1:
{
lean_object* v_fvarId_628_; lean_object* v___x_629_; 
lean_dec(v_h__7_621_);
lean_dec(v_h__6_620_);
lean_dec(v_h__5_619_);
lean_dec(v_h__3_617_);
lean_dec(v_h__2_616_);
lean_dec(v_h__1_615_);
v_fvarId_628_ = lean_ctor_get(v_e_614_, 0);
lean_inc(v_fvarId_628_);
lean_dec_ref(v_e_614_);
v___x_629_ = lean_apply_1(v_h__4_618_, v_fvarId_628_);
return v___x_629_;
}
case 4:
{
lean_object* v_declName_630_; lean_object* v_us_631_; lean_object* v___x_632_; 
lean_dec(v_h__7_621_);
lean_dec(v_h__6_620_);
lean_dec(v_h__4_618_);
lean_dec(v_h__3_617_);
lean_dec(v_h__2_616_);
lean_dec(v_h__1_615_);
v_declName_630_ = lean_ctor_get(v_e_614_, 0);
lean_inc(v_declName_630_);
v_us_631_ = lean_ctor_get(v_e_614_, 1);
lean_inc(v_us_631_);
lean_dec_ref(v_e_614_);
v___x_632_ = lean_apply_2(v_h__5_619_, v_declName_630_, v_us_631_);
return v___x_632_;
}
case 3:
{
lean_object* v_u_633_; lean_object* v___x_634_; 
lean_dec(v_h__7_621_);
lean_dec(v_h__5_619_);
lean_dec(v_h__4_618_);
lean_dec(v_h__3_617_);
lean_dec(v_h__2_616_);
lean_dec(v_h__1_615_);
v_u_633_ = lean_ctor_get(v_e_614_, 0);
lean_inc(v_u_633_);
lean_dec_ref(v_e_614_);
v___x_634_ = lean_apply_1(v_h__6_620_, v_u_633_);
return v___x_634_;
}
default: 
{
lean_object* v___x_635_; 
lean_dec(v_h__6_620_);
lean_dec(v_h__5_619_);
lean_dec(v_h__4_618_);
lean_dec(v_h__3_617_);
lean_dec(v_h__2_616_);
lean_dec(v_h__1_615_);
v___x_635_ = lean_apply_7(v_h__7_621_, v_e_614_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_635_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit_match__1_splitter___redArg(lean_object* v_e_636_, lean_object* v_h__1_637_, lean_object* v_h__2_638_, lean_object* v_h__3_639_, lean_object* v_h__4_640_, lean_object* v_h__5_641_, lean_object* v_h__6_642_, lean_object* v_h__7_643_, lean_object* v_h__8_644_, lean_object* v_h__9_645_, lean_object* v_h__10_646_, lean_object* v_h__11_647_, lean_object* v_h__12_648_){
_start:
{
switch(lean_obj_tag(v_e_636_))
{
case 0:
{
lean_object* v_deBruijnIndex_649_; lean_object* v___x_650_; 
lean_dec(v_h__12_648_);
lean_dec(v_h__11_647_);
lean_dec(v_h__10_646_);
lean_dec(v_h__9_645_);
lean_dec(v_h__8_644_);
lean_dec(v_h__7_643_);
lean_dec(v_h__6_642_);
lean_dec(v_h__5_641_);
lean_dec(v_h__4_640_);
lean_dec(v_h__2_638_);
lean_dec(v_h__1_637_);
v_deBruijnIndex_649_ = lean_ctor_get(v_e_636_, 0);
lean_inc(v_deBruijnIndex_649_);
lean_dec_ref(v_e_636_);
v___x_650_ = lean_apply_1(v_h__3_639_, v_deBruijnIndex_649_);
return v___x_650_;
}
case 1:
{
lean_object* v_fvarId_651_; lean_object* v___x_652_; 
lean_dec(v_h__12_648_);
lean_dec(v_h__11_647_);
lean_dec(v_h__10_646_);
lean_dec(v_h__9_645_);
lean_dec(v_h__8_644_);
lean_dec(v_h__7_643_);
lean_dec(v_h__6_642_);
lean_dec(v_h__5_641_);
lean_dec(v_h__3_639_);
lean_dec(v_h__2_638_);
lean_dec(v_h__1_637_);
v_fvarId_651_ = lean_ctor_get(v_e_636_, 0);
lean_inc(v_fvarId_651_);
lean_dec_ref(v_e_636_);
v___x_652_ = lean_apply_1(v_h__4_640_, v_fvarId_651_);
return v___x_652_;
}
case 2:
{
lean_object* v_mvarId_653_; lean_object* v___x_654_; 
lean_dec(v_h__12_648_);
lean_dec(v_h__11_647_);
lean_dec(v_h__10_646_);
lean_dec(v_h__9_645_);
lean_dec(v_h__8_644_);
lean_dec(v_h__7_643_);
lean_dec(v_h__6_642_);
lean_dec(v_h__5_641_);
lean_dec(v_h__4_640_);
lean_dec(v_h__3_639_);
lean_dec(v_h__1_637_);
v_mvarId_653_ = lean_ctor_get(v_e_636_, 0);
lean_inc(v_mvarId_653_);
lean_dec_ref(v_e_636_);
v___x_654_ = lean_apply_1(v_h__2_638_, v_mvarId_653_);
return v___x_654_;
}
case 3:
{
lean_object* v_u_655_; lean_object* v___x_656_; 
lean_dec(v_h__12_648_);
lean_dec(v_h__11_647_);
lean_dec(v_h__10_646_);
lean_dec(v_h__9_645_);
lean_dec(v_h__8_644_);
lean_dec(v_h__7_643_);
lean_dec(v_h__5_641_);
lean_dec(v_h__4_640_);
lean_dec(v_h__3_639_);
lean_dec(v_h__2_638_);
lean_dec(v_h__1_637_);
v_u_655_ = lean_ctor_get(v_e_636_, 0);
lean_inc(v_u_655_);
lean_dec_ref(v_e_636_);
v___x_656_ = lean_apply_1(v_h__6_642_, v_u_655_);
return v___x_656_;
}
case 4:
{
lean_object* v_declName_657_; lean_object* v_us_658_; lean_object* v___x_659_; 
lean_dec(v_h__12_648_);
lean_dec(v_h__11_647_);
lean_dec(v_h__10_646_);
lean_dec(v_h__9_645_);
lean_dec(v_h__8_644_);
lean_dec(v_h__7_643_);
lean_dec(v_h__6_642_);
lean_dec(v_h__4_640_);
lean_dec(v_h__3_639_);
lean_dec(v_h__2_638_);
lean_dec(v_h__1_637_);
v_declName_657_ = lean_ctor_get(v_e_636_, 0);
lean_inc(v_declName_657_);
v_us_658_ = lean_ctor_get(v_e_636_, 1);
lean_inc(v_us_658_);
lean_dec_ref(v_e_636_);
v___x_659_ = lean_apply_2(v_h__5_641_, v_declName_657_, v_us_658_);
return v___x_659_;
}
case 5:
{
lean_object* v_fn_660_; lean_object* v_arg_661_; lean_object* v___x_662_; 
lean_dec(v_h__12_648_);
lean_dec(v_h__11_647_);
lean_dec(v_h__10_646_);
lean_dec(v_h__9_645_);
lean_dec(v_h__8_644_);
lean_dec(v_h__6_642_);
lean_dec(v_h__5_641_);
lean_dec(v_h__4_640_);
lean_dec(v_h__3_639_);
lean_dec(v_h__2_638_);
lean_dec(v_h__1_637_);
v_fn_660_ = lean_ctor_get(v_e_636_, 0);
lean_inc_ref(v_fn_660_);
v_arg_661_ = lean_ctor_get(v_e_636_, 1);
lean_inc_ref(v_arg_661_);
lean_dec_ref(v_e_636_);
v___x_662_ = lean_apply_2(v_h__7_643_, v_fn_660_, v_arg_661_);
return v___x_662_;
}
case 6:
{
lean_object* v_binderName_663_; lean_object* v_binderType_664_; lean_object* v_body_665_; uint8_t v_binderInfo_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
lean_dec(v_h__12_648_);
lean_dec(v_h__10_646_);
lean_dec(v_h__9_645_);
lean_dec(v_h__8_644_);
lean_dec(v_h__7_643_);
lean_dec(v_h__6_642_);
lean_dec(v_h__5_641_);
lean_dec(v_h__4_640_);
lean_dec(v_h__3_639_);
lean_dec(v_h__2_638_);
lean_dec(v_h__1_637_);
v_binderName_663_ = lean_ctor_get(v_e_636_, 0);
lean_inc(v_binderName_663_);
v_binderType_664_ = lean_ctor_get(v_e_636_, 1);
lean_inc_ref(v_binderType_664_);
v_body_665_ = lean_ctor_get(v_e_636_, 2);
lean_inc_ref(v_body_665_);
v_binderInfo_666_ = lean_ctor_get_uint8(v_e_636_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_636_);
v___x_667_ = lean_box(v_binderInfo_666_);
v___x_668_ = lean_apply_4(v_h__11_647_, v_binderName_663_, v_binderType_664_, v_body_665_, v___x_667_);
return v___x_668_;
}
case 7:
{
lean_object* v_binderName_669_; lean_object* v_binderType_670_; lean_object* v_body_671_; uint8_t v_binderInfo_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
lean_dec(v_h__12_648_);
lean_dec(v_h__11_647_);
lean_dec(v_h__9_645_);
lean_dec(v_h__8_644_);
lean_dec(v_h__7_643_);
lean_dec(v_h__6_642_);
lean_dec(v_h__5_641_);
lean_dec(v_h__4_640_);
lean_dec(v_h__3_639_);
lean_dec(v_h__2_638_);
lean_dec(v_h__1_637_);
v_binderName_669_ = lean_ctor_get(v_e_636_, 0);
lean_inc(v_binderName_669_);
v_binderType_670_ = lean_ctor_get(v_e_636_, 1);
lean_inc_ref(v_binderType_670_);
v_body_671_ = lean_ctor_get(v_e_636_, 2);
lean_inc_ref(v_body_671_);
v_binderInfo_672_ = lean_ctor_get_uint8(v_e_636_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_636_);
v___x_673_ = lean_box(v_binderInfo_672_);
v___x_674_ = lean_apply_4(v_h__10_646_, v_binderName_669_, v_binderType_670_, v_body_671_, v___x_673_);
return v___x_674_;
}
case 8:
{
lean_object* v_declName_675_; lean_object* v_type_676_; lean_object* v_value_677_; lean_object* v_body_678_; uint8_t v_nondep_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
lean_dec(v_h__11_647_);
lean_dec(v_h__10_646_);
lean_dec(v_h__9_645_);
lean_dec(v_h__8_644_);
lean_dec(v_h__7_643_);
lean_dec(v_h__6_642_);
lean_dec(v_h__5_641_);
lean_dec(v_h__4_640_);
lean_dec(v_h__3_639_);
lean_dec(v_h__2_638_);
lean_dec(v_h__1_637_);
v_declName_675_ = lean_ctor_get(v_e_636_, 0);
lean_inc(v_declName_675_);
v_type_676_ = lean_ctor_get(v_e_636_, 1);
lean_inc_ref(v_type_676_);
v_value_677_ = lean_ctor_get(v_e_636_, 2);
lean_inc_ref(v_value_677_);
v_body_678_ = lean_ctor_get(v_e_636_, 3);
lean_inc_ref(v_body_678_);
v_nondep_679_ = lean_ctor_get_uint8(v_e_636_, sizeof(void*)*4 + 8);
lean_dec_ref(v_e_636_);
v___x_680_ = lean_box(v_nondep_679_);
v___x_681_ = lean_apply_5(v_h__12_648_, v_declName_675_, v_type_676_, v_value_677_, v_body_678_, v___x_680_);
return v___x_681_;
}
case 9:
{
lean_object* v_a_682_; lean_object* v___x_683_; 
lean_dec(v_h__12_648_);
lean_dec(v_h__11_647_);
lean_dec(v_h__10_646_);
lean_dec(v_h__9_645_);
lean_dec(v_h__8_644_);
lean_dec(v_h__7_643_);
lean_dec(v_h__6_642_);
lean_dec(v_h__5_641_);
lean_dec(v_h__4_640_);
lean_dec(v_h__3_639_);
lean_dec(v_h__2_638_);
v_a_682_ = lean_ctor_get(v_e_636_, 0);
lean_inc_ref(v_a_682_);
lean_dec_ref(v_e_636_);
v___x_683_ = lean_apply_1(v_h__1_637_, v_a_682_);
return v___x_683_;
}
case 10:
{
lean_object* v_data_684_; lean_object* v_expr_685_; lean_object* v___x_686_; 
lean_dec(v_h__12_648_);
lean_dec(v_h__11_647_);
lean_dec(v_h__10_646_);
lean_dec(v_h__9_645_);
lean_dec(v_h__7_643_);
lean_dec(v_h__6_642_);
lean_dec(v_h__5_641_);
lean_dec(v_h__4_640_);
lean_dec(v_h__3_639_);
lean_dec(v_h__2_638_);
lean_dec(v_h__1_637_);
v_data_684_ = lean_ctor_get(v_e_636_, 0);
lean_inc(v_data_684_);
v_expr_685_ = lean_ctor_get(v_e_636_, 1);
lean_inc_ref(v_expr_685_);
lean_dec_ref(v_e_636_);
v___x_686_ = lean_apply_2(v_h__8_644_, v_data_684_, v_expr_685_);
return v___x_686_;
}
default: 
{
lean_object* v_typeName_687_; lean_object* v_idx_688_; lean_object* v_struct_689_; lean_object* v___x_690_; 
lean_dec(v_h__12_648_);
lean_dec(v_h__11_647_);
lean_dec(v_h__10_646_);
lean_dec(v_h__8_644_);
lean_dec(v_h__7_643_);
lean_dec(v_h__6_642_);
lean_dec(v_h__5_641_);
lean_dec(v_h__4_640_);
lean_dec(v_h__3_639_);
lean_dec(v_h__2_638_);
lean_dec(v_h__1_637_);
v_typeName_687_ = lean_ctor_get(v_e_636_, 0);
lean_inc(v_typeName_687_);
v_idx_688_ = lean_ctor_get(v_e_636_, 1);
lean_inc(v_idx_688_);
v_struct_689_ = lean_ctor_get(v_e_636_, 2);
lean_inc_ref(v_struct_689_);
lean_dec_ref(v_e_636_);
v___x_690_ = lean_apply_3(v_h__9_645_, v_typeName_687_, v_idx_688_, v_struct_689_);
return v___x_690_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit_match__1_splitter(lean_object* v_motive_691_, lean_object* v_e_692_, lean_object* v_h__1_693_, lean_object* v_h__2_694_, lean_object* v_h__3_695_, lean_object* v_h__4_696_, lean_object* v_h__5_697_, lean_object* v_h__6_698_, lean_object* v_h__7_699_, lean_object* v_h__8_700_, lean_object* v_h__9_701_, lean_object* v_h__10_702_, lean_object* v_h__11_703_, lean_object* v_h__12_704_){
_start:
{
switch(lean_obj_tag(v_e_692_))
{
case 0:
{
lean_object* v_deBruijnIndex_705_; lean_object* v___x_706_; 
lean_dec(v_h__12_704_);
lean_dec(v_h__11_703_);
lean_dec(v_h__10_702_);
lean_dec(v_h__9_701_);
lean_dec(v_h__8_700_);
lean_dec(v_h__7_699_);
lean_dec(v_h__6_698_);
lean_dec(v_h__5_697_);
lean_dec(v_h__4_696_);
lean_dec(v_h__2_694_);
lean_dec(v_h__1_693_);
v_deBruijnIndex_705_ = lean_ctor_get(v_e_692_, 0);
lean_inc(v_deBruijnIndex_705_);
lean_dec_ref(v_e_692_);
v___x_706_ = lean_apply_1(v_h__3_695_, v_deBruijnIndex_705_);
return v___x_706_;
}
case 1:
{
lean_object* v_fvarId_707_; lean_object* v___x_708_; 
lean_dec(v_h__12_704_);
lean_dec(v_h__11_703_);
lean_dec(v_h__10_702_);
lean_dec(v_h__9_701_);
lean_dec(v_h__8_700_);
lean_dec(v_h__7_699_);
lean_dec(v_h__6_698_);
lean_dec(v_h__5_697_);
lean_dec(v_h__3_695_);
lean_dec(v_h__2_694_);
lean_dec(v_h__1_693_);
v_fvarId_707_ = lean_ctor_get(v_e_692_, 0);
lean_inc(v_fvarId_707_);
lean_dec_ref(v_e_692_);
v___x_708_ = lean_apply_1(v_h__4_696_, v_fvarId_707_);
return v___x_708_;
}
case 2:
{
lean_object* v_mvarId_709_; lean_object* v___x_710_; 
lean_dec(v_h__12_704_);
lean_dec(v_h__11_703_);
lean_dec(v_h__10_702_);
lean_dec(v_h__9_701_);
lean_dec(v_h__8_700_);
lean_dec(v_h__7_699_);
lean_dec(v_h__6_698_);
lean_dec(v_h__5_697_);
lean_dec(v_h__4_696_);
lean_dec(v_h__3_695_);
lean_dec(v_h__1_693_);
v_mvarId_709_ = lean_ctor_get(v_e_692_, 0);
lean_inc(v_mvarId_709_);
lean_dec_ref(v_e_692_);
v___x_710_ = lean_apply_1(v_h__2_694_, v_mvarId_709_);
return v___x_710_;
}
case 3:
{
lean_object* v_u_711_; lean_object* v___x_712_; 
lean_dec(v_h__12_704_);
lean_dec(v_h__11_703_);
lean_dec(v_h__10_702_);
lean_dec(v_h__9_701_);
lean_dec(v_h__8_700_);
lean_dec(v_h__7_699_);
lean_dec(v_h__5_697_);
lean_dec(v_h__4_696_);
lean_dec(v_h__3_695_);
lean_dec(v_h__2_694_);
lean_dec(v_h__1_693_);
v_u_711_ = lean_ctor_get(v_e_692_, 0);
lean_inc(v_u_711_);
lean_dec_ref(v_e_692_);
v___x_712_ = lean_apply_1(v_h__6_698_, v_u_711_);
return v___x_712_;
}
case 4:
{
lean_object* v_declName_713_; lean_object* v_us_714_; lean_object* v___x_715_; 
lean_dec(v_h__12_704_);
lean_dec(v_h__11_703_);
lean_dec(v_h__10_702_);
lean_dec(v_h__9_701_);
lean_dec(v_h__8_700_);
lean_dec(v_h__7_699_);
lean_dec(v_h__6_698_);
lean_dec(v_h__4_696_);
lean_dec(v_h__3_695_);
lean_dec(v_h__2_694_);
lean_dec(v_h__1_693_);
v_declName_713_ = lean_ctor_get(v_e_692_, 0);
lean_inc(v_declName_713_);
v_us_714_ = lean_ctor_get(v_e_692_, 1);
lean_inc(v_us_714_);
lean_dec_ref(v_e_692_);
v___x_715_ = lean_apply_2(v_h__5_697_, v_declName_713_, v_us_714_);
return v___x_715_;
}
case 5:
{
lean_object* v_fn_716_; lean_object* v_arg_717_; lean_object* v___x_718_; 
lean_dec(v_h__12_704_);
lean_dec(v_h__11_703_);
lean_dec(v_h__10_702_);
lean_dec(v_h__9_701_);
lean_dec(v_h__8_700_);
lean_dec(v_h__6_698_);
lean_dec(v_h__5_697_);
lean_dec(v_h__4_696_);
lean_dec(v_h__3_695_);
lean_dec(v_h__2_694_);
lean_dec(v_h__1_693_);
v_fn_716_ = lean_ctor_get(v_e_692_, 0);
lean_inc_ref(v_fn_716_);
v_arg_717_ = lean_ctor_get(v_e_692_, 1);
lean_inc_ref(v_arg_717_);
lean_dec_ref(v_e_692_);
v___x_718_ = lean_apply_2(v_h__7_699_, v_fn_716_, v_arg_717_);
return v___x_718_;
}
case 6:
{
lean_object* v_binderName_719_; lean_object* v_binderType_720_; lean_object* v_body_721_; uint8_t v_binderInfo_722_; lean_object* v___x_723_; lean_object* v___x_724_; 
lean_dec(v_h__12_704_);
lean_dec(v_h__10_702_);
lean_dec(v_h__9_701_);
lean_dec(v_h__8_700_);
lean_dec(v_h__7_699_);
lean_dec(v_h__6_698_);
lean_dec(v_h__5_697_);
lean_dec(v_h__4_696_);
lean_dec(v_h__3_695_);
lean_dec(v_h__2_694_);
lean_dec(v_h__1_693_);
v_binderName_719_ = lean_ctor_get(v_e_692_, 0);
lean_inc(v_binderName_719_);
v_binderType_720_ = lean_ctor_get(v_e_692_, 1);
lean_inc_ref(v_binderType_720_);
v_body_721_ = lean_ctor_get(v_e_692_, 2);
lean_inc_ref(v_body_721_);
v_binderInfo_722_ = lean_ctor_get_uint8(v_e_692_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_692_);
v___x_723_ = lean_box(v_binderInfo_722_);
v___x_724_ = lean_apply_4(v_h__11_703_, v_binderName_719_, v_binderType_720_, v_body_721_, v___x_723_);
return v___x_724_;
}
case 7:
{
lean_object* v_binderName_725_; lean_object* v_binderType_726_; lean_object* v_body_727_; uint8_t v_binderInfo_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
lean_dec(v_h__12_704_);
lean_dec(v_h__11_703_);
lean_dec(v_h__9_701_);
lean_dec(v_h__8_700_);
lean_dec(v_h__7_699_);
lean_dec(v_h__6_698_);
lean_dec(v_h__5_697_);
lean_dec(v_h__4_696_);
lean_dec(v_h__3_695_);
lean_dec(v_h__2_694_);
lean_dec(v_h__1_693_);
v_binderName_725_ = lean_ctor_get(v_e_692_, 0);
lean_inc(v_binderName_725_);
v_binderType_726_ = lean_ctor_get(v_e_692_, 1);
lean_inc_ref(v_binderType_726_);
v_body_727_ = lean_ctor_get(v_e_692_, 2);
lean_inc_ref(v_body_727_);
v_binderInfo_728_ = lean_ctor_get_uint8(v_e_692_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_692_);
v___x_729_ = lean_box(v_binderInfo_728_);
v___x_730_ = lean_apply_4(v_h__10_702_, v_binderName_725_, v_binderType_726_, v_body_727_, v___x_729_);
return v___x_730_;
}
case 8:
{
lean_object* v_declName_731_; lean_object* v_type_732_; lean_object* v_value_733_; lean_object* v_body_734_; uint8_t v_nondep_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
lean_dec(v_h__11_703_);
lean_dec(v_h__10_702_);
lean_dec(v_h__9_701_);
lean_dec(v_h__8_700_);
lean_dec(v_h__7_699_);
lean_dec(v_h__6_698_);
lean_dec(v_h__5_697_);
lean_dec(v_h__4_696_);
lean_dec(v_h__3_695_);
lean_dec(v_h__2_694_);
lean_dec(v_h__1_693_);
v_declName_731_ = lean_ctor_get(v_e_692_, 0);
lean_inc(v_declName_731_);
v_type_732_ = lean_ctor_get(v_e_692_, 1);
lean_inc_ref(v_type_732_);
v_value_733_ = lean_ctor_get(v_e_692_, 2);
lean_inc_ref(v_value_733_);
v_body_734_ = lean_ctor_get(v_e_692_, 3);
lean_inc_ref(v_body_734_);
v_nondep_735_ = lean_ctor_get_uint8(v_e_692_, sizeof(void*)*4 + 8);
lean_dec_ref(v_e_692_);
v___x_736_ = lean_box(v_nondep_735_);
v___x_737_ = lean_apply_5(v_h__12_704_, v_declName_731_, v_type_732_, v_value_733_, v_body_734_, v___x_736_);
return v___x_737_;
}
case 9:
{
lean_object* v_a_738_; lean_object* v___x_739_; 
lean_dec(v_h__12_704_);
lean_dec(v_h__11_703_);
lean_dec(v_h__10_702_);
lean_dec(v_h__9_701_);
lean_dec(v_h__8_700_);
lean_dec(v_h__7_699_);
lean_dec(v_h__6_698_);
lean_dec(v_h__5_697_);
lean_dec(v_h__4_696_);
lean_dec(v_h__3_695_);
lean_dec(v_h__2_694_);
v_a_738_ = lean_ctor_get(v_e_692_, 0);
lean_inc_ref(v_a_738_);
lean_dec_ref(v_e_692_);
v___x_739_ = lean_apply_1(v_h__1_693_, v_a_738_);
return v___x_739_;
}
case 10:
{
lean_object* v_data_740_; lean_object* v_expr_741_; lean_object* v___x_742_; 
lean_dec(v_h__12_704_);
lean_dec(v_h__11_703_);
lean_dec(v_h__10_702_);
lean_dec(v_h__9_701_);
lean_dec(v_h__7_699_);
lean_dec(v_h__6_698_);
lean_dec(v_h__5_697_);
lean_dec(v_h__4_696_);
lean_dec(v_h__3_695_);
lean_dec(v_h__2_694_);
lean_dec(v_h__1_693_);
v_data_740_ = lean_ctor_get(v_e_692_, 0);
lean_inc(v_data_740_);
v_expr_741_ = lean_ctor_get(v_e_692_, 1);
lean_inc_ref(v_expr_741_);
lean_dec_ref(v_e_692_);
v___x_742_ = lean_apply_2(v_h__8_700_, v_data_740_, v_expr_741_);
return v___x_742_;
}
default: 
{
lean_object* v_typeName_743_; lean_object* v_idx_744_; lean_object* v_struct_745_; lean_object* v___x_746_; 
lean_dec(v_h__12_704_);
lean_dec(v_h__11_703_);
lean_dec(v_h__10_702_);
lean_dec(v_h__8_700_);
lean_dec(v_h__7_699_);
lean_dec(v_h__6_698_);
lean_dec(v_h__5_697_);
lean_dec(v_h__4_696_);
lean_dec(v_h__3_695_);
lean_dec(v_h__2_694_);
lean_dec(v_h__1_693_);
v_typeName_743_ = lean_ctor_get(v_e_692_, 0);
lean_inc(v_typeName_743_);
v_idx_744_ = lean_ctor_get(v_e_692_, 1);
lean_inc(v_idx_744_);
v_struct_745_ = lean_ctor_get(v_e_692_, 2);
lean_inc_ref(v_struct_745_);
lean_dec_ref(v_e_692_);
v___x_746_ = lean_apply_3(v_h__9_701_, v_typeName_743_, v_idx_744_, v_struct_745_);
return v___x_746_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Sym_replaceS_x27___closed__0(void){
_start:
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_747_ = lean_box(0);
v___x_748_ = lean_unsigned_to_nat(16u);
v___x_749_ = lean_mk_array(v___x_748_, v___x_747_);
return v___x_749_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_replaceS_x27___closed__1(void){
_start:
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_750_ = lean_obj_once(&l_Lean_Meta_Sym_replaceS_x27___closed__0, &l_Lean_Meta_Sym_replaceS_x27___closed__0_once, _init_l_Lean_Meta_Sym_replaceS_x27___closed__0);
v___x_751_ = lean_unsigned_to_nat(0u);
v___x_752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_752_, 0, v___x_751_);
lean_ctor_set(v___x_752_, 1, v___x_750_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_replaceS_x27(lean_object* v_e_753_, lean_object* v_f_754_, uint8_t v_a_755_, lean_object* v_a_756_){
_start:
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v_fst_760_; 
v___x_757_ = lean_unsigned_to_nat(0u);
v___x_758_ = lean_box(v_a_755_);
lean_inc_ref(v_f_754_);
lean_inc_ref(v_e_753_);
v___x_759_ = lean_apply_4(v_f_754_, v_e_753_, v___x_757_, v___x_758_, v_a_756_);
v_fst_760_ = lean_ctor_get(v___x_759_, 0);
lean_inc(v_fst_760_);
if (lean_obj_tag(v_fst_760_) == 1)
{
lean_object* v_snd_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_769_; 
lean_dec_ref(v_f_754_);
lean_dec_ref(v_e_753_);
v_snd_761_ = lean_ctor_get(v___x_759_, 1);
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_769_ == 0)
{
lean_object* v_unused_770_; 
v_unused_770_ = lean_ctor_get(v___x_759_, 0);
lean_dec(v_unused_770_);
v___x_763_ = v___x_759_;
v_isShared_764_ = v_isSharedCheck_769_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_snd_761_);
lean_dec(v___x_759_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_769_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v_val_765_; lean_object* v___x_767_; 
v_val_765_ = lean_ctor_get(v_fst_760_, 0);
lean_inc(v_val_765_);
lean_dec_ref(v_fst_760_);
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 0, v_val_765_);
v___x_767_ = v___x_763_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_val_765_);
lean_ctor_set(v_reuseFailAlloc_768_, 1, v_snd_761_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
else
{
lean_dec(v_fst_760_);
switch(lean_obj_tag(v_e_753_))
{
case 9:
{
lean_object* v_snd_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_778_; 
lean_dec_ref(v_f_754_);
v_snd_771_ = lean_ctor_get(v___x_759_, 1);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_778_ == 0)
{
lean_object* v_unused_779_; 
v_unused_779_ = lean_ctor_get(v___x_759_, 0);
lean_dec(v_unused_779_);
v___x_773_ = v___x_759_;
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_snd_771_);
lean_dec(v___x_759_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_776_; 
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 0, v_e_753_);
v___x_776_ = v___x_773_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_e_753_);
lean_ctor_set(v_reuseFailAlloc_777_, 1, v_snd_771_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
case 2:
{
lean_object* v_snd_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_787_; 
lean_dec_ref(v_f_754_);
v_snd_780_ = lean_ctor_get(v___x_759_, 1);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_787_ == 0)
{
lean_object* v_unused_788_; 
v_unused_788_ = lean_ctor_get(v___x_759_, 0);
lean_dec(v_unused_788_);
v___x_782_ = v___x_759_;
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_snd_780_);
lean_dec(v___x_759_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_785_; 
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 0, v_e_753_);
v___x_785_ = v___x_782_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_e_753_);
lean_ctor_set(v_reuseFailAlloc_786_, 1, v_snd_780_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
case 0:
{
lean_object* v_snd_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_796_; 
lean_dec_ref(v_f_754_);
v_snd_789_ = lean_ctor_get(v___x_759_, 1);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_796_ == 0)
{
lean_object* v_unused_797_; 
v_unused_797_ = lean_ctor_get(v___x_759_, 0);
lean_dec(v_unused_797_);
v___x_791_ = v___x_759_;
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_snd_789_);
lean_dec(v___x_759_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_794_; 
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 0, v_e_753_);
v___x_794_ = v___x_791_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_e_753_);
lean_ctor_set(v_reuseFailAlloc_795_, 1, v_snd_789_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
case 1:
{
lean_object* v_snd_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_805_; 
lean_dec_ref(v_f_754_);
v_snd_798_ = lean_ctor_get(v___x_759_, 1);
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_805_ == 0)
{
lean_object* v_unused_806_; 
v_unused_806_ = lean_ctor_get(v___x_759_, 0);
lean_dec(v_unused_806_);
v___x_800_ = v___x_759_;
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_snd_798_);
lean_dec(v___x_759_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_803_; 
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 0, v_e_753_);
v___x_803_ = v___x_800_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_e_753_);
lean_ctor_set(v_reuseFailAlloc_804_, 1, v_snd_798_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
}
case 4:
{
lean_object* v_snd_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_814_; 
lean_dec_ref(v_f_754_);
v_snd_807_ = lean_ctor_get(v___x_759_, 1);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_814_ == 0)
{
lean_object* v_unused_815_; 
v_unused_815_ = lean_ctor_get(v___x_759_, 0);
lean_dec(v_unused_815_);
v___x_809_ = v___x_759_;
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_snd_807_);
lean_dec(v___x_759_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_812_; 
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 0, v_e_753_);
v___x_812_ = v___x_809_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_e_753_);
lean_ctor_set(v_reuseFailAlloc_813_, 1, v_snd_807_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
}
}
}
case 3:
{
lean_object* v_snd_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_823_; 
lean_dec_ref(v_f_754_);
v_snd_816_ = lean_ctor_get(v___x_759_, 1);
v_isSharedCheck_823_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_823_ == 0)
{
lean_object* v_unused_824_; 
v_unused_824_ = lean_ctor_get(v___x_759_, 0);
lean_dec(v_unused_824_);
v___x_818_ = v___x_759_;
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_snd_816_);
lean_dec(v___x_759_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v___x_821_; 
if (v_isShared_819_ == 0)
{
lean_ctor_set(v___x_818_, 0, v_e_753_);
v___x_821_ = v___x_818_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v_e_753_);
lean_ctor_set(v_reuseFailAlloc_822_, 1, v_snd_816_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
}
default: 
{
lean_object* v_snd_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v_fst_828_; lean_object* v_snd_829_; lean_object* v_fst_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_837_; 
v_snd_825_ = lean_ctor_get(v___x_759_, 1);
lean_inc(v_snd_825_);
lean_dec_ref(v___x_759_);
v___x_826_ = lean_obj_once(&l_Lean_Meta_Sym_replaceS_x27___closed__1, &l_Lean_Meta_Sym_replaceS_x27___closed__1_once, _init_l_Lean_Meta_Sym_replaceS_x27___closed__1);
v___x_827_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit(v_e_753_, v___x_757_, v_f_754_, v___x_826_, v_a_755_, v_snd_825_);
v_fst_828_ = lean_ctor_get(v___x_827_, 0);
lean_inc(v_fst_828_);
v_snd_829_ = lean_ctor_get(v___x_827_, 1);
lean_inc(v_snd_829_);
lean_dec_ref(v___x_827_);
v_fst_830_ = lean_ctor_get(v_fst_828_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v_fst_828_);
if (v_isSharedCheck_837_ == 0)
{
lean_object* v_unused_838_; 
v_unused_838_ = lean_ctor_get(v_fst_828_, 1);
lean_dec(v_unused_838_);
v___x_832_ = v_fst_828_;
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_fst_830_);
lean_dec(v_fst_828_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_835_; 
if (v_isShared_833_ == 0)
{
lean_ctor_set(v___x_832_, 1, v_snd_829_);
v___x_835_ = v___x_832_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_fst_830_);
lean_ctor_set(v_reuseFailAlloc_836_, 1, v_snd_829_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_replaceS_x27___boxed(lean_object* v_e_839_, lean_object* v_f_840_, lean_object* v_a_841_, lean_object* v_a_842_){
_start:
{
uint8_t v_a_boxed_843_; lean_object* v_res_844_; 
v_a_boxed_843_ = lean_unbox(v_a_841_);
v_res_844_ = l_Lean_Meta_Sym_replaceS_x27(v_e_839_, v_f_840_, v_a_boxed_843_, v_a_842_);
return v_res_844_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_replaceS___redArg___closed__2(void){
_start:
{
lean_object* v___f_847_; lean_object* v___f_848_; lean_object* v___x_849_; 
v___f_847_ = ((lean_object*)(l_Lean_Meta_Sym_replaceS___redArg___closed__1));
v___f_848_ = ((lean_object*)(l_Lean_Meta_Sym_replaceS___redArg___closed__0));
v___x_849_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___f_848_, v___f_847_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_replaceS___redArg(lean_object* v_e_850_, lean_object* v_f_851_, lean_object* v_a_852_){
_start:
{
lean_object* v___x_854_; lean_object* v_share_855_; lean_object* v_maxFVar_856_; lean_object* v_proofInstInfo_857_; lean_object* v_inferType_858_; lean_object* v_getLevel_859_; lean_object* v_congrInfo_860_; lean_object* v_defEqI_861_; lean_object* v_extensions_862_; lean_object* v_issues_863_; lean_object* v_canon_864_; uint8_t v_debug_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_918_; 
v___x_854_ = lean_st_ref_take(v_a_852_);
v_share_855_ = lean_ctor_get(v___x_854_, 0);
v_maxFVar_856_ = lean_ctor_get(v___x_854_, 1);
v_proofInstInfo_857_ = lean_ctor_get(v___x_854_, 2);
v_inferType_858_ = lean_ctor_get(v___x_854_, 3);
v_getLevel_859_ = lean_ctor_get(v___x_854_, 4);
v_congrInfo_860_ = lean_ctor_get(v___x_854_, 5);
v_defEqI_861_ = lean_ctor_get(v___x_854_, 6);
v_extensions_862_ = lean_ctor_get(v___x_854_, 7);
v_issues_863_ = lean_ctor_get(v___x_854_, 8);
v_canon_864_ = lean_ctor_get(v___x_854_, 9);
v_debug_865_ = lean_ctor_get_uint8(v___x_854_, sizeof(void*)*10);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_918_ == 0)
{
v___x_867_ = v___x_854_;
v_isShared_868_ = v_isSharedCheck_918_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_canon_864_);
lean_inc(v_issues_863_);
lean_inc(v_extensions_862_);
lean_inc(v_defEqI_861_);
lean_inc(v_congrInfo_860_);
lean_inc(v_getLevel_859_);
lean_inc(v_inferType_858_);
lean_inc(v_proofInstInfo_857_);
lean_inc(v_maxFVar_856_);
lean_inc(v_share_855_);
lean_dec(v___x_854_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_918_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_869_; lean_object* v___x_871_; 
v___x_869_ = lean_obj_once(&l_Lean_Meta_Sym_replaceS___redArg___closed__2, &l_Lean_Meta_Sym_replaceS___redArg___closed__2_once, _init_l_Lean_Meta_Sym_replaceS___redArg___closed__2);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 0, v___x_869_);
v___x_871_ = v___x_867_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v___x_869_);
lean_ctor_set(v_reuseFailAlloc_917_, 1, v_maxFVar_856_);
lean_ctor_set(v_reuseFailAlloc_917_, 2, v_proofInstInfo_857_);
lean_ctor_set(v_reuseFailAlloc_917_, 3, v_inferType_858_);
lean_ctor_set(v_reuseFailAlloc_917_, 4, v_getLevel_859_);
lean_ctor_set(v_reuseFailAlloc_917_, 5, v_congrInfo_860_);
lean_ctor_set(v_reuseFailAlloc_917_, 6, v_defEqI_861_);
lean_ctor_set(v_reuseFailAlloc_917_, 7, v_extensions_862_);
lean_ctor_set(v_reuseFailAlloc_917_, 8, v_issues_863_);
lean_ctor_set(v_reuseFailAlloc_917_, 9, v_canon_864_);
lean_ctor_set_uint8(v_reuseFailAlloc_917_, sizeof(void*)*10, v_debug_865_);
v___x_871_ = v_reuseFailAlloc_917_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v_fst_875_; lean_object* v_snd_876_; uint8_t v_debug_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v_fst_902_; 
v___x_872_ = lean_st_ref_set(v_a_852_, v___x_871_);
v___x_873_ = lean_st_ref_get(v_a_852_);
v_debug_898_ = lean_ctor_get_uint8(v___x_873_, sizeof(void*)*10);
lean_dec(v___x_873_);
v___x_899_ = lean_unsigned_to_nat(0u);
v___x_900_ = lean_box(v_debug_898_);
lean_inc_ref(v_f_851_);
lean_inc_ref(v_e_850_);
v___x_901_ = lean_apply_4(v_f_851_, v_e_850_, v___x_899_, v___x_900_, v_share_855_);
v_fst_902_ = lean_ctor_get(v___x_901_, 0);
lean_inc(v_fst_902_);
if (lean_obj_tag(v_fst_902_) == 1)
{
lean_object* v_snd_903_; lean_object* v_val_904_; 
lean_dec_ref(v_f_851_);
lean_dec_ref(v_e_850_);
v_snd_903_ = lean_ctor_get(v___x_901_, 1);
lean_inc(v_snd_903_);
lean_dec_ref(v___x_901_);
v_val_904_ = lean_ctor_get(v_fst_902_, 0);
lean_inc(v_val_904_);
lean_dec_ref(v_fst_902_);
v_fst_875_ = v_val_904_;
v_snd_876_ = v_snd_903_;
goto v___jp_874_;
}
else
{
lean_dec(v_fst_902_);
switch(lean_obj_tag(v_e_850_))
{
case 9:
{
lean_object* v_snd_905_; 
lean_dec_ref(v_f_851_);
v_snd_905_ = lean_ctor_get(v___x_901_, 1);
lean_inc(v_snd_905_);
lean_dec_ref(v___x_901_);
v_fst_875_ = v_e_850_;
v_snd_876_ = v_snd_905_;
goto v___jp_874_;
}
case 2:
{
lean_object* v_snd_906_; 
lean_dec_ref(v_f_851_);
v_snd_906_ = lean_ctor_get(v___x_901_, 1);
lean_inc(v_snd_906_);
lean_dec_ref(v___x_901_);
v_fst_875_ = v_e_850_;
v_snd_876_ = v_snd_906_;
goto v___jp_874_;
}
case 0:
{
lean_object* v_snd_907_; 
lean_dec_ref(v_f_851_);
v_snd_907_ = lean_ctor_get(v___x_901_, 1);
lean_inc(v_snd_907_);
lean_dec_ref(v___x_901_);
v_fst_875_ = v_e_850_;
v_snd_876_ = v_snd_907_;
goto v___jp_874_;
}
case 1:
{
lean_object* v_snd_908_; 
lean_dec_ref(v_f_851_);
v_snd_908_ = lean_ctor_get(v___x_901_, 1);
lean_inc(v_snd_908_);
lean_dec_ref(v___x_901_);
v_fst_875_ = v_e_850_;
v_snd_876_ = v_snd_908_;
goto v___jp_874_;
}
case 4:
{
lean_object* v_snd_909_; 
lean_dec_ref(v_f_851_);
v_snd_909_ = lean_ctor_get(v___x_901_, 1);
lean_inc(v_snd_909_);
lean_dec_ref(v___x_901_);
v_fst_875_ = v_e_850_;
v_snd_876_ = v_snd_909_;
goto v___jp_874_;
}
case 3:
{
lean_object* v_snd_910_; 
lean_dec_ref(v_f_851_);
v_snd_910_ = lean_ctor_get(v___x_901_, 1);
lean_inc(v_snd_910_);
lean_dec_ref(v___x_901_);
v_fst_875_ = v_e_850_;
v_snd_876_ = v_snd_910_;
goto v___jp_874_;
}
default: 
{
lean_object* v_snd_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v_fst_914_; lean_object* v_snd_915_; lean_object* v_fst_916_; 
v_snd_911_ = lean_ctor_get(v___x_901_, 1);
lean_inc(v_snd_911_);
lean_dec_ref(v___x_901_);
v___x_912_ = lean_obj_once(&l_Lean_Meta_Sym_replaceS_x27___closed__1, &l_Lean_Meta_Sym_replaceS_x27___closed__1_once, _init_l_Lean_Meta_Sym_replaceS_x27___closed__1);
v___x_913_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit(v_e_850_, v___x_899_, v_f_851_, v___x_912_, v_debug_898_, v_snd_911_);
v_fst_914_ = lean_ctor_get(v___x_913_, 0);
lean_inc(v_fst_914_);
v_snd_915_ = lean_ctor_get(v___x_913_, 1);
lean_inc(v_snd_915_);
lean_dec_ref(v___x_913_);
v_fst_916_ = lean_ctor_get(v_fst_914_, 0);
lean_inc(v_fst_916_);
lean_dec(v_fst_914_);
v_fst_875_ = v_fst_916_;
v_snd_876_ = v_snd_915_;
goto v___jp_874_;
}
}
}
v___jp_874_:
{
lean_object* v___x_877_; lean_object* v_maxFVar_878_; lean_object* v_proofInstInfo_879_; lean_object* v_inferType_880_; lean_object* v_getLevel_881_; lean_object* v_congrInfo_882_; lean_object* v_defEqI_883_; lean_object* v_extensions_884_; lean_object* v_issues_885_; lean_object* v_canon_886_; uint8_t v_debug_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_896_; 
v___x_877_ = lean_st_ref_take(v_a_852_);
v_maxFVar_878_ = lean_ctor_get(v___x_877_, 1);
v_proofInstInfo_879_ = lean_ctor_get(v___x_877_, 2);
v_inferType_880_ = lean_ctor_get(v___x_877_, 3);
v_getLevel_881_ = lean_ctor_get(v___x_877_, 4);
v_congrInfo_882_ = lean_ctor_get(v___x_877_, 5);
v_defEqI_883_ = lean_ctor_get(v___x_877_, 6);
v_extensions_884_ = lean_ctor_get(v___x_877_, 7);
v_issues_885_ = lean_ctor_get(v___x_877_, 8);
v_canon_886_ = lean_ctor_get(v___x_877_, 9);
v_debug_887_ = lean_ctor_get_uint8(v___x_877_, sizeof(void*)*10);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_877_);
if (v_isSharedCheck_896_ == 0)
{
lean_object* v_unused_897_; 
v_unused_897_ = lean_ctor_get(v___x_877_, 0);
lean_dec(v_unused_897_);
v___x_889_ = v___x_877_;
v_isShared_890_ = v_isSharedCheck_896_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_canon_886_);
lean_inc(v_issues_885_);
lean_inc(v_extensions_884_);
lean_inc(v_defEqI_883_);
lean_inc(v_congrInfo_882_);
lean_inc(v_getLevel_881_);
lean_inc(v_inferType_880_);
lean_inc(v_proofInstInfo_879_);
lean_inc(v_maxFVar_878_);
lean_dec(v___x_877_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_896_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_892_; 
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 0, v_snd_876_);
v___x_892_ = v___x_889_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_snd_876_);
lean_ctor_set(v_reuseFailAlloc_895_, 1, v_maxFVar_878_);
lean_ctor_set(v_reuseFailAlloc_895_, 2, v_proofInstInfo_879_);
lean_ctor_set(v_reuseFailAlloc_895_, 3, v_inferType_880_);
lean_ctor_set(v_reuseFailAlloc_895_, 4, v_getLevel_881_);
lean_ctor_set(v_reuseFailAlloc_895_, 5, v_congrInfo_882_);
lean_ctor_set(v_reuseFailAlloc_895_, 6, v_defEqI_883_);
lean_ctor_set(v_reuseFailAlloc_895_, 7, v_extensions_884_);
lean_ctor_set(v_reuseFailAlloc_895_, 8, v_issues_885_);
lean_ctor_set(v_reuseFailAlloc_895_, 9, v_canon_886_);
lean_ctor_set_uint8(v_reuseFailAlloc_895_, sizeof(void*)*10, v_debug_887_);
v___x_892_ = v_reuseFailAlloc_895_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_893_ = lean_st_ref_set(v_a_852_, v___x_892_);
v___x_894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_894_, 0, v_fst_875_);
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
lean_object* v___x_933_; lean_object* v_share_934_; lean_object* v_maxFVar_935_; lean_object* v_proofInstInfo_936_; lean_object* v_inferType_937_; lean_object* v_getLevel_938_; lean_object* v_congrInfo_939_; lean_object* v_defEqI_940_; lean_object* v_extensions_941_; lean_object* v_issues_942_; lean_object* v_canon_943_; uint8_t v_debug_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_997_; 
v___x_933_ = lean_st_ref_take(v_a_927_);
v_share_934_ = lean_ctor_get(v___x_933_, 0);
v_maxFVar_935_ = lean_ctor_get(v___x_933_, 1);
v_proofInstInfo_936_ = lean_ctor_get(v___x_933_, 2);
v_inferType_937_ = lean_ctor_get(v___x_933_, 3);
v_getLevel_938_ = lean_ctor_get(v___x_933_, 4);
v_congrInfo_939_ = lean_ctor_get(v___x_933_, 5);
v_defEqI_940_ = lean_ctor_get(v___x_933_, 6);
v_extensions_941_ = lean_ctor_get(v___x_933_, 7);
v_issues_942_ = lean_ctor_get(v___x_933_, 8);
v_canon_943_ = lean_ctor_get(v___x_933_, 9);
v_debug_944_ = lean_ctor_get_uint8(v___x_933_, sizeof(void*)*10);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_997_ == 0)
{
v___x_946_ = v___x_933_;
v_isShared_947_ = v_isSharedCheck_997_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_canon_943_);
lean_inc(v_issues_942_);
lean_inc(v_extensions_941_);
lean_inc(v_defEqI_940_);
lean_inc(v_congrInfo_939_);
lean_inc(v_getLevel_938_);
lean_inc(v_inferType_937_);
lean_inc(v_proofInstInfo_936_);
lean_inc(v_maxFVar_935_);
lean_inc(v_share_934_);
lean_dec(v___x_933_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_997_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_948_; lean_object* v___x_950_; 
v___x_948_ = lean_obj_once(&l_Lean_Meta_Sym_replaceS___redArg___closed__2, &l_Lean_Meta_Sym_replaceS___redArg___closed__2_once, _init_l_Lean_Meta_Sym_replaceS___redArg___closed__2);
if (v_isShared_947_ == 0)
{
lean_ctor_set(v___x_946_, 0, v___x_948_);
v___x_950_ = v___x_946_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v___x_948_);
lean_ctor_set(v_reuseFailAlloc_996_, 1, v_maxFVar_935_);
lean_ctor_set(v_reuseFailAlloc_996_, 2, v_proofInstInfo_936_);
lean_ctor_set(v_reuseFailAlloc_996_, 3, v_inferType_937_);
lean_ctor_set(v_reuseFailAlloc_996_, 4, v_getLevel_938_);
lean_ctor_set(v_reuseFailAlloc_996_, 5, v_congrInfo_939_);
lean_ctor_set(v_reuseFailAlloc_996_, 6, v_defEqI_940_);
lean_ctor_set(v_reuseFailAlloc_996_, 7, v_extensions_941_);
lean_ctor_set(v_reuseFailAlloc_996_, 8, v_issues_942_);
lean_ctor_set(v_reuseFailAlloc_996_, 9, v_canon_943_);
lean_ctor_set_uint8(v_reuseFailAlloc_996_, sizeof(void*)*10, v_debug_944_);
v___x_950_ = v_reuseFailAlloc_996_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v_fst_954_; lean_object* v_snd_955_; uint8_t v_debug_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v_fst_981_; 
v___x_951_ = lean_st_ref_set(v_a_927_, v___x_950_);
v___x_952_ = lean_st_ref_get(v_a_927_);
v_debug_977_ = lean_ctor_get_uint8(v___x_952_, sizeof(void*)*10);
lean_dec(v___x_952_);
v___x_978_ = lean_unsigned_to_nat(0u);
v___x_979_ = lean_box(v_debug_977_);
lean_inc_ref(v_f_925_);
lean_inc_ref(v_e_924_);
v___x_980_ = lean_apply_4(v_f_925_, v_e_924_, v___x_978_, v___x_979_, v_share_934_);
v_fst_981_ = lean_ctor_get(v___x_980_, 0);
lean_inc(v_fst_981_);
if (lean_obj_tag(v_fst_981_) == 1)
{
lean_object* v_snd_982_; lean_object* v_val_983_; 
lean_dec_ref(v_f_925_);
lean_dec_ref(v_e_924_);
v_snd_982_ = lean_ctor_get(v___x_980_, 1);
lean_inc(v_snd_982_);
lean_dec_ref(v___x_980_);
v_val_983_ = lean_ctor_get(v_fst_981_, 0);
lean_inc(v_val_983_);
lean_dec_ref(v_fst_981_);
v_fst_954_ = v_val_983_;
v_snd_955_ = v_snd_982_;
goto v___jp_953_;
}
else
{
lean_dec(v_fst_981_);
switch(lean_obj_tag(v_e_924_))
{
case 9:
{
lean_object* v_snd_984_; 
lean_dec_ref(v_f_925_);
v_snd_984_ = lean_ctor_get(v___x_980_, 1);
lean_inc(v_snd_984_);
lean_dec_ref(v___x_980_);
v_fst_954_ = v_e_924_;
v_snd_955_ = v_snd_984_;
goto v___jp_953_;
}
case 2:
{
lean_object* v_snd_985_; 
lean_dec_ref(v_f_925_);
v_snd_985_ = lean_ctor_get(v___x_980_, 1);
lean_inc(v_snd_985_);
lean_dec_ref(v___x_980_);
v_fst_954_ = v_e_924_;
v_snd_955_ = v_snd_985_;
goto v___jp_953_;
}
case 0:
{
lean_object* v_snd_986_; 
lean_dec_ref(v_f_925_);
v_snd_986_ = lean_ctor_get(v___x_980_, 1);
lean_inc(v_snd_986_);
lean_dec_ref(v___x_980_);
v_fst_954_ = v_e_924_;
v_snd_955_ = v_snd_986_;
goto v___jp_953_;
}
case 1:
{
lean_object* v_snd_987_; 
lean_dec_ref(v_f_925_);
v_snd_987_ = lean_ctor_get(v___x_980_, 1);
lean_inc(v_snd_987_);
lean_dec_ref(v___x_980_);
v_fst_954_ = v_e_924_;
v_snd_955_ = v_snd_987_;
goto v___jp_953_;
}
case 4:
{
lean_object* v_snd_988_; 
lean_dec_ref(v_f_925_);
v_snd_988_ = lean_ctor_get(v___x_980_, 1);
lean_inc(v_snd_988_);
lean_dec_ref(v___x_980_);
v_fst_954_ = v_e_924_;
v_snd_955_ = v_snd_988_;
goto v___jp_953_;
}
case 3:
{
lean_object* v_snd_989_; 
lean_dec_ref(v_f_925_);
v_snd_989_ = lean_ctor_get(v___x_980_, 1);
lean_inc(v_snd_989_);
lean_dec_ref(v___x_980_);
v_fst_954_ = v_e_924_;
v_snd_955_ = v_snd_989_;
goto v___jp_953_;
}
default: 
{
lean_object* v_snd_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v_fst_993_; lean_object* v_snd_994_; lean_object* v_fst_995_; 
v_snd_990_ = lean_ctor_get(v___x_980_, 1);
lean_inc(v_snd_990_);
lean_dec_ref(v___x_980_);
v___x_991_ = lean_obj_once(&l_Lean_Meta_Sym_replaceS_x27___closed__1, &l_Lean_Meta_Sym_replaceS_x27___closed__1_once, _init_l_Lean_Meta_Sym_replaceS_x27___closed__1);
v___x_992_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit(v_e_924_, v___x_978_, v_f_925_, v___x_991_, v_debug_977_, v_snd_990_);
v_fst_993_ = lean_ctor_get(v___x_992_, 0);
lean_inc(v_fst_993_);
v_snd_994_ = lean_ctor_get(v___x_992_, 1);
lean_inc(v_snd_994_);
lean_dec_ref(v___x_992_);
v_fst_995_ = lean_ctor_get(v_fst_993_, 0);
lean_inc(v_fst_995_);
lean_dec(v_fst_993_);
v_fst_954_ = v_fst_995_;
v_snd_955_ = v_snd_994_;
goto v___jp_953_;
}
}
}
v___jp_953_:
{
lean_object* v___x_956_; lean_object* v_maxFVar_957_; lean_object* v_proofInstInfo_958_; lean_object* v_inferType_959_; lean_object* v_getLevel_960_; lean_object* v_congrInfo_961_; lean_object* v_defEqI_962_; lean_object* v_extensions_963_; lean_object* v_issues_964_; lean_object* v_canon_965_; uint8_t v_debug_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_975_; 
v___x_956_ = lean_st_ref_take(v_a_927_);
v_maxFVar_957_ = lean_ctor_get(v___x_956_, 1);
v_proofInstInfo_958_ = lean_ctor_get(v___x_956_, 2);
v_inferType_959_ = lean_ctor_get(v___x_956_, 3);
v_getLevel_960_ = lean_ctor_get(v___x_956_, 4);
v_congrInfo_961_ = lean_ctor_get(v___x_956_, 5);
v_defEqI_962_ = lean_ctor_get(v___x_956_, 6);
v_extensions_963_ = lean_ctor_get(v___x_956_, 7);
v_issues_964_ = lean_ctor_get(v___x_956_, 8);
v_canon_965_ = lean_ctor_get(v___x_956_, 9);
v_debug_966_ = lean_ctor_get_uint8(v___x_956_, sizeof(void*)*10);
v_isSharedCheck_975_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_975_ == 0)
{
lean_object* v_unused_976_; 
v_unused_976_ = lean_ctor_get(v___x_956_, 0);
lean_dec(v_unused_976_);
v___x_968_ = v___x_956_;
v_isShared_969_ = v_isSharedCheck_975_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_canon_965_);
lean_inc(v_issues_964_);
lean_inc(v_extensions_963_);
lean_inc(v_defEqI_962_);
lean_inc(v_congrInfo_961_);
lean_inc(v_getLevel_960_);
lean_inc(v_inferType_959_);
lean_inc(v_proofInstInfo_958_);
lean_inc(v_maxFVar_957_);
lean_dec(v___x_956_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_975_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_971_; 
if (v_isShared_969_ == 0)
{
lean_ctor_set(v___x_968_, 0, v_snd_955_);
v___x_971_ = v___x_968_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_snd_955_);
lean_ctor_set(v_reuseFailAlloc_974_, 1, v_maxFVar_957_);
lean_ctor_set(v_reuseFailAlloc_974_, 2, v_proofInstInfo_958_);
lean_ctor_set(v_reuseFailAlloc_974_, 3, v_inferType_959_);
lean_ctor_set(v_reuseFailAlloc_974_, 4, v_getLevel_960_);
lean_ctor_set(v_reuseFailAlloc_974_, 5, v_congrInfo_961_);
lean_ctor_set(v_reuseFailAlloc_974_, 6, v_defEqI_962_);
lean_ctor_set(v_reuseFailAlloc_974_, 7, v_extensions_963_);
lean_ctor_set(v_reuseFailAlloc_974_, 8, v_issues_964_);
lean_ctor_set(v_reuseFailAlloc_974_, 9, v_canon_965_);
lean_ctor_set_uint8(v_reuseFailAlloc_974_, sizeof(void*)*10, v_debug_966_);
v___x_971_ = v_reuseFailAlloc_974_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_972_ = lean_st_ref_set(v_a_927_, v___x_971_);
v___x_973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_973_, 0, v_fst_954_);
return v___x_973_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_replaceS___boxed(lean_object* v_e_998_, lean_object* v_f_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_){
_start:
{
lean_object* v_res_1007_; 
v_res_1007_ = l_Lean_Meta_Sym_replaceS(v_e_998_, v_f_999_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_);
lean_dec(v_a_1005_);
lean_dec_ref(v_a_1004_);
lean_dec(v_a_1003_);
lean_dec_ref(v_a_1002_);
lean_dec(v_a_1001_);
lean_dec_ref(v_a_1000_);
return v_res_1007_;
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
