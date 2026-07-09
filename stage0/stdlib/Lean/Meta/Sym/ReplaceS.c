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
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
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
lean_object* l_EStateM_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableEqNat___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_seqRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_hashPtrExpr_unsafe__1___boxed(lean_object*);
lean_object* l_UInt64_ofNat___boxed(lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Sym_instInhabitedSymM(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Sym_runShareCommonM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_bind, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__8 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__8_value;
static const lean_closure_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_seqRight, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__6 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__6_value;
static const lean_closure_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___lam__2, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__2_value;
static const lean_closure_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___lam__1, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__1_value;
static const lean_closure_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_pure, .m_arity = 5, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__5 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__5_value;
static const lean_closure_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___lam__0, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_map, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__3_value),((lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__4 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__4_value),((lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__5_value),((lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__1_value),((lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__2_value),((lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__6_value)}};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__7 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__7_value),((lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__8_value)}};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__9 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__9_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__10;
static lean_once_cell_t l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11;
static lean_once_cell_t l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20;
static lean_once_cell_t l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__15;
static lean_once_cell_t l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__14;
static lean_once_cell_t l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__13;
static lean_once_cell_t l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__18;
static lean_once_cell_t l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__12;
static lean_once_cell_t l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__16;
static lean_once_cell_t l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__17;
static lean_once_cell_t l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__19;
static lean_once_cell_t l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__21;
static lean_once_cell_t l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__22;
static lean_once_cell_t l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__23;
static const lean_string_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__26 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__26_value;
static const lean_string_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "_private.Lean.Meta.Sym.ReplaceS.0.Lean.Meta.Sym.visit"};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__25 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__25_value;
static const lean_string_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Meta.Sym.ReplaceS"};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__24 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__24_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__27;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_replaceS_x27(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_replaceS_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Sym_replaceS___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_replaceS___closed__0;
static const lean_string_object l_Lean_Meta_Sym_replaceS___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Meta.Sym.AlphaShareBuilder"};
static const lean_object* l_Lean_Meta_Sym_replaceS___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_replaceS___closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_replaceS___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Lean.Meta.Sym.Internal.liftBuilderM"};
static const lean_object* l_Lean_Meta_Sym_replaceS___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_replaceS___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Sym_replaceS___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_replaceS___closed__3;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(lean_object* v_key_155_, lean_object* v_r_156_, lean_object* v_a_157_, uint8_t v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(v_key_155_, v_r_156_, v_a_157_, v_a_160_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___boxed(lean_object* v_key_162_, lean_object* v_r_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_){
_start:
{
uint8_t v_a_boxed_168_; lean_object* v_res_169_; 
v_a_boxed_168_ = lean_unbox(v_a_165_);
v_res_169_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_162_, v_r_163_, v_a_164_, v_a_boxed_168_, v_a_166_, v_a_167_);
lean_dec_ref(v_a_166_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0(lean_object* v_00_u03b2_170_, lean_object* v_m_171_, lean_object* v_a_172_, lean_object* v_b_173_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0___redArg(v_m_171_, v_a_172_, v_b_173_);
return v___x_174_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0(lean_object* v_00_u03b2_175_, lean_object* v_a_176_, lean_object* v_x_177_){
_start:
{
uint8_t v___x_178_; 
v___x_178_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_a_176_, v_x_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0___boxed(lean_object* v_00_u03b2_179_, lean_object* v_a_180_, lean_object* v_x_181_){
_start:
{
uint8_t v_res_182_; lean_object* v_r_183_; 
v_res_182_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0(v_00_u03b2_179_, v_a_180_, v_x_181_);
lean_dec(v_x_181_);
lean_dec_ref(v_a_180_);
v_r_183_ = lean_box(v_res_182_);
return v_r_183_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1(lean_object* v_00_u03b2_184_, lean_object* v_data_185_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1___redArg(v_data_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__2(lean_object* v_00_u03b2_187_, lean_object* v_a_188_, lean_object* v_b_189_, lean_object* v_x_190_){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(v_a_188_, v_b_189_, v_x_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_192_, lean_object* v_i_193_, lean_object* v_source_194_, lean_object* v_target_195_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2___redArg(v_i_193_, v_source_194_, v_target_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_197_, lean_object* v_x_198_, lean_object* v_x_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3___redArg(v_x_198_, v_x_199_);
return v___x_200_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__4(void){
_start:
{
lean_object* v___x_207_; lean_object* v___f_208_; 
v___x_207_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___f_208_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_208_, 0, v___x_207_);
return v___f_208_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__5(void){
_start:
{
lean_object* v___f_209_; lean_object* v___f_210_; lean_object* v___f_211_; 
v___f_209_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__4, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__4_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__4);
v___f_210_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__0));
v___f_211_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_211_, 0, v___f_210_);
lean_closure_set(v___f_211_, 1, v___f_209_);
return v___f_211_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__10(void){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_231_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__9));
v___x_232_ = l_ReaderT_instMonad___redArg(v___x_231_);
return v___x_232_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11(void){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_233_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__10, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__10_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__10);
v___x_234_ = l_ReaderT_instMonad___redArg(v___x_233_);
return v___x_234_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20(void){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_235_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11);
v___x_236_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_236_, 0, lean_box(0));
lean_closure_set(v___x_236_, 1, lean_box(0));
lean_closure_set(v___x_236_, 2, v___x_235_);
return v___x_236_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__15(void){
_start:
{
lean_object* v___x_237_; lean_object* v___f_238_; 
v___x_237_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11);
v___f_238_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_238_, 0, v___x_237_);
return v___f_238_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__14(void){
_start:
{
lean_object* v___x_239_; lean_object* v___f_240_; 
v___x_239_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11);
v___f_240_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_240_, 0, v___x_239_);
return v___f_240_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__13(void){
_start:
{
lean_object* v___x_241_; lean_object* v___f_242_; 
v___x_241_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11);
v___f_242_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_242_, 0, v___x_241_);
return v___f_242_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__18(void){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_243_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11);
v___x_244_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_244_, 0, lean_box(0));
lean_closure_set(v___x_244_, 1, lean_box(0));
lean_closure_set(v___x_244_, 2, v___x_243_);
return v___x_244_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__12(void){
_start:
{
lean_object* v___x_245_; lean_object* v___f_246_; 
v___x_245_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11);
v___f_246_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_246_, 0, v___x_245_);
return v___f_246_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__16(void){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_247_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11);
v___x_248_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_248_, 0, lean_box(0));
lean_closure_set(v___x_248_, 1, lean_box(0));
lean_closure_set(v___x_248_, 2, v___x_247_);
return v___x_248_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__17(void){
_start:
{
lean_object* v___f_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v___f_249_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__12, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__12_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__12);
v___x_250_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__16, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__16_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__16);
v___x_251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
lean_ctor_set(v___x_251_, 1, v___f_249_);
return v___x_251_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__19(void){
_start:
{
lean_object* v___f_252_; lean_object* v___f_253_; lean_object* v___f_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v___f_252_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__15, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__15_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__15);
v___f_253_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__14, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__14_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__14);
v___f_254_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__13, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__13_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__13);
v___x_255_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__18, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__18_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__18);
v___x_256_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__17, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__17_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__17);
v___x_257_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_257_, 0, v___x_256_);
lean_ctor_set(v___x_257_, 1, v___x_255_);
lean_ctor_set(v___x_257_, 2, v___f_254_);
lean_ctor_set(v___x_257_, 3, v___f_253_);
lean_ctor_set(v___x_257_, 4, v___f_252_);
return v___x_257_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__21(void){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_258_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20);
v___x_259_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__19, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__19_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__19);
v___x_260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_260_, 0, v___x_259_);
lean_ctor_set(v___x_260_, 1, v___x_258_);
return v___x_260_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__22(void){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_261_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11);
v___x_262_ = lean_alloc_closure((void*)(l_StateT_lift), 6, 3);
lean_closure_set(v___x_262_, 0, lean_box(0));
lean_closure_set(v___x_262_, 1, lean_box(0));
lean_closure_set(v___x_262_, 2, v___x_261_);
return v___x_262_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__23(void){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_263_ = l_Lean_instInhabitedExpr;
v___x_264_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__21, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__21_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__21);
v___x_265_ = l_instInhabitedOfMonad___redArg(v___x_264_, v___x_263_);
return v___x_265_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__27(void){
_start:
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_269_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__26));
v___x_270_ = lean_unsigned_to_nat(67u);
v___x_271_ = lean_unsigned_to_nat(35u);
v___x_272_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__25));
v___x_273_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__24));
v___x_274_ = l_mkPanicMessageWithDecl(v___x_273_, v___x_272_, v___x_271_, v___x_270_, v___x_269_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit(lean_object* v_e_275_, lean_object* v_offset_276_, lean_object* v_fn_277_, lean_object* v_a_278_, uint8_t v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v_share1_285_; lean_object* v_assertShared_286_; lean_object* v_isDebugEnabled_287_; lean_object* v___x_288_; lean_object* v___f_289_; lean_object* v___f_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_282_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11);
v___x_283_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__21, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__21_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__21);
v___x_284_ = l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM;
v_share1_285_ = lean_ctor_get(v___x_284_, 0);
v_assertShared_286_ = lean_ctor_get(v___x_284_, 1);
v_isDebugEnabled_287_ = lean_ctor_get(v___x_284_, 2);
v___x_288_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__22, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__22_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__22);
lean_inc(v_share1_285_);
v___f_289_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_289_, 0, v_share1_285_);
lean_closure_set(v___f_289_, 1, v___x_288_);
lean_inc(v_assertShared_286_);
v___f_290_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift___redArg___lam__1), 3, 2);
lean_closure_set(v___f_290_, 0, v_assertShared_286_);
lean_closure_set(v___f_290_, 1, v___x_288_);
lean_inc(v_isDebugEnabled_287_);
v___x_291_ = lean_alloc_closure((void*)(l_StateT_lift), 6, 5);
lean_closure_set(v___x_291_, 0, lean_box(0));
lean_closure_set(v___x_291_, 1, lean_box(0));
lean_closure_set(v___x_291_, 2, v___x_282_);
lean_closure_set(v___x_291_, 3, lean_box(0));
lean_closure_set(v___x_291_, 4, v_isDebugEnabled_287_);
v___x_292_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_292_, 0, v___f_289_);
lean_ctor_set(v___x_292_, 1, v___f_290_);
lean_ctor_set(v___x_292_, 2, v___x_291_);
switch(lean_obj_tag(v_e_275_))
{
case 5:
{
lean_object* v_fn_293_; lean_object* v_arg_294_; lean_object* v___x_295_; 
v_fn_293_ = lean_ctor_get(v_e_275_, 0);
v_arg_294_ = lean_ctor_get(v_e_275_, 1);
lean_inc_ref(v_fn_277_);
lean_inc(v_offset_276_);
lean_inc_ref(v_fn_293_);
v___x_295_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_fn_293_, v_offset_276_, v_fn_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_);
if (lean_obj_tag(v___x_295_) == 0)
{
lean_object* v_a_296_; lean_object* v_a_297_; lean_object* v_fst_298_; lean_object* v_snd_299_; lean_object* v___x_300_; 
v_a_296_ = lean_ctor_get(v___x_295_, 0);
lean_inc(v_a_296_);
v_a_297_ = lean_ctor_get(v___x_295_, 1);
lean_inc(v_a_297_);
lean_dec_ref_known(v___x_295_, 2);
v_fst_298_ = lean_ctor_get(v_a_296_, 0);
lean_inc(v_fst_298_);
v_snd_299_ = lean_ctor_get(v_a_296_, 1);
lean_inc(v_snd_299_);
lean_dec(v_a_296_);
lean_inc_ref(v_arg_294_);
v___x_300_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_arg_294_, v_offset_276_, v_fn_277_, v_snd_299_, v_a_279_, v_a_280_, v_a_297_);
if (lean_obj_tag(v___x_300_) == 0)
{
lean_object* v_a_301_; lean_object* v_a_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_325_; 
v_a_301_ = lean_ctor_get(v___x_300_, 0);
v_a_302_ = lean_ctor_get(v___x_300_, 1);
v_isSharedCheck_325_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_325_ == 0)
{
v___x_304_ = v___x_300_;
v_isShared_305_ = v_isSharedCheck_325_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_a_302_);
lean_inc(v_a_301_);
lean_dec(v___x_300_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_325_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v_fst_306_; lean_object* v_snd_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_324_; 
v_fst_306_ = lean_ctor_get(v_a_301_, 0);
v_snd_307_ = lean_ctor_get(v_a_301_, 1);
v_isSharedCheck_324_ = !lean_is_exclusive(v_a_301_);
if (v_isSharedCheck_324_ == 0)
{
v___x_309_ = v_a_301_;
v_isShared_310_ = v_isSharedCheck_324_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_snd_307_);
lean_inc(v_fst_306_);
lean_dec(v_a_301_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_324_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
uint8_t v___y_312_; uint8_t v___x_322_; 
v___x_322_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_293_, v_fst_298_);
if (v___x_322_ == 0)
{
v___y_312_ = v___x_322_;
goto v___jp_311_;
}
else
{
uint8_t v___x_323_; 
v___x_323_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_294_, v_fst_306_);
v___y_312_ = v___x_323_;
goto v___jp_311_;
}
v___jp_311_:
{
if (v___y_312_ == 0)
{
lean_object* v___x_11171__overap_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
lean_del_object(v___x_309_);
lean_del_object(v___x_304_);
lean_dec_ref_known(v_e_275_, 2);
v___x_11171__overap_313_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v___x_292_, v___x_283_, v_fst_298_, v_fst_306_);
v___x_314_ = lean_box(v_a_279_);
lean_inc_ref(v_a_280_);
v___x_315_ = lean_apply_4(v___x_11171__overap_313_, v_snd_307_, v___x_314_, v_a_280_, v_a_302_);
return v___x_315_;
}
else
{
lean_object* v___x_317_; 
lean_dec(v_fst_306_);
lean_dec(v_fst_298_);
lean_dec_ref_known(v___x_292_, 3);
if (v_isShared_310_ == 0)
{
lean_ctor_set(v___x_309_, 0, v_e_275_);
v___x_317_ = v___x_309_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v_e_275_);
lean_ctor_set(v_reuseFailAlloc_321_, 1, v_snd_307_);
v___x_317_ = v_reuseFailAlloc_321_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
lean_object* v___x_319_; 
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 0, v___x_317_);
v___x_319_ = v___x_304_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v___x_317_);
lean_ctor_set(v_reuseFailAlloc_320_, 1, v_a_302_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_298_);
lean_dec_ref_known(v_e_275_, 2);
lean_dec_ref_known(v___x_292_, 3);
return v___x_300_;
}
}
else
{
lean_dec_ref_known(v_e_275_, 2);
lean_dec_ref_known(v___x_292_, 3);
lean_dec_ref(v_fn_277_);
lean_dec(v_offset_276_);
return v___x_295_;
}
}
case 6:
{
lean_object* v_binderName_326_; lean_object* v_binderType_327_; lean_object* v_body_328_; uint8_t v_binderInfo_329_; lean_object* v___x_330_; 
v_binderName_326_ = lean_ctor_get(v_e_275_, 0);
v_binderType_327_ = lean_ctor_get(v_e_275_, 1);
v_body_328_ = lean_ctor_get(v_e_275_, 2);
v_binderInfo_329_ = lean_ctor_get_uint8(v_e_275_, sizeof(void*)*3 + 8);
lean_inc_ref(v_fn_277_);
lean_inc(v_offset_276_);
lean_inc_ref(v_binderType_327_);
v___x_330_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_binderType_327_, v_offset_276_, v_fn_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_);
if (lean_obj_tag(v___x_330_) == 0)
{
lean_object* v_a_331_; lean_object* v_a_332_; lean_object* v_fst_333_; lean_object* v_snd_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v_a_331_ = lean_ctor_get(v___x_330_, 0);
lean_inc(v_a_331_);
v_a_332_ = lean_ctor_get(v___x_330_, 1);
lean_inc(v_a_332_);
lean_dec_ref_known(v___x_330_, 2);
v_fst_333_ = lean_ctor_get(v_a_331_, 0);
lean_inc(v_fst_333_);
v_snd_334_ = lean_ctor_get(v_a_331_, 1);
lean_inc(v_snd_334_);
lean_dec(v_a_331_);
v___x_335_ = lean_unsigned_to_nat(1u);
v___x_336_ = lean_nat_add(v_offset_276_, v___x_335_);
lean_dec(v_offset_276_);
lean_inc_ref(v_body_328_);
v___x_337_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_body_328_, v___x_336_, v_fn_277_, v_snd_334_, v_a_279_, v_a_280_, v_a_332_);
if (lean_obj_tag(v___x_337_) == 0)
{
lean_object* v_a_338_; lean_object* v_a_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_362_; 
v_a_338_ = lean_ctor_get(v___x_337_, 0);
v_a_339_ = lean_ctor_get(v___x_337_, 1);
v_isSharedCheck_362_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_362_ == 0)
{
v___x_341_ = v___x_337_;
v_isShared_342_ = v_isSharedCheck_362_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_a_339_);
lean_inc(v_a_338_);
lean_dec(v___x_337_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_362_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v_fst_343_; lean_object* v_snd_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_361_; 
v_fst_343_ = lean_ctor_get(v_a_338_, 0);
v_snd_344_ = lean_ctor_get(v_a_338_, 1);
v_isSharedCheck_361_ = !lean_is_exclusive(v_a_338_);
if (v_isSharedCheck_361_ == 0)
{
v___x_346_ = v_a_338_;
v_isShared_347_ = v_isSharedCheck_361_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_snd_344_);
lean_inc(v_fst_343_);
lean_dec(v_a_338_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_361_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
uint8_t v___y_349_; uint8_t v___x_359_; 
v___x_359_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_327_, v_fst_333_);
if (v___x_359_ == 0)
{
v___y_349_ = v___x_359_;
goto v___jp_348_;
}
else
{
uint8_t v___x_360_; 
v___x_360_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_328_, v_fst_343_);
v___y_349_ = v___x_360_;
goto v___jp_348_;
}
v___jp_348_:
{
if (v___y_349_ == 0)
{
lean_object* v___x_11413__overap_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
lean_inc(v_binderName_326_);
lean_del_object(v___x_346_);
lean_del_object(v___x_341_);
lean_dec_ref_known(v_e_275_, 3);
v___x_11413__overap_350_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v___x_292_, v___x_283_, v_binderName_326_, v_binderInfo_329_, v_fst_333_, v_fst_343_);
v___x_351_ = lean_box(v_a_279_);
lean_inc_ref(v_a_280_);
v___x_352_ = lean_apply_4(v___x_11413__overap_350_, v_snd_344_, v___x_351_, v_a_280_, v_a_339_);
return v___x_352_;
}
else
{
lean_object* v___x_354_; 
lean_dec(v_fst_343_);
lean_dec(v_fst_333_);
lean_dec_ref_known(v___x_292_, 3);
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 0, v_e_275_);
v___x_354_ = v___x_346_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v_e_275_);
lean_ctor_set(v_reuseFailAlloc_358_, 1, v_snd_344_);
v___x_354_ = v_reuseFailAlloc_358_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
lean_object* v___x_356_; 
if (v_isShared_342_ == 0)
{
lean_ctor_set(v___x_341_, 0, v___x_354_);
v___x_356_ = v___x_341_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v___x_354_);
lean_ctor_set(v_reuseFailAlloc_357_, 1, v_a_339_);
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
}
}
else
{
lean_dec(v_fst_333_);
lean_dec_ref_known(v_e_275_, 3);
lean_dec_ref_known(v___x_292_, 3);
return v___x_337_;
}
}
else
{
lean_dec_ref_known(v_e_275_, 3);
lean_dec_ref_known(v___x_292_, 3);
lean_dec_ref(v_fn_277_);
lean_dec(v_offset_276_);
return v___x_330_;
}
}
case 7:
{
lean_object* v_binderName_363_; lean_object* v_binderType_364_; lean_object* v_body_365_; uint8_t v_binderInfo_366_; lean_object* v___x_367_; 
v_binderName_363_ = lean_ctor_get(v_e_275_, 0);
v_binderType_364_ = lean_ctor_get(v_e_275_, 1);
v_body_365_ = lean_ctor_get(v_e_275_, 2);
v_binderInfo_366_ = lean_ctor_get_uint8(v_e_275_, sizeof(void*)*3 + 8);
lean_inc_ref(v_fn_277_);
lean_inc(v_offset_276_);
lean_inc_ref(v_binderType_364_);
v___x_367_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_binderType_364_, v_offset_276_, v_fn_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_);
if (lean_obj_tag(v___x_367_) == 0)
{
lean_object* v_a_368_; lean_object* v_a_369_; lean_object* v_fst_370_; lean_object* v_snd_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v_a_368_ = lean_ctor_get(v___x_367_, 0);
lean_inc(v_a_368_);
v_a_369_ = lean_ctor_get(v___x_367_, 1);
lean_inc(v_a_369_);
lean_dec_ref_known(v___x_367_, 2);
v_fst_370_ = lean_ctor_get(v_a_368_, 0);
lean_inc(v_fst_370_);
v_snd_371_ = lean_ctor_get(v_a_368_, 1);
lean_inc(v_snd_371_);
lean_dec(v_a_368_);
v___x_372_ = lean_unsigned_to_nat(1u);
v___x_373_ = lean_nat_add(v_offset_276_, v___x_372_);
lean_dec(v_offset_276_);
lean_inc_ref(v_body_365_);
v___x_374_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_body_365_, v___x_373_, v_fn_277_, v_snd_371_, v_a_279_, v_a_280_, v_a_369_);
if (lean_obj_tag(v___x_374_) == 0)
{
lean_object* v_a_375_; lean_object* v_a_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_399_; 
v_a_375_ = lean_ctor_get(v___x_374_, 0);
v_a_376_ = lean_ctor_get(v___x_374_, 1);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_399_ == 0)
{
v___x_378_ = v___x_374_;
v_isShared_379_ = v_isSharedCheck_399_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_a_376_);
lean_inc(v_a_375_);
lean_dec(v___x_374_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_399_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v_fst_380_; lean_object* v_snd_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_398_; 
v_fst_380_ = lean_ctor_get(v_a_375_, 0);
v_snd_381_ = lean_ctor_get(v_a_375_, 1);
v_isSharedCheck_398_ = !lean_is_exclusive(v_a_375_);
if (v_isSharedCheck_398_ == 0)
{
v___x_383_ = v_a_375_;
v_isShared_384_ = v_isSharedCheck_398_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_snd_381_);
lean_inc(v_fst_380_);
lean_dec(v_a_375_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_398_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
uint8_t v___y_386_; uint8_t v___x_396_; 
v___x_396_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_364_, v_fst_370_);
if (v___x_396_ == 0)
{
v___y_386_ = v___x_396_;
goto v___jp_385_;
}
else
{
uint8_t v___x_397_; 
v___x_397_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_365_, v_fst_380_);
v___y_386_ = v___x_397_;
goto v___jp_385_;
}
v___jp_385_:
{
if (v___y_386_ == 0)
{
lean_object* v___x_11663__overap_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
lean_inc(v_binderName_363_);
lean_del_object(v___x_383_);
lean_del_object(v___x_378_);
lean_dec_ref_known(v_e_275_, 3);
v___x_11663__overap_387_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v___x_292_, v___x_283_, v_binderName_363_, v_binderInfo_366_, v_fst_370_, v_fst_380_);
v___x_388_ = lean_box(v_a_279_);
lean_inc_ref(v_a_280_);
v___x_389_ = lean_apply_4(v___x_11663__overap_387_, v_snd_381_, v___x_388_, v_a_280_, v_a_376_);
return v___x_389_;
}
else
{
lean_object* v___x_391_; 
lean_dec(v_fst_380_);
lean_dec(v_fst_370_);
lean_dec_ref_known(v___x_292_, 3);
if (v_isShared_384_ == 0)
{
lean_ctor_set(v___x_383_, 0, v_e_275_);
v___x_391_ = v___x_383_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_e_275_);
lean_ctor_set(v_reuseFailAlloc_395_, 1, v_snd_381_);
v___x_391_ = v_reuseFailAlloc_395_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
lean_object* v___x_393_; 
if (v_isShared_379_ == 0)
{
lean_ctor_set(v___x_378_, 0, v___x_391_);
v___x_393_ = v___x_378_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v___x_391_);
lean_ctor_set(v_reuseFailAlloc_394_, 1, v_a_376_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
return v___x_393_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_370_);
lean_dec_ref_known(v_e_275_, 3);
lean_dec_ref_known(v___x_292_, 3);
return v___x_374_;
}
}
else
{
lean_dec_ref_known(v_e_275_, 3);
lean_dec_ref_known(v___x_292_, 3);
lean_dec_ref(v_fn_277_);
lean_dec(v_offset_276_);
return v___x_367_;
}
}
case 8:
{
lean_object* v_declName_400_; lean_object* v_type_401_; lean_object* v_value_402_; lean_object* v_body_403_; uint8_t v_nondep_404_; lean_object* v___x_405_; 
v_declName_400_ = lean_ctor_get(v_e_275_, 0);
v_type_401_ = lean_ctor_get(v_e_275_, 1);
v_value_402_ = lean_ctor_get(v_e_275_, 2);
v_body_403_ = lean_ctor_get(v_e_275_, 3);
v_nondep_404_ = lean_ctor_get_uint8(v_e_275_, sizeof(void*)*4 + 8);
lean_inc_ref(v_fn_277_);
lean_inc(v_offset_276_);
lean_inc_ref(v_type_401_);
v___x_405_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_type_401_, v_offset_276_, v_fn_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_);
if (lean_obj_tag(v___x_405_) == 0)
{
lean_object* v_a_406_; lean_object* v_a_407_; lean_object* v_fst_408_; lean_object* v_snd_409_; lean_object* v___x_410_; 
v_a_406_ = lean_ctor_get(v___x_405_, 0);
lean_inc(v_a_406_);
v_a_407_ = lean_ctor_get(v___x_405_, 1);
lean_inc(v_a_407_);
lean_dec_ref_known(v___x_405_, 2);
v_fst_408_ = lean_ctor_get(v_a_406_, 0);
lean_inc(v_fst_408_);
v_snd_409_ = lean_ctor_get(v_a_406_, 1);
lean_inc(v_snd_409_);
lean_dec(v_a_406_);
lean_inc_ref(v_fn_277_);
lean_inc(v_offset_276_);
lean_inc_ref(v_value_402_);
v___x_410_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_value_402_, v_offset_276_, v_fn_277_, v_snd_409_, v_a_279_, v_a_280_, v_a_407_);
if (lean_obj_tag(v___x_410_) == 0)
{
lean_object* v_a_411_; lean_object* v_a_412_; lean_object* v_fst_413_; lean_object* v_snd_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v_a_411_ = lean_ctor_get(v___x_410_, 0);
lean_inc(v_a_411_);
v_a_412_ = lean_ctor_get(v___x_410_, 1);
lean_inc(v_a_412_);
lean_dec_ref_known(v___x_410_, 2);
v_fst_413_ = lean_ctor_get(v_a_411_, 0);
lean_inc(v_fst_413_);
v_snd_414_ = lean_ctor_get(v_a_411_, 1);
lean_inc(v_snd_414_);
lean_dec(v_a_411_);
v___x_415_ = lean_unsigned_to_nat(1u);
v___x_416_ = lean_nat_add(v_offset_276_, v___x_415_);
lean_dec(v_offset_276_);
lean_inc_ref(v_body_403_);
v___x_417_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_body_403_, v___x_416_, v_fn_277_, v_snd_414_, v_a_279_, v_a_280_, v_a_412_);
if (lean_obj_tag(v___x_417_) == 0)
{
lean_object* v_a_418_; lean_object* v_a_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_446_; 
v_a_418_ = lean_ctor_get(v___x_417_, 0);
v_a_419_ = lean_ctor_get(v___x_417_, 1);
v_isSharedCheck_446_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_446_ == 0)
{
v___x_421_ = v___x_417_;
v_isShared_422_ = v_isSharedCheck_446_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_a_419_);
lean_inc(v_a_418_);
lean_dec(v___x_417_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_446_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v_fst_423_; lean_object* v_snd_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_445_; 
v_fst_423_ = lean_ctor_get(v_a_418_, 0);
v_snd_424_ = lean_ctor_get(v_a_418_, 1);
v_isSharedCheck_445_ = !lean_is_exclusive(v_a_418_);
if (v_isSharedCheck_445_ == 0)
{
v___x_426_ = v_a_418_;
v_isShared_427_ = v_isSharedCheck_445_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_snd_424_);
lean_inc(v_fst_423_);
lean_dec(v_a_418_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_445_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
uint8_t v___y_429_; uint8_t v___x_443_; 
v___x_443_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_type_401_, v_fst_408_);
if (v___x_443_ == 0)
{
v___y_429_ = v___x_443_;
goto v___jp_428_;
}
else
{
uint8_t v___x_444_; 
v___x_444_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_value_402_, v_fst_413_);
v___y_429_ = v___x_444_;
goto v___jp_428_;
}
v___jp_428_:
{
if (v___y_429_ == 0)
{
lean_object* v___x_11949__overap_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
lean_inc(v_declName_400_);
lean_del_object(v___x_426_);
lean_del_object(v___x_421_);
lean_dec_ref_known(v_e_275_, 4);
v___x_11949__overap_430_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v___x_292_, v___x_283_, v_declName_400_, v_fst_408_, v_fst_413_, v_fst_423_, v_nondep_404_);
v___x_431_ = lean_box(v_a_279_);
lean_inc_ref(v_a_280_);
v___x_432_ = lean_apply_4(v___x_11949__overap_430_, v_snd_424_, v___x_431_, v_a_280_, v_a_419_);
return v___x_432_;
}
else
{
uint8_t v___x_433_; 
v___x_433_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_403_, v_fst_423_);
if (v___x_433_ == 0)
{
lean_object* v___x_11951__overap_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
lean_inc(v_declName_400_);
lean_del_object(v___x_426_);
lean_del_object(v___x_421_);
lean_dec_ref_known(v_e_275_, 4);
v___x_11951__overap_434_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v___x_292_, v___x_283_, v_declName_400_, v_fst_408_, v_fst_413_, v_fst_423_, v_nondep_404_);
v___x_435_ = lean_box(v_a_279_);
lean_inc_ref(v_a_280_);
v___x_436_ = lean_apply_4(v___x_11951__overap_434_, v_snd_424_, v___x_435_, v_a_280_, v_a_419_);
return v___x_436_;
}
else
{
lean_object* v___x_438_; 
lean_dec(v_fst_423_);
lean_dec(v_fst_413_);
lean_dec(v_fst_408_);
lean_dec_ref_known(v___x_292_, 3);
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 0, v_e_275_);
v___x_438_ = v___x_426_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_e_275_);
lean_ctor_set(v_reuseFailAlloc_442_, 1, v_snd_424_);
v___x_438_ = v_reuseFailAlloc_442_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
lean_object* v___x_440_; 
if (v_isShared_422_ == 0)
{
lean_ctor_set(v___x_421_, 0, v___x_438_);
v___x_440_ = v___x_421_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v___x_438_);
lean_ctor_set(v_reuseFailAlloc_441_, 1, v_a_419_);
v___x_440_ = v_reuseFailAlloc_441_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
return v___x_440_;
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
lean_dec(v_fst_413_);
lean_dec(v_fst_408_);
lean_dec_ref_known(v_e_275_, 4);
lean_dec_ref_known(v___x_292_, 3);
return v___x_417_;
}
}
else
{
lean_dec(v_fst_408_);
lean_dec_ref_known(v_e_275_, 4);
lean_dec_ref_known(v___x_292_, 3);
lean_dec_ref(v_fn_277_);
lean_dec(v_offset_276_);
return v___x_410_;
}
}
else
{
lean_dec_ref_known(v_e_275_, 4);
lean_dec_ref_known(v___x_292_, 3);
lean_dec_ref(v_fn_277_);
lean_dec(v_offset_276_);
return v___x_405_;
}
}
case 10:
{
lean_object* v_data_447_; lean_object* v_expr_448_; lean_object* v___x_449_; 
v_data_447_ = lean_ctor_get(v_e_275_, 0);
v_expr_448_ = lean_ctor_get(v_e_275_, 1);
lean_inc_ref(v_expr_448_);
v___x_449_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_expr_448_, v_offset_276_, v_fn_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_);
if (lean_obj_tag(v___x_449_) == 0)
{
lean_object* v_a_450_; lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_471_; 
v_a_450_ = lean_ctor_get(v___x_449_, 0);
v_a_451_ = lean_ctor_get(v___x_449_, 1);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_471_ == 0)
{
v___x_453_ = v___x_449_;
v_isShared_454_ = v_isSharedCheck_471_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_inc(v_a_450_);
lean_dec(v___x_449_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_471_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v_fst_455_; lean_object* v_snd_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_470_; 
v_fst_455_ = lean_ctor_get(v_a_450_, 0);
v_snd_456_ = lean_ctor_get(v_a_450_, 1);
v_isSharedCheck_470_ = !lean_is_exclusive(v_a_450_);
if (v_isSharedCheck_470_ == 0)
{
v___x_458_ = v_a_450_;
v_isShared_459_ = v_isSharedCheck_470_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_snd_456_);
lean_inc(v_fst_455_);
lean_dec(v_a_450_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_470_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
uint8_t v___x_460_; 
v___x_460_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_expr_448_, v_fst_455_);
if (v___x_460_ == 0)
{
lean_object* v___x_12192__overap_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
lean_inc(v_data_447_);
lean_del_object(v___x_458_);
lean_del_object(v___x_453_);
lean_dec_ref_known(v_e_275_, 2);
v___x_12192__overap_461_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg(v___x_292_, v___x_283_, v_data_447_, v_fst_455_);
v___x_462_ = lean_box(v_a_279_);
lean_inc_ref(v_a_280_);
v___x_463_ = lean_apply_4(v___x_12192__overap_461_, v_snd_456_, v___x_462_, v_a_280_, v_a_451_);
return v___x_463_;
}
else
{
lean_object* v___x_465_; 
lean_dec(v_fst_455_);
lean_dec_ref_known(v___x_292_, 3);
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 0, v_e_275_);
v___x_465_ = v___x_458_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_e_275_);
lean_ctor_set(v_reuseFailAlloc_469_, 1, v_snd_456_);
v___x_465_ = v_reuseFailAlloc_469_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
lean_object* v___x_467_; 
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 0, v___x_465_);
v___x_467_ = v___x_453_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v___x_465_);
lean_ctor_set(v_reuseFailAlloc_468_, 1, v_a_451_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_275_, 2);
lean_dec_ref_known(v___x_292_, 3);
return v___x_449_;
}
}
case 11:
{
lean_object* v_typeName_472_; lean_object* v_idx_473_; lean_object* v_struct_474_; lean_object* v___x_475_; 
v_typeName_472_ = lean_ctor_get(v_e_275_, 0);
v_idx_473_ = lean_ctor_get(v_e_275_, 1);
v_struct_474_ = lean_ctor_get(v_e_275_, 2);
lean_inc_ref(v_struct_474_);
v___x_475_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_struct_474_, v_offset_276_, v_fn_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_);
if (lean_obj_tag(v___x_475_) == 0)
{
lean_object* v_a_476_; lean_object* v_a_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_497_; 
v_a_476_ = lean_ctor_get(v___x_475_, 0);
v_a_477_ = lean_ctor_get(v___x_475_, 1);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_475_);
if (v_isSharedCheck_497_ == 0)
{
v___x_479_ = v___x_475_;
v_isShared_480_ = v_isSharedCheck_497_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_a_477_);
lean_inc(v_a_476_);
lean_dec(v___x_475_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_497_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v_fst_481_; lean_object* v_snd_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_496_; 
v_fst_481_ = lean_ctor_get(v_a_476_, 0);
v_snd_482_ = lean_ctor_get(v_a_476_, 1);
v_isSharedCheck_496_ = !lean_is_exclusive(v_a_476_);
if (v_isSharedCheck_496_ == 0)
{
v___x_484_ = v_a_476_;
v_isShared_485_ = v_isSharedCheck_496_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_snd_482_);
lean_inc(v_fst_481_);
lean_dec(v_a_476_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_496_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
uint8_t v___x_486_; 
v___x_486_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_474_, v_fst_481_);
if (v___x_486_ == 0)
{
lean_object* v___x_12354__overap_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
lean_inc(v_idx_473_);
lean_inc(v_typeName_472_);
lean_del_object(v___x_484_);
lean_del_object(v___x_479_);
lean_dec_ref_known(v_e_275_, 3);
v___x_12354__overap_487_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg(v___x_292_, v___x_283_, v_typeName_472_, v_idx_473_, v_fst_481_);
v___x_488_ = lean_box(v_a_279_);
lean_inc_ref(v_a_280_);
v___x_489_ = lean_apply_4(v___x_12354__overap_487_, v_snd_482_, v___x_488_, v_a_280_, v_a_477_);
return v___x_489_;
}
else
{
lean_object* v___x_491_; 
lean_dec(v_fst_481_);
lean_dec_ref_known(v___x_292_, 3);
if (v_isShared_485_ == 0)
{
lean_ctor_set(v___x_484_, 0, v_e_275_);
v___x_491_ = v___x_484_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v_e_275_);
lean_ctor_set(v_reuseFailAlloc_495_, 1, v_snd_482_);
v___x_491_ = v_reuseFailAlloc_495_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
lean_object* v___x_493_; 
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 0, v___x_491_);
v___x_493_ = v___x_479_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v___x_491_);
lean_ctor_set(v_reuseFailAlloc_494_, 1, v_a_477_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_275_, 3);
lean_dec_ref_known(v___x_292_, 3);
return v___x_475_;
}
}
default: 
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_11015__overap_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
lean_dec_ref_known(v___x_292_, 3);
lean_dec_ref(v_fn_277_);
lean_dec(v_offset_276_);
lean_dec_ref(v_e_275_);
v___x_498_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__23, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__23_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__23);
v___x_499_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__27, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__27_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__27);
v___x_11015__overap_500_ = l_panic___redArg(v___x_498_, v___x_499_);
v___x_501_ = lean_box(v_a_279_);
lean_inc_ref(v_a_280_);
v___x_502_ = lean_apply_4(v___x_11015__overap_500_, v_a_278_, v___x_501_, v_a_280_, v_a_281_);
return v___x_502_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(lean_object* v_e_503_, lean_object* v_offset_504_, lean_object* v_f_505_, lean_object* v_a_506_, uint8_t v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_){
_start:
{
lean_object* v___f_510_; lean_object* v_key_511_; lean_object* v___f_512_; lean_object* v___x_513_; 
v___f_510_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__3));
lean_inc(v_offset_504_);
lean_inc_ref(v_e_503_);
v_key_511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_511_, 0, v_e_503_);
lean_ctor_set(v_key_511_, 1, v_offset_504_);
v___f_512_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__5, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__5_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__5);
lean_inc_ref(v_key_511_);
v___x_513_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_512_, v___f_510_, v_a_506_, v_key_511_);
if (lean_obj_tag(v___x_513_) == 1)
{
lean_object* v_val_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
lean_dec_ref_known(v_key_511_, 2);
lean_dec_ref(v_f_505_);
lean_dec(v_offset_504_);
lean_dec_ref(v_e_503_);
v_val_514_ = lean_ctor_get(v___x_513_, 0);
lean_inc(v_val_514_);
lean_dec_ref_known(v___x_513_, 1);
v___x_515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_515_, 0, v_val_514_);
lean_ctor_set(v___x_515_, 1, v_a_506_);
v___x_516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_516_, 0, v___x_515_);
lean_ctor_set(v___x_516_, 1, v_a_509_);
return v___x_516_;
}
else
{
lean_object* v___x_517_; lean_object* v___x_518_; 
lean_dec(v___x_513_);
v___x_517_ = lean_box(v_a_507_);
lean_inc_ref(v_f_505_);
lean_inc_ref(v_a_508_);
lean_inc(v_offset_504_);
lean_inc_ref(v_e_503_);
v___x_518_ = lean_apply_5(v_f_505_, v_e_503_, v_offset_504_, v___x_517_, v_a_508_, v_a_509_);
if (lean_obj_tag(v___x_518_) == 0)
{
lean_object* v_a_519_; 
v_a_519_ = lean_ctor_get(v___x_518_, 0);
lean_inc(v_a_519_);
if (lean_obj_tag(v_a_519_) == 1)
{
lean_object* v_a_520_; lean_object* v_val_521_; lean_object* v___x_522_; 
lean_dec_ref(v_f_505_);
lean_dec(v_offset_504_);
lean_dec_ref(v_e_503_);
v_a_520_ = lean_ctor_get(v___x_518_, 1);
lean_inc(v_a_520_);
lean_dec_ref_known(v___x_518_, 2);
v_val_521_ = lean_ctor_get(v_a_519_, 0);
lean_inc(v_val_521_);
lean_dec_ref_known(v_a_519_, 1);
v___x_522_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(v_key_511_, v_val_521_, v_a_506_, v_a_520_);
return v___x_522_;
}
else
{
lean_dec(v_a_519_);
switch(lean_obj_tag(v_e_503_))
{
case 9:
{
lean_object* v_a_523_; lean_object* v___x_524_; 
lean_dec_ref(v_f_505_);
lean_dec(v_offset_504_);
v_a_523_ = lean_ctor_get(v___x_518_, 1);
lean_inc(v_a_523_);
lean_dec_ref_known(v___x_518_, 2);
v___x_524_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(v_key_511_, v_e_503_, v_a_506_, v_a_523_);
return v___x_524_;
}
case 2:
{
lean_object* v_a_525_; lean_object* v___x_526_; 
lean_dec_ref(v_f_505_);
lean_dec(v_offset_504_);
v_a_525_ = lean_ctor_get(v___x_518_, 1);
lean_inc(v_a_525_);
lean_dec_ref_known(v___x_518_, 2);
v___x_526_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(v_key_511_, v_e_503_, v_a_506_, v_a_525_);
return v___x_526_;
}
case 0:
{
lean_object* v_a_527_; lean_object* v___x_528_; 
lean_dec_ref(v_f_505_);
lean_dec(v_offset_504_);
v_a_527_ = lean_ctor_get(v___x_518_, 1);
lean_inc(v_a_527_);
lean_dec_ref_known(v___x_518_, 2);
v___x_528_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(v_key_511_, v_e_503_, v_a_506_, v_a_527_);
return v___x_528_;
}
case 1:
{
lean_object* v_a_529_; lean_object* v___x_530_; 
lean_dec_ref(v_f_505_);
lean_dec(v_offset_504_);
v_a_529_ = lean_ctor_get(v___x_518_, 1);
lean_inc(v_a_529_);
lean_dec_ref_known(v___x_518_, 2);
v___x_530_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(v_key_511_, v_e_503_, v_a_506_, v_a_529_);
return v___x_530_;
}
case 4:
{
lean_object* v_a_531_; lean_object* v___x_532_; 
lean_dec_ref(v_f_505_);
lean_dec(v_offset_504_);
v_a_531_ = lean_ctor_get(v___x_518_, 1);
lean_inc(v_a_531_);
lean_dec_ref_known(v___x_518_, 2);
v___x_532_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(v_key_511_, v_e_503_, v_a_506_, v_a_531_);
return v___x_532_;
}
case 3:
{
lean_object* v_a_533_; lean_object* v___x_534_; 
lean_dec_ref(v_f_505_);
lean_dec(v_offset_504_);
v_a_533_ = lean_ctor_get(v___x_518_, 1);
lean_inc(v_a_533_);
lean_dec_ref_known(v___x_518_, 2);
v___x_534_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(v_key_511_, v_e_503_, v_a_506_, v_a_533_);
return v___x_534_;
}
default: 
{
lean_object* v_a_535_; lean_object* v___x_536_; 
v_a_535_ = lean_ctor_get(v___x_518_, 1);
lean_inc(v_a_535_);
lean_dec_ref_known(v___x_518_, 2);
v___x_536_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit(v_e_503_, v_offset_504_, v_f_505_, v_a_506_, v_a_507_, v_a_508_, v_a_535_);
if (lean_obj_tag(v___x_536_) == 0)
{
lean_object* v_a_537_; lean_object* v_a_538_; lean_object* v_fst_539_; lean_object* v_snd_540_; lean_object* v___x_541_; 
v_a_537_ = lean_ctor_get(v___x_536_, 0);
lean_inc(v_a_537_);
v_a_538_ = lean_ctor_get(v___x_536_, 1);
lean_inc(v_a_538_);
lean_dec_ref_known(v___x_536_, 2);
v_fst_539_ = lean_ctor_get(v_a_537_, 0);
lean_inc(v_fst_539_);
v_snd_540_ = lean_ctor_get(v_a_537_, 1);
lean_inc(v_snd_540_);
lean_dec(v_a_537_);
v___x_541_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(v_key_511_, v_fst_539_, v_snd_540_, v_a_538_);
return v___x_541_;
}
else
{
lean_dec_ref_known(v_key_511_, 2);
return v___x_536_;
}
}
}
}
}
else
{
lean_object* v_a_542_; lean_object* v_a_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_550_; 
lean_dec_ref_known(v_key_511_, 2);
lean_dec_ref(v_a_506_);
lean_dec_ref(v_f_505_);
lean_dec(v_offset_504_);
lean_dec_ref(v_e_503_);
v_a_542_ = lean_ctor_get(v___x_518_, 0);
v_a_543_ = lean_ctor_get(v___x_518_, 1);
v_isSharedCheck_550_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_550_ == 0)
{
v___x_545_ = v___x_518_;
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_a_543_);
lean_inc(v_a_542_);
lean_dec(v___x_518_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_548_; 
if (v_isShared_546_ == 0)
{
v___x_548_ = v___x_545_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v_a_542_);
lean_ctor_set(v_reuseFailAlloc_549_, 1, v_a_543_);
v___x_548_ = v_reuseFailAlloc_549_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
return v___x_548_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___boxed(lean_object* v_e_551_, lean_object* v_offset_552_, lean_object* v_f_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_){
_start:
{
uint8_t v_a_boxed_558_; lean_object* v_res_559_; 
v_a_boxed_558_ = lean_unbox(v_a_555_);
v_res_559_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_e_551_, v_offset_552_, v_f_553_, v_a_554_, v_a_boxed_558_, v_a_556_, v_a_557_);
lean_dec_ref(v_a_556_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___boxed(lean_object* v_e_560_, lean_object* v_offset_561_, lean_object* v_fn_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_){
_start:
{
uint8_t v_a_boxed_567_; lean_object* v_res_568_; 
v_a_boxed_567_ = lean_unbox(v_a_564_);
v_res_568_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit(v_e_560_, v_offset_561_, v_fn_562_, v_a_563_, v_a_boxed_567_, v_a_565_, v_a_566_);
lean_dec_ref(v_a_565_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild_match__4_splitter___redArg(lean_object* v_____do__lift_569_, lean_object* v_h__1_570_, lean_object* v_h__2_571_){
_start:
{
if (lean_obj_tag(v_____do__lift_569_) == 1)
{
lean_object* v_val_572_; lean_object* v___x_573_; 
lean_dec(v_h__2_571_);
v_val_572_ = lean_ctor_get(v_____do__lift_569_, 0);
lean_inc(v_val_572_);
lean_dec_ref_known(v_____do__lift_569_, 1);
v___x_573_ = lean_apply_1(v_h__1_570_, v_val_572_);
return v___x_573_;
}
else
{
lean_object* v___x_574_; 
lean_dec(v_h__1_570_);
v___x_574_ = lean_apply_2(v_h__2_571_, v_____do__lift_569_, lean_box(0));
return v___x_574_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild_match__4_splitter(lean_object* v_motive_575_, lean_object* v_____do__lift_576_, lean_object* v_h__1_577_, lean_object* v_h__2_578_){
_start:
{
if (lean_obj_tag(v_____do__lift_576_) == 1)
{
lean_object* v_val_579_; lean_object* v___x_580_; 
lean_dec(v_h__2_578_);
v_val_579_ = lean_ctor_get(v_____do__lift_576_, 0);
lean_inc(v_val_579_);
lean_dec_ref_known(v_____do__lift_576_, 1);
v___x_580_ = lean_apply_1(v_h__1_577_, v_val_579_);
return v___x_580_;
}
else
{
lean_object* v___x_581_; 
lean_dec(v_h__1_577_);
v___x_581_ = lean_apply_2(v_h__2_578_, v_____do__lift_576_, lean_box(0));
return v___x_581_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild_match__1_splitter___redArg(lean_object* v_e_582_, lean_object* v_h__1_583_, lean_object* v_h__2_584_, lean_object* v_h__3_585_, lean_object* v_h__4_586_, lean_object* v_h__5_587_, lean_object* v_h__6_588_, lean_object* v_h__7_589_){
_start:
{
switch(lean_obj_tag(v_e_582_))
{
case 9:
{
lean_object* v_a_590_; lean_object* v___x_591_; 
lean_dec(v_h__7_589_);
lean_dec(v_h__6_588_);
lean_dec(v_h__5_587_);
lean_dec(v_h__4_586_);
lean_dec(v_h__3_585_);
lean_dec(v_h__2_584_);
v_a_590_ = lean_ctor_get(v_e_582_, 0);
lean_inc_ref(v_a_590_);
lean_dec_ref_known(v_e_582_, 1);
v___x_591_ = lean_apply_1(v_h__1_583_, v_a_590_);
return v___x_591_;
}
case 2:
{
lean_object* v_mvarId_592_; lean_object* v___x_593_; 
lean_dec(v_h__7_589_);
lean_dec(v_h__6_588_);
lean_dec(v_h__5_587_);
lean_dec(v_h__4_586_);
lean_dec(v_h__3_585_);
lean_dec(v_h__1_583_);
v_mvarId_592_ = lean_ctor_get(v_e_582_, 0);
lean_inc(v_mvarId_592_);
lean_dec_ref_known(v_e_582_, 1);
v___x_593_ = lean_apply_1(v_h__2_584_, v_mvarId_592_);
return v___x_593_;
}
case 0:
{
lean_object* v_deBruijnIndex_594_; lean_object* v___x_595_; 
lean_dec(v_h__7_589_);
lean_dec(v_h__6_588_);
lean_dec(v_h__5_587_);
lean_dec(v_h__4_586_);
lean_dec(v_h__2_584_);
lean_dec(v_h__1_583_);
v_deBruijnIndex_594_ = lean_ctor_get(v_e_582_, 0);
lean_inc(v_deBruijnIndex_594_);
lean_dec_ref_known(v_e_582_, 1);
v___x_595_ = lean_apply_1(v_h__3_585_, v_deBruijnIndex_594_);
return v___x_595_;
}
case 1:
{
lean_object* v_fvarId_596_; lean_object* v___x_597_; 
lean_dec(v_h__7_589_);
lean_dec(v_h__6_588_);
lean_dec(v_h__5_587_);
lean_dec(v_h__3_585_);
lean_dec(v_h__2_584_);
lean_dec(v_h__1_583_);
v_fvarId_596_ = lean_ctor_get(v_e_582_, 0);
lean_inc(v_fvarId_596_);
lean_dec_ref_known(v_e_582_, 1);
v___x_597_ = lean_apply_1(v_h__4_586_, v_fvarId_596_);
return v___x_597_;
}
case 4:
{
lean_object* v_declName_598_; lean_object* v_us_599_; lean_object* v___x_600_; 
lean_dec(v_h__7_589_);
lean_dec(v_h__6_588_);
lean_dec(v_h__4_586_);
lean_dec(v_h__3_585_);
lean_dec(v_h__2_584_);
lean_dec(v_h__1_583_);
v_declName_598_ = lean_ctor_get(v_e_582_, 0);
lean_inc(v_declName_598_);
v_us_599_ = lean_ctor_get(v_e_582_, 1);
lean_inc(v_us_599_);
lean_dec_ref_known(v_e_582_, 2);
v___x_600_ = lean_apply_2(v_h__5_587_, v_declName_598_, v_us_599_);
return v___x_600_;
}
case 3:
{
lean_object* v_u_601_; lean_object* v___x_602_; 
lean_dec(v_h__7_589_);
lean_dec(v_h__5_587_);
lean_dec(v_h__4_586_);
lean_dec(v_h__3_585_);
lean_dec(v_h__2_584_);
lean_dec(v_h__1_583_);
v_u_601_ = lean_ctor_get(v_e_582_, 0);
lean_inc(v_u_601_);
lean_dec_ref_known(v_e_582_, 1);
v___x_602_ = lean_apply_1(v_h__6_588_, v_u_601_);
return v___x_602_;
}
default: 
{
lean_object* v___x_603_; 
lean_dec(v_h__6_588_);
lean_dec(v_h__5_587_);
lean_dec(v_h__4_586_);
lean_dec(v_h__3_585_);
lean_dec(v_h__2_584_);
lean_dec(v_h__1_583_);
v___x_603_ = lean_apply_7(v_h__7_589_, v_e_582_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_603_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild_match__1_splitter(lean_object* v_motive_604_, lean_object* v_e_605_, lean_object* v_h__1_606_, lean_object* v_h__2_607_, lean_object* v_h__3_608_, lean_object* v_h__4_609_, lean_object* v_h__5_610_, lean_object* v_h__6_611_, lean_object* v_h__7_612_){
_start:
{
switch(lean_obj_tag(v_e_605_))
{
case 9:
{
lean_object* v_a_613_; lean_object* v___x_614_; 
lean_dec(v_h__7_612_);
lean_dec(v_h__6_611_);
lean_dec(v_h__5_610_);
lean_dec(v_h__4_609_);
lean_dec(v_h__3_608_);
lean_dec(v_h__2_607_);
v_a_613_ = lean_ctor_get(v_e_605_, 0);
lean_inc_ref(v_a_613_);
lean_dec_ref_known(v_e_605_, 1);
v___x_614_ = lean_apply_1(v_h__1_606_, v_a_613_);
return v___x_614_;
}
case 2:
{
lean_object* v_mvarId_615_; lean_object* v___x_616_; 
lean_dec(v_h__7_612_);
lean_dec(v_h__6_611_);
lean_dec(v_h__5_610_);
lean_dec(v_h__4_609_);
lean_dec(v_h__3_608_);
lean_dec(v_h__1_606_);
v_mvarId_615_ = lean_ctor_get(v_e_605_, 0);
lean_inc(v_mvarId_615_);
lean_dec_ref_known(v_e_605_, 1);
v___x_616_ = lean_apply_1(v_h__2_607_, v_mvarId_615_);
return v___x_616_;
}
case 0:
{
lean_object* v_deBruijnIndex_617_; lean_object* v___x_618_; 
lean_dec(v_h__7_612_);
lean_dec(v_h__6_611_);
lean_dec(v_h__5_610_);
lean_dec(v_h__4_609_);
lean_dec(v_h__2_607_);
lean_dec(v_h__1_606_);
v_deBruijnIndex_617_ = lean_ctor_get(v_e_605_, 0);
lean_inc(v_deBruijnIndex_617_);
lean_dec_ref_known(v_e_605_, 1);
v___x_618_ = lean_apply_1(v_h__3_608_, v_deBruijnIndex_617_);
return v___x_618_;
}
case 1:
{
lean_object* v_fvarId_619_; lean_object* v___x_620_; 
lean_dec(v_h__7_612_);
lean_dec(v_h__6_611_);
lean_dec(v_h__5_610_);
lean_dec(v_h__3_608_);
lean_dec(v_h__2_607_);
lean_dec(v_h__1_606_);
v_fvarId_619_ = lean_ctor_get(v_e_605_, 0);
lean_inc(v_fvarId_619_);
lean_dec_ref_known(v_e_605_, 1);
v___x_620_ = lean_apply_1(v_h__4_609_, v_fvarId_619_);
return v___x_620_;
}
case 4:
{
lean_object* v_declName_621_; lean_object* v_us_622_; lean_object* v___x_623_; 
lean_dec(v_h__7_612_);
lean_dec(v_h__6_611_);
lean_dec(v_h__4_609_);
lean_dec(v_h__3_608_);
lean_dec(v_h__2_607_);
lean_dec(v_h__1_606_);
v_declName_621_ = lean_ctor_get(v_e_605_, 0);
lean_inc(v_declName_621_);
v_us_622_ = lean_ctor_get(v_e_605_, 1);
lean_inc(v_us_622_);
lean_dec_ref_known(v_e_605_, 2);
v___x_623_ = lean_apply_2(v_h__5_610_, v_declName_621_, v_us_622_);
return v___x_623_;
}
case 3:
{
lean_object* v_u_624_; lean_object* v___x_625_; 
lean_dec(v_h__7_612_);
lean_dec(v_h__5_610_);
lean_dec(v_h__4_609_);
lean_dec(v_h__3_608_);
lean_dec(v_h__2_607_);
lean_dec(v_h__1_606_);
v_u_624_ = lean_ctor_get(v_e_605_, 0);
lean_inc(v_u_624_);
lean_dec_ref_known(v_e_605_, 1);
v___x_625_ = lean_apply_1(v_h__6_611_, v_u_624_);
return v___x_625_;
}
default: 
{
lean_object* v___x_626_; 
lean_dec(v_h__6_611_);
lean_dec(v_h__5_610_);
lean_dec(v_h__4_609_);
lean_dec(v_h__3_608_);
lean_dec(v_h__2_607_);
lean_dec(v_h__1_606_);
v___x_626_ = lean_apply_7(v_h__7_612_, v_e_605_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_626_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit_match__1_splitter___redArg(lean_object* v_e_627_, lean_object* v_h__1_628_, lean_object* v_h__2_629_, lean_object* v_h__3_630_, lean_object* v_h__4_631_, lean_object* v_h__5_632_, lean_object* v_h__6_633_, lean_object* v_h__7_634_, lean_object* v_h__8_635_, lean_object* v_h__9_636_, lean_object* v_h__10_637_, lean_object* v_h__11_638_, lean_object* v_h__12_639_){
_start:
{
switch(lean_obj_tag(v_e_627_))
{
case 0:
{
lean_object* v_deBruijnIndex_640_; lean_object* v___x_641_; 
lean_dec(v_h__12_639_);
lean_dec(v_h__11_638_);
lean_dec(v_h__10_637_);
lean_dec(v_h__9_636_);
lean_dec(v_h__8_635_);
lean_dec(v_h__7_634_);
lean_dec(v_h__6_633_);
lean_dec(v_h__5_632_);
lean_dec(v_h__4_631_);
lean_dec(v_h__2_629_);
lean_dec(v_h__1_628_);
v_deBruijnIndex_640_ = lean_ctor_get(v_e_627_, 0);
lean_inc(v_deBruijnIndex_640_);
lean_dec_ref_known(v_e_627_, 1);
v___x_641_ = lean_apply_1(v_h__3_630_, v_deBruijnIndex_640_);
return v___x_641_;
}
case 1:
{
lean_object* v_fvarId_642_; lean_object* v___x_643_; 
lean_dec(v_h__12_639_);
lean_dec(v_h__11_638_);
lean_dec(v_h__10_637_);
lean_dec(v_h__9_636_);
lean_dec(v_h__8_635_);
lean_dec(v_h__7_634_);
lean_dec(v_h__6_633_);
lean_dec(v_h__5_632_);
lean_dec(v_h__3_630_);
lean_dec(v_h__2_629_);
lean_dec(v_h__1_628_);
v_fvarId_642_ = lean_ctor_get(v_e_627_, 0);
lean_inc(v_fvarId_642_);
lean_dec_ref_known(v_e_627_, 1);
v___x_643_ = lean_apply_1(v_h__4_631_, v_fvarId_642_);
return v___x_643_;
}
case 2:
{
lean_object* v_mvarId_644_; lean_object* v___x_645_; 
lean_dec(v_h__12_639_);
lean_dec(v_h__11_638_);
lean_dec(v_h__10_637_);
lean_dec(v_h__9_636_);
lean_dec(v_h__8_635_);
lean_dec(v_h__7_634_);
lean_dec(v_h__6_633_);
lean_dec(v_h__5_632_);
lean_dec(v_h__4_631_);
lean_dec(v_h__3_630_);
lean_dec(v_h__1_628_);
v_mvarId_644_ = lean_ctor_get(v_e_627_, 0);
lean_inc(v_mvarId_644_);
lean_dec_ref_known(v_e_627_, 1);
v___x_645_ = lean_apply_1(v_h__2_629_, v_mvarId_644_);
return v___x_645_;
}
case 3:
{
lean_object* v_u_646_; lean_object* v___x_647_; 
lean_dec(v_h__12_639_);
lean_dec(v_h__11_638_);
lean_dec(v_h__10_637_);
lean_dec(v_h__9_636_);
lean_dec(v_h__8_635_);
lean_dec(v_h__7_634_);
lean_dec(v_h__5_632_);
lean_dec(v_h__4_631_);
lean_dec(v_h__3_630_);
lean_dec(v_h__2_629_);
lean_dec(v_h__1_628_);
v_u_646_ = lean_ctor_get(v_e_627_, 0);
lean_inc(v_u_646_);
lean_dec_ref_known(v_e_627_, 1);
v___x_647_ = lean_apply_1(v_h__6_633_, v_u_646_);
return v___x_647_;
}
case 4:
{
lean_object* v_declName_648_; lean_object* v_us_649_; lean_object* v___x_650_; 
lean_dec(v_h__12_639_);
lean_dec(v_h__11_638_);
lean_dec(v_h__10_637_);
lean_dec(v_h__9_636_);
lean_dec(v_h__8_635_);
lean_dec(v_h__7_634_);
lean_dec(v_h__6_633_);
lean_dec(v_h__4_631_);
lean_dec(v_h__3_630_);
lean_dec(v_h__2_629_);
lean_dec(v_h__1_628_);
v_declName_648_ = lean_ctor_get(v_e_627_, 0);
lean_inc(v_declName_648_);
v_us_649_ = lean_ctor_get(v_e_627_, 1);
lean_inc(v_us_649_);
lean_dec_ref_known(v_e_627_, 2);
v___x_650_ = lean_apply_2(v_h__5_632_, v_declName_648_, v_us_649_);
return v___x_650_;
}
case 5:
{
lean_object* v_fn_651_; lean_object* v_arg_652_; lean_object* v___x_653_; 
lean_dec(v_h__12_639_);
lean_dec(v_h__11_638_);
lean_dec(v_h__10_637_);
lean_dec(v_h__9_636_);
lean_dec(v_h__8_635_);
lean_dec(v_h__6_633_);
lean_dec(v_h__5_632_);
lean_dec(v_h__4_631_);
lean_dec(v_h__3_630_);
lean_dec(v_h__2_629_);
lean_dec(v_h__1_628_);
v_fn_651_ = lean_ctor_get(v_e_627_, 0);
lean_inc_ref(v_fn_651_);
v_arg_652_ = lean_ctor_get(v_e_627_, 1);
lean_inc_ref(v_arg_652_);
lean_dec_ref_known(v_e_627_, 2);
v___x_653_ = lean_apply_2(v_h__7_634_, v_fn_651_, v_arg_652_);
return v___x_653_;
}
case 6:
{
lean_object* v_binderName_654_; lean_object* v_binderType_655_; lean_object* v_body_656_; uint8_t v_binderInfo_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
lean_dec(v_h__12_639_);
lean_dec(v_h__10_637_);
lean_dec(v_h__9_636_);
lean_dec(v_h__8_635_);
lean_dec(v_h__7_634_);
lean_dec(v_h__6_633_);
lean_dec(v_h__5_632_);
lean_dec(v_h__4_631_);
lean_dec(v_h__3_630_);
lean_dec(v_h__2_629_);
lean_dec(v_h__1_628_);
v_binderName_654_ = lean_ctor_get(v_e_627_, 0);
lean_inc(v_binderName_654_);
v_binderType_655_ = lean_ctor_get(v_e_627_, 1);
lean_inc_ref(v_binderType_655_);
v_body_656_ = lean_ctor_get(v_e_627_, 2);
lean_inc_ref(v_body_656_);
v_binderInfo_657_ = lean_ctor_get_uint8(v_e_627_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_627_, 3);
v___x_658_ = lean_box(v_binderInfo_657_);
v___x_659_ = lean_apply_4(v_h__11_638_, v_binderName_654_, v_binderType_655_, v_body_656_, v___x_658_);
return v___x_659_;
}
case 7:
{
lean_object* v_binderName_660_; lean_object* v_binderType_661_; lean_object* v_body_662_; uint8_t v_binderInfo_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
lean_dec(v_h__12_639_);
lean_dec(v_h__11_638_);
lean_dec(v_h__9_636_);
lean_dec(v_h__8_635_);
lean_dec(v_h__7_634_);
lean_dec(v_h__6_633_);
lean_dec(v_h__5_632_);
lean_dec(v_h__4_631_);
lean_dec(v_h__3_630_);
lean_dec(v_h__2_629_);
lean_dec(v_h__1_628_);
v_binderName_660_ = lean_ctor_get(v_e_627_, 0);
lean_inc(v_binderName_660_);
v_binderType_661_ = lean_ctor_get(v_e_627_, 1);
lean_inc_ref(v_binderType_661_);
v_body_662_ = lean_ctor_get(v_e_627_, 2);
lean_inc_ref(v_body_662_);
v_binderInfo_663_ = lean_ctor_get_uint8(v_e_627_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_627_, 3);
v___x_664_ = lean_box(v_binderInfo_663_);
v___x_665_ = lean_apply_4(v_h__10_637_, v_binderName_660_, v_binderType_661_, v_body_662_, v___x_664_);
return v___x_665_;
}
case 8:
{
lean_object* v_declName_666_; lean_object* v_type_667_; lean_object* v_value_668_; lean_object* v_body_669_; uint8_t v_nondep_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
lean_dec(v_h__11_638_);
lean_dec(v_h__10_637_);
lean_dec(v_h__9_636_);
lean_dec(v_h__8_635_);
lean_dec(v_h__7_634_);
lean_dec(v_h__6_633_);
lean_dec(v_h__5_632_);
lean_dec(v_h__4_631_);
lean_dec(v_h__3_630_);
lean_dec(v_h__2_629_);
lean_dec(v_h__1_628_);
v_declName_666_ = lean_ctor_get(v_e_627_, 0);
lean_inc(v_declName_666_);
v_type_667_ = lean_ctor_get(v_e_627_, 1);
lean_inc_ref(v_type_667_);
v_value_668_ = lean_ctor_get(v_e_627_, 2);
lean_inc_ref(v_value_668_);
v_body_669_ = lean_ctor_get(v_e_627_, 3);
lean_inc_ref(v_body_669_);
v_nondep_670_ = lean_ctor_get_uint8(v_e_627_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_627_, 4);
v___x_671_ = lean_box(v_nondep_670_);
v___x_672_ = lean_apply_5(v_h__12_639_, v_declName_666_, v_type_667_, v_value_668_, v_body_669_, v___x_671_);
return v___x_672_;
}
case 9:
{
lean_object* v_a_673_; lean_object* v___x_674_; 
lean_dec(v_h__12_639_);
lean_dec(v_h__11_638_);
lean_dec(v_h__10_637_);
lean_dec(v_h__9_636_);
lean_dec(v_h__8_635_);
lean_dec(v_h__7_634_);
lean_dec(v_h__6_633_);
lean_dec(v_h__5_632_);
lean_dec(v_h__4_631_);
lean_dec(v_h__3_630_);
lean_dec(v_h__2_629_);
v_a_673_ = lean_ctor_get(v_e_627_, 0);
lean_inc_ref(v_a_673_);
lean_dec_ref_known(v_e_627_, 1);
v___x_674_ = lean_apply_1(v_h__1_628_, v_a_673_);
return v___x_674_;
}
case 10:
{
lean_object* v_data_675_; lean_object* v_expr_676_; lean_object* v___x_677_; 
lean_dec(v_h__12_639_);
lean_dec(v_h__11_638_);
lean_dec(v_h__10_637_);
lean_dec(v_h__9_636_);
lean_dec(v_h__7_634_);
lean_dec(v_h__6_633_);
lean_dec(v_h__5_632_);
lean_dec(v_h__4_631_);
lean_dec(v_h__3_630_);
lean_dec(v_h__2_629_);
lean_dec(v_h__1_628_);
v_data_675_ = lean_ctor_get(v_e_627_, 0);
lean_inc(v_data_675_);
v_expr_676_ = lean_ctor_get(v_e_627_, 1);
lean_inc_ref(v_expr_676_);
lean_dec_ref_known(v_e_627_, 2);
v___x_677_ = lean_apply_2(v_h__8_635_, v_data_675_, v_expr_676_);
return v___x_677_;
}
default: 
{
lean_object* v_typeName_678_; lean_object* v_idx_679_; lean_object* v_struct_680_; lean_object* v___x_681_; 
lean_dec(v_h__12_639_);
lean_dec(v_h__11_638_);
lean_dec(v_h__10_637_);
lean_dec(v_h__8_635_);
lean_dec(v_h__7_634_);
lean_dec(v_h__6_633_);
lean_dec(v_h__5_632_);
lean_dec(v_h__4_631_);
lean_dec(v_h__3_630_);
lean_dec(v_h__2_629_);
lean_dec(v_h__1_628_);
v_typeName_678_ = lean_ctor_get(v_e_627_, 0);
lean_inc(v_typeName_678_);
v_idx_679_ = lean_ctor_get(v_e_627_, 1);
lean_inc(v_idx_679_);
v_struct_680_ = lean_ctor_get(v_e_627_, 2);
lean_inc_ref(v_struct_680_);
lean_dec_ref_known(v_e_627_, 3);
v___x_681_ = lean_apply_3(v_h__9_636_, v_typeName_678_, v_idx_679_, v_struct_680_);
return v___x_681_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit_match__1_splitter(lean_object* v_motive_682_, lean_object* v_e_683_, lean_object* v_h__1_684_, lean_object* v_h__2_685_, lean_object* v_h__3_686_, lean_object* v_h__4_687_, lean_object* v_h__5_688_, lean_object* v_h__6_689_, lean_object* v_h__7_690_, lean_object* v_h__8_691_, lean_object* v_h__9_692_, lean_object* v_h__10_693_, lean_object* v_h__11_694_, lean_object* v_h__12_695_){
_start:
{
switch(lean_obj_tag(v_e_683_))
{
case 0:
{
lean_object* v_deBruijnIndex_696_; lean_object* v___x_697_; 
lean_dec(v_h__12_695_);
lean_dec(v_h__11_694_);
lean_dec(v_h__10_693_);
lean_dec(v_h__9_692_);
lean_dec(v_h__8_691_);
lean_dec(v_h__7_690_);
lean_dec(v_h__6_689_);
lean_dec(v_h__5_688_);
lean_dec(v_h__4_687_);
lean_dec(v_h__2_685_);
lean_dec(v_h__1_684_);
v_deBruijnIndex_696_ = lean_ctor_get(v_e_683_, 0);
lean_inc(v_deBruijnIndex_696_);
lean_dec_ref_known(v_e_683_, 1);
v___x_697_ = lean_apply_1(v_h__3_686_, v_deBruijnIndex_696_);
return v___x_697_;
}
case 1:
{
lean_object* v_fvarId_698_; lean_object* v___x_699_; 
lean_dec(v_h__12_695_);
lean_dec(v_h__11_694_);
lean_dec(v_h__10_693_);
lean_dec(v_h__9_692_);
lean_dec(v_h__8_691_);
lean_dec(v_h__7_690_);
lean_dec(v_h__6_689_);
lean_dec(v_h__5_688_);
lean_dec(v_h__3_686_);
lean_dec(v_h__2_685_);
lean_dec(v_h__1_684_);
v_fvarId_698_ = lean_ctor_get(v_e_683_, 0);
lean_inc(v_fvarId_698_);
lean_dec_ref_known(v_e_683_, 1);
v___x_699_ = lean_apply_1(v_h__4_687_, v_fvarId_698_);
return v___x_699_;
}
case 2:
{
lean_object* v_mvarId_700_; lean_object* v___x_701_; 
lean_dec(v_h__12_695_);
lean_dec(v_h__11_694_);
lean_dec(v_h__10_693_);
lean_dec(v_h__9_692_);
lean_dec(v_h__8_691_);
lean_dec(v_h__7_690_);
lean_dec(v_h__6_689_);
lean_dec(v_h__5_688_);
lean_dec(v_h__4_687_);
lean_dec(v_h__3_686_);
lean_dec(v_h__1_684_);
v_mvarId_700_ = lean_ctor_get(v_e_683_, 0);
lean_inc(v_mvarId_700_);
lean_dec_ref_known(v_e_683_, 1);
v___x_701_ = lean_apply_1(v_h__2_685_, v_mvarId_700_);
return v___x_701_;
}
case 3:
{
lean_object* v_u_702_; lean_object* v___x_703_; 
lean_dec(v_h__12_695_);
lean_dec(v_h__11_694_);
lean_dec(v_h__10_693_);
lean_dec(v_h__9_692_);
lean_dec(v_h__8_691_);
lean_dec(v_h__7_690_);
lean_dec(v_h__5_688_);
lean_dec(v_h__4_687_);
lean_dec(v_h__3_686_);
lean_dec(v_h__2_685_);
lean_dec(v_h__1_684_);
v_u_702_ = lean_ctor_get(v_e_683_, 0);
lean_inc(v_u_702_);
lean_dec_ref_known(v_e_683_, 1);
v___x_703_ = lean_apply_1(v_h__6_689_, v_u_702_);
return v___x_703_;
}
case 4:
{
lean_object* v_declName_704_; lean_object* v_us_705_; lean_object* v___x_706_; 
lean_dec(v_h__12_695_);
lean_dec(v_h__11_694_);
lean_dec(v_h__10_693_);
lean_dec(v_h__9_692_);
lean_dec(v_h__8_691_);
lean_dec(v_h__7_690_);
lean_dec(v_h__6_689_);
lean_dec(v_h__4_687_);
lean_dec(v_h__3_686_);
lean_dec(v_h__2_685_);
lean_dec(v_h__1_684_);
v_declName_704_ = lean_ctor_get(v_e_683_, 0);
lean_inc(v_declName_704_);
v_us_705_ = lean_ctor_get(v_e_683_, 1);
lean_inc(v_us_705_);
lean_dec_ref_known(v_e_683_, 2);
v___x_706_ = lean_apply_2(v_h__5_688_, v_declName_704_, v_us_705_);
return v___x_706_;
}
case 5:
{
lean_object* v_fn_707_; lean_object* v_arg_708_; lean_object* v___x_709_; 
lean_dec(v_h__12_695_);
lean_dec(v_h__11_694_);
lean_dec(v_h__10_693_);
lean_dec(v_h__9_692_);
lean_dec(v_h__8_691_);
lean_dec(v_h__6_689_);
lean_dec(v_h__5_688_);
lean_dec(v_h__4_687_);
lean_dec(v_h__3_686_);
lean_dec(v_h__2_685_);
lean_dec(v_h__1_684_);
v_fn_707_ = lean_ctor_get(v_e_683_, 0);
lean_inc_ref(v_fn_707_);
v_arg_708_ = lean_ctor_get(v_e_683_, 1);
lean_inc_ref(v_arg_708_);
lean_dec_ref_known(v_e_683_, 2);
v___x_709_ = lean_apply_2(v_h__7_690_, v_fn_707_, v_arg_708_);
return v___x_709_;
}
case 6:
{
lean_object* v_binderName_710_; lean_object* v_binderType_711_; lean_object* v_body_712_; uint8_t v_binderInfo_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
lean_dec(v_h__12_695_);
lean_dec(v_h__10_693_);
lean_dec(v_h__9_692_);
lean_dec(v_h__8_691_);
lean_dec(v_h__7_690_);
lean_dec(v_h__6_689_);
lean_dec(v_h__5_688_);
lean_dec(v_h__4_687_);
lean_dec(v_h__3_686_);
lean_dec(v_h__2_685_);
lean_dec(v_h__1_684_);
v_binderName_710_ = lean_ctor_get(v_e_683_, 0);
lean_inc(v_binderName_710_);
v_binderType_711_ = lean_ctor_get(v_e_683_, 1);
lean_inc_ref(v_binderType_711_);
v_body_712_ = lean_ctor_get(v_e_683_, 2);
lean_inc_ref(v_body_712_);
v_binderInfo_713_ = lean_ctor_get_uint8(v_e_683_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_683_, 3);
v___x_714_ = lean_box(v_binderInfo_713_);
v___x_715_ = lean_apply_4(v_h__11_694_, v_binderName_710_, v_binderType_711_, v_body_712_, v___x_714_);
return v___x_715_;
}
case 7:
{
lean_object* v_binderName_716_; lean_object* v_binderType_717_; lean_object* v_body_718_; uint8_t v_binderInfo_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
lean_dec(v_h__12_695_);
lean_dec(v_h__11_694_);
lean_dec(v_h__9_692_);
lean_dec(v_h__8_691_);
lean_dec(v_h__7_690_);
lean_dec(v_h__6_689_);
lean_dec(v_h__5_688_);
lean_dec(v_h__4_687_);
lean_dec(v_h__3_686_);
lean_dec(v_h__2_685_);
lean_dec(v_h__1_684_);
v_binderName_716_ = lean_ctor_get(v_e_683_, 0);
lean_inc(v_binderName_716_);
v_binderType_717_ = lean_ctor_get(v_e_683_, 1);
lean_inc_ref(v_binderType_717_);
v_body_718_ = lean_ctor_get(v_e_683_, 2);
lean_inc_ref(v_body_718_);
v_binderInfo_719_ = lean_ctor_get_uint8(v_e_683_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_683_, 3);
v___x_720_ = lean_box(v_binderInfo_719_);
v___x_721_ = lean_apply_4(v_h__10_693_, v_binderName_716_, v_binderType_717_, v_body_718_, v___x_720_);
return v___x_721_;
}
case 8:
{
lean_object* v_declName_722_; lean_object* v_type_723_; lean_object* v_value_724_; lean_object* v_body_725_; uint8_t v_nondep_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
lean_dec(v_h__11_694_);
lean_dec(v_h__10_693_);
lean_dec(v_h__9_692_);
lean_dec(v_h__8_691_);
lean_dec(v_h__7_690_);
lean_dec(v_h__6_689_);
lean_dec(v_h__5_688_);
lean_dec(v_h__4_687_);
lean_dec(v_h__3_686_);
lean_dec(v_h__2_685_);
lean_dec(v_h__1_684_);
v_declName_722_ = lean_ctor_get(v_e_683_, 0);
lean_inc(v_declName_722_);
v_type_723_ = lean_ctor_get(v_e_683_, 1);
lean_inc_ref(v_type_723_);
v_value_724_ = lean_ctor_get(v_e_683_, 2);
lean_inc_ref(v_value_724_);
v_body_725_ = lean_ctor_get(v_e_683_, 3);
lean_inc_ref(v_body_725_);
v_nondep_726_ = lean_ctor_get_uint8(v_e_683_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_683_, 4);
v___x_727_ = lean_box(v_nondep_726_);
v___x_728_ = lean_apply_5(v_h__12_695_, v_declName_722_, v_type_723_, v_value_724_, v_body_725_, v___x_727_);
return v___x_728_;
}
case 9:
{
lean_object* v_a_729_; lean_object* v___x_730_; 
lean_dec(v_h__12_695_);
lean_dec(v_h__11_694_);
lean_dec(v_h__10_693_);
lean_dec(v_h__9_692_);
lean_dec(v_h__8_691_);
lean_dec(v_h__7_690_);
lean_dec(v_h__6_689_);
lean_dec(v_h__5_688_);
lean_dec(v_h__4_687_);
lean_dec(v_h__3_686_);
lean_dec(v_h__2_685_);
v_a_729_ = lean_ctor_get(v_e_683_, 0);
lean_inc_ref(v_a_729_);
lean_dec_ref_known(v_e_683_, 1);
v___x_730_ = lean_apply_1(v_h__1_684_, v_a_729_);
return v___x_730_;
}
case 10:
{
lean_object* v_data_731_; lean_object* v_expr_732_; lean_object* v___x_733_; 
lean_dec(v_h__12_695_);
lean_dec(v_h__11_694_);
lean_dec(v_h__10_693_);
lean_dec(v_h__9_692_);
lean_dec(v_h__7_690_);
lean_dec(v_h__6_689_);
lean_dec(v_h__5_688_);
lean_dec(v_h__4_687_);
lean_dec(v_h__3_686_);
lean_dec(v_h__2_685_);
lean_dec(v_h__1_684_);
v_data_731_ = lean_ctor_get(v_e_683_, 0);
lean_inc(v_data_731_);
v_expr_732_ = lean_ctor_get(v_e_683_, 1);
lean_inc_ref(v_expr_732_);
lean_dec_ref_known(v_e_683_, 2);
v___x_733_ = lean_apply_2(v_h__8_691_, v_data_731_, v_expr_732_);
return v___x_733_;
}
default: 
{
lean_object* v_typeName_734_; lean_object* v_idx_735_; lean_object* v_struct_736_; lean_object* v___x_737_; 
lean_dec(v_h__12_695_);
lean_dec(v_h__11_694_);
lean_dec(v_h__10_693_);
lean_dec(v_h__8_691_);
lean_dec(v_h__7_690_);
lean_dec(v_h__6_689_);
lean_dec(v_h__5_688_);
lean_dec(v_h__4_687_);
lean_dec(v_h__3_686_);
lean_dec(v_h__2_685_);
lean_dec(v_h__1_684_);
v_typeName_734_ = lean_ctor_get(v_e_683_, 0);
lean_inc(v_typeName_734_);
v_idx_735_ = lean_ctor_get(v_e_683_, 1);
lean_inc(v_idx_735_);
v_struct_736_ = lean_ctor_get(v_e_683_, 2);
lean_inc_ref(v_struct_736_);
lean_dec_ref_known(v_e_683_, 3);
v___x_737_ = lean_apply_3(v_h__9_692_, v_typeName_734_, v_idx_735_, v_struct_736_);
return v___x_737_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Sym_replaceS_x27___closed__0(void){
_start:
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_738_ = lean_box(0);
v___x_739_ = lean_unsigned_to_nat(16u);
v___x_740_ = lean_mk_array(v___x_739_, v___x_738_);
return v___x_740_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_replaceS_x27___closed__1(void){
_start:
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_741_ = lean_obj_once(&l_Lean_Meta_Sym_replaceS_x27___closed__0, &l_Lean_Meta_Sym_replaceS_x27___closed__0_once, _init_l_Lean_Meta_Sym_replaceS_x27___closed__0);
v___x_742_ = lean_unsigned_to_nat(0u);
v___x_743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_743_, 0, v___x_742_);
lean_ctor_set(v___x_743_, 1, v___x_741_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_replaceS_x27(lean_object* v_e_744_, lean_object* v_f_745_, uint8_t v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_){
_start:
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_749_ = lean_unsigned_to_nat(0u);
v___x_750_ = lean_box(v_a_746_);
lean_inc_ref(v_f_745_);
lean_inc_ref(v_a_747_);
lean_inc_ref(v_e_744_);
v___x_751_ = lean_apply_5(v_f_745_, v_e_744_, v___x_749_, v___x_750_, v_a_747_, v_a_748_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_object* v_a_752_; 
v_a_752_ = lean_ctor_get(v___x_751_, 0);
lean_inc(v_a_752_);
if (lean_obj_tag(v_a_752_) == 1)
{
lean_object* v_a_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_761_; 
lean_dec_ref(v_f_745_);
lean_dec_ref(v_e_744_);
v_a_753_ = lean_ctor_get(v___x_751_, 1);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_761_ == 0)
{
lean_object* v_unused_762_; 
v_unused_762_ = lean_ctor_get(v___x_751_, 0);
lean_dec(v_unused_762_);
v___x_755_ = v___x_751_;
v_isShared_756_ = v_isSharedCheck_761_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_a_753_);
lean_dec(v___x_751_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_761_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v_val_757_; lean_object* v___x_759_; 
v_val_757_ = lean_ctor_get(v_a_752_, 0);
lean_inc(v_val_757_);
lean_dec_ref_known(v_a_752_, 1);
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 0, v_val_757_);
v___x_759_ = v___x_755_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_val_757_);
lean_ctor_set(v_reuseFailAlloc_760_, 1, v_a_753_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
else
{
lean_dec(v_a_752_);
switch(lean_obj_tag(v_e_744_))
{
case 9:
{
lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_770_; 
lean_dec_ref(v_f_745_);
v_a_763_ = lean_ctor_get(v___x_751_, 1);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_770_ == 0)
{
lean_object* v_unused_771_; 
v_unused_771_ = lean_ctor_get(v___x_751_, 0);
lean_dec(v_unused_771_);
v___x_765_ = v___x_751_;
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_751_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_768_; 
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 0, v_e_744_);
v___x_768_ = v___x_765_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_e_744_);
lean_ctor_set(v_reuseFailAlloc_769_, 1, v_a_763_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
case 2:
{
lean_object* v_a_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_779_; 
lean_dec_ref(v_f_745_);
v_a_772_ = lean_ctor_get(v___x_751_, 1);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_779_ == 0)
{
lean_object* v_unused_780_; 
v_unused_780_ = lean_ctor_get(v___x_751_, 0);
lean_dec(v_unused_780_);
v___x_774_ = v___x_751_;
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_a_772_);
lean_dec(v___x_751_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_777_; 
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 0, v_e_744_);
v___x_777_ = v___x_774_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_e_744_);
lean_ctor_set(v_reuseFailAlloc_778_, 1, v_a_772_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
}
case 0:
{
lean_object* v_a_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_788_; 
lean_dec_ref(v_f_745_);
v_a_781_ = lean_ctor_get(v___x_751_, 1);
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_788_ == 0)
{
lean_object* v_unused_789_; 
v_unused_789_ = lean_ctor_get(v___x_751_, 0);
lean_dec(v_unused_789_);
v___x_783_ = v___x_751_;
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_a_781_);
lean_dec(v___x_751_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_786_; 
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 0, v_e_744_);
v___x_786_ = v___x_783_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_e_744_);
lean_ctor_set(v_reuseFailAlloc_787_, 1, v_a_781_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
case 1:
{
lean_object* v_a_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_797_; 
lean_dec_ref(v_f_745_);
v_a_790_ = lean_ctor_get(v___x_751_, 1);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_797_ == 0)
{
lean_object* v_unused_798_; 
v_unused_798_ = lean_ctor_get(v___x_751_, 0);
lean_dec(v_unused_798_);
v___x_792_ = v___x_751_;
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_a_790_);
lean_dec(v___x_751_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_795_; 
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 0, v_e_744_);
v___x_795_ = v___x_792_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_e_744_);
lean_ctor_set(v_reuseFailAlloc_796_, 1, v_a_790_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
case 4:
{
lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_806_; 
lean_dec_ref(v_f_745_);
v_a_799_ = lean_ctor_get(v___x_751_, 1);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_806_ == 0)
{
lean_object* v_unused_807_; 
v_unused_807_ = lean_ctor_get(v___x_751_, 0);
lean_dec(v_unused_807_);
v___x_801_ = v___x_751_;
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_dec(v___x_751_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_804_; 
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 0, v_e_744_);
v___x_804_ = v___x_801_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_e_744_);
lean_ctor_set(v_reuseFailAlloc_805_, 1, v_a_799_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
case 3:
{
lean_object* v_a_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_815_; 
lean_dec_ref(v_f_745_);
v_a_808_ = lean_ctor_get(v___x_751_, 1);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_815_ == 0)
{
lean_object* v_unused_816_; 
v_unused_816_ = lean_ctor_get(v___x_751_, 0);
lean_dec(v_unused_816_);
v___x_810_ = v___x_751_;
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_a_808_);
lean_dec(v___x_751_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v___x_813_; 
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 0, v_e_744_);
v___x_813_ = v___x_810_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_e_744_);
lean_ctor_set(v_reuseFailAlloc_814_, 1, v_a_808_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
default: 
{
lean_object* v_a_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v_a_817_ = lean_ctor_get(v___x_751_, 1);
lean_inc(v_a_817_);
lean_dec_ref_known(v___x_751_, 2);
v___x_818_ = lean_obj_once(&l_Lean_Meta_Sym_replaceS_x27___closed__1, &l_Lean_Meta_Sym_replaceS_x27___closed__1_once, _init_l_Lean_Meta_Sym_replaceS_x27___closed__1);
v___x_819_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit(v_e_744_, v___x_749_, v_f_745_, v___x_818_, v_a_746_, v_a_747_, v_a_817_);
if (lean_obj_tag(v___x_819_) == 0)
{
lean_object* v_a_820_; lean_object* v_a_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_829_; 
v_a_820_ = lean_ctor_get(v___x_819_, 0);
v_a_821_ = lean_ctor_get(v___x_819_, 1);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_819_);
if (v_isSharedCheck_829_ == 0)
{
v___x_823_ = v___x_819_;
v_isShared_824_ = v_isSharedCheck_829_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_a_821_);
lean_inc(v_a_820_);
lean_dec(v___x_819_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_829_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v_fst_825_; lean_object* v___x_827_; 
v_fst_825_ = lean_ctor_get(v_a_820_, 0);
lean_inc(v_fst_825_);
lean_dec(v_a_820_);
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 0, v_fst_825_);
v___x_827_ = v___x_823_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_fst_825_);
lean_ctor_set(v_reuseFailAlloc_828_, 1, v_a_821_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
}
else
{
lean_object* v_a_830_; lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_838_; 
v_a_830_ = lean_ctor_get(v___x_819_, 0);
v_a_831_ = lean_ctor_get(v___x_819_, 1);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_819_);
if (v_isSharedCheck_838_ == 0)
{
v___x_833_ = v___x_819_;
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_inc(v_a_830_);
lean_dec(v___x_819_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_836_; 
if (v_isShared_834_ == 0)
{
v___x_836_ = v___x_833_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_a_830_);
lean_ctor_set(v_reuseFailAlloc_837_, 1, v_a_831_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_839_; lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_847_; 
lean_dec_ref(v_f_745_);
lean_dec_ref(v_e_744_);
v_a_839_ = lean_ctor_get(v___x_751_, 0);
v_a_840_ = lean_ctor_get(v___x_751_, 1);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_847_ == 0)
{
v___x_842_ = v___x_751_;
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_inc(v_a_839_);
lean_dec(v___x_751_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_845_; 
if (v_isShared_843_ == 0)
{
v___x_845_ = v___x_842_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_a_839_);
lean_ctor_set(v_reuseFailAlloc_846_, 1, v_a_840_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_replaceS_x27___boxed(lean_object* v_e_848_, lean_object* v_f_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_){
_start:
{
uint8_t v_a_boxed_853_; lean_object* v_res_854_; 
v_a_boxed_853_ = lean_unbox(v_a_850_);
v_res_854_ = l_Lean_Meta_Sym_replaceS_x27(v_e_848_, v_f_849_, v_a_boxed_853_, v_a_851_, v_a_852_);
lean_dec_ref(v_a_851_);
return v_res_854_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_replaceS___closed__0(void){
_start:
{
lean_object* v___x_855_; 
v___x_855_ = l_Lean_Meta_Sym_instInhabitedSymM(lean_box(0));
return v___x_855_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_replaceS___closed__3(void){
_start:
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_858_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__26));
v___x_859_ = lean_unsigned_to_nat(16u);
v___x_860_ = lean_unsigned_to_nat(62u);
v___x_861_ = ((lean_object*)(l_Lean_Meta_Sym_replaceS___closed__2));
v___x_862_ = ((lean_object*)(l_Lean_Meta_Sym_replaceS___closed__1));
v___x_863_ = l_mkPanicMessageWithDecl(v___x_862_, v___x_861_, v___x_860_, v___x_859_, v___x_858_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_replaceS(lean_object* v_e_864_, lean_object* v_f_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_){
_start:
{
lean_object* v___x_873_; lean_object* v___x_874_; uint8_t v_debug_875_; lean_object* v_env_876_; lean_object* v___x_877_; lean_object* v___x_878_; uint8_t v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_873_ = lean_st_ref_get(v_a_867_);
v___x_874_ = lean_st_ref_get(v_a_871_);
v_debug_875_ = lean_ctor_get_uint8(v___x_873_, sizeof(void*)*10);
lean_dec(v___x_873_);
v_env_876_ = lean_ctor_get(v___x_874_, 0);
lean_inc_ref(v_env_876_);
lean_dec(v___x_874_);
v___x_877_ = lean_box(v_debug_875_);
v___x_878_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_replaceS_x27___boxed), 5, 3);
lean_closure_set(v___x_878_, 0, v_e_864_);
lean_closure_set(v___x_878_, 1, v_f_865_);
lean_closure_set(v___x_878_, 2, v___x_877_);
v___x_879_ = 0;
v___x_880_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_880_, 0, v_env_876_);
lean_ctor_set_uint8(v___x_880_, sizeof(void*)*1, v___x_879_);
lean_ctor_set_uint8(v___x_880_, sizeof(void*)*1 + 1, v___x_879_);
v___x_881_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___x_878_, v___x_880_, v_a_867_);
if (lean_obj_tag(v___x_881_) == 0)
{
lean_object* v_a_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_894_; 
v_a_882_ = lean_ctor_get(v___x_881_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_881_);
if (v_isSharedCheck_894_ == 0)
{
v___x_884_ = v___x_881_;
v_isShared_885_ = v_isSharedCheck_894_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_a_882_);
lean_dec(v___x_881_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_894_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
if (lean_obj_tag(v_a_882_) == 0)
{
lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_27__overap_888_; lean_object* v___x_889_; 
lean_dec_ref_known(v_a_882_, 1);
lean_del_object(v___x_884_);
v___x_886_ = lean_obj_once(&l_Lean_Meta_Sym_replaceS___closed__0, &l_Lean_Meta_Sym_replaceS___closed__0_once, _init_l_Lean_Meta_Sym_replaceS___closed__0);
v___x_887_ = lean_obj_once(&l_Lean_Meta_Sym_replaceS___closed__3, &l_Lean_Meta_Sym_replaceS___closed__3_once, _init_l_Lean_Meta_Sym_replaceS___closed__3);
v___x_27__overap_888_ = l_panic___redArg(v___x_886_, v___x_887_);
lean_inc(v_a_871_);
lean_inc_ref(v_a_870_);
lean_inc(v_a_869_);
lean_inc_ref(v_a_868_);
lean_inc(v_a_867_);
lean_inc_ref(v_a_866_);
v___x_889_ = lean_apply_7(v___x_27__overap_888_, v_a_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, lean_box(0));
return v___x_889_;
}
else
{
lean_object* v_a_890_; lean_object* v___x_892_; 
v_a_890_ = lean_ctor_get(v_a_882_, 0);
lean_inc(v_a_890_);
lean_dec_ref_known(v_a_882_, 1);
if (v_isShared_885_ == 0)
{
lean_ctor_set(v___x_884_, 0, v_a_890_);
v___x_892_ = v___x_884_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_a_890_);
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
else
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_902_; 
v_a_895_ = lean_ctor_get(v___x_881_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_881_);
if (v_isSharedCheck_902_ == 0)
{
v___x_897_ = v___x_881_;
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_881_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_900_; 
if (v_isShared_898_ == 0)
{
v___x_900_ = v___x_897_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_a_895_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_replaceS___boxed(lean_object* v_e_903_, lean_object* v_f_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l_Lean_Meta_Sym_replaceS(v_e_903_, v_f_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_);
lean_dec(v_a_910_);
lean_dec_ref(v_a_909_);
lean_dec(v_a_908_);
lean_dec_ref(v_a_907_);
lean_dec(v_a_906_);
lean_dec_ref(v_a_905_);
return v_res_912_;
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
