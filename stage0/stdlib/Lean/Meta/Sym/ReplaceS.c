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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_noption_get(lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Sym_instHashableExprPtr___lam__0___boxed(lean_object*);
lean_object* l_UInt64_ofNat___boxed(lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instHashableProd___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instBEqExprPtr___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_instBEqProd___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_instBEqExprPtr___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_instHashableExprPtr___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
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
static lean_once_cell_t l_Lean_Meta_Sym_replaceS_x27___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_replaceS_x27___closed__2;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(lean_object* v_m_1_, lean_object* v_query_2_, lean_object* v_x_3_, lean_object* v_x_4_, lean_object* v_x_5_){
_start:
{
lean_object* v_zero_6_; uint8_t v_isZero_7_; 
v_zero_6_ = lean_unsigned_to_nat(0u);
v_isZero_7_ = lean_nat_dec_eq(v_x_4_, v_zero_6_);
if (v_isZero_7_ == 1)
{
lean_dec(v_x_5_);
lean_dec(v_x_4_);
if (lean_obj_tag(v_x_3_) == 0)
{
lean_object* v___x_8_; 
v___x_8_ = lean_box(2);
return v___x_8_;
}
else
{
lean_object* v_val_9_; lean_object* v___x_11_; uint8_t v_isShared_12_; uint8_t v_isSharedCheck_16_; 
v_val_9_ = lean_ctor_get(v_x_3_, 0);
v_isSharedCheck_16_ = !lean_is_exclusive(v_x_3_);
if (v_isSharedCheck_16_ == 0)
{
v___x_11_ = v_x_3_;
v_isShared_12_ = v_isSharedCheck_16_;
goto v_resetjp_10_;
}
else
{
lean_inc(v_val_9_);
lean_dec(v_x_3_);
v___x_11_ = lean_box(0);
v_isShared_12_ = v_isSharedCheck_16_;
goto v_resetjp_10_;
}
v_resetjp_10_:
{
lean_object* v___x_14_; 
if (v_isShared_12_ == 0)
{
v___x_14_ = v___x_11_;
goto v_reusejp_13_;
}
else
{
lean_object* v_reuseFailAlloc_15_; 
v_reuseFailAlloc_15_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_15_, 0, v_val_9_);
v___x_14_ = v_reuseFailAlloc_15_;
goto v_reusejp_13_;
}
v_reusejp_13_:
{
return v___x_14_;
}
}
}
}
else
{
lean_object* v_keyArray_17_; lean_object* v_valueArray_18_; lean_object* v___x_19_; uint8_t v_isSome_20_; 
v_keyArray_17_ = lean_ctor_get(v_m_1_, 1);
v_valueArray_18_ = lean_ctor_get(v_m_1_, 2);
v___x_19_ = lean_array_fget_borrowed(v_keyArray_17_, v_x_5_);
v_isSome_20_ = lean_noption_is_some(v___x_19_);
if (v_isSome_20_ == 0)
{
lean_dec(v_x_4_);
if (lean_obj_tag(v_x_3_) == 0)
{
lean_object* v___x_21_; 
v___x_21_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_21_, 0, v_x_5_);
return v___x_21_;
}
else
{
lean_object* v_val_22_; lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_29_; 
lean_dec(v_x_5_);
v_val_22_ = lean_ctor_get(v_x_3_, 0);
v_isSharedCheck_29_ = !lean_is_exclusive(v_x_3_);
if (v_isSharedCheck_29_ == 0)
{
v___x_24_ = v_x_3_;
v_isShared_25_ = v_isSharedCheck_29_;
goto v_resetjp_23_;
}
else
{
lean_inc(v_val_22_);
lean_dec(v_x_3_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_29_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
lean_object* v___x_27_; 
if (v_isShared_25_ == 0)
{
v___x_27_ = v___x_24_;
goto v_reusejp_26_;
}
else
{
lean_object* v_reuseFailAlloc_28_; 
v_reuseFailAlloc_28_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_28_, 0, v_val_22_);
v___x_27_ = v_reuseFailAlloc_28_;
goto v_reusejp_26_;
}
v_reusejp_26_:
{
return v___x_27_;
}
}
}
}
else
{
lean_object* v_one_30_; lean_object* v_n_31_; lean_object* v___y_33_; 
v_one_30_ = lean_unsigned_to_nat(1u);
v_n_31_ = lean_nat_sub(v_x_4_, v_one_30_);
lean_dec(v_x_4_);
if (v_isSome_20_ == 0)
{
goto v___jp_39_;
}
else
{
lean_object* v___x_41_; uint8_t v_isSome_42_; 
v___x_41_ = lean_array_fget_borrowed(v_valueArray_18_, v_x_5_);
v_isSome_42_ = lean_noption_is_some(v___x_41_);
if (v_isSome_42_ == 0)
{
goto v___jp_39_;
}
else
{
lean_object* v_val_43_; lean_object* v_fst_44_; lean_object* v_snd_45_; lean_object* v_fst_46_; lean_object* v_snd_47_; lean_object* v_val_48_; uint8_t v___y_50_; size_t v___x_57_; size_t v___x_58_; uint8_t v___x_59_; 
lean_inc(v___x_19_);
v_val_43_ = lean_noption_get(v___x_19_);
v_fst_44_ = lean_ctor_get(v_val_43_, 0);
lean_inc(v_fst_44_);
v_snd_45_ = lean_ctor_get(v_val_43_, 1);
lean_inc(v_snd_45_);
v_fst_46_ = lean_ctor_get(v_query_2_, 0);
v_snd_47_ = lean_ctor_get(v_query_2_, 1);
lean_inc(v___x_41_);
v_val_48_ = lean_noption_get(v___x_41_);
v___x_57_ = lean_ptr_addr(v_fst_44_);
lean_dec(v_fst_44_);
v___x_58_ = lean_ptr_addr(v_fst_46_);
v___x_59_ = lean_usize_dec_eq(v___x_57_, v___x_58_);
if (v___x_59_ == 0)
{
lean_dec(v_snd_45_);
v___y_50_ = v___x_59_;
goto v___jp_49_;
}
else
{
uint8_t v___x_60_; 
v___x_60_ = lean_nat_dec_eq(v_snd_45_, v_snd_47_);
lean_dec(v_snd_45_);
v___y_50_ = v___x_60_;
goto v___jp_49_;
}
v___jp_49_:
{
if (v___y_50_ == 0)
{
lean_object* v___x_51_; lean_object* v___x_52_; uint8_t v___x_53_; 
lean_dec(v_val_48_);
lean_dec(v_val_43_);
v___x_51_ = lean_array_get_size(v_keyArray_17_);
v___x_52_ = lean_nat_add(v_x_5_, v_one_30_);
lean_dec(v_x_5_);
v___x_53_ = lean_nat_dec_lt(v___x_52_, v___x_51_);
if (v___x_53_ == 0)
{
lean_dec(v___x_52_);
v_x_4_ = v_n_31_;
v_x_5_ = v_zero_6_;
goto _start;
}
else
{
v_x_4_ = v_n_31_;
v_x_5_ = v___x_52_;
goto _start;
}
}
else
{
lean_object* v___x_56_; 
lean_dec(v_n_31_);
lean_dec(v_x_3_);
v___x_56_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_56_, 0, v_x_5_);
lean_ctor_set(v___x_56_, 1, v_val_43_);
lean_ctor_set(v___x_56_, 2, v_val_48_);
return v___x_56_;
}
}
}
}
v___jp_32_:
{
lean_object* v___x_34_; lean_object* v___x_35_; uint8_t v___x_36_; 
v___x_34_ = lean_array_get_size(v_keyArray_17_);
v___x_35_ = lean_nat_add(v_x_5_, v_one_30_);
lean_dec(v_x_5_);
v___x_36_ = lean_nat_dec_lt(v___x_35_, v___x_34_);
if (v___x_36_ == 0)
{
lean_dec(v___x_35_);
v_x_3_ = v___y_33_;
v_x_4_ = v_n_31_;
v_x_5_ = v_zero_6_;
goto _start;
}
else
{
v_x_3_ = v___y_33_;
v_x_4_ = v_n_31_;
v_x_5_ = v___x_35_;
goto _start;
}
}
v___jp_39_:
{
if (lean_obj_tag(v_x_3_) == 0)
{
lean_object* v___x_40_; 
lean_inc(v_x_5_);
v___x_40_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_40_, 0, v_x_5_);
v___y_33_ = v___x_40_;
goto v___jp_32_;
}
else
{
v___y_33_ = v_x_3_;
goto v___jp_32_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg___boxed(lean_object* v_m_61_, lean_object* v_query_62_, lean_object* v_x_63_, lean_object* v_x_64_, lean_object* v_x_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_m_61_, v_query_62_, v_x_63_, v_x_64_, v_x_65_);
lean_dec_ref(v_query_62_);
lean_dec_ref(v_m_61_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0___redArg(lean_object* v_m_67_, lean_object* v_query_68_){
_start:
{
lean_object* v_keyArray_69_; lean_object* v_fst_70_; lean_object* v_snd_71_; lean_object* v___x_72_; size_t v___x_73_; size_t v___x_74_; size_t v___x_75_; uint64_t v___x_76_; uint64_t v___x_77_; uint64_t v___x_78_; uint64_t v___x_79_; uint64_t v___x_80_; uint64_t v_fold_81_; uint64_t v___x_82_; uint64_t v___x_83_; uint64_t v___x_84_; size_t v___x_85_; size_t v___x_86_; size_t v___x_87_; size_t v___x_88_; size_t v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v_keyArray_69_ = lean_ctor_get(v_m_67_, 1);
v_fst_70_ = lean_ctor_get(v_query_68_, 0);
v_snd_71_ = lean_ctor_get(v_query_68_, 1);
v___x_72_ = lean_array_get_size(v_keyArray_69_);
v___x_73_ = lean_ptr_addr(v_fst_70_);
v___x_74_ = ((size_t)3ULL);
v___x_75_ = lean_usize_shift_right(v___x_73_, v___x_74_);
v___x_76_ = lean_usize_to_uint64(v___x_75_);
v___x_77_ = lean_uint64_of_nat(v_snd_71_);
v___x_78_ = lean_uint64_mix_hash(v___x_76_, v___x_77_);
v___x_79_ = 32ULL;
v___x_80_ = lean_uint64_shift_right(v___x_78_, v___x_79_);
v_fold_81_ = lean_uint64_xor(v___x_78_, v___x_80_);
v___x_82_ = 16ULL;
v___x_83_ = lean_uint64_shift_right(v_fold_81_, v___x_82_);
v___x_84_ = lean_uint64_xor(v_fold_81_, v___x_83_);
v___x_85_ = lean_uint64_to_usize(v___x_84_);
v___x_86_ = lean_usize_of_nat(v___x_72_);
v___x_87_ = ((size_t)1ULL);
v___x_88_ = lean_usize_sub(v___x_86_, v___x_87_);
v___x_89_ = lean_usize_land(v___x_85_, v___x_88_);
v___x_90_ = lean_usize_to_nat(v___x_89_);
v___x_91_ = lean_box(0);
v___x_92_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_m_67_, v_query_68_, v___x_91_, v___x_72_, v___x_90_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0___redArg___boxed(lean_object* v_m_93_, lean_object* v_query_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0___redArg(v_m_93_, v_query_94_);
lean_dec_ref(v_query_94_);
lean_dec_ref(v_m_93_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__1_spec__2_spec__3___redArg(lean_object* v_b_96_, lean_object* v_acc_97_, lean_object* v_i_98_){
_start:
{
lean_object* v___y_100_; lean_object* v_keyArray_108_; lean_object* v_valueArray_109_; lean_object* v___x_110_; uint8_t v___x_111_; 
v_keyArray_108_ = lean_ctor_get(v_b_96_, 1);
v_valueArray_109_ = lean_ctor_get(v_b_96_, 2);
v___x_110_ = lean_array_get_size(v_keyArray_108_);
v___x_111_ = lean_nat_dec_lt(v_i_98_, v___x_110_);
if (v___x_111_ == 0)
{
lean_dec(v_i_98_);
return v_acc_97_;
}
else
{
lean_object* v___x_112_; uint8_t v_isSome_113_; 
v___x_112_ = lean_array_fget_borrowed(v_keyArray_108_, v_i_98_);
v_isSome_113_ = lean_noption_is_some(v___x_112_);
if (v_isSome_113_ == 0)
{
goto v___jp_104_;
}
else
{
lean_object* v___x_114_; uint8_t v_isSome_115_; 
v___x_114_ = lean_array_fget_borrowed(v_valueArray_109_, v_i_98_);
v_isSome_115_ = lean_noption_is_some(v___x_114_);
if (v_isSome_115_ == 0)
{
goto v___jp_104_;
}
else
{
lean_object* v_val_116_; lean_object* v_val_117_; lean_object* v_i_119_; lean_object* v___x_124_; 
lean_inc(v___x_112_);
v_val_116_ = lean_noption_get(v___x_112_);
lean_inc(v___x_114_);
v_val_117_ = lean_noption_get(v___x_114_);
v___x_124_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0___redArg(v_acc_97_, v_val_116_);
switch(lean_obj_tag(v___x_124_))
{
case 0:
{
lean_object* v_index_125_; lean_object* v_size_126_; lean_object* v___x_127_; 
v_index_125_ = lean_ctor_get(v___x_124_, 0);
lean_inc(v_index_125_);
lean_dec_ref_known(v___x_124_, 3);
v_size_126_ = lean_ctor_get(v_acc_97_, 0);
lean_inc(v_size_126_);
v___x_127_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_97_, v_size_126_, v_index_125_, v_val_116_, v_val_117_);
lean_dec(v_index_125_);
v___y_100_ = v___x_127_;
goto v___jp_99_;
}
case 1:
{
lean_object* v_index_128_; 
v_index_128_ = lean_ctor_get(v___x_124_, 0);
lean_inc(v_index_128_);
lean_dec_ref_known(v___x_124_, 1);
v_i_119_ = v_index_128_;
goto v___jp_118_;
}
default: 
{
lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_129_ = lean_unsigned_to_nat(0u);
v___x_130_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_97_, v___x_129_);
if (lean_obj_tag(v___x_130_) == 0)
{
lean_object* v_index_131_; 
v_index_131_ = lean_ctor_get(v___x_130_, 0);
lean_inc(v_index_131_);
lean_dec_ref_known(v___x_130_, 1);
v_i_119_ = v_index_131_;
goto v___jp_118_;
}
else
{
lean_dec(v_val_117_);
lean_dec(v_val_116_);
v___y_100_ = v_acc_97_;
goto v___jp_99_;
}
}
}
v___jp_118_:
{
lean_object* v_size_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v_size_120_ = lean_ctor_get(v_acc_97_, 0);
v___x_121_ = lean_unsigned_to_nat(1u);
v___x_122_ = lean_nat_add(v_size_120_, v___x_121_);
v___x_123_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_97_, v___x_122_, v_i_119_, v_val_116_, v_val_117_);
lean_dec(v_i_119_);
v___y_100_ = v___x_123_;
goto v___jp_99_;
}
}
}
}
v___jp_99_:
{
lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_101_ = lean_unsigned_to_nat(1u);
v___x_102_ = lean_nat_add(v_i_98_, v___x_101_);
lean_dec(v_i_98_);
v_acc_97_ = v___y_100_;
v_i_98_ = v___x_102_;
goto _start;
}
v___jp_104_:
{
lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_105_ = lean_unsigned_to_nat(1u);
v___x_106_ = lean_nat_add(v_i_98_, v___x_105_);
lean_dec(v_i_98_);
v_i_98_ = v___x_106_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_b_132_, lean_object* v_acc_133_, lean_object* v_i_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__1_spec__2_spec__3___redArg(v_b_132_, v_acc_133_, v_i_134_);
lean_dec_ref(v_b_132_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(lean_object* v_init_136_, lean_object* v_b_137_){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_138_ = lean_unsigned_to_nat(0u);
v___x_139_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__1_spec__2_spec__3___redArg(v_b_137_, v_init_136_, v___x_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg___boxed(lean_object* v_init_140_, lean_object* v_b_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(v_init_140_, v_b_141_);
lean_dec_ref(v_b_141_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__1___redArg(lean_object* v_m_143_){
_start:
{
lean_object* v_keyArray_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v_cellCount_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v_target_151_; lean_object* v___x_152_; 
v_keyArray_144_ = lean_ctor_get(v_m_143_, 1);
v___x_145_ = lean_array_get_size(v_keyArray_144_);
v___x_146_ = lean_unsigned_to_nat(2u);
v_cellCount_147_ = lean_nat_mul(v___x_145_, v___x_146_);
v___x_148_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_147_);
v___x_149_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_147_);
v___x_150_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_147_);
v_target_151_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_151_, 0, v___x_148_);
lean_ctor_set(v_target_151_, 1, v___x_149_);
lean_ctor_set(v_target_151_, 2, v___x_150_);
v___x_152_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(v_target_151_, v_m_143_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__1___redArg___boxed(lean_object* v_m_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__1___redArg(v_m_153_);
lean_dec_ref(v_m_153_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(lean_object* v_key_155_, lean_object* v_r_156_, lean_object* v_a_157_, lean_object* v_a_158_){
_start:
{
lean_object* v___y_160_; lean_object* v___y_164_; lean_object* v_i_165_; lean_object* v___y_181_; lean_object* v_i_182_; lean_object* v___y_188_; lean_object* v___x_197_; 
v___x_197_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_157_, v_key_155_);
switch(lean_obj_tag(v___x_197_))
{
case 0:
{
lean_object* v_index_198_; lean_object* v_size_199_; lean_object* v___x_200_; 
v_index_198_ = lean_ctor_get(v___x_197_, 0);
lean_inc(v_index_198_);
lean_dec_ref_known(v___x_197_, 3);
v_size_199_ = lean_ctor_get(v_a_157_, 0);
lean_inc(v_size_199_);
lean_inc_ref(v_r_156_);
v___x_200_ = l_Std_DHashMap_Raw_setEntry___redArg(v_a_157_, v_size_199_, v_index_198_, v_key_155_, v_r_156_);
lean_dec(v_index_198_);
v___y_160_ = v___x_200_;
goto v___jp_159_;
}
case 1:
{
lean_object* v_index_201_; lean_object* v_size_202_; lean_object* v_keyArray_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; uint8_t v___x_207_; 
v_index_201_ = lean_ctor_get(v___x_197_, 0);
lean_inc(v_index_201_);
lean_dec_ref_known(v___x_197_, 1);
v_size_202_ = lean_ctor_get(v_a_157_, 0);
v_keyArray_203_ = lean_ctor_get(v_a_157_, 1);
v___x_204_ = lean_unsigned_to_nat(1u);
v___x_205_ = lean_nat_add(v_size_202_, v___x_204_);
v___x_206_ = lean_array_get_size(v_keyArray_203_);
v___x_207_ = lean_nat_dec_lt(v___x_205_, v___x_206_);
if (v___x_207_ == 0)
{
lean_dec(v___x_205_);
lean_dec(v_index_201_);
goto v___jp_170_;
}
else
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; uint8_t v___x_212_; 
v___x_208_ = lean_unsigned_to_nat(4u);
v___x_209_ = lean_nat_mul(v___x_205_, v___x_208_);
v___x_210_ = lean_unsigned_to_nat(3u);
v___x_211_ = lean_nat_mul(v___x_206_, v___x_210_);
v___x_212_ = lean_nat_dec_le(v___x_209_, v___x_211_);
lean_dec(v___x_211_);
lean_dec(v___x_209_);
if (v___x_212_ == 0)
{
lean_dec(v___x_205_);
lean_dec(v_index_201_);
goto v___jp_170_;
}
else
{
lean_object* v___x_213_; 
lean_inc_ref(v_r_156_);
v___x_213_ = l_Std_DHashMap_Raw_setEntry___redArg(v_a_157_, v___x_205_, v_index_201_, v_key_155_, v_r_156_);
lean_dec(v_index_201_);
v___y_160_ = v___x_213_;
goto v___jp_159_;
}
}
}
default: 
{
lean_object* v_size_214_; lean_object* v_keyArray_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; uint8_t v___x_219_; 
v_size_214_ = lean_ctor_get(v_a_157_, 0);
v_keyArray_215_ = lean_ctor_get(v_a_157_, 1);
v___x_216_ = lean_unsigned_to_nat(1u);
v___x_217_ = lean_nat_add(v_size_214_, v___x_216_);
v___x_218_ = lean_array_get_size(v_keyArray_215_);
v___x_219_ = lean_nat_dec_lt(v___x_217_, v___x_218_);
if (v___x_219_ == 0)
{
lean_object* v___x_220_; 
lean_dec(v___x_217_);
v___x_220_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__1___redArg(v_a_157_);
lean_dec_ref(v_a_157_);
v___y_188_ = v___x_220_;
goto v___jp_187_;
}
else
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; uint8_t v___x_225_; 
v___x_221_ = lean_unsigned_to_nat(4u);
v___x_222_ = lean_nat_mul(v___x_217_, v___x_221_);
lean_dec(v___x_217_);
v___x_223_ = lean_unsigned_to_nat(3u);
v___x_224_ = lean_nat_mul(v___x_218_, v___x_223_);
v___x_225_ = lean_nat_dec_le(v___x_222_, v___x_224_);
lean_dec(v___x_224_);
lean_dec(v___x_222_);
if (v___x_225_ == 0)
{
lean_object* v___x_226_; 
v___x_226_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__1___redArg(v_a_157_);
lean_dec_ref(v_a_157_);
v___y_188_ = v___x_226_;
goto v___jp_187_;
}
else
{
v___y_188_ = v_a_157_;
goto v___jp_187_;
}
}
}
}
v___jp_159_:
{
lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_161_, 0, v_r_156_);
lean_ctor_set(v___x_161_, 1, v___y_160_);
v___x_162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
lean_ctor_set(v___x_162_, 1, v_a_158_);
return v___x_162_;
}
v___jp_163_:
{
lean_object* v_size_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v_size_166_ = lean_ctor_get(v___y_164_, 0);
v___x_167_ = lean_unsigned_to_nat(1u);
v___x_168_ = lean_nat_add(v_size_166_, v___x_167_);
lean_inc_ref(v_r_156_);
v___x_169_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_164_, v___x_168_, v_i_165_, v_key_155_, v_r_156_);
lean_dec(v_i_165_);
v___y_160_ = v___x_169_;
goto v___jp_159_;
}
v___jp_170_:
{
lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_171_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__1___redArg(v_a_157_);
lean_dec_ref(v_a_157_);
v___x_172_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0___redArg(v___x_171_, v_key_155_);
switch(lean_obj_tag(v___x_172_))
{
case 0:
{
lean_object* v_index_173_; lean_object* v_size_174_; lean_object* v___x_175_; 
v_index_173_ = lean_ctor_get(v___x_172_, 0);
lean_inc(v_index_173_);
lean_dec_ref_known(v___x_172_, 3);
v_size_174_ = lean_ctor_get(v___x_171_, 0);
lean_inc(v_size_174_);
lean_inc_ref(v_r_156_);
v___x_175_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_171_, v_size_174_, v_index_173_, v_key_155_, v_r_156_);
lean_dec(v_index_173_);
v___y_160_ = v___x_175_;
goto v___jp_159_;
}
case 1:
{
lean_object* v_index_176_; 
v_index_176_ = lean_ctor_get(v___x_172_, 0);
lean_inc(v_index_176_);
lean_dec_ref_known(v___x_172_, 1);
v___y_164_ = v___x_171_;
v_i_165_ = v_index_176_;
goto v___jp_163_;
}
default: 
{
lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_177_ = lean_unsigned_to_nat(0u);
v___x_178_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_171_, v___x_177_);
if (lean_obj_tag(v___x_178_) == 0)
{
lean_object* v_index_179_; 
v_index_179_ = lean_ctor_get(v___x_178_, 0);
lean_inc(v_index_179_);
lean_dec_ref_known(v___x_178_, 1);
v___y_164_ = v___x_171_;
v_i_165_ = v_index_179_;
goto v___jp_163_;
}
else
{
lean_dec_ref(v_key_155_);
v___y_160_ = v___x_171_;
goto v___jp_159_;
}
}
}
}
v___jp_180_:
{
lean_object* v_size_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v_size_183_ = lean_ctor_get(v___y_181_, 0);
v___x_184_ = lean_unsigned_to_nat(1u);
v___x_185_ = lean_nat_add(v_size_183_, v___x_184_);
lean_inc_ref(v_r_156_);
v___x_186_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_181_, v___x_185_, v_i_182_, v_key_155_, v_r_156_);
lean_dec(v_i_182_);
v___y_160_ = v___x_186_;
goto v___jp_159_;
}
v___jp_187_:
{
lean_object* v___x_189_; 
v___x_189_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0___redArg(v___y_188_, v_key_155_);
switch(lean_obj_tag(v___x_189_))
{
case 0:
{
lean_object* v_index_190_; lean_object* v_size_191_; lean_object* v___x_192_; 
v_index_190_ = lean_ctor_get(v___x_189_, 0);
lean_inc(v_index_190_);
lean_dec_ref_known(v___x_189_, 3);
v_size_191_ = lean_ctor_get(v___y_188_, 0);
lean_inc(v_size_191_);
lean_inc_ref(v_r_156_);
v___x_192_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_188_, v_size_191_, v_index_190_, v_key_155_, v_r_156_);
lean_dec(v_index_190_);
v___y_160_ = v___x_192_;
goto v___jp_159_;
}
case 1:
{
lean_object* v_index_193_; 
v_index_193_ = lean_ctor_get(v___x_189_, 0);
lean_inc(v_index_193_);
lean_dec_ref_known(v___x_189_, 1);
v___y_181_ = v___y_188_;
v_i_182_ = v_index_193_;
goto v___jp_180_;
}
default: 
{
lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_194_ = lean_unsigned_to_nat(0u);
v___x_195_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_188_, v___x_194_);
if (lean_obj_tag(v___x_195_) == 0)
{
lean_object* v_index_196_; 
v_index_196_ = lean_ctor_get(v___x_195_, 0);
lean_inc(v_index_196_);
lean_dec_ref_known(v___x_195_, 1);
v___y_181_ = v___y_188_;
v_i_182_ = v_index_196_;
goto v___jp_180_;
}
else
{
lean_dec_ref(v_key_155_);
v___y_160_ = v___y_188_;
goto v___jp_159_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(lean_object* v_key_227_, lean_object* v_r_228_, lean_object* v_a_229_, uint8_t v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(v_key_227_, v_r_228_, v_a_229_, v_a_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___boxed(lean_object* v_key_234_, lean_object* v_r_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_){
_start:
{
uint8_t v_a_boxed_240_; lean_object* v_res_241_; 
v_a_boxed_240_ = lean_unbox(v_a_237_);
v_res_241_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_234_, v_r_235_, v_a_236_, v_a_boxed_240_, v_a_238_, v_a_239_);
lean_dec_ref(v_a_238_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0(lean_object* v_00_u03b2_242_, lean_object* v_m_243_, lean_object* v_query_244_){
_start:
{
lean_object* v___x_245_; 
v___x_245_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0___redArg(v_m_243_, v_query_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0___boxed(lean_object* v_00_u03b2_246_, lean_object* v_m_247_, lean_object* v_query_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0(v_00_u03b2_246_, v_m_247_, v_query_248_);
lean_dec_ref(v_query_248_);
lean_dec_ref(v_m_247_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__1(lean_object* v_00_u03b2_250_, lean_object* v_m_251_){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__1___redArg(v_m_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__1___boxed(lean_object* v_00_u03b2_253_, lean_object* v_m_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__1(v_00_u03b2_253_, v_m_254_);
lean_dec_ref(v_m_254_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0(lean_object* v_00_u03b2_256_, lean_object* v_m_257_, lean_object* v_query_258_, lean_object* v_x_259_, lean_object* v_x_260_, lean_object* v_x_261_, lean_object* v_x_262_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_m_257_, v_query_258_, v_x_259_, v_x_260_, v_x_261_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0___boxed(lean_object* v_00_u03b2_264_, lean_object* v_m_265_, lean_object* v_query_266_, lean_object* v_x_267_, lean_object* v_x_268_, lean_object* v_x_269_, lean_object* v_x_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0(v_00_u03b2_264_, v_m_265_, v_query_266_, v_x_267_, v_x_268_, v_x_269_, v_x_270_);
lean_dec_ref(v_query_266_);
lean_dec_ref(v_m_265_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__1_spec__2(lean_object* v_00_u03b2_272_, lean_object* v_init_273_, lean_object* v_b_274_){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(v_init_273_, v_b_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__1_spec__2___boxed(lean_object* v_00_u03b2_276_, lean_object* v_init_277_, lean_object* v_b_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__1_spec__2(v_00_u03b2_276_, v_init_277_, v_b_278_);
lean_dec_ref(v_b_278_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_280_, lean_object* v_b_281_, lean_object* v_acc_282_, lean_object* v_i_283_){
_start:
{
lean_object* v___x_284_; 
v___x_284_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__1_spec__2_spec__3___redArg(v_b_281_, v_acc_282_, v_i_283_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_285_, lean_object* v_b_286_, lean_object* v_acc_287_, lean_object* v_i_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__1_spec__2_spec__3(v_00_u03b2_285_, v_b_286_, v_acc_287_, v_i_288_);
lean_dec_ref(v_b_286_);
return v_res_289_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__4(void){
_start:
{
lean_object* v___x_296_; lean_object* v___f_297_; 
v___x_296_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___f_297_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_297_, 0, v___x_296_);
return v___f_297_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__5(void){
_start:
{
lean_object* v___f_298_; lean_object* v___f_299_; lean_object* v___f_300_; 
v___f_298_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__4, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__4_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__4);
v___f_299_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__0));
v___f_300_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_300_, 0, v___f_299_);
lean_closure_set(v___f_300_, 1, v___f_298_);
return v___f_300_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__10(void){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_320_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__9));
v___x_321_ = l_ReaderT_instMonad___redArg(v___x_320_);
return v___x_321_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11(void){
_start:
{
lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_322_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__10, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__10_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__10);
v___x_323_ = l_ReaderT_instMonad___redArg(v___x_322_);
return v___x_323_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20(void){
_start:
{
lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_324_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11);
v___x_325_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_325_, 0, lean_box(0));
lean_closure_set(v___x_325_, 1, lean_box(0));
lean_closure_set(v___x_325_, 2, v___x_324_);
return v___x_325_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__15(void){
_start:
{
lean_object* v___x_326_; lean_object* v___f_327_; 
v___x_326_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11);
v___f_327_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_327_, 0, v___x_326_);
return v___f_327_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__14(void){
_start:
{
lean_object* v___x_328_; lean_object* v___f_329_; 
v___x_328_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11);
v___f_329_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_329_, 0, v___x_328_);
return v___f_329_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__13(void){
_start:
{
lean_object* v___x_330_; lean_object* v___f_331_; 
v___x_330_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11);
v___f_331_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_331_, 0, v___x_330_);
return v___f_331_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__18(void){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_332_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11);
v___x_333_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_333_, 0, lean_box(0));
lean_closure_set(v___x_333_, 1, lean_box(0));
lean_closure_set(v___x_333_, 2, v___x_332_);
return v___x_333_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__12(void){
_start:
{
lean_object* v___x_334_; lean_object* v___f_335_; 
v___x_334_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11);
v___f_335_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_335_, 0, v___x_334_);
return v___f_335_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__16(void){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_336_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11);
v___x_337_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_337_, 0, lean_box(0));
lean_closure_set(v___x_337_, 1, lean_box(0));
lean_closure_set(v___x_337_, 2, v___x_336_);
return v___x_337_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__17(void){
_start:
{
lean_object* v___f_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v___f_338_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__12, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__12_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__12);
v___x_339_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__16, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__16_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__16);
v___x_340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
lean_ctor_set(v___x_340_, 1, v___f_338_);
return v___x_340_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__19(void){
_start:
{
lean_object* v___f_341_; lean_object* v___f_342_; lean_object* v___f_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___f_341_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__15, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__15_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__15);
v___f_342_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__14, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__14_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__14);
v___f_343_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__13, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__13_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__13);
v___x_344_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__18, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__18_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__18);
v___x_345_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__17, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__17_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__17);
v___x_346_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
lean_ctor_set(v___x_346_, 1, v___x_344_);
lean_ctor_set(v___x_346_, 2, v___f_343_);
lean_ctor_set(v___x_346_, 3, v___f_342_);
lean_ctor_set(v___x_346_, 4, v___f_341_);
return v___x_346_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__21(void){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_347_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20);
v___x_348_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__19, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__19_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__19);
v___x_349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_349_, 0, v___x_348_);
lean_ctor_set(v___x_349_, 1, v___x_347_);
return v___x_349_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__22(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11);
v___x_351_ = lean_alloc_closure((void*)(l_StateT_lift), 6, 3);
lean_closure_set(v___x_351_, 0, lean_box(0));
lean_closure_set(v___x_351_, 1, lean_box(0));
lean_closure_set(v___x_351_, 2, v___x_350_);
return v___x_351_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__23(void){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_352_ = l_Lean_instInhabitedExpr;
v___x_353_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__21, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__21_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__21);
v___x_354_ = l_instInhabitedOfMonad___redArg(v___x_353_, v___x_352_);
return v___x_354_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__27(void){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_358_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__26));
v___x_359_ = lean_unsigned_to_nat(67u);
v___x_360_ = lean_unsigned_to_nat(35u);
v___x_361_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__25));
v___x_362_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__24));
v___x_363_ = l_mkPanicMessageWithDecl(v___x_362_, v___x_361_, v___x_360_, v___x_359_, v___x_358_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit(lean_object* v_e_364_, lean_object* v_offset_365_, lean_object* v_fn_366_, lean_object* v_a_367_, uint8_t v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v_share1_374_; lean_object* v_assertShared_375_; lean_object* v_isDebugEnabled_376_; lean_object* v___x_377_; lean_object* v___f_378_; lean_object* v___f_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_371_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11);
v___x_372_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__21, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__21_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__21);
v___x_373_ = l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM;
v_share1_374_ = lean_ctor_get(v___x_373_, 0);
v_assertShared_375_ = lean_ctor_get(v___x_373_, 1);
v_isDebugEnabled_376_ = lean_ctor_get(v___x_373_, 2);
v___x_377_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__22, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__22_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__22);
lean_inc(v_share1_374_);
v___f_378_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_378_, 0, v_share1_374_);
lean_closure_set(v___f_378_, 1, v___x_377_);
lean_inc(v_assertShared_375_);
v___f_379_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift___redArg___lam__1), 3, 2);
lean_closure_set(v___f_379_, 0, v_assertShared_375_);
lean_closure_set(v___f_379_, 1, v___x_377_);
lean_inc(v_isDebugEnabled_376_);
v___x_380_ = lean_alloc_closure((void*)(l_StateT_lift), 6, 5);
lean_closure_set(v___x_380_, 0, lean_box(0));
lean_closure_set(v___x_380_, 1, lean_box(0));
lean_closure_set(v___x_380_, 2, v___x_371_);
lean_closure_set(v___x_380_, 3, lean_box(0));
lean_closure_set(v___x_380_, 4, v_isDebugEnabled_376_);
v___x_381_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_381_, 0, v___f_378_);
lean_ctor_set(v___x_381_, 1, v___f_379_);
lean_ctor_set(v___x_381_, 2, v___x_380_);
switch(lean_obj_tag(v_e_364_))
{
case 5:
{
lean_object* v_fn_382_; lean_object* v_arg_383_; lean_object* v___x_384_; 
v_fn_382_ = lean_ctor_get(v_e_364_, 0);
v_arg_383_ = lean_ctor_get(v_e_364_, 1);
lean_inc_ref(v_fn_366_);
lean_inc(v_offset_365_);
lean_inc_ref(v_fn_382_);
v___x_384_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_fn_382_, v_offset_365_, v_fn_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_);
if (lean_obj_tag(v___x_384_) == 0)
{
lean_object* v_a_385_; lean_object* v_a_386_; lean_object* v_fst_387_; lean_object* v_snd_388_; lean_object* v___x_389_; 
v_a_385_ = lean_ctor_get(v___x_384_, 0);
lean_inc(v_a_385_);
v_a_386_ = lean_ctor_get(v___x_384_, 1);
lean_inc(v_a_386_);
lean_dec_ref_known(v___x_384_, 2);
v_fst_387_ = lean_ctor_get(v_a_385_, 0);
lean_inc(v_fst_387_);
v_snd_388_ = lean_ctor_get(v_a_385_, 1);
lean_inc(v_snd_388_);
lean_dec(v_a_385_);
lean_inc_ref(v_arg_383_);
v___x_389_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_arg_383_, v_offset_365_, v_fn_366_, v_snd_388_, v_a_368_, v_a_369_, v_a_386_);
if (lean_obj_tag(v___x_389_) == 0)
{
lean_object* v_a_390_; lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_418_; 
v_a_390_ = lean_ctor_get(v___x_389_, 0);
v_a_391_ = lean_ctor_get(v___x_389_, 1);
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_389_);
if (v_isSharedCheck_418_ == 0)
{
v___x_393_ = v___x_389_;
v_isShared_394_ = v_isSharedCheck_418_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_inc(v_a_390_);
lean_dec(v___x_389_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_418_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v_fst_395_; lean_object* v_snd_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_417_; 
v_fst_395_ = lean_ctor_get(v_a_390_, 0);
v_snd_396_ = lean_ctor_get(v_a_390_, 1);
v_isSharedCheck_417_ = !lean_is_exclusive(v_a_390_);
if (v_isSharedCheck_417_ == 0)
{
v___x_398_ = v_a_390_;
v_isShared_399_ = v_isSharedCheck_417_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_snd_396_);
lean_inc(v_fst_395_);
lean_dec(v_a_390_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_417_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
uint8_t v___y_401_; size_t v___x_411_; size_t v___x_412_; uint8_t v___x_413_; 
v___x_411_ = lean_ptr_addr(v_fn_382_);
v___x_412_ = lean_ptr_addr(v_fst_387_);
v___x_413_ = lean_usize_dec_eq(v___x_411_, v___x_412_);
if (v___x_413_ == 0)
{
v___y_401_ = v___x_413_;
goto v___jp_400_;
}
else
{
size_t v___x_414_; size_t v___x_415_; uint8_t v___x_416_; 
v___x_414_ = lean_ptr_addr(v_arg_383_);
v___x_415_ = lean_ptr_addr(v_fst_395_);
v___x_416_ = lean_usize_dec_eq(v___x_414_, v___x_415_);
v___y_401_ = v___x_416_;
goto v___jp_400_;
}
v___jp_400_:
{
if (v___y_401_ == 0)
{
lean_object* v___x_11955__overap_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
lean_del_object(v___x_398_);
lean_del_object(v___x_393_);
lean_dec_ref_known(v_e_364_, 2);
v___x_11955__overap_402_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v___x_381_, v___x_372_, v_fst_387_, v_fst_395_);
v___x_403_ = lean_box(v_a_368_);
lean_inc_ref(v_a_369_);
v___x_404_ = lean_apply_4(v___x_11955__overap_402_, v_snd_396_, v___x_403_, v_a_369_, v_a_391_);
return v___x_404_;
}
else
{
lean_object* v___x_406_; 
lean_dec(v_fst_395_);
lean_dec(v_fst_387_);
lean_dec_ref_known(v___x_381_, 3);
if (v_isShared_399_ == 0)
{
lean_ctor_set(v___x_398_, 0, v_e_364_);
v___x_406_ = v___x_398_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v_e_364_);
lean_ctor_set(v_reuseFailAlloc_410_, 1, v_snd_396_);
v___x_406_ = v_reuseFailAlloc_410_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
lean_object* v___x_408_; 
if (v_isShared_394_ == 0)
{
lean_ctor_set(v___x_393_, 0, v___x_406_);
v___x_408_ = v___x_393_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_406_);
lean_ctor_set(v_reuseFailAlloc_409_, 1, v_a_391_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_387_);
lean_dec_ref_known(v_e_364_, 2);
lean_dec_ref_known(v___x_381_, 3);
return v___x_389_;
}
}
else
{
lean_dec_ref_known(v_e_364_, 2);
lean_dec_ref_known(v___x_381_, 3);
lean_dec_ref(v_fn_366_);
lean_dec(v_offset_365_);
return v___x_384_;
}
}
case 6:
{
lean_object* v_binderName_419_; lean_object* v_binderType_420_; lean_object* v_body_421_; uint8_t v_binderInfo_422_; lean_object* v___x_423_; 
v_binderName_419_ = lean_ctor_get(v_e_364_, 0);
v_binderType_420_ = lean_ctor_get(v_e_364_, 1);
v_body_421_ = lean_ctor_get(v_e_364_, 2);
v_binderInfo_422_ = lean_ctor_get_uint8(v_e_364_, sizeof(void*)*3 + 8);
lean_inc_ref(v_fn_366_);
lean_inc(v_offset_365_);
lean_inc_ref(v_binderType_420_);
v___x_423_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_binderType_420_, v_offset_365_, v_fn_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_);
if (lean_obj_tag(v___x_423_) == 0)
{
lean_object* v_a_424_; lean_object* v_a_425_; lean_object* v_fst_426_; lean_object* v_snd_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v_a_424_ = lean_ctor_get(v___x_423_, 0);
lean_inc(v_a_424_);
v_a_425_ = lean_ctor_get(v___x_423_, 1);
lean_inc(v_a_425_);
lean_dec_ref_known(v___x_423_, 2);
v_fst_426_ = lean_ctor_get(v_a_424_, 0);
lean_inc(v_fst_426_);
v_snd_427_ = lean_ctor_get(v_a_424_, 1);
lean_inc(v_snd_427_);
lean_dec(v_a_424_);
v___x_428_ = lean_unsigned_to_nat(1u);
v___x_429_ = lean_nat_add(v_offset_365_, v___x_428_);
lean_dec(v_offset_365_);
lean_inc_ref(v_body_421_);
v___x_430_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_body_421_, v___x_429_, v_fn_366_, v_snd_427_, v_a_368_, v_a_369_, v_a_425_);
if (lean_obj_tag(v___x_430_) == 0)
{
lean_object* v_a_431_; lean_object* v_a_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_459_; 
v_a_431_ = lean_ctor_get(v___x_430_, 0);
v_a_432_ = lean_ctor_get(v___x_430_, 1);
v_isSharedCheck_459_ = !lean_is_exclusive(v___x_430_);
if (v_isSharedCheck_459_ == 0)
{
v___x_434_ = v___x_430_;
v_isShared_435_ = v_isSharedCheck_459_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_a_432_);
lean_inc(v_a_431_);
lean_dec(v___x_430_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_459_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v_fst_436_; lean_object* v_snd_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_458_; 
v_fst_436_ = lean_ctor_get(v_a_431_, 0);
v_snd_437_ = lean_ctor_get(v_a_431_, 1);
v_isSharedCheck_458_ = !lean_is_exclusive(v_a_431_);
if (v_isSharedCheck_458_ == 0)
{
v___x_439_ = v_a_431_;
v_isShared_440_ = v_isSharedCheck_458_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_snd_437_);
lean_inc(v_fst_436_);
lean_dec(v_a_431_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_458_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
uint8_t v___y_442_; size_t v___x_452_; size_t v___x_453_; uint8_t v___x_454_; 
v___x_452_ = lean_ptr_addr(v_binderType_420_);
v___x_453_ = lean_ptr_addr(v_fst_426_);
v___x_454_ = lean_usize_dec_eq(v___x_452_, v___x_453_);
if (v___x_454_ == 0)
{
v___y_442_ = v___x_454_;
goto v___jp_441_;
}
else
{
size_t v___x_455_; size_t v___x_456_; uint8_t v___x_457_; 
v___x_455_ = lean_ptr_addr(v_body_421_);
v___x_456_ = lean_ptr_addr(v_fst_436_);
v___x_457_ = lean_usize_dec_eq(v___x_455_, v___x_456_);
v___y_442_ = v___x_457_;
goto v___jp_441_;
}
v___jp_441_:
{
if (v___y_442_ == 0)
{
lean_object* v___x_12239__overap_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
lean_inc(v_binderName_419_);
lean_del_object(v___x_439_);
lean_del_object(v___x_434_);
lean_dec_ref_known(v_e_364_, 3);
v___x_12239__overap_443_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v___x_381_, v___x_372_, v_binderName_419_, v_binderInfo_422_, v_fst_426_, v_fst_436_);
v___x_444_ = lean_box(v_a_368_);
lean_inc_ref(v_a_369_);
v___x_445_ = lean_apply_4(v___x_12239__overap_443_, v_snd_437_, v___x_444_, v_a_369_, v_a_432_);
return v___x_445_;
}
else
{
lean_object* v___x_447_; 
lean_dec(v_fst_436_);
lean_dec(v_fst_426_);
lean_dec_ref_known(v___x_381_, 3);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 0, v_e_364_);
v___x_447_ = v___x_439_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v_e_364_);
lean_ctor_set(v_reuseFailAlloc_451_, 1, v_snd_437_);
v___x_447_ = v_reuseFailAlloc_451_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
lean_object* v___x_449_; 
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 0, v___x_447_);
v___x_449_ = v___x_434_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v___x_447_);
lean_ctor_set(v_reuseFailAlloc_450_, 1, v_a_432_);
v___x_449_ = v_reuseFailAlloc_450_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
return v___x_449_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_426_);
lean_dec_ref_known(v_e_364_, 3);
lean_dec_ref_known(v___x_381_, 3);
return v___x_430_;
}
}
else
{
lean_dec_ref_known(v_e_364_, 3);
lean_dec_ref_known(v___x_381_, 3);
lean_dec_ref(v_fn_366_);
lean_dec(v_offset_365_);
return v___x_423_;
}
}
case 7:
{
lean_object* v_binderName_460_; lean_object* v_binderType_461_; lean_object* v_body_462_; uint8_t v_binderInfo_463_; lean_object* v___x_464_; 
v_binderName_460_ = lean_ctor_get(v_e_364_, 0);
v_binderType_461_ = lean_ctor_get(v_e_364_, 1);
v_body_462_ = lean_ctor_get(v_e_364_, 2);
v_binderInfo_463_ = lean_ctor_get_uint8(v_e_364_, sizeof(void*)*3 + 8);
lean_inc_ref(v_fn_366_);
lean_inc(v_offset_365_);
lean_inc_ref(v_binderType_461_);
v___x_464_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_binderType_461_, v_offset_365_, v_fn_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_);
if (lean_obj_tag(v___x_464_) == 0)
{
lean_object* v_a_465_; lean_object* v_a_466_; lean_object* v_fst_467_; lean_object* v_snd_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v_a_465_ = lean_ctor_get(v___x_464_, 0);
lean_inc(v_a_465_);
v_a_466_ = lean_ctor_get(v___x_464_, 1);
lean_inc(v_a_466_);
lean_dec_ref_known(v___x_464_, 2);
v_fst_467_ = lean_ctor_get(v_a_465_, 0);
lean_inc(v_fst_467_);
v_snd_468_ = lean_ctor_get(v_a_465_, 1);
lean_inc(v_snd_468_);
lean_dec(v_a_465_);
v___x_469_ = lean_unsigned_to_nat(1u);
v___x_470_ = lean_nat_add(v_offset_365_, v___x_469_);
lean_dec(v_offset_365_);
lean_inc_ref(v_body_462_);
v___x_471_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_body_462_, v___x_470_, v_fn_366_, v_snd_468_, v_a_368_, v_a_369_, v_a_466_);
if (lean_obj_tag(v___x_471_) == 0)
{
lean_object* v_a_472_; lean_object* v_a_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_500_; 
v_a_472_ = lean_ctor_get(v___x_471_, 0);
v_a_473_ = lean_ctor_get(v___x_471_, 1);
v_isSharedCheck_500_ = !lean_is_exclusive(v___x_471_);
if (v_isSharedCheck_500_ == 0)
{
v___x_475_ = v___x_471_;
v_isShared_476_ = v_isSharedCheck_500_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_a_473_);
lean_inc(v_a_472_);
lean_dec(v___x_471_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_500_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v_fst_477_; lean_object* v_snd_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_499_; 
v_fst_477_ = lean_ctor_get(v_a_472_, 0);
v_snd_478_ = lean_ctor_get(v_a_472_, 1);
v_isSharedCheck_499_ = !lean_is_exclusive(v_a_472_);
if (v_isSharedCheck_499_ == 0)
{
v___x_480_ = v_a_472_;
v_isShared_481_ = v_isSharedCheck_499_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_snd_478_);
lean_inc(v_fst_477_);
lean_dec(v_a_472_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_499_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
uint8_t v___y_483_; size_t v___x_493_; size_t v___x_494_; uint8_t v___x_495_; 
v___x_493_ = lean_ptr_addr(v_binderType_461_);
v___x_494_ = lean_ptr_addr(v_fst_467_);
v___x_495_ = lean_usize_dec_eq(v___x_493_, v___x_494_);
if (v___x_495_ == 0)
{
v___y_483_ = v___x_495_;
goto v___jp_482_;
}
else
{
size_t v___x_496_; size_t v___x_497_; uint8_t v___x_498_; 
v___x_496_ = lean_ptr_addr(v_body_462_);
v___x_497_ = lean_ptr_addr(v_fst_477_);
v___x_498_ = lean_usize_dec_eq(v___x_496_, v___x_497_);
v___y_483_ = v___x_498_;
goto v___jp_482_;
}
v___jp_482_:
{
if (v___y_483_ == 0)
{
lean_object* v___x_12531__overap_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
lean_inc(v_binderName_460_);
lean_del_object(v___x_480_);
lean_del_object(v___x_475_);
lean_dec_ref_known(v_e_364_, 3);
v___x_12531__overap_484_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v___x_381_, v___x_372_, v_binderName_460_, v_binderInfo_463_, v_fst_467_, v_fst_477_);
v___x_485_ = lean_box(v_a_368_);
lean_inc_ref(v_a_369_);
v___x_486_ = lean_apply_4(v___x_12531__overap_484_, v_snd_478_, v___x_485_, v_a_369_, v_a_473_);
return v___x_486_;
}
else
{
lean_object* v___x_488_; 
lean_dec(v_fst_477_);
lean_dec(v_fst_467_);
lean_dec_ref_known(v___x_381_, 3);
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 0, v_e_364_);
v___x_488_ = v___x_480_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_e_364_);
lean_ctor_set(v_reuseFailAlloc_492_, 1, v_snd_478_);
v___x_488_ = v_reuseFailAlloc_492_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
lean_object* v___x_490_; 
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 0, v___x_488_);
v___x_490_ = v___x_475_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v___x_488_);
lean_ctor_set(v_reuseFailAlloc_491_, 1, v_a_473_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_467_);
lean_dec_ref_known(v_e_364_, 3);
lean_dec_ref_known(v___x_381_, 3);
return v___x_471_;
}
}
else
{
lean_dec_ref_known(v_e_364_, 3);
lean_dec_ref_known(v___x_381_, 3);
lean_dec_ref(v_fn_366_);
lean_dec(v_offset_365_);
return v___x_464_;
}
}
case 8:
{
lean_object* v_declName_501_; lean_object* v_type_502_; lean_object* v_value_503_; lean_object* v_body_504_; uint8_t v_nondep_505_; lean_object* v___x_506_; 
v_declName_501_ = lean_ctor_get(v_e_364_, 0);
v_type_502_ = lean_ctor_get(v_e_364_, 1);
v_value_503_ = lean_ctor_get(v_e_364_, 2);
v_body_504_ = lean_ctor_get(v_e_364_, 3);
v_nondep_505_ = lean_ctor_get_uint8(v_e_364_, sizeof(void*)*4 + 8);
lean_inc_ref(v_fn_366_);
lean_inc(v_offset_365_);
lean_inc_ref(v_type_502_);
v___x_506_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_type_502_, v_offset_365_, v_fn_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_);
if (lean_obj_tag(v___x_506_) == 0)
{
lean_object* v_a_507_; lean_object* v_a_508_; lean_object* v_fst_509_; lean_object* v_snd_510_; lean_object* v___x_511_; 
v_a_507_ = lean_ctor_get(v___x_506_, 0);
lean_inc(v_a_507_);
v_a_508_ = lean_ctor_get(v___x_506_, 1);
lean_inc(v_a_508_);
lean_dec_ref_known(v___x_506_, 2);
v_fst_509_ = lean_ctor_get(v_a_507_, 0);
lean_inc(v_fst_509_);
v_snd_510_ = lean_ctor_get(v_a_507_, 1);
lean_inc(v_snd_510_);
lean_dec(v_a_507_);
lean_inc_ref(v_fn_366_);
lean_inc(v_offset_365_);
lean_inc_ref(v_value_503_);
v___x_511_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_value_503_, v_offset_365_, v_fn_366_, v_snd_510_, v_a_368_, v_a_369_, v_a_508_);
if (lean_obj_tag(v___x_511_) == 0)
{
lean_object* v_a_512_; lean_object* v_a_513_; lean_object* v_fst_514_; lean_object* v_snd_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
v_a_512_ = lean_ctor_get(v___x_511_, 0);
lean_inc(v_a_512_);
v_a_513_ = lean_ctor_get(v___x_511_, 1);
lean_inc(v_a_513_);
lean_dec_ref_known(v___x_511_, 2);
v_fst_514_ = lean_ctor_get(v_a_512_, 0);
lean_inc(v_fst_514_);
v_snd_515_ = lean_ctor_get(v_a_512_, 1);
lean_inc(v_snd_515_);
lean_dec(v_a_512_);
v___x_516_ = lean_unsigned_to_nat(1u);
v___x_517_ = lean_nat_add(v_offset_365_, v___x_516_);
lean_dec(v_offset_365_);
lean_inc_ref(v_body_504_);
v___x_518_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_body_504_, v___x_517_, v_fn_366_, v_snd_515_, v_a_368_, v_a_369_, v_a_513_);
if (lean_obj_tag(v___x_518_) == 0)
{
lean_object* v_a_519_; lean_object* v_a_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_553_; 
v_a_519_ = lean_ctor_get(v___x_518_, 0);
v_a_520_ = lean_ctor_get(v___x_518_, 1);
v_isSharedCheck_553_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_553_ == 0)
{
v___x_522_ = v___x_518_;
v_isShared_523_ = v_isSharedCheck_553_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_a_520_);
lean_inc(v_a_519_);
lean_dec(v___x_518_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_553_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v_fst_524_; lean_object* v_snd_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_552_; 
v_fst_524_ = lean_ctor_get(v_a_519_, 0);
v_snd_525_ = lean_ctor_get(v_a_519_, 1);
v_isSharedCheck_552_ = !lean_is_exclusive(v_a_519_);
if (v_isSharedCheck_552_ == 0)
{
v___x_527_ = v_a_519_;
v_isShared_528_ = v_isSharedCheck_552_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_snd_525_);
lean_inc(v_fst_524_);
lean_dec(v_a_519_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_552_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
uint8_t v___y_530_; size_t v___x_546_; size_t v___x_547_; uint8_t v___x_548_; 
v___x_546_ = lean_ptr_addr(v_type_502_);
v___x_547_ = lean_ptr_addr(v_fst_509_);
v___x_548_ = lean_usize_dec_eq(v___x_546_, v___x_547_);
if (v___x_548_ == 0)
{
v___y_530_ = v___x_548_;
goto v___jp_529_;
}
else
{
size_t v___x_549_; size_t v___x_550_; uint8_t v___x_551_; 
v___x_549_ = lean_ptr_addr(v_value_503_);
v___x_550_ = lean_ptr_addr(v_fst_514_);
v___x_551_ = lean_usize_dec_eq(v___x_549_, v___x_550_);
v___y_530_ = v___x_551_;
goto v___jp_529_;
}
v___jp_529_:
{
if (v___y_530_ == 0)
{
lean_object* v___x_12868__overap_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
lean_inc(v_declName_501_);
lean_del_object(v___x_527_);
lean_del_object(v___x_522_);
lean_dec_ref_known(v_e_364_, 4);
v___x_12868__overap_531_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v___x_381_, v___x_372_, v_declName_501_, v_fst_509_, v_fst_514_, v_fst_524_, v_nondep_505_);
v___x_532_ = lean_box(v_a_368_);
lean_inc_ref(v_a_369_);
v___x_533_ = lean_apply_4(v___x_12868__overap_531_, v_snd_525_, v___x_532_, v_a_369_, v_a_520_);
return v___x_533_;
}
else
{
size_t v___x_534_; size_t v___x_535_; uint8_t v___x_536_; 
v___x_534_ = lean_ptr_addr(v_body_504_);
v___x_535_ = lean_ptr_addr(v_fst_524_);
v___x_536_ = lean_usize_dec_eq(v___x_534_, v___x_535_);
if (v___x_536_ == 0)
{
lean_object* v___x_12873__overap_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
lean_inc(v_declName_501_);
lean_del_object(v___x_527_);
lean_del_object(v___x_522_);
lean_dec_ref_known(v_e_364_, 4);
v___x_12873__overap_537_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v___x_381_, v___x_372_, v_declName_501_, v_fst_509_, v_fst_514_, v_fst_524_, v_nondep_505_);
v___x_538_ = lean_box(v_a_368_);
lean_inc_ref(v_a_369_);
v___x_539_ = lean_apply_4(v___x_12873__overap_537_, v_snd_525_, v___x_538_, v_a_369_, v_a_520_);
return v___x_539_;
}
else
{
lean_object* v___x_541_; 
lean_dec(v_fst_524_);
lean_dec(v_fst_514_);
lean_dec(v_fst_509_);
lean_dec_ref_known(v___x_381_, 3);
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 0, v_e_364_);
v___x_541_ = v___x_527_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_e_364_);
lean_ctor_set(v_reuseFailAlloc_545_, 1, v_snd_525_);
v___x_541_ = v_reuseFailAlloc_545_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
lean_object* v___x_543_; 
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 0, v___x_541_);
v___x_543_ = v___x_522_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v___x_541_);
lean_ctor_set(v_reuseFailAlloc_544_, 1, v_a_520_);
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
}
else
{
lean_dec(v_fst_514_);
lean_dec(v_fst_509_);
lean_dec_ref_known(v_e_364_, 4);
lean_dec_ref_known(v___x_381_, 3);
return v___x_518_;
}
}
else
{
lean_dec(v_fst_509_);
lean_dec_ref_known(v_e_364_, 4);
lean_dec_ref_known(v___x_381_, 3);
lean_dec_ref(v_fn_366_);
lean_dec(v_offset_365_);
return v___x_511_;
}
}
else
{
lean_dec_ref_known(v_e_364_, 4);
lean_dec_ref_known(v___x_381_, 3);
lean_dec_ref(v_fn_366_);
lean_dec(v_offset_365_);
return v___x_506_;
}
}
case 10:
{
lean_object* v_data_554_; lean_object* v_expr_555_; lean_object* v___x_556_; 
v_data_554_ = lean_ctor_get(v_e_364_, 0);
v_expr_555_ = lean_ctor_get(v_e_364_, 1);
lean_inc_ref(v_expr_555_);
v___x_556_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_expr_555_, v_offset_365_, v_fn_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_);
if (lean_obj_tag(v___x_556_) == 0)
{
lean_object* v_a_557_; lean_object* v_a_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_580_; 
v_a_557_ = lean_ctor_get(v___x_556_, 0);
v_a_558_ = lean_ctor_get(v___x_556_, 1);
v_isSharedCheck_580_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_580_ == 0)
{
v___x_560_ = v___x_556_;
v_isShared_561_ = v_isSharedCheck_580_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_a_558_);
lean_inc(v_a_557_);
lean_dec(v___x_556_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_580_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v_fst_562_; lean_object* v_snd_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_579_; 
v_fst_562_ = lean_ctor_get(v_a_557_, 0);
v_snd_563_ = lean_ctor_get(v_a_557_, 1);
v_isSharedCheck_579_ = !lean_is_exclusive(v_a_557_);
if (v_isSharedCheck_579_ == 0)
{
v___x_565_ = v_a_557_;
v_isShared_566_ = v_isSharedCheck_579_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_snd_563_);
lean_inc(v_fst_562_);
lean_dec(v_a_557_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_579_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
size_t v___x_567_; size_t v___x_568_; uint8_t v___x_569_; 
v___x_567_ = lean_ptr_addr(v_expr_555_);
v___x_568_ = lean_ptr_addr(v_fst_562_);
v___x_569_ = lean_usize_dec_eq(v___x_567_, v___x_568_);
if (v___x_569_ == 0)
{
lean_object* v___x_13159__overap_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
lean_inc(v_data_554_);
lean_del_object(v___x_565_);
lean_del_object(v___x_560_);
lean_dec_ref_known(v_e_364_, 2);
v___x_13159__overap_570_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg(v___x_381_, v___x_372_, v_data_554_, v_fst_562_);
v___x_571_ = lean_box(v_a_368_);
lean_inc_ref(v_a_369_);
v___x_572_ = lean_apply_4(v___x_13159__overap_570_, v_snd_563_, v___x_571_, v_a_369_, v_a_558_);
return v___x_572_;
}
else
{
lean_object* v___x_574_; 
lean_dec(v_fst_562_);
lean_dec_ref_known(v___x_381_, 3);
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 0, v_e_364_);
v___x_574_ = v___x_565_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_e_364_);
lean_ctor_set(v_reuseFailAlloc_578_, 1, v_snd_563_);
v___x_574_ = v_reuseFailAlloc_578_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
lean_object* v___x_576_; 
if (v_isShared_561_ == 0)
{
lean_ctor_set(v___x_560_, 0, v___x_574_);
v___x_576_ = v___x_560_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v___x_574_);
lean_ctor_set(v_reuseFailAlloc_577_, 1, v_a_558_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_364_, 2);
lean_dec_ref_known(v___x_381_, 3);
return v___x_556_;
}
}
case 11:
{
lean_object* v_typeName_581_; lean_object* v_idx_582_; lean_object* v_struct_583_; lean_object* v___x_584_; 
v_typeName_581_ = lean_ctor_get(v_e_364_, 0);
v_idx_582_ = lean_ctor_get(v_e_364_, 1);
v_struct_583_ = lean_ctor_get(v_e_364_, 2);
lean_inc_ref(v_struct_583_);
v___x_584_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_struct_583_, v_offset_365_, v_fn_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_);
if (lean_obj_tag(v___x_584_) == 0)
{
lean_object* v_a_585_; lean_object* v_a_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_608_; 
v_a_585_ = lean_ctor_get(v___x_584_, 0);
v_a_586_ = lean_ctor_get(v___x_584_, 1);
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_608_ == 0)
{
v___x_588_ = v___x_584_;
v_isShared_589_ = v_isSharedCheck_608_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_inc(v_a_585_);
lean_dec(v___x_584_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_608_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v_fst_590_; lean_object* v_snd_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_607_; 
v_fst_590_ = lean_ctor_get(v_a_585_, 0);
v_snd_591_ = lean_ctor_get(v_a_585_, 1);
v_isSharedCheck_607_ = !lean_is_exclusive(v_a_585_);
if (v_isSharedCheck_607_ == 0)
{
v___x_593_ = v_a_585_;
v_isShared_594_ = v_isSharedCheck_607_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_snd_591_);
lean_inc(v_fst_590_);
lean_dec(v_a_585_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_607_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
size_t v___x_595_; size_t v___x_596_; uint8_t v___x_597_; 
v___x_595_ = lean_ptr_addr(v_struct_583_);
v___x_596_ = lean_ptr_addr(v_fst_590_);
v___x_597_ = lean_usize_dec_eq(v___x_595_, v___x_596_);
if (v___x_597_ == 0)
{
lean_object* v___x_13342__overap_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
lean_inc(v_idx_582_);
lean_inc(v_typeName_581_);
lean_del_object(v___x_593_);
lean_del_object(v___x_588_);
lean_dec_ref_known(v_e_364_, 3);
v___x_13342__overap_598_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg(v___x_381_, v___x_372_, v_typeName_581_, v_idx_582_, v_fst_590_);
v___x_599_ = lean_box(v_a_368_);
lean_inc_ref(v_a_369_);
v___x_600_ = lean_apply_4(v___x_13342__overap_598_, v_snd_591_, v___x_599_, v_a_369_, v_a_586_);
return v___x_600_;
}
else
{
lean_object* v___x_602_; 
lean_dec(v_fst_590_);
lean_dec_ref_known(v___x_381_, 3);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 0, v_e_364_);
v___x_602_ = v___x_593_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_e_364_);
lean_ctor_set(v_reuseFailAlloc_606_, 1, v_snd_591_);
v___x_602_ = v_reuseFailAlloc_606_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
lean_object* v___x_604_; 
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 0, v___x_602_);
v___x_604_ = v___x_588_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v___x_602_);
lean_ctor_set(v_reuseFailAlloc_605_, 1, v_a_586_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
return v___x_604_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_364_, 3);
lean_dec_ref_known(v___x_381_, 3);
return v___x_584_;
}
}
default: 
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_11781__overap_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
lean_dec_ref_known(v___x_381_, 3);
lean_dec_ref(v_fn_366_);
lean_dec(v_offset_365_);
lean_dec_ref(v_e_364_);
v___x_609_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__23, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__23_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__23);
v___x_610_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__27, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__27_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__27);
v___x_11781__overap_611_ = l_panic___redArg(v___x_609_, v___x_610_);
v___x_612_ = lean_box(v_a_368_);
lean_inc_ref(v_a_369_);
v___x_613_ = lean_apply_4(v___x_11781__overap_611_, v_a_367_, v___x_612_, v_a_369_, v_a_370_);
return v___x_613_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(lean_object* v_e_614_, lean_object* v_offset_615_, lean_object* v_f_616_, lean_object* v_a_617_, uint8_t v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_){
_start:
{
lean_object* v___f_621_; lean_object* v_key_622_; lean_object* v___f_623_; lean_object* v___x_624_; 
v___f_621_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__3));
lean_inc(v_offset_615_);
lean_inc_ref(v_e_614_);
v_key_622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_622_, 0, v_e_614_);
lean_ctor_set(v_key_622_, 1, v_offset_615_);
v___f_623_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__5, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__5_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__5);
lean_inc_ref(v_key_622_);
v___x_624_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_623_, v___f_621_, v_a_617_, v_key_622_);
if (lean_obj_tag(v___x_624_) == 1)
{
lean_object* v_val_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
lean_dec_ref_known(v_key_622_, 2);
lean_dec_ref(v_f_616_);
lean_dec(v_offset_615_);
lean_dec_ref(v_e_614_);
v_val_625_ = lean_ctor_get(v___x_624_, 0);
lean_inc(v_val_625_);
lean_dec_ref_known(v___x_624_, 1);
v___x_626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_626_, 0, v_val_625_);
lean_ctor_set(v___x_626_, 1, v_a_617_);
v___x_627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
lean_ctor_set(v___x_627_, 1, v_a_620_);
return v___x_627_;
}
else
{
lean_object* v___x_628_; lean_object* v___x_629_; 
lean_dec(v___x_624_);
v___x_628_ = lean_box(v_a_618_);
lean_inc_ref(v_f_616_);
lean_inc_ref(v_a_619_);
lean_inc(v_offset_615_);
lean_inc_ref(v_e_614_);
v___x_629_ = lean_apply_5(v_f_616_, v_e_614_, v_offset_615_, v___x_628_, v_a_619_, v_a_620_);
if (lean_obj_tag(v___x_629_) == 0)
{
lean_object* v_a_630_; 
v_a_630_ = lean_ctor_get(v___x_629_, 0);
lean_inc(v_a_630_);
if (lean_obj_tag(v_a_630_) == 1)
{
lean_object* v_a_631_; lean_object* v_val_632_; lean_object* v___x_633_; 
lean_dec_ref(v_f_616_);
lean_dec(v_offset_615_);
lean_dec_ref(v_e_614_);
v_a_631_ = lean_ctor_get(v___x_629_, 1);
lean_inc(v_a_631_);
lean_dec_ref_known(v___x_629_, 2);
v_val_632_ = lean_ctor_get(v_a_630_, 0);
lean_inc(v_val_632_);
lean_dec_ref_known(v_a_630_, 1);
v___x_633_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(v_key_622_, v_val_632_, v_a_617_, v_a_631_);
return v___x_633_;
}
else
{
lean_dec(v_a_630_);
switch(lean_obj_tag(v_e_614_))
{
case 9:
{
lean_object* v_a_634_; lean_object* v___x_635_; 
lean_dec_ref(v_f_616_);
lean_dec(v_offset_615_);
v_a_634_ = lean_ctor_get(v___x_629_, 1);
lean_inc(v_a_634_);
lean_dec_ref_known(v___x_629_, 2);
v___x_635_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(v_key_622_, v_e_614_, v_a_617_, v_a_634_);
return v___x_635_;
}
case 2:
{
lean_object* v_a_636_; lean_object* v___x_637_; 
lean_dec_ref(v_f_616_);
lean_dec(v_offset_615_);
v_a_636_ = lean_ctor_get(v___x_629_, 1);
lean_inc(v_a_636_);
lean_dec_ref_known(v___x_629_, 2);
v___x_637_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(v_key_622_, v_e_614_, v_a_617_, v_a_636_);
return v___x_637_;
}
case 0:
{
lean_object* v_a_638_; lean_object* v___x_639_; 
lean_dec_ref(v_f_616_);
lean_dec(v_offset_615_);
v_a_638_ = lean_ctor_get(v___x_629_, 1);
lean_inc(v_a_638_);
lean_dec_ref_known(v___x_629_, 2);
v___x_639_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(v_key_622_, v_e_614_, v_a_617_, v_a_638_);
return v___x_639_;
}
case 1:
{
lean_object* v_a_640_; lean_object* v___x_641_; 
lean_dec_ref(v_f_616_);
lean_dec(v_offset_615_);
v_a_640_ = lean_ctor_get(v___x_629_, 1);
lean_inc(v_a_640_);
lean_dec_ref_known(v___x_629_, 2);
v___x_641_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(v_key_622_, v_e_614_, v_a_617_, v_a_640_);
return v___x_641_;
}
case 4:
{
lean_object* v_a_642_; lean_object* v___x_643_; 
lean_dec_ref(v_f_616_);
lean_dec(v_offset_615_);
v_a_642_ = lean_ctor_get(v___x_629_, 1);
lean_inc(v_a_642_);
lean_dec_ref_known(v___x_629_, 2);
v___x_643_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(v_key_622_, v_e_614_, v_a_617_, v_a_642_);
return v___x_643_;
}
case 3:
{
lean_object* v_a_644_; lean_object* v___x_645_; 
lean_dec_ref(v_f_616_);
lean_dec(v_offset_615_);
v_a_644_ = lean_ctor_get(v___x_629_, 1);
lean_inc(v_a_644_);
lean_dec_ref_known(v___x_629_, 2);
v___x_645_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(v_key_622_, v_e_614_, v_a_617_, v_a_644_);
return v___x_645_;
}
default: 
{
lean_object* v_a_646_; lean_object* v___x_647_; 
v_a_646_ = lean_ctor_get(v___x_629_, 1);
lean_inc(v_a_646_);
lean_dec_ref_known(v___x_629_, 2);
v___x_647_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit(v_e_614_, v_offset_615_, v_f_616_, v_a_617_, v_a_618_, v_a_619_, v_a_646_);
if (lean_obj_tag(v___x_647_) == 0)
{
lean_object* v_a_648_; lean_object* v_a_649_; lean_object* v_fst_650_; lean_object* v_snd_651_; lean_object* v___x_652_; 
v_a_648_ = lean_ctor_get(v___x_647_, 0);
lean_inc(v_a_648_);
v_a_649_ = lean_ctor_get(v___x_647_, 1);
lean_inc(v_a_649_);
lean_dec_ref_known(v___x_647_, 2);
v_fst_650_ = lean_ctor_get(v_a_648_, 0);
lean_inc(v_fst_650_);
v_snd_651_ = lean_ctor_get(v_a_648_, 1);
lean_inc(v_snd_651_);
lean_dec(v_a_648_);
v___x_652_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(v_key_622_, v_fst_650_, v_snd_651_, v_a_649_);
return v___x_652_;
}
else
{
lean_dec_ref_known(v_key_622_, 2);
return v___x_647_;
}
}
}
}
}
else
{
lean_object* v_a_653_; lean_object* v_a_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_661_; 
lean_dec_ref_known(v_key_622_, 2);
lean_dec_ref(v_a_617_);
lean_dec_ref(v_f_616_);
lean_dec(v_offset_615_);
lean_dec_ref(v_e_614_);
v_a_653_ = lean_ctor_get(v___x_629_, 0);
v_a_654_ = lean_ctor_get(v___x_629_, 1);
v_isSharedCheck_661_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_661_ == 0)
{
v___x_656_ = v___x_629_;
v_isShared_657_ = v_isSharedCheck_661_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_a_654_);
lean_inc(v_a_653_);
lean_dec(v___x_629_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_661_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_659_; 
if (v_isShared_657_ == 0)
{
v___x_659_ = v___x_656_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_a_653_);
lean_ctor_set(v_reuseFailAlloc_660_, 1, v_a_654_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___boxed(lean_object* v_e_662_, lean_object* v_offset_663_, lean_object* v_f_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_){
_start:
{
uint8_t v_a_boxed_669_; lean_object* v_res_670_; 
v_a_boxed_669_ = lean_unbox(v_a_666_);
v_res_670_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_e_662_, v_offset_663_, v_f_664_, v_a_665_, v_a_boxed_669_, v_a_667_, v_a_668_);
lean_dec_ref(v_a_667_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___boxed(lean_object* v_e_671_, lean_object* v_offset_672_, lean_object* v_fn_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_){
_start:
{
uint8_t v_a_boxed_678_; lean_object* v_res_679_; 
v_a_boxed_678_ = lean_unbox(v_a_675_);
v_res_679_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit(v_e_671_, v_offset_672_, v_fn_673_, v_a_674_, v_a_boxed_678_, v_a_676_, v_a_677_);
lean_dec_ref(v_a_676_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild_match__4_splitter___redArg(lean_object* v_____do__lift_680_, lean_object* v_h__1_681_, lean_object* v_h__2_682_){
_start:
{
if (lean_obj_tag(v_____do__lift_680_) == 1)
{
lean_object* v_val_683_; lean_object* v___x_684_; 
lean_dec(v_h__2_682_);
v_val_683_ = lean_ctor_get(v_____do__lift_680_, 0);
lean_inc(v_val_683_);
lean_dec_ref_known(v_____do__lift_680_, 1);
v___x_684_ = lean_apply_1(v_h__1_681_, v_val_683_);
return v___x_684_;
}
else
{
lean_object* v___x_685_; 
lean_dec(v_h__1_681_);
v___x_685_ = lean_apply_2(v_h__2_682_, v_____do__lift_680_, lean_box(0));
return v___x_685_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild_match__4_splitter(lean_object* v_motive_686_, lean_object* v_____do__lift_687_, lean_object* v_h__1_688_, lean_object* v_h__2_689_){
_start:
{
if (lean_obj_tag(v_____do__lift_687_) == 1)
{
lean_object* v_val_690_; lean_object* v___x_691_; 
lean_dec(v_h__2_689_);
v_val_690_ = lean_ctor_get(v_____do__lift_687_, 0);
lean_inc(v_val_690_);
lean_dec_ref_known(v_____do__lift_687_, 1);
v___x_691_ = lean_apply_1(v_h__1_688_, v_val_690_);
return v___x_691_;
}
else
{
lean_object* v___x_692_; 
lean_dec(v_h__1_688_);
v___x_692_ = lean_apply_2(v_h__2_689_, v_____do__lift_687_, lean_box(0));
return v___x_692_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild_match__1_splitter___redArg(lean_object* v_e_693_, lean_object* v_h__1_694_, lean_object* v_h__2_695_, lean_object* v_h__3_696_, lean_object* v_h__4_697_, lean_object* v_h__5_698_, lean_object* v_h__6_699_, lean_object* v_h__7_700_){
_start:
{
switch(lean_obj_tag(v_e_693_))
{
case 9:
{
lean_object* v_a_701_; lean_object* v___x_702_; 
lean_dec(v_h__7_700_);
lean_dec(v_h__6_699_);
lean_dec(v_h__5_698_);
lean_dec(v_h__4_697_);
lean_dec(v_h__3_696_);
lean_dec(v_h__2_695_);
v_a_701_ = lean_ctor_get(v_e_693_, 0);
lean_inc_ref(v_a_701_);
lean_dec_ref_known(v_e_693_, 1);
v___x_702_ = lean_apply_1(v_h__1_694_, v_a_701_);
return v___x_702_;
}
case 2:
{
lean_object* v_mvarId_703_; lean_object* v___x_704_; 
lean_dec(v_h__7_700_);
lean_dec(v_h__6_699_);
lean_dec(v_h__5_698_);
lean_dec(v_h__4_697_);
lean_dec(v_h__3_696_);
lean_dec(v_h__1_694_);
v_mvarId_703_ = lean_ctor_get(v_e_693_, 0);
lean_inc(v_mvarId_703_);
lean_dec_ref_known(v_e_693_, 1);
v___x_704_ = lean_apply_1(v_h__2_695_, v_mvarId_703_);
return v___x_704_;
}
case 0:
{
lean_object* v_deBruijnIndex_705_; lean_object* v___x_706_; 
lean_dec(v_h__7_700_);
lean_dec(v_h__6_699_);
lean_dec(v_h__5_698_);
lean_dec(v_h__4_697_);
lean_dec(v_h__2_695_);
lean_dec(v_h__1_694_);
v_deBruijnIndex_705_ = lean_ctor_get(v_e_693_, 0);
lean_inc(v_deBruijnIndex_705_);
lean_dec_ref_known(v_e_693_, 1);
v___x_706_ = lean_apply_1(v_h__3_696_, v_deBruijnIndex_705_);
return v___x_706_;
}
case 1:
{
lean_object* v_fvarId_707_; lean_object* v___x_708_; 
lean_dec(v_h__7_700_);
lean_dec(v_h__6_699_);
lean_dec(v_h__5_698_);
lean_dec(v_h__3_696_);
lean_dec(v_h__2_695_);
lean_dec(v_h__1_694_);
v_fvarId_707_ = lean_ctor_get(v_e_693_, 0);
lean_inc(v_fvarId_707_);
lean_dec_ref_known(v_e_693_, 1);
v___x_708_ = lean_apply_1(v_h__4_697_, v_fvarId_707_);
return v___x_708_;
}
case 4:
{
lean_object* v_declName_709_; lean_object* v_us_710_; lean_object* v___x_711_; 
lean_dec(v_h__7_700_);
lean_dec(v_h__6_699_);
lean_dec(v_h__4_697_);
lean_dec(v_h__3_696_);
lean_dec(v_h__2_695_);
lean_dec(v_h__1_694_);
v_declName_709_ = lean_ctor_get(v_e_693_, 0);
lean_inc(v_declName_709_);
v_us_710_ = lean_ctor_get(v_e_693_, 1);
lean_inc(v_us_710_);
lean_dec_ref_known(v_e_693_, 2);
v___x_711_ = lean_apply_2(v_h__5_698_, v_declName_709_, v_us_710_);
return v___x_711_;
}
case 3:
{
lean_object* v_u_712_; lean_object* v___x_713_; 
lean_dec(v_h__7_700_);
lean_dec(v_h__5_698_);
lean_dec(v_h__4_697_);
lean_dec(v_h__3_696_);
lean_dec(v_h__2_695_);
lean_dec(v_h__1_694_);
v_u_712_ = lean_ctor_get(v_e_693_, 0);
lean_inc(v_u_712_);
lean_dec_ref_known(v_e_693_, 1);
v___x_713_ = lean_apply_1(v_h__6_699_, v_u_712_);
return v___x_713_;
}
default: 
{
lean_object* v___x_714_; 
lean_dec(v_h__6_699_);
lean_dec(v_h__5_698_);
lean_dec(v_h__4_697_);
lean_dec(v_h__3_696_);
lean_dec(v_h__2_695_);
lean_dec(v_h__1_694_);
v___x_714_ = lean_apply_7(v_h__7_700_, v_e_693_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_714_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild_match__1_splitter(lean_object* v_motive_715_, lean_object* v_e_716_, lean_object* v_h__1_717_, lean_object* v_h__2_718_, lean_object* v_h__3_719_, lean_object* v_h__4_720_, lean_object* v_h__5_721_, lean_object* v_h__6_722_, lean_object* v_h__7_723_){
_start:
{
switch(lean_obj_tag(v_e_716_))
{
case 9:
{
lean_object* v_a_724_; lean_object* v___x_725_; 
lean_dec(v_h__7_723_);
lean_dec(v_h__6_722_);
lean_dec(v_h__5_721_);
lean_dec(v_h__4_720_);
lean_dec(v_h__3_719_);
lean_dec(v_h__2_718_);
v_a_724_ = lean_ctor_get(v_e_716_, 0);
lean_inc_ref(v_a_724_);
lean_dec_ref_known(v_e_716_, 1);
v___x_725_ = lean_apply_1(v_h__1_717_, v_a_724_);
return v___x_725_;
}
case 2:
{
lean_object* v_mvarId_726_; lean_object* v___x_727_; 
lean_dec(v_h__7_723_);
lean_dec(v_h__6_722_);
lean_dec(v_h__5_721_);
lean_dec(v_h__4_720_);
lean_dec(v_h__3_719_);
lean_dec(v_h__1_717_);
v_mvarId_726_ = lean_ctor_get(v_e_716_, 0);
lean_inc(v_mvarId_726_);
lean_dec_ref_known(v_e_716_, 1);
v___x_727_ = lean_apply_1(v_h__2_718_, v_mvarId_726_);
return v___x_727_;
}
case 0:
{
lean_object* v_deBruijnIndex_728_; lean_object* v___x_729_; 
lean_dec(v_h__7_723_);
lean_dec(v_h__6_722_);
lean_dec(v_h__5_721_);
lean_dec(v_h__4_720_);
lean_dec(v_h__2_718_);
lean_dec(v_h__1_717_);
v_deBruijnIndex_728_ = lean_ctor_get(v_e_716_, 0);
lean_inc(v_deBruijnIndex_728_);
lean_dec_ref_known(v_e_716_, 1);
v___x_729_ = lean_apply_1(v_h__3_719_, v_deBruijnIndex_728_);
return v___x_729_;
}
case 1:
{
lean_object* v_fvarId_730_; lean_object* v___x_731_; 
lean_dec(v_h__7_723_);
lean_dec(v_h__6_722_);
lean_dec(v_h__5_721_);
lean_dec(v_h__3_719_);
lean_dec(v_h__2_718_);
lean_dec(v_h__1_717_);
v_fvarId_730_ = lean_ctor_get(v_e_716_, 0);
lean_inc(v_fvarId_730_);
lean_dec_ref_known(v_e_716_, 1);
v___x_731_ = lean_apply_1(v_h__4_720_, v_fvarId_730_);
return v___x_731_;
}
case 4:
{
lean_object* v_declName_732_; lean_object* v_us_733_; lean_object* v___x_734_; 
lean_dec(v_h__7_723_);
lean_dec(v_h__6_722_);
lean_dec(v_h__4_720_);
lean_dec(v_h__3_719_);
lean_dec(v_h__2_718_);
lean_dec(v_h__1_717_);
v_declName_732_ = lean_ctor_get(v_e_716_, 0);
lean_inc(v_declName_732_);
v_us_733_ = lean_ctor_get(v_e_716_, 1);
lean_inc(v_us_733_);
lean_dec_ref_known(v_e_716_, 2);
v___x_734_ = lean_apply_2(v_h__5_721_, v_declName_732_, v_us_733_);
return v___x_734_;
}
case 3:
{
lean_object* v_u_735_; lean_object* v___x_736_; 
lean_dec(v_h__7_723_);
lean_dec(v_h__5_721_);
lean_dec(v_h__4_720_);
lean_dec(v_h__3_719_);
lean_dec(v_h__2_718_);
lean_dec(v_h__1_717_);
v_u_735_ = lean_ctor_get(v_e_716_, 0);
lean_inc(v_u_735_);
lean_dec_ref_known(v_e_716_, 1);
v___x_736_ = lean_apply_1(v_h__6_722_, v_u_735_);
return v___x_736_;
}
default: 
{
lean_object* v___x_737_; 
lean_dec(v_h__6_722_);
lean_dec(v_h__5_721_);
lean_dec(v_h__4_720_);
lean_dec(v_h__3_719_);
lean_dec(v_h__2_718_);
lean_dec(v_h__1_717_);
v___x_737_ = lean_apply_7(v_h__7_723_, v_e_716_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_737_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit_match__1_splitter___redArg(lean_object* v_e_738_, lean_object* v_h__1_739_, lean_object* v_h__2_740_, lean_object* v_h__3_741_, lean_object* v_h__4_742_, lean_object* v_h__5_743_, lean_object* v_h__6_744_, lean_object* v_h__7_745_, lean_object* v_h__8_746_, lean_object* v_h__9_747_, lean_object* v_h__10_748_, lean_object* v_h__11_749_, lean_object* v_h__12_750_){
_start:
{
switch(lean_obj_tag(v_e_738_))
{
case 0:
{
lean_object* v_deBruijnIndex_751_; lean_object* v___x_752_; 
lean_dec(v_h__12_750_);
lean_dec(v_h__11_749_);
lean_dec(v_h__10_748_);
lean_dec(v_h__9_747_);
lean_dec(v_h__8_746_);
lean_dec(v_h__7_745_);
lean_dec(v_h__6_744_);
lean_dec(v_h__5_743_);
lean_dec(v_h__4_742_);
lean_dec(v_h__2_740_);
lean_dec(v_h__1_739_);
v_deBruijnIndex_751_ = lean_ctor_get(v_e_738_, 0);
lean_inc(v_deBruijnIndex_751_);
lean_dec_ref_known(v_e_738_, 1);
v___x_752_ = lean_apply_1(v_h__3_741_, v_deBruijnIndex_751_);
return v___x_752_;
}
case 1:
{
lean_object* v_fvarId_753_; lean_object* v___x_754_; 
lean_dec(v_h__12_750_);
lean_dec(v_h__11_749_);
lean_dec(v_h__10_748_);
lean_dec(v_h__9_747_);
lean_dec(v_h__8_746_);
lean_dec(v_h__7_745_);
lean_dec(v_h__6_744_);
lean_dec(v_h__5_743_);
lean_dec(v_h__3_741_);
lean_dec(v_h__2_740_);
lean_dec(v_h__1_739_);
v_fvarId_753_ = lean_ctor_get(v_e_738_, 0);
lean_inc(v_fvarId_753_);
lean_dec_ref_known(v_e_738_, 1);
v___x_754_ = lean_apply_1(v_h__4_742_, v_fvarId_753_);
return v___x_754_;
}
case 2:
{
lean_object* v_mvarId_755_; lean_object* v___x_756_; 
lean_dec(v_h__12_750_);
lean_dec(v_h__11_749_);
lean_dec(v_h__10_748_);
lean_dec(v_h__9_747_);
lean_dec(v_h__8_746_);
lean_dec(v_h__7_745_);
lean_dec(v_h__6_744_);
lean_dec(v_h__5_743_);
lean_dec(v_h__4_742_);
lean_dec(v_h__3_741_);
lean_dec(v_h__1_739_);
v_mvarId_755_ = lean_ctor_get(v_e_738_, 0);
lean_inc(v_mvarId_755_);
lean_dec_ref_known(v_e_738_, 1);
v___x_756_ = lean_apply_1(v_h__2_740_, v_mvarId_755_);
return v___x_756_;
}
case 3:
{
lean_object* v_u_757_; lean_object* v___x_758_; 
lean_dec(v_h__12_750_);
lean_dec(v_h__11_749_);
lean_dec(v_h__10_748_);
lean_dec(v_h__9_747_);
lean_dec(v_h__8_746_);
lean_dec(v_h__7_745_);
lean_dec(v_h__5_743_);
lean_dec(v_h__4_742_);
lean_dec(v_h__3_741_);
lean_dec(v_h__2_740_);
lean_dec(v_h__1_739_);
v_u_757_ = lean_ctor_get(v_e_738_, 0);
lean_inc(v_u_757_);
lean_dec_ref_known(v_e_738_, 1);
v___x_758_ = lean_apply_1(v_h__6_744_, v_u_757_);
return v___x_758_;
}
case 4:
{
lean_object* v_declName_759_; lean_object* v_us_760_; lean_object* v___x_761_; 
lean_dec(v_h__12_750_);
lean_dec(v_h__11_749_);
lean_dec(v_h__10_748_);
lean_dec(v_h__9_747_);
lean_dec(v_h__8_746_);
lean_dec(v_h__7_745_);
lean_dec(v_h__6_744_);
lean_dec(v_h__4_742_);
lean_dec(v_h__3_741_);
lean_dec(v_h__2_740_);
lean_dec(v_h__1_739_);
v_declName_759_ = lean_ctor_get(v_e_738_, 0);
lean_inc(v_declName_759_);
v_us_760_ = lean_ctor_get(v_e_738_, 1);
lean_inc(v_us_760_);
lean_dec_ref_known(v_e_738_, 2);
v___x_761_ = lean_apply_2(v_h__5_743_, v_declName_759_, v_us_760_);
return v___x_761_;
}
case 5:
{
lean_object* v_fn_762_; lean_object* v_arg_763_; lean_object* v___x_764_; 
lean_dec(v_h__12_750_);
lean_dec(v_h__11_749_);
lean_dec(v_h__10_748_);
lean_dec(v_h__9_747_);
lean_dec(v_h__8_746_);
lean_dec(v_h__6_744_);
lean_dec(v_h__5_743_);
lean_dec(v_h__4_742_);
lean_dec(v_h__3_741_);
lean_dec(v_h__2_740_);
lean_dec(v_h__1_739_);
v_fn_762_ = lean_ctor_get(v_e_738_, 0);
lean_inc_ref(v_fn_762_);
v_arg_763_ = lean_ctor_get(v_e_738_, 1);
lean_inc_ref(v_arg_763_);
lean_dec_ref_known(v_e_738_, 2);
v___x_764_ = lean_apply_2(v_h__7_745_, v_fn_762_, v_arg_763_);
return v___x_764_;
}
case 6:
{
lean_object* v_binderName_765_; lean_object* v_binderType_766_; lean_object* v_body_767_; uint8_t v_binderInfo_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
lean_dec(v_h__12_750_);
lean_dec(v_h__10_748_);
lean_dec(v_h__9_747_);
lean_dec(v_h__8_746_);
lean_dec(v_h__7_745_);
lean_dec(v_h__6_744_);
lean_dec(v_h__5_743_);
lean_dec(v_h__4_742_);
lean_dec(v_h__3_741_);
lean_dec(v_h__2_740_);
lean_dec(v_h__1_739_);
v_binderName_765_ = lean_ctor_get(v_e_738_, 0);
lean_inc(v_binderName_765_);
v_binderType_766_ = lean_ctor_get(v_e_738_, 1);
lean_inc_ref(v_binderType_766_);
v_body_767_ = lean_ctor_get(v_e_738_, 2);
lean_inc_ref(v_body_767_);
v_binderInfo_768_ = lean_ctor_get_uint8(v_e_738_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_738_, 3);
v___x_769_ = lean_box(v_binderInfo_768_);
v___x_770_ = lean_apply_4(v_h__11_749_, v_binderName_765_, v_binderType_766_, v_body_767_, v___x_769_);
return v___x_770_;
}
case 7:
{
lean_object* v_binderName_771_; lean_object* v_binderType_772_; lean_object* v_body_773_; uint8_t v_binderInfo_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
lean_dec(v_h__12_750_);
lean_dec(v_h__11_749_);
lean_dec(v_h__9_747_);
lean_dec(v_h__8_746_);
lean_dec(v_h__7_745_);
lean_dec(v_h__6_744_);
lean_dec(v_h__5_743_);
lean_dec(v_h__4_742_);
lean_dec(v_h__3_741_);
lean_dec(v_h__2_740_);
lean_dec(v_h__1_739_);
v_binderName_771_ = lean_ctor_get(v_e_738_, 0);
lean_inc(v_binderName_771_);
v_binderType_772_ = lean_ctor_get(v_e_738_, 1);
lean_inc_ref(v_binderType_772_);
v_body_773_ = lean_ctor_get(v_e_738_, 2);
lean_inc_ref(v_body_773_);
v_binderInfo_774_ = lean_ctor_get_uint8(v_e_738_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_738_, 3);
v___x_775_ = lean_box(v_binderInfo_774_);
v___x_776_ = lean_apply_4(v_h__10_748_, v_binderName_771_, v_binderType_772_, v_body_773_, v___x_775_);
return v___x_776_;
}
case 8:
{
lean_object* v_declName_777_; lean_object* v_type_778_; lean_object* v_value_779_; lean_object* v_body_780_; uint8_t v_nondep_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
lean_dec(v_h__11_749_);
lean_dec(v_h__10_748_);
lean_dec(v_h__9_747_);
lean_dec(v_h__8_746_);
lean_dec(v_h__7_745_);
lean_dec(v_h__6_744_);
lean_dec(v_h__5_743_);
lean_dec(v_h__4_742_);
lean_dec(v_h__3_741_);
lean_dec(v_h__2_740_);
lean_dec(v_h__1_739_);
v_declName_777_ = lean_ctor_get(v_e_738_, 0);
lean_inc(v_declName_777_);
v_type_778_ = lean_ctor_get(v_e_738_, 1);
lean_inc_ref(v_type_778_);
v_value_779_ = lean_ctor_get(v_e_738_, 2);
lean_inc_ref(v_value_779_);
v_body_780_ = lean_ctor_get(v_e_738_, 3);
lean_inc_ref(v_body_780_);
v_nondep_781_ = lean_ctor_get_uint8(v_e_738_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_738_, 4);
v___x_782_ = lean_box(v_nondep_781_);
v___x_783_ = lean_apply_5(v_h__12_750_, v_declName_777_, v_type_778_, v_value_779_, v_body_780_, v___x_782_);
return v___x_783_;
}
case 9:
{
lean_object* v_a_784_; lean_object* v___x_785_; 
lean_dec(v_h__12_750_);
lean_dec(v_h__11_749_);
lean_dec(v_h__10_748_);
lean_dec(v_h__9_747_);
lean_dec(v_h__8_746_);
lean_dec(v_h__7_745_);
lean_dec(v_h__6_744_);
lean_dec(v_h__5_743_);
lean_dec(v_h__4_742_);
lean_dec(v_h__3_741_);
lean_dec(v_h__2_740_);
v_a_784_ = lean_ctor_get(v_e_738_, 0);
lean_inc_ref(v_a_784_);
lean_dec_ref_known(v_e_738_, 1);
v___x_785_ = lean_apply_1(v_h__1_739_, v_a_784_);
return v___x_785_;
}
case 10:
{
lean_object* v_data_786_; lean_object* v_expr_787_; lean_object* v___x_788_; 
lean_dec(v_h__12_750_);
lean_dec(v_h__11_749_);
lean_dec(v_h__10_748_);
lean_dec(v_h__9_747_);
lean_dec(v_h__7_745_);
lean_dec(v_h__6_744_);
lean_dec(v_h__5_743_);
lean_dec(v_h__4_742_);
lean_dec(v_h__3_741_);
lean_dec(v_h__2_740_);
lean_dec(v_h__1_739_);
v_data_786_ = lean_ctor_get(v_e_738_, 0);
lean_inc(v_data_786_);
v_expr_787_ = lean_ctor_get(v_e_738_, 1);
lean_inc_ref(v_expr_787_);
lean_dec_ref_known(v_e_738_, 2);
v___x_788_ = lean_apply_2(v_h__8_746_, v_data_786_, v_expr_787_);
return v___x_788_;
}
default: 
{
lean_object* v_typeName_789_; lean_object* v_idx_790_; lean_object* v_struct_791_; lean_object* v___x_792_; 
lean_dec(v_h__12_750_);
lean_dec(v_h__11_749_);
lean_dec(v_h__10_748_);
lean_dec(v_h__8_746_);
lean_dec(v_h__7_745_);
lean_dec(v_h__6_744_);
lean_dec(v_h__5_743_);
lean_dec(v_h__4_742_);
lean_dec(v_h__3_741_);
lean_dec(v_h__2_740_);
lean_dec(v_h__1_739_);
v_typeName_789_ = lean_ctor_get(v_e_738_, 0);
lean_inc(v_typeName_789_);
v_idx_790_ = lean_ctor_get(v_e_738_, 1);
lean_inc(v_idx_790_);
v_struct_791_ = lean_ctor_get(v_e_738_, 2);
lean_inc_ref(v_struct_791_);
lean_dec_ref_known(v_e_738_, 3);
v___x_792_ = lean_apply_3(v_h__9_747_, v_typeName_789_, v_idx_790_, v_struct_791_);
return v___x_792_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit_match__1_splitter(lean_object* v_motive_793_, lean_object* v_e_794_, lean_object* v_h__1_795_, lean_object* v_h__2_796_, lean_object* v_h__3_797_, lean_object* v_h__4_798_, lean_object* v_h__5_799_, lean_object* v_h__6_800_, lean_object* v_h__7_801_, lean_object* v_h__8_802_, lean_object* v_h__9_803_, lean_object* v_h__10_804_, lean_object* v_h__11_805_, lean_object* v_h__12_806_){
_start:
{
switch(lean_obj_tag(v_e_794_))
{
case 0:
{
lean_object* v_deBruijnIndex_807_; lean_object* v___x_808_; 
lean_dec(v_h__12_806_);
lean_dec(v_h__11_805_);
lean_dec(v_h__10_804_);
lean_dec(v_h__9_803_);
lean_dec(v_h__8_802_);
lean_dec(v_h__7_801_);
lean_dec(v_h__6_800_);
lean_dec(v_h__5_799_);
lean_dec(v_h__4_798_);
lean_dec(v_h__2_796_);
lean_dec(v_h__1_795_);
v_deBruijnIndex_807_ = lean_ctor_get(v_e_794_, 0);
lean_inc(v_deBruijnIndex_807_);
lean_dec_ref_known(v_e_794_, 1);
v___x_808_ = lean_apply_1(v_h__3_797_, v_deBruijnIndex_807_);
return v___x_808_;
}
case 1:
{
lean_object* v_fvarId_809_; lean_object* v___x_810_; 
lean_dec(v_h__12_806_);
lean_dec(v_h__11_805_);
lean_dec(v_h__10_804_);
lean_dec(v_h__9_803_);
lean_dec(v_h__8_802_);
lean_dec(v_h__7_801_);
lean_dec(v_h__6_800_);
lean_dec(v_h__5_799_);
lean_dec(v_h__3_797_);
lean_dec(v_h__2_796_);
lean_dec(v_h__1_795_);
v_fvarId_809_ = lean_ctor_get(v_e_794_, 0);
lean_inc(v_fvarId_809_);
lean_dec_ref_known(v_e_794_, 1);
v___x_810_ = lean_apply_1(v_h__4_798_, v_fvarId_809_);
return v___x_810_;
}
case 2:
{
lean_object* v_mvarId_811_; lean_object* v___x_812_; 
lean_dec(v_h__12_806_);
lean_dec(v_h__11_805_);
lean_dec(v_h__10_804_);
lean_dec(v_h__9_803_);
lean_dec(v_h__8_802_);
lean_dec(v_h__7_801_);
lean_dec(v_h__6_800_);
lean_dec(v_h__5_799_);
lean_dec(v_h__4_798_);
lean_dec(v_h__3_797_);
lean_dec(v_h__1_795_);
v_mvarId_811_ = lean_ctor_get(v_e_794_, 0);
lean_inc(v_mvarId_811_);
lean_dec_ref_known(v_e_794_, 1);
v___x_812_ = lean_apply_1(v_h__2_796_, v_mvarId_811_);
return v___x_812_;
}
case 3:
{
lean_object* v_u_813_; lean_object* v___x_814_; 
lean_dec(v_h__12_806_);
lean_dec(v_h__11_805_);
lean_dec(v_h__10_804_);
lean_dec(v_h__9_803_);
lean_dec(v_h__8_802_);
lean_dec(v_h__7_801_);
lean_dec(v_h__5_799_);
lean_dec(v_h__4_798_);
lean_dec(v_h__3_797_);
lean_dec(v_h__2_796_);
lean_dec(v_h__1_795_);
v_u_813_ = lean_ctor_get(v_e_794_, 0);
lean_inc(v_u_813_);
lean_dec_ref_known(v_e_794_, 1);
v___x_814_ = lean_apply_1(v_h__6_800_, v_u_813_);
return v___x_814_;
}
case 4:
{
lean_object* v_declName_815_; lean_object* v_us_816_; lean_object* v___x_817_; 
lean_dec(v_h__12_806_);
lean_dec(v_h__11_805_);
lean_dec(v_h__10_804_);
lean_dec(v_h__9_803_);
lean_dec(v_h__8_802_);
lean_dec(v_h__7_801_);
lean_dec(v_h__6_800_);
lean_dec(v_h__4_798_);
lean_dec(v_h__3_797_);
lean_dec(v_h__2_796_);
lean_dec(v_h__1_795_);
v_declName_815_ = lean_ctor_get(v_e_794_, 0);
lean_inc(v_declName_815_);
v_us_816_ = lean_ctor_get(v_e_794_, 1);
lean_inc(v_us_816_);
lean_dec_ref_known(v_e_794_, 2);
v___x_817_ = lean_apply_2(v_h__5_799_, v_declName_815_, v_us_816_);
return v___x_817_;
}
case 5:
{
lean_object* v_fn_818_; lean_object* v_arg_819_; lean_object* v___x_820_; 
lean_dec(v_h__12_806_);
lean_dec(v_h__11_805_);
lean_dec(v_h__10_804_);
lean_dec(v_h__9_803_);
lean_dec(v_h__8_802_);
lean_dec(v_h__6_800_);
lean_dec(v_h__5_799_);
lean_dec(v_h__4_798_);
lean_dec(v_h__3_797_);
lean_dec(v_h__2_796_);
lean_dec(v_h__1_795_);
v_fn_818_ = lean_ctor_get(v_e_794_, 0);
lean_inc_ref(v_fn_818_);
v_arg_819_ = lean_ctor_get(v_e_794_, 1);
lean_inc_ref(v_arg_819_);
lean_dec_ref_known(v_e_794_, 2);
v___x_820_ = lean_apply_2(v_h__7_801_, v_fn_818_, v_arg_819_);
return v___x_820_;
}
case 6:
{
lean_object* v_binderName_821_; lean_object* v_binderType_822_; lean_object* v_body_823_; uint8_t v_binderInfo_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
lean_dec(v_h__12_806_);
lean_dec(v_h__10_804_);
lean_dec(v_h__9_803_);
lean_dec(v_h__8_802_);
lean_dec(v_h__7_801_);
lean_dec(v_h__6_800_);
lean_dec(v_h__5_799_);
lean_dec(v_h__4_798_);
lean_dec(v_h__3_797_);
lean_dec(v_h__2_796_);
lean_dec(v_h__1_795_);
v_binderName_821_ = lean_ctor_get(v_e_794_, 0);
lean_inc(v_binderName_821_);
v_binderType_822_ = lean_ctor_get(v_e_794_, 1);
lean_inc_ref(v_binderType_822_);
v_body_823_ = lean_ctor_get(v_e_794_, 2);
lean_inc_ref(v_body_823_);
v_binderInfo_824_ = lean_ctor_get_uint8(v_e_794_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_794_, 3);
v___x_825_ = lean_box(v_binderInfo_824_);
v___x_826_ = lean_apply_4(v_h__11_805_, v_binderName_821_, v_binderType_822_, v_body_823_, v___x_825_);
return v___x_826_;
}
case 7:
{
lean_object* v_binderName_827_; lean_object* v_binderType_828_; lean_object* v_body_829_; uint8_t v_binderInfo_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
lean_dec(v_h__12_806_);
lean_dec(v_h__11_805_);
lean_dec(v_h__9_803_);
lean_dec(v_h__8_802_);
lean_dec(v_h__7_801_);
lean_dec(v_h__6_800_);
lean_dec(v_h__5_799_);
lean_dec(v_h__4_798_);
lean_dec(v_h__3_797_);
lean_dec(v_h__2_796_);
lean_dec(v_h__1_795_);
v_binderName_827_ = lean_ctor_get(v_e_794_, 0);
lean_inc(v_binderName_827_);
v_binderType_828_ = lean_ctor_get(v_e_794_, 1);
lean_inc_ref(v_binderType_828_);
v_body_829_ = lean_ctor_get(v_e_794_, 2);
lean_inc_ref(v_body_829_);
v_binderInfo_830_ = lean_ctor_get_uint8(v_e_794_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_794_, 3);
v___x_831_ = lean_box(v_binderInfo_830_);
v___x_832_ = lean_apply_4(v_h__10_804_, v_binderName_827_, v_binderType_828_, v_body_829_, v___x_831_);
return v___x_832_;
}
case 8:
{
lean_object* v_declName_833_; lean_object* v_type_834_; lean_object* v_value_835_; lean_object* v_body_836_; uint8_t v_nondep_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
lean_dec(v_h__11_805_);
lean_dec(v_h__10_804_);
lean_dec(v_h__9_803_);
lean_dec(v_h__8_802_);
lean_dec(v_h__7_801_);
lean_dec(v_h__6_800_);
lean_dec(v_h__5_799_);
lean_dec(v_h__4_798_);
lean_dec(v_h__3_797_);
lean_dec(v_h__2_796_);
lean_dec(v_h__1_795_);
v_declName_833_ = lean_ctor_get(v_e_794_, 0);
lean_inc(v_declName_833_);
v_type_834_ = lean_ctor_get(v_e_794_, 1);
lean_inc_ref(v_type_834_);
v_value_835_ = lean_ctor_get(v_e_794_, 2);
lean_inc_ref(v_value_835_);
v_body_836_ = lean_ctor_get(v_e_794_, 3);
lean_inc_ref(v_body_836_);
v_nondep_837_ = lean_ctor_get_uint8(v_e_794_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_794_, 4);
v___x_838_ = lean_box(v_nondep_837_);
v___x_839_ = lean_apply_5(v_h__12_806_, v_declName_833_, v_type_834_, v_value_835_, v_body_836_, v___x_838_);
return v___x_839_;
}
case 9:
{
lean_object* v_a_840_; lean_object* v___x_841_; 
lean_dec(v_h__12_806_);
lean_dec(v_h__11_805_);
lean_dec(v_h__10_804_);
lean_dec(v_h__9_803_);
lean_dec(v_h__8_802_);
lean_dec(v_h__7_801_);
lean_dec(v_h__6_800_);
lean_dec(v_h__5_799_);
lean_dec(v_h__4_798_);
lean_dec(v_h__3_797_);
lean_dec(v_h__2_796_);
v_a_840_ = lean_ctor_get(v_e_794_, 0);
lean_inc_ref(v_a_840_);
lean_dec_ref_known(v_e_794_, 1);
v___x_841_ = lean_apply_1(v_h__1_795_, v_a_840_);
return v___x_841_;
}
case 10:
{
lean_object* v_data_842_; lean_object* v_expr_843_; lean_object* v___x_844_; 
lean_dec(v_h__12_806_);
lean_dec(v_h__11_805_);
lean_dec(v_h__10_804_);
lean_dec(v_h__9_803_);
lean_dec(v_h__7_801_);
lean_dec(v_h__6_800_);
lean_dec(v_h__5_799_);
lean_dec(v_h__4_798_);
lean_dec(v_h__3_797_);
lean_dec(v_h__2_796_);
lean_dec(v_h__1_795_);
v_data_842_ = lean_ctor_get(v_e_794_, 0);
lean_inc(v_data_842_);
v_expr_843_ = lean_ctor_get(v_e_794_, 1);
lean_inc_ref(v_expr_843_);
lean_dec_ref_known(v_e_794_, 2);
v___x_844_ = lean_apply_2(v_h__8_802_, v_data_842_, v_expr_843_);
return v___x_844_;
}
default: 
{
lean_object* v_typeName_845_; lean_object* v_idx_846_; lean_object* v_struct_847_; lean_object* v___x_848_; 
lean_dec(v_h__12_806_);
lean_dec(v_h__11_805_);
lean_dec(v_h__10_804_);
lean_dec(v_h__8_802_);
lean_dec(v_h__7_801_);
lean_dec(v_h__6_800_);
lean_dec(v_h__5_799_);
lean_dec(v_h__4_798_);
lean_dec(v_h__3_797_);
lean_dec(v_h__2_796_);
lean_dec(v_h__1_795_);
v_typeName_845_ = lean_ctor_get(v_e_794_, 0);
lean_inc(v_typeName_845_);
v_idx_846_ = lean_ctor_get(v_e_794_, 1);
lean_inc(v_idx_846_);
v_struct_847_ = lean_ctor_get(v_e_794_, 2);
lean_inc_ref(v_struct_847_);
lean_dec_ref_known(v_e_794_, 3);
v___x_848_ = lean_apply_3(v_h__9_803_, v_typeName_845_, v_idx_846_, v_struct_847_);
return v___x_848_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Sym_replaceS_x27___closed__0(void){
_start:
{
lean_object* v_cellCount_849_; lean_object* v___x_850_; 
v_cellCount_849_ = lean_unsigned_to_nat(16u);
v___x_850_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_849_);
return v___x_850_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_replaceS_x27___closed__1(void){
_start:
{
lean_object* v_cellCount_851_; lean_object* v___x_852_; 
v_cellCount_851_ = lean_unsigned_to_nat(16u);
v___x_852_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_851_);
return v___x_852_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_replaceS_x27___closed__2(void){
_start:
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_853_ = lean_obj_once(&l_Lean_Meta_Sym_replaceS_x27___closed__1, &l_Lean_Meta_Sym_replaceS_x27___closed__1_once, _init_l_Lean_Meta_Sym_replaceS_x27___closed__1);
v___x_854_ = lean_obj_once(&l_Lean_Meta_Sym_replaceS_x27___closed__0, &l_Lean_Meta_Sym_replaceS_x27___closed__0_once, _init_l_Lean_Meta_Sym_replaceS_x27___closed__0);
v___x_855_ = lean_unsigned_to_nat(0u);
v___x_856_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_856_, 0, v___x_855_);
lean_ctor_set(v___x_856_, 1, v___x_854_);
lean_ctor_set(v___x_856_, 2, v___x_853_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_replaceS_x27(lean_object* v_e_857_, lean_object* v_f_858_, uint8_t v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_862_ = lean_unsigned_to_nat(0u);
v___x_863_ = lean_box(v_a_859_);
lean_inc_ref(v_f_858_);
lean_inc_ref(v_a_860_);
lean_inc_ref(v_e_857_);
v___x_864_ = lean_apply_5(v_f_858_, v_e_857_, v___x_862_, v___x_863_, v_a_860_, v_a_861_);
if (lean_obj_tag(v___x_864_) == 0)
{
lean_object* v_a_865_; 
v_a_865_ = lean_ctor_get(v___x_864_, 0);
lean_inc(v_a_865_);
if (lean_obj_tag(v_a_865_) == 1)
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_874_; 
lean_dec_ref(v_f_858_);
lean_dec_ref(v_e_857_);
v_a_866_ = lean_ctor_get(v___x_864_, 1);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_874_ == 0)
{
lean_object* v_unused_875_; 
v_unused_875_ = lean_ctor_get(v___x_864_, 0);
lean_dec(v_unused_875_);
v___x_868_ = v___x_864_;
v_isShared_869_ = v_isSharedCheck_874_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_864_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_874_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v_val_870_; lean_object* v___x_872_; 
v_val_870_ = lean_ctor_get(v_a_865_, 0);
lean_inc(v_val_870_);
lean_dec_ref_known(v_a_865_, 1);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 0, v_val_870_);
v___x_872_ = v___x_868_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_val_870_);
lean_ctor_set(v_reuseFailAlloc_873_, 1, v_a_866_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
else
{
lean_dec(v_a_865_);
switch(lean_obj_tag(v_e_857_))
{
case 9:
{
lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_883_; 
lean_dec_ref(v_f_858_);
v_a_876_ = lean_ctor_get(v___x_864_, 1);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_883_ == 0)
{
lean_object* v_unused_884_; 
v_unused_884_ = lean_ctor_get(v___x_864_, 0);
lean_dec(v_unused_884_);
v___x_878_ = v___x_864_;
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v___x_864_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_881_; 
if (v_isShared_879_ == 0)
{
lean_ctor_set(v___x_878_, 0, v_e_857_);
v___x_881_ = v___x_878_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_e_857_);
lean_ctor_set(v_reuseFailAlloc_882_, 1, v_a_876_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
case 2:
{
lean_object* v_a_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_892_; 
lean_dec_ref(v_f_858_);
v_a_885_ = lean_ctor_get(v___x_864_, 1);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_892_ == 0)
{
lean_object* v_unused_893_; 
v_unused_893_ = lean_ctor_get(v___x_864_, 0);
lean_dec(v_unused_893_);
v___x_887_ = v___x_864_;
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_a_885_);
lean_dec(v___x_864_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_890_; 
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 0, v_e_857_);
v___x_890_ = v___x_887_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_e_857_);
lean_ctor_set(v_reuseFailAlloc_891_, 1, v_a_885_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
case 0:
{
lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_901_; 
lean_dec_ref(v_f_858_);
v_a_894_ = lean_ctor_get(v___x_864_, 1);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_901_ == 0)
{
lean_object* v_unused_902_; 
v_unused_902_ = lean_ctor_get(v___x_864_, 0);
lean_dec(v_unused_902_);
v___x_896_ = v___x_864_;
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_a_894_);
lean_dec(v___x_864_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___x_899_; 
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 0, v_e_857_);
v___x_899_ = v___x_896_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_e_857_);
lean_ctor_set(v_reuseFailAlloc_900_, 1, v_a_894_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
case 1:
{
lean_object* v_a_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_910_; 
lean_dec_ref(v_f_858_);
v_a_903_ = lean_ctor_get(v___x_864_, 1);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_910_ == 0)
{
lean_object* v_unused_911_; 
v_unused_911_ = lean_ctor_get(v___x_864_, 0);
lean_dec(v_unused_911_);
v___x_905_ = v___x_864_;
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_a_903_);
lean_dec(v___x_864_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_908_; 
if (v_isShared_906_ == 0)
{
lean_ctor_set(v___x_905_, 0, v_e_857_);
v___x_908_ = v___x_905_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_e_857_);
lean_ctor_set(v_reuseFailAlloc_909_, 1, v_a_903_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
}
case 4:
{
lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_919_; 
lean_dec_ref(v_f_858_);
v_a_912_ = lean_ctor_get(v___x_864_, 1);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_919_ == 0)
{
lean_object* v_unused_920_; 
v_unused_920_ = lean_ctor_get(v___x_864_, 0);
lean_dec(v_unused_920_);
v___x_914_ = v___x_864_;
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_864_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_917_; 
if (v_isShared_915_ == 0)
{
lean_ctor_set(v___x_914_, 0, v_e_857_);
v___x_917_ = v___x_914_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_e_857_);
lean_ctor_set(v_reuseFailAlloc_918_, 1, v_a_912_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
case 3:
{
lean_object* v_a_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_928_; 
lean_dec_ref(v_f_858_);
v_a_921_ = lean_ctor_get(v___x_864_, 1);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_928_ == 0)
{
lean_object* v_unused_929_; 
v_unused_929_ = lean_ctor_get(v___x_864_, 0);
lean_dec(v_unused_929_);
v___x_923_ = v___x_864_;
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_a_921_);
lean_dec(v___x_864_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v___x_926_; 
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 0, v_e_857_);
v___x_926_ = v___x_923_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_e_857_);
lean_ctor_set(v_reuseFailAlloc_927_, 1, v_a_921_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
}
}
}
default: 
{
lean_object* v_a_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
v_a_930_ = lean_ctor_get(v___x_864_, 1);
lean_inc(v_a_930_);
lean_dec_ref_known(v___x_864_, 2);
v___x_931_ = lean_obj_once(&l_Lean_Meta_Sym_replaceS_x27___closed__2, &l_Lean_Meta_Sym_replaceS_x27___closed__2_once, _init_l_Lean_Meta_Sym_replaceS_x27___closed__2);
v___x_932_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit(v_e_857_, v___x_862_, v_f_858_, v___x_931_, v_a_859_, v_a_860_, v_a_930_);
if (lean_obj_tag(v___x_932_) == 0)
{
lean_object* v_a_933_; lean_object* v_a_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_942_; 
v_a_933_ = lean_ctor_get(v___x_932_, 0);
v_a_934_ = lean_ctor_get(v___x_932_, 1);
v_isSharedCheck_942_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_942_ == 0)
{
v___x_936_ = v___x_932_;
v_isShared_937_ = v_isSharedCheck_942_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_a_934_);
lean_inc(v_a_933_);
lean_dec(v___x_932_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_942_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v_fst_938_; lean_object* v___x_940_; 
v_fst_938_ = lean_ctor_get(v_a_933_, 0);
lean_inc(v_fst_938_);
lean_dec(v_a_933_);
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 0, v_fst_938_);
v___x_940_ = v___x_936_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_fst_938_);
lean_ctor_set(v_reuseFailAlloc_941_, 1, v_a_934_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
}
else
{
lean_object* v_a_943_; lean_object* v_a_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_951_; 
v_a_943_ = lean_ctor_get(v___x_932_, 0);
v_a_944_ = lean_ctor_get(v___x_932_, 1);
v_isSharedCheck_951_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_951_ == 0)
{
v___x_946_ = v___x_932_;
v_isShared_947_ = v_isSharedCheck_951_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_a_944_);
lean_inc(v_a_943_);
lean_dec(v___x_932_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_951_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_949_; 
if (v_isShared_947_ == 0)
{
v___x_949_ = v___x_946_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_a_943_);
lean_ctor_set(v_reuseFailAlloc_950_, 1, v_a_944_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_952_; lean_object* v_a_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_960_; 
lean_dec_ref(v_f_858_);
lean_dec_ref(v_e_857_);
v_a_952_ = lean_ctor_get(v___x_864_, 0);
v_a_953_ = lean_ctor_get(v___x_864_, 1);
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_960_ == 0)
{
v___x_955_ = v___x_864_;
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_a_953_);
lean_inc(v_a_952_);
lean_dec(v___x_864_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_958_; 
if (v_isShared_956_ == 0)
{
v___x_958_ = v___x_955_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_a_952_);
lean_ctor_set(v_reuseFailAlloc_959_, 1, v_a_953_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
return v___x_958_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_replaceS_x27___boxed(lean_object* v_e_961_, lean_object* v_f_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_){
_start:
{
uint8_t v_a_boxed_966_; lean_object* v_res_967_; 
v_a_boxed_966_ = lean_unbox(v_a_963_);
v_res_967_ = l_Lean_Meta_Sym_replaceS_x27(v_e_961_, v_f_962_, v_a_boxed_966_, v_a_964_, v_a_965_);
lean_dec_ref(v_a_964_);
return v_res_967_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_replaceS___closed__0(void){
_start:
{
lean_object* v___x_968_; 
v___x_968_ = l_Lean_Meta_Sym_instInhabitedSymM(lean_box(0));
return v___x_968_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_replaceS___closed__3(void){
_start:
{
lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_971_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__26));
v___x_972_ = lean_unsigned_to_nat(16u);
v___x_973_ = lean_unsigned_to_nat(62u);
v___x_974_ = ((lean_object*)(l_Lean_Meta_Sym_replaceS___closed__2));
v___x_975_ = ((lean_object*)(l_Lean_Meta_Sym_replaceS___closed__1));
v___x_976_ = l_mkPanicMessageWithDecl(v___x_975_, v___x_974_, v___x_973_, v___x_972_, v___x_971_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_replaceS(lean_object* v_e_977_, lean_object* v_f_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_){
_start:
{
lean_object* v___x_986_; lean_object* v___x_987_; uint8_t v_debug_988_; lean_object* v_env_989_; lean_object* v___x_990_; lean_object* v___x_991_; uint8_t v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_986_ = lean_st_ref_get(v_a_980_);
v___x_987_ = lean_st_ref_get(v_a_984_);
v_debug_988_ = lean_ctor_get_uint8(v___x_986_, sizeof(void*)*11);
lean_dec(v___x_986_);
v_env_989_ = lean_ctor_get(v___x_987_, 0);
lean_inc_ref(v_env_989_);
lean_dec(v___x_987_);
v___x_990_ = lean_box(v_debug_988_);
v___x_991_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_replaceS_x27___boxed), 5, 3);
lean_closure_set(v___x_991_, 0, v_e_977_);
lean_closure_set(v___x_991_, 1, v_f_978_);
lean_closure_set(v___x_991_, 2, v___x_990_);
v___x_992_ = 0;
v___x_993_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_993_, 0, v_env_989_);
lean_ctor_set_uint8(v___x_993_, sizeof(void*)*1, v___x_992_);
lean_ctor_set_uint8(v___x_993_, sizeof(void*)*1 + 1, v___x_992_);
v___x_994_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___x_991_, v___x_993_, v_a_980_);
if (lean_obj_tag(v___x_994_) == 0)
{
lean_object* v_a_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1007_; 
v_a_995_ = lean_ctor_get(v___x_994_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_997_ = v___x_994_;
v_isShared_998_ = v_isSharedCheck_1007_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_a_995_);
lean_dec(v___x_994_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1007_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
if (lean_obj_tag(v_a_995_) == 0)
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_27__overap_1001_; lean_object* v___x_1002_; 
lean_dec_ref_known(v_a_995_, 1);
lean_del_object(v___x_997_);
v___x_999_ = lean_obj_once(&l_Lean_Meta_Sym_replaceS___closed__0, &l_Lean_Meta_Sym_replaceS___closed__0_once, _init_l_Lean_Meta_Sym_replaceS___closed__0);
v___x_1000_ = lean_obj_once(&l_Lean_Meta_Sym_replaceS___closed__3, &l_Lean_Meta_Sym_replaceS___closed__3_once, _init_l_Lean_Meta_Sym_replaceS___closed__3);
v___x_27__overap_1001_ = l_panic___redArg(v___x_999_, v___x_1000_);
lean_inc(v_a_984_);
lean_inc_ref(v_a_983_);
lean_inc(v_a_982_);
lean_inc_ref(v_a_981_);
lean_inc(v_a_980_);
lean_inc_ref(v_a_979_);
v___x_1002_ = lean_apply_7(v___x_27__overap_1001_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, lean_box(0));
return v___x_1002_;
}
else
{
lean_object* v_a_1003_; lean_object* v___x_1005_; 
v_a_1003_ = lean_ctor_get(v_a_995_, 0);
lean_inc(v_a_1003_);
lean_dec_ref_known(v_a_995_, 1);
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 0, v_a_1003_);
v___x_1005_ = v___x_997_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_a_1003_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
}
else
{
lean_object* v_a_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1015_; 
v_a_1008_ = lean_ctor_get(v___x_994_, 0);
v_isSharedCheck_1015_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_1010_ = v___x_994_;
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_a_1008_);
lean_dec(v___x_994_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v___x_1013_; 
if (v_isShared_1011_ == 0)
{
v___x_1013_ = v___x_1010_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_a_1008_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_replaceS___boxed(lean_object* v_e_1016_, lean_object* v_f_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_Lean_Meta_Sym_replaceS(v_e_1016_, v_f_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_);
lean_dec(v_a_1023_);
lean_dec_ref(v_a_1022_);
lean_dec(v_a_1021_);
lean_dec_ref(v_a_1020_);
lean_dec(v_a_1019_);
lean_dec_ref(v_a_1018_);
return v_res_1025_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_ReplaceS(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
