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
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
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
lean_object* l_Lean_Meta_Sym_instHashableExprPtr___lam__0___boxed(lean_object*);
lean_object* l_UInt64_ofNat___boxed(lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_instHashableProd___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instBEqExprPtr___lam__0___boxed(lean_object*, lean_object*);
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
lean_object* v_key_4_; lean_object* v_tail_5_; lean_object* v_fst_6_; lean_object* v_snd_7_; lean_object* v_fst_8_; lean_object* v_snd_9_; size_t v___x_10_; size_t v___x_11_; uint8_t v___x_12_; 
v_key_4_ = lean_ctor_get(v_x_2_, 0);
v_tail_5_ = lean_ctor_get(v_x_2_, 2);
v_fst_6_ = lean_ctor_get(v_key_4_, 0);
v_snd_7_ = lean_ctor_get(v_key_4_, 1);
v_fst_8_ = lean_ctor_get(v_a_1_, 0);
v_snd_9_ = lean_ctor_get(v_a_1_, 1);
v___x_10_ = lean_ptr_addr(v_fst_6_);
v___x_11_ = lean_ptr_addr(v_fst_8_);
v___x_12_ = lean_usize_dec_eq(v___x_10_, v___x_11_);
if (v___x_12_ == 0)
{
v_x_2_ = v_tail_5_;
goto _start;
}
else
{
uint8_t v___x_14_; 
v___x_14_ = lean_nat_dec_eq(v_snd_7_, v_snd_9_);
if (v___x_14_ == 0)
{
v_x_2_ = v_tail_5_;
goto _start;
}
else
{
return v___x_14_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg___boxed(lean_object* v_a_16_, lean_object* v_x_17_){
_start:
{
uint8_t v_res_18_; lean_object* v_r_19_; 
v_res_18_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_a_16_, v_x_17_);
lean_dec(v_x_17_);
lean_dec_ref(v_a_16_);
v_r_19_ = lean_box(v_res_18_);
return v_r_19_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_20_, lean_object* v_x_21_){
_start:
{
if (lean_obj_tag(v_x_21_) == 0)
{
return v_x_20_;
}
else
{
lean_object* v_key_22_; lean_object* v_value_23_; lean_object* v_tail_24_; lean_object* v___x_26_; uint8_t v_isShared_27_; uint8_t v_isSharedCheck_54_; 
v_key_22_ = lean_ctor_get(v_x_21_, 0);
v_value_23_ = lean_ctor_get(v_x_21_, 1);
v_tail_24_ = lean_ctor_get(v_x_21_, 2);
v_isSharedCheck_54_ = !lean_is_exclusive(v_x_21_);
if (v_isSharedCheck_54_ == 0)
{
v___x_26_ = v_x_21_;
v_isShared_27_ = v_isSharedCheck_54_;
goto v_resetjp_25_;
}
else
{
lean_inc(v_tail_24_);
lean_inc(v_value_23_);
lean_inc(v_key_22_);
lean_dec(v_x_21_);
v___x_26_ = lean_box(0);
v_isShared_27_ = v_isSharedCheck_54_;
goto v_resetjp_25_;
}
v_resetjp_25_:
{
lean_object* v_fst_28_; lean_object* v_snd_29_; lean_object* v___x_30_; size_t v___x_31_; size_t v___x_32_; size_t v___x_33_; uint64_t v___x_34_; uint64_t v___x_35_; uint64_t v___x_36_; uint64_t v___x_37_; uint64_t v___x_38_; uint64_t v_fold_39_; uint64_t v___x_40_; uint64_t v___x_41_; uint64_t v___x_42_; size_t v___x_43_; size_t v___x_44_; size_t v___x_45_; size_t v___x_46_; size_t v___x_47_; lean_object* v___x_48_; lean_object* v___x_50_; 
v_fst_28_ = lean_ctor_get(v_key_22_, 0);
v_snd_29_ = lean_ctor_get(v_key_22_, 1);
v___x_30_ = lean_array_get_size(v_x_20_);
v___x_31_ = lean_ptr_addr(v_fst_28_);
v___x_32_ = ((size_t)3ULL);
v___x_33_ = lean_usize_shift_right(v___x_31_, v___x_32_);
v___x_34_ = lean_usize_to_uint64(v___x_33_);
v___x_35_ = lean_uint64_of_nat(v_snd_29_);
v___x_36_ = lean_uint64_mix_hash(v___x_34_, v___x_35_);
v___x_37_ = 32ULL;
v___x_38_ = lean_uint64_shift_right(v___x_36_, v___x_37_);
v_fold_39_ = lean_uint64_xor(v___x_36_, v___x_38_);
v___x_40_ = 16ULL;
v___x_41_ = lean_uint64_shift_right(v_fold_39_, v___x_40_);
v___x_42_ = lean_uint64_xor(v_fold_39_, v___x_41_);
v___x_43_ = lean_uint64_to_usize(v___x_42_);
v___x_44_ = lean_usize_of_nat(v___x_30_);
v___x_45_ = ((size_t)1ULL);
v___x_46_ = lean_usize_sub(v___x_44_, v___x_45_);
v___x_47_ = lean_usize_land(v___x_43_, v___x_46_);
v___x_48_ = lean_array_uget_borrowed(v_x_20_, v___x_47_);
lean_inc(v___x_48_);
if (v_isShared_27_ == 0)
{
lean_ctor_set(v___x_26_, 2, v___x_48_);
v___x_50_ = v___x_26_;
goto v_reusejp_49_;
}
else
{
lean_object* v_reuseFailAlloc_53_; 
v_reuseFailAlloc_53_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_53_, 0, v_key_22_);
lean_ctor_set(v_reuseFailAlloc_53_, 1, v_value_23_);
lean_ctor_set(v_reuseFailAlloc_53_, 2, v___x_48_);
v___x_50_ = v_reuseFailAlloc_53_;
goto v_reusejp_49_;
}
v_reusejp_49_:
{
lean_object* v___x_51_; 
v___x_51_ = lean_array_uset(v_x_20_, v___x_47_, v___x_50_);
v_x_20_ = v___x_51_;
v_x_21_ = v_tail_24_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2___redArg(lean_object* v_i_55_, lean_object* v_source_56_, lean_object* v_target_57_){
_start:
{
lean_object* v___x_58_; uint8_t v___x_59_; 
v___x_58_ = lean_array_get_size(v_source_56_);
v___x_59_ = lean_nat_dec_lt(v_i_55_, v___x_58_);
if (v___x_59_ == 0)
{
lean_dec_ref(v_source_56_);
lean_dec(v_i_55_);
return v_target_57_;
}
else
{
lean_object* v_es_60_; lean_object* v___x_61_; lean_object* v_source_62_; lean_object* v_target_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v_es_60_ = lean_array_fget(v_source_56_, v_i_55_);
v___x_61_ = lean_box(0);
v_source_62_ = lean_array_fset(v_source_56_, v_i_55_, v___x_61_);
v_target_63_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3___redArg(v_target_57_, v_es_60_);
v___x_64_ = lean_unsigned_to_nat(1u);
v___x_65_ = lean_nat_add(v_i_55_, v___x_64_);
lean_dec(v_i_55_);
v_i_55_ = v___x_65_;
v_source_56_ = v_source_62_;
v_target_57_ = v_target_63_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1___redArg(lean_object* v_data_67_){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v_nbuckets_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_68_ = lean_array_get_size(v_data_67_);
v___x_69_ = lean_unsigned_to_nat(2u);
v_nbuckets_70_ = lean_nat_mul(v___x_68_, v___x_69_);
v___x_71_ = lean_unsigned_to_nat(0u);
v___x_72_ = lean_box(0);
v___x_73_ = lean_mk_array(v_nbuckets_70_, v___x_72_);
v___x_74_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2___redArg(v___x_71_, v_data_67_, v___x_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(lean_object* v_a_75_, lean_object* v_b_76_, lean_object* v_x_77_){
_start:
{
if (lean_obj_tag(v_x_77_) == 0)
{
lean_dec(v_b_76_);
lean_dec_ref(v_a_75_);
return v_x_77_;
}
else
{
lean_object* v_key_78_; lean_object* v_value_79_; lean_object* v_tail_80_; lean_object* v___x_82_; uint8_t v_isShared_83_; uint8_t v_isSharedCheck_98_; 
v_key_78_ = lean_ctor_get(v_x_77_, 0);
v_value_79_ = lean_ctor_get(v_x_77_, 1);
v_tail_80_ = lean_ctor_get(v_x_77_, 2);
v_isSharedCheck_98_ = !lean_is_exclusive(v_x_77_);
if (v_isSharedCheck_98_ == 0)
{
v___x_82_ = v_x_77_;
v_isShared_83_ = v_isSharedCheck_98_;
goto v_resetjp_81_;
}
else
{
lean_inc(v_tail_80_);
lean_inc(v_value_79_);
lean_inc(v_key_78_);
lean_dec(v_x_77_);
v___x_82_ = lean_box(0);
v_isShared_83_ = v_isSharedCheck_98_;
goto v_resetjp_81_;
}
v_resetjp_81_:
{
lean_object* v_fst_89_; lean_object* v_snd_90_; lean_object* v_fst_91_; lean_object* v_snd_92_; size_t v___x_93_; size_t v___x_94_; uint8_t v___x_95_; 
v_fst_89_ = lean_ctor_get(v_key_78_, 0);
v_snd_90_ = lean_ctor_get(v_key_78_, 1);
v_fst_91_ = lean_ctor_get(v_a_75_, 0);
v_snd_92_ = lean_ctor_get(v_a_75_, 1);
v___x_93_ = lean_ptr_addr(v_fst_89_);
v___x_94_ = lean_ptr_addr(v_fst_91_);
v___x_95_ = lean_usize_dec_eq(v___x_93_, v___x_94_);
if (v___x_95_ == 0)
{
goto v___jp_84_;
}
else
{
uint8_t v___x_96_; 
v___x_96_ = lean_nat_dec_eq(v_snd_90_, v_snd_92_);
if (v___x_96_ == 0)
{
goto v___jp_84_;
}
else
{
lean_object* v___x_97_; 
lean_del_object(v___x_82_);
lean_dec(v_value_79_);
lean_dec(v_key_78_);
v___x_97_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_97_, 0, v_a_75_);
lean_ctor_set(v___x_97_, 1, v_b_76_);
lean_ctor_set(v___x_97_, 2, v_tail_80_);
return v___x_97_;
}
}
v___jp_84_:
{
lean_object* v___x_85_; lean_object* v___x_87_; 
v___x_85_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(v_a_75_, v_b_76_, v_tail_80_);
if (v_isShared_83_ == 0)
{
lean_ctor_set(v___x_82_, 2, v___x_85_);
v___x_87_ = v___x_82_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v_key_78_);
lean_ctor_set(v_reuseFailAlloc_88_, 1, v_value_79_);
lean_ctor_set(v_reuseFailAlloc_88_, 2, v___x_85_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0___redArg(lean_object* v_m_99_, lean_object* v_a_100_, lean_object* v_b_101_){
_start:
{
lean_object* v_size_102_; lean_object* v_buckets_103_; lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_153_; 
v_size_102_ = lean_ctor_get(v_m_99_, 0);
v_buckets_103_ = lean_ctor_get(v_m_99_, 1);
v_isSharedCheck_153_ = !lean_is_exclusive(v_m_99_);
if (v_isSharedCheck_153_ == 0)
{
v___x_105_ = v_m_99_;
v_isShared_106_ = v_isSharedCheck_153_;
goto v_resetjp_104_;
}
else
{
lean_inc(v_buckets_103_);
lean_inc(v_size_102_);
lean_dec(v_m_99_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_153_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
lean_object* v_fst_107_; lean_object* v_snd_108_; lean_object* v___x_109_; size_t v___x_110_; size_t v___x_111_; size_t v___x_112_; uint64_t v___x_113_; uint64_t v___x_114_; uint64_t v___x_115_; uint64_t v___x_116_; uint64_t v___x_117_; uint64_t v_fold_118_; uint64_t v___x_119_; uint64_t v___x_120_; uint64_t v___x_121_; size_t v___x_122_; size_t v___x_123_; size_t v___x_124_; size_t v___x_125_; size_t v___x_126_; lean_object* v_bkt_127_; uint8_t v___x_128_; 
v_fst_107_ = lean_ctor_get(v_a_100_, 0);
v_snd_108_ = lean_ctor_get(v_a_100_, 1);
v___x_109_ = lean_array_get_size(v_buckets_103_);
v___x_110_ = lean_ptr_addr(v_fst_107_);
v___x_111_ = ((size_t)3ULL);
v___x_112_ = lean_usize_shift_right(v___x_110_, v___x_111_);
v___x_113_ = lean_usize_to_uint64(v___x_112_);
v___x_114_ = lean_uint64_of_nat(v_snd_108_);
v___x_115_ = lean_uint64_mix_hash(v___x_113_, v___x_114_);
v___x_116_ = 32ULL;
v___x_117_ = lean_uint64_shift_right(v___x_115_, v___x_116_);
v_fold_118_ = lean_uint64_xor(v___x_115_, v___x_117_);
v___x_119_ = 16ULL;
v___x_120_ = lean_uint64_shift_right(v_fold_118_, v___x_119_);
v___x_121_ = lean_uint64_xor(v_fold_118_, v___x_120_);
v___x_122_ = lean_uint64_to_usize(v___x_121_);
v___x_123_ = lean_usize_of_nat(v___x_109_);
v___x_124_ = ((size_t)1ULL);
v___x_125_ = lean_usize_sub(v___x_123_, v___x_124_);
v___x_126_ = lean_usize_land(v___x_122_, v___x_125_);
v_bkt_127_ = lean_array_uget_borrowed(v_buckets_103_, v___x_126_);
v___x_128_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_a_100_, v_bkt_127_);
if (v___x_128_ == 0)
{
lean_object* v___x_129_; lean_object* v_size_x27_130_; lean_object* v___x_131_; lean_object* v_buckets_x27_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; uint8_t v___x_138_; 
v___x_129_ = lean_unsigned_to_nat(1u);
v_size_x27_130_ = lean_nat_add(v_size_102_, v___x_129_);
lean_dec(v_size_102_);
lean_inc(v_bkt_127_);
v___x_131_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_131_, 0, v_a_100_);
lean_ctor_set(v___x_131_, 1, v_b_101_);
lean_ctor_set(v___x_131_, 2, v_bkt_127_);
v_buckets_x27_132_ = lean_array_uset(v_buckets_103_, v___x_126_, v___x_131_);
v___x_133_ = lean_unsigned_to_nat(4u);
v___x_134_ = lean_nat_mul(v_size_x27_130_, v___x_133_);
v___x_135_ = lean_unsigned_to_nat(3u);
v___x_136_ = lean_nat_div(v___x_134_, v___x_135_);
lean_dec(v___x_134_);
v___x_137_ = lean_array_get_size(v_buckets_x27_132_);
v___x_138_ = lean_nat_dec_le(v___x_136_, v___x_137_);
lean_dec(v___x_136_);
if (v___x_138_ == 0)
{
lean_object* v_val_139_; lean_object* v___x_141_; 
v_val_139_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1___redArg(v_buckets_x27_132_);
if (v_isShared_106_ == 0)
{
lean_ctor_set(v___x_105_, 1, v_val_139_);
lean_ctor_set(v___x_105_, 0, v_size_x27_130_);
v___x_141_ = v___x_105_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v_size_x27_130_);
lean_ctor_set(v_reuseFailAlloc_142_, 1, v_val_139_);
v___x_141_ = v_reuseFailAlloc_142_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
return v___x_141_;
}
}
else
{
lean_object* v___x_144_; 
if (v_isShared_106_ == 0)
{
lean_ctor_set(v___x_105_, 1, v_buckets_x27_132_);
lean_ctor_set(v___x_105_, 0, v_size_x27_130_);
v___x_144_ = v___x_105_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_size_x27_130_);
lean_ctor_set(v_reuseFailAlloc_145_, 1, v_buckets_x27_132_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
}
else
{
lean_object* v___x_146_; lean_object* v_buckets_x27_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_151_; 
lean_inc(v_bkt_127_);
v___x_146_ = lean_box(0);
v_buckets_x27_147_ = lean_array_uset(v_buckets_103_, v___x_126_, v___x_146_);
v___x_148_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(v_a_100_, v_b_101_, v_bkt_127_);
v___x_149_ = lean_array_uset(v_buckets_x27_147_, v___x_126_, v___x_148_);
if (v_isShared_106_ == 0)
{
lean_ctor_set(v___x_105_, 1, v___x_149_);
v___x_151_ = v___x_105_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_size_102_);
lean_ctor_set(v_reuseFailAlloc_152_, 1, v___x_149_);
v___x_151_ = v_reuseFailAlloc_152_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
return v___x_151_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(lean_object* v_key_154_, lean_object* v_r_155_, lean_object* v_a_156_, lean_object* v_a_157_){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
lean_inc_ref(v_r_155_);
v___x_158_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_156_, v_key_154_, v_r_155_);
v___x_159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_159_, 0, v_r_155_);
lean_ctor_set(v___x_159_, 1, v___x_158_);
v___x_160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
lean_ctor_set(v___x_160_, 1, v_a_157_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(lean_object* v_key_161_, lean_object* v_r_162_, lean_object* v_a_163_, uint8_t v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(v_key_161_, v_r_162_, v_a_163_, v_a_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___boxed(lean_object* v_key_168_, lean_object* v_r_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_){
_start:
{
uint8_t v_a_boxed_174_; lean_object* v_res_175_; 
v_a_boxed_174_ = lean_unbox(v_a_171_);
v_res_175_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_168_, v_r_169_, v_a_170_, v_a_boxed_174_, v_a_172_, v_a_173_);
lean_dec_ref(v_a_172_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0(lean_object* v_00_u03b2_176_, lean_object* v_m_177_, lean_object* v_a_178_, lean_object* v_b_179_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0___redArg(v_m_177_, v_a_178_, v_b_179_);
return v___x_180_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0(lean_object* v_00_u03b2_181_, lean_object* v_a_182_, lean_object* v_x_183_){
_start:
{
uint8_t v___x_184_; 
v___x_184_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_a_182_, v_x_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0___boxed(lean_object* v_00_u03b2_185_, lean_object* v_a_186_, lean_object* v_x_187_){
_start:
{
uint8_t v_res_188_; lean_object* v_r_189_; 
v_res_188_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0(v_00_u03b2_185_, v_a_186_, v_x_187_);
lean_dec(v_x_187_);
lean_dec_ref(v_a_186_);
v_r_189_ = lean_box(v_res_188_);
return v_r_189_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1(lean_object* v_00_u03b2_190_, lean_object* v_data_191_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1___redArg(v_data_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__2(lean_object* v_00_u03b2_193_, lean_object* v_a_194_, lean_object* v_b_195_, lean_object* v_x_196_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(v_a_194_, v_b_195_, v_x_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_198_, lean_object* v_i_199_, lean_object* v_source_200_, lean_object* v_target_201_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2___redArg(v_i_199_, v_source_200_, v_target_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_203_, lean_object* v_x_204_, lean_object* v_x_205_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3___redArg(v_x_204_, v_x_205_);
return v___x_206_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__4(void){
_start:
{
lean_object* v___x_213_; lean_object* v___f_214_; 
v___x_213_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___f_214_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_214_, 0, v___x_213_);
return v___f_214_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__5(void){
_start:
{
lean_object* v___f_215_; lean_object* v___f_216_; lean_object* v___f_217_; 
v___f_215_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__4, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__4_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__4);
v___f_216_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__0));
v___f_217_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_217_, 0, v___f_216_);
lean_closure_set(v___f_217_, 1, v___f_215_);
return v___f_217_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__10(void){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_237_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__9));
v___x_238_ = l_ReaderT_instMonad___redArg(v___x_237_);
return v___x_238_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11(void){
_start:
{
lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_239_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__10, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__10_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__10);
v___x_240_ = l_ReaderT_instMonad___redArg(v___x_239_);
return v___x_240_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20(void){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_241_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11);
v___x_242_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_242_, 0, lean_box(0));
lean_closure_set(v___x_242_, 1, lean_box(0));
lean_closure_set(v___x_242_, 2, v___x_241_);
return v___x_242_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__15(void){
_start:
{
lean_object* v___x_243_; lean_object* v___f_244_; 
v___x_243_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11);
v___f_244_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_244_, 0, v___x_243_);
return v___f_244_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__14(void){
_start:
{
lean_object* v___x_245_; lean_object* v___f_246_; 
v___x_245_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11);
v___f_246_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_246_, 0, v___x_245_);
return v___f_246_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__13(void){
_start:
{
lean_object* v___x_247_; lean_object* v___f_248_; 
v___x_247_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11);
v___f_248_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_248_, 0, v___x_247_);
return v___f_248_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__18(void){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_249_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11);
v___x_250_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_250_, 0, lean_box(0));
lean_closure_set(v___x_250_, 1, lean_box(0));
lean_closure_set(v___x_250_, 2, v___x_249_);
return v___x_250_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__12(void){
_start:
{
lean_object* v___x_251_; lean_object* v___f_252_; 
v___x_251_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11);
v___f_252_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_252_, 0, v___x_251_);
return v___f_252_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__16(void){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_253_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11);
v___x_254_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_254_, 0, lean_box(0));
lean_closure_set(v___x_254_, 1, lean_box(0));
lean_closure_set(v___x_254_, 2, v___x_253_);
return v___x_254_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__17(void){
_start:
{
lean_object* v___f_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v___f_255_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__12, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__12_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__12);
v___x_256_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__16, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__16_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__16);
v___x_257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_257_, 0, v___x_256_);
lean_ctor_set(v___x_257_, 1, v___f_255_);
return v___x_257_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__19(void){
_start:
{
lean_object* v___f_258_; lean_object* v___f_259_; lean_object* v___f_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v___f_258_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__15, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__15_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__15);
v___f_259_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__14, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__14_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__14);
v___f_260_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__13, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__13_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__13);
v___x_261_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__18, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__18_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__18);
v___x_262_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__17, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__17_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__17);
v___x_263_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
lean_ctor_set(v___x_263_, 1, v___x_261_);
lean_ctor_set(v___x_263_, 2, v___f_260_);
lean_ctor_set(v___x_263_, 3, v___f_259_);
lean_ctor_set(v___x_263_, 4, v___f_258_);
return v___x_263_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__21(void){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_264_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20);
v___x_265_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__19, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__19_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__19);
v___x_266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_266_, 0, v___x_265_);
lean_ctor_set(v___x_266_, 1, v___x_264_);
return v___x_266_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__22(void){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_267_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11);
v___x_268_ = lean_alloc_closure((void*)(l_StateT_lift), 6, 3);
lean_closure_set(v___x_268_, 0, lean_box(0));
lean_closure_set(v___x_268_, 1, lean_box(0));
lean_closure_set(v___x_268_, 2, v___x_267_);
return v___x_268_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__23(void){
_start:
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_269_ = l_Lean_instInhabitedExpr;
v___x_270_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__21, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__21_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__21);
v___x_271_ = l_instInhabitedOfMonad___redArg(v___x_270_, v___x_269_);
return v___x_271_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__27(void){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_275_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__26));
v___x_276_ = lean_unsigned_to_nat(67u);
v___x_277_ = lean_unsigned_to_nat(35u);
v___x_278_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__25));
v___x_279_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__24));
v___x_280_ = l_mkPanicMessageWithDecl(v___x_279_, v___x_278_, v___x_277_, v___x_276_, v___x_275_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit(lean_object* v_e_281_, lean_object* v_offset_282_, lean_object* v_fn_283_, lean_object* v_a_284_, uint8_t v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v_share1_291_; lean_object* v_assertShared_292_; lean_object* v_isDebugEnabled_293_; lean_object* v___x_294_; lean_object* v___f_295_; lean_object* v___f_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_288_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11);
v___x_289_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__21, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__21_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__21);
v___x_290_ = l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM;
v_share1_291_ = lean_ctor_get(v___x_290_, 0);
v_assertShared_292_ = lean_ctor_get(v___x_290_, 1);
v_isDebugEnabled_293_ = lean_ctor_get(v___x_290_, 2);
v___x_294_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__22, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__22_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__22);
lean_inc(v_share1_291_);
v___f_295_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_295_, 0, v_share1_291_);
lean_closure_set(v___f_295_, 1, v___x_294_);
lean_inc(v_assertShared_292_);
v___f_296_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift___redArg___lam__1), 3, 2);
lean_closure_set(v___f_296_, 0, v_assertShared_292_);
lean_closure_set(v___f_296_, 1, v___x_294_);
lean_inc(v_isDebugEnabled_293_);
v___x_297_ = lean_alloc_closure((void*)(l_StateT_lift), 6, 5);
lean_closure_set(v___x_297_, 0, lean_box(0));
lean_closure_set(v___x_297_, 1, lean_box(0));
lean_closure_set(v___x_297_, 2, v___x_288_);
lean_closure_set(v___x_297_, 3, lean_box(0));
lean_closure_set(v___x_297_, 4, v_isDebugEnabled_293_);
v___x_298_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_298_, 0, v___f_295_);
lean_ctor_set(v___x_298_, 1, v___f_296_);
lean_ctor_set(v___x_298_, 2, v___x_297_);
switch(lean_obj_tag(v_e_281_))
{
case 5:
{
lean_object* v_fn_299_; lean_object* v_arg_300_; lean_object* v___x_301_; 
v_fn_299_ = lean_ctor_get(v_e_281_, 0);
v_arg_300_ = lean_ctor_get(v_e_281_, 1);
lean_inc_ref(v_fn_283_);
lean_inc(v_offset_282_);
lean_inc_ref(v_fn_299_);
v___x_301_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_fn_299_, v_offset_282_, v_fn_283_, v_a_284_, v_a_285_, v_a_286_, v_a_287_);
if (lean_obj_tag(v___x_301_) == 0)
{
lean_object* v_a_302_; lean_object* v_a_303_; lean_object* v_fst_304_; lean_object* v_snd_305_; lean_object* v___x_306_; 
v_a_302_ = lean_ctor_get(v___x_301_, 0);
lean_inc(v_a_302_);
v_a_303_ = lean_ctor_get(v___x_301_, 1);
lean_inc(v_a_303_);
lean_dec_ref_known(v___x_301_, 2);
v_fst_304_ = lean_ctor_get(v_a_302_, 0);
lean_inc(v_fst_304_);
v_snd_305_ = lean_ctor_get(v_a_302_, 1);
lean_inc(v_snd_305_);
lean_dec(v_a_302_);
lean_inc_ref(v_arg_300_);
v___x_306_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_arg_300_, v_offset_282_, v_fn_283_, v_snd_305_, v_a_285_, v_a_286_, v_a_303_);
if (lean_obj_tag(v___x_306_) == 0)
{
lean_object* v_a_307_; lean_object* v_a_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_336_; 
v_a_307_ = lean_ctor_get(v___x_306_, 0);
v_a_308_ = lean_ctor_get(v___x_306_, 1);
v_isSharedCheck_336_ = !lean_is_exclusive(v___x_306_);
if (v_isSharedCheck_336_ == 0)
{
v___x_310_ = v___x_306_;
v_isShared_311_ = v_isSharedCheck_336_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_a_308_);
lean_inc(v_a_307_);
lean_dec(v___x_306_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_336_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v_fst_312_; lean_object* v_snd_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_335_; 
v_fst_312_ = lean_ctor_get(v_a_307_, 0);
v_snd_313_ = lean_ctor_get(v_a_307_, 1);
v_isSharedCheck_335_ = !lean_is_exclusive(v_a_307_);
if (v_isSharedCheck_335_ == 0)
{
v___x_315_ = v_a_307_;
v_isShared_316_ = v_isSharedCheck_335_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_snd_313_);
lean_inc(v_fst_312_);
lean_dec(v_a_307_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_335_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
size_t v___x_317_; size_t v___x_318_; uint8_t v___x_319_; 
v___x_317_ = lean_ptr_addr(v_fn_299_);
v___x_318_ = lean_ptr_addr(v_fst_304_);
v___x_319_ = lean_usize_dec_eq(v___x_317_, v___x_318_);
if (v___x_319_ == 0)
{
lean_object* v___x_12039__overap_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
lean_del_object(v___x_315_);
lean_del_object(v___x_310_);
lean_dec_ref_known(v_e_281_, 2);
v___x_12039__overap_320_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v___x_298_, v___x_289_, v_fst_304_, v_fst_312_);
v___x_321_ = lean_box(v_a_285_);
lean_inc_ref(v_a_286_);
v___x_322_ = lean_apply_4(v___x_12039__overap_320_, v_snd_313_, v___x_321_, v_a_286_, v_a_308_);
return v___x_322_;
}
else
{
size_t v___x_323_; size_t v___x_324_; uint8_t v___x_325_; 
v___x_323_ = lean_ptr_addr(v_arg_300_);
v___x_324_ = lean_ptr_addr(v_fst_312_);
v___x_325_ = lean_usize_dec_eq(v___x_323_, v___x_324_);
if (v___x_325_ == 0)
{
lean_object* v___x_12044__overap_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
lean_del_object(v___x_315_);
lean_del_object(v___x_310_);
lean_dec_ref_known(v_e_281_, 2);
v___x_12044__overap_326_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v___x_298_, v___x_289_, v_fst_304_, v_fst_312_);
v___x_327_ = lean_box(v_a_285_);
lean_inc_ref(v_a_286_);
v___x_328_ = lean_apply_4(v___x_12044__overap_326_, v_snd_313_, v___x_327_, v_a_286_, v_a_308_);
return v___x_328_;
}
else
{
lean_object* v___x_330_; 
lean_dec(v_fst_312_);
lean_dec(v_fst_304_);
lean_dec_ref_known(v___x_298_, 3);
if (v_isShared_316_ == 0)
{
lean_ctor_set(v___x_315_, 0, v_e_281_);
v___x_330_ = v___x_315_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_e_281_);
lean_ctor_set(v_reuseFailAlloc_334_, 1, v_snd_313_);
v___x_330_ = v_reuseFailAlloc_334_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
lean_object* v___x_332_; 
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 0, v___x_330_);
v___x_332_ = v___x_310_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v___x_330_);
lean_ctor_set(v_reuseFailAlloc_333_, 1, v_a_308_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_304_);
lean_dec_ref_known(v_e_281_, 2);
lean_dec_ref_known(v___x_298_, 3);
return v___x_306_;
}
}
else
{
lean_dec_ref_known(v_e_281_, 2);
lean_dec_ref_known(v___x_298_, 3);
lean_dec_ref(v_fn_283_);
lean_dec(v_offset_282_);
return v___x_301_;
}
}
case 6:
{
lean_object* v_binderName_337_; lean_object* v_binderType_338_; lean_object* v_body_339_; uint8_t v_binderInfo_340_; lean_object* v___x_341_; 
v_binderName_337_ = lean_ctor_get(v_e_281_, 0);
v_binderType_338_ = lean_ctor_get(v_e_281_, 1);
v_body_339_ = lean_ctor_get(v_e_281_, 2);
v_binderInfo_340_ = lean_ctor_get_uint8(v_e_281_, sizeof(void*)*3 + 8);
lean_inc_ref(v_fn_283_);
lean_inc(v_offset_282_);
lean_inc_ref(v_binderType_338_);
v___x_341_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_binderType_338_, v_offset_282_, v_fn_283_, v_a_284_, v_a_285_, v_a_286_, v_a_287_);
if (lean_obj_tag(v___x_341_) == 0)
{
lean_object* v_a_342_; lean_object* v_a_343_; lean_object* v_fst_344_; lean_object* v_snd_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v_a_342_ = lean_ctor_get(v___x_341_, 0);
lean_inc(v_a_342_);
v_a_343_ = lean_ctor_get(v___x_341_, 1);
lean_inc(v_a_343_);
lean_dec_ref_known(v___x_341_, 2);
v_fst_344_ = lean_ctor_get(v_a_342_, 0);
lean_inc(v_fst_344_);
v_snd_345_ = lean_ctor_get(v_a_342_, 1);
lean_inc(v_snd_345_);
lean_dec(v_a_342_);
v___x_346_ = lean_unsigned_to_nat(1u);
v___x_347_ = lean_nat_add(v_offset_282_, v___x_346_);
lean_dec(v_offset_282_);
lean_inc_ref(v_body_339_);
v___x_348_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_body_339_, v___x_347_, v_fn_283_, v_snd_345_, v_a_285_, v_a_286_, v_a_343_);
if (lean_obj_tag(v___x_348_) == 0)
{
lean_object* v_a_349_; lean_object* v_a_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_378_; 
v_a_349_ = lean_ctor_get(v___x_348_, 0);
v_a_350_ = lean_ctor_get(v___x_348_, 1);
v_isSharedCheck_378_ = !lean_is_exclusive(v___x_348_);
if (v_isSharedCheck_378_ == 0)
{
v___x_352_ = v___x_348_;
v_isShared_353_ = v_isSharedCheck_378_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_a_350_);
lean_inc(v_a_349_);
lean_dec(v___x_348_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_378_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v_fst_354_; lean_object* v_snd_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_377_; 
v_fst_354_ = lean_ctor_get(v_a_349_, 0);
v_snd_355_ = lean_ctor_get(v_a_349_, 1);
v_isSharedCheck_377_ = !lean_is_exclusive(v_a_349_);
if (v_isSharedCheck_377_ == 0)
{
v___x_357_ = v_a_349_;
v_isShared_358_ = v_isSharedCheck_377_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_snd_355_);
lean_inc(v_fst_354_);
lean_dec(v_a_349_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_377_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
size_t v___x_359_; size_t v___x_360_; uint8_t v___x_361_; 
v___x_359_ = lean_ptr_addr(v_binderType_338_);
v___x_360_ = lean_ptr_addr(v_fst_344_);
v___x_361_ = lean_usize_dec_eq(v___x_359_, v___x_360_);
if (v___x_361_ == 0)
{
lean_object* v___x_12320__overap_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
lean_inc(v_binderName_337_);
lean_del_object(v___x_357_);
lean_del_object(v___x_352_);
lean_dec_ref_known(v_e_281_, 3);
v___x_12320__overap_362_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v___x_298_, v___x_289_, v_binderName_337_, v_binderInfo_340_, v_fst_344_, v_fst_354_);
v___x_363_ = lean_box(v_a_285_);
lean_inc_ref(v_a_286_);
v___x_364_ = lean_apply_4(v___x_12320__overap_362_, v_snd_355_, v___x_363_, v_a_286_, v_a_350_);
return v___x_364_;
}
else
{
size_t v___x_365_; size_t v___x_366_; uint8_t v___x_367_; 
v___x_365_ = lean_ptr_addr(v_body_339_);
v___x_366_ = lean_ptr_addr(v_fst_354_);
v___x_367_ = lean_usize_dec_eq(v___x_365_, v___x_366_);
if (v___x_367_ == 0)
{
lean_object* v___x_12325__overap_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
lean_inc(v_binderName_337_);
lean_del_object(v___x_357_);
lean_del_object(v___x_352_);
lean_dec_ref_known(v_e_281_, 3);
v___x_12325__overap_368_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v___x_298_, v___x_289_, v_binderName_337_, v_binderInfo_340_, v_fst_344_, v_fst_354_);
v___x_369_ = lean_box(v_a_285_);
lean_inc_ref(v_a_286_);
v___x_370_ = lean_apply_4(v___x_12325__overap_368_, v_snd_355_, v___x_369_, v_a_286_, v_a_350_);
return v___x_370_;
}
else
{
lean_object* v___x_372_; 
lean_dec(v_fst_354_);
lean_dec(v_fst_344_);
lean_dec_ref_known(v___x_298_, 3);
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 0, v_e_281_);
v___x_372_ = v___x_357_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_e_281_);
lean_ctor_set(v_reuseFailAlloc_376_, 1, v_snd_355_);
v___x_372_ = v_reuseFailAlloc_376_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
lean_object* v___x_374_; 
if (v_isShared_353_ == 0)
{
lean_ctor_set(v___x_352_, 0, v___x_372_);
v___x_374_ = v___x_352_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v___x_372_);
lean_ctor_set(v_reuseFailAlloc_375_, 1, v_a_350_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_344_);
lean_dec_ref_known(v_e_281_, 3);
lean_dec_ref_known(v___x_298_, 3);
return v___x_348_;
}
}
else
{
lean_dec_ref_known(v_e_281_, 3);
lean_dec_ref_known(v___x_298_, 3);
lean_dec_ref(v_fn_283_);
lean_dec(v_offset_282_);
return v___x_341_;
}
}
case 7:
{
lean_object* v_binderName_379_; lean_object* v_binderType_380_; lean_object* v_body_381_; uint8_t v_binderInfo_382_; lean_object* v___x_383_; 
v_binderName_379_ = lean_ctor_get(v_e_281_, 0);
v_binderType_380_ = lean_ctor_get(v_e_281_, 1);
v_body_381_ = lean_ctor_get(v_e_281_, 2);
v_binderInfo_382_ = lean_ctor_get_uint8(v_e_281_, sizeof(void*)*3 + 8);
lean_inc_ref(v_fn_283_);
lean_inc(v_offset_282_);
lean_inc_ref(v_binderType_380_);
v___x_383_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_binderType_380_, v_offset_282_, v_fn_283_, v_a_284_, v_a_285_, v_a_286_, v_a_287_);
if (lean_obj_tag(v___x_383_) == 0)
{
lean_object* v_a_384_; lean_object* v_a_385_; lean_object* v_fst_386_; lean_object* v_snd_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v_a_384_ = lean_ctor_get(v___x_383_, 0);
lean_inc(v_a_384_);
v_a_385_ = lean_ctor_get(v___x_383_, 1);
lean_inc(v_a_385_);
lean_dec_ref_known(v___x_383_, 2);
v_fst_386_ = lean_ctor_get(v_a_384_, 0);
lean_inc(v_fst_386_);
v_snd_387_ = lean_ctor_get(v_a_384_, 1);
lean_inc(v_snd_387_);
lean_dec(v_a_384_);
v___x_388_ = lean_unsigned_to_nat(1u);
v___x_389_ = lean_nat_add(v_offset_282_, v___x_388_);
lean_dec(v_offset_282_);
lean_inc_ref(v_body_381_);
v___x_390_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_body_381_, v___x_389_, v_fn_283_, v_snd_387_, v_a_285_, v_a_286_, v_a_385_);
if (lean_obj_tag(v___x_390_) == 0)
{
lean_object* v_a_391_; lean_object* v_a_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_420_; 
v_a_391_ = lean_ctor_get(v___x_390_, 0);
v_a_392_ = lean_ctor_get(v___x_390_, 1);
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_420_ == 0)
{
v___x_394_ = v___x_390_;
v_isShared_395_ = v_isSharedCheck_420_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_a_392_);
lean_inc(v_a_391_);
lean_dec(v___x_390_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_420_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v_fst_396_; lean_object* v_snd_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_419_; 
v_fst_396_ = lean_ctor_get(v_a_391_, 0);
v_snd_397_ = lean_ctor_get(v_a_391_, 1);
v_isSharedCheck_419_ = !lean_is_exclusive(v_a_391_);
if (v_isSharedCheck_419_ == 0)
{
v___x_399_ = v_a_391_;
v_isShared_400_ = v_isSharedCheck_419_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_snd_397_);
lean_inc(v_fst_396_);
lean_dec(v_a_391_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_419_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
size_t v___x_401_; size_t v___x_402_; uint8_t v___x_403_; 
v___x_401_ = lean_ptr_addr(v_binderType_380_);
v___x_402_ = lean_ptr_addr(v_fst_386_);
v___x_403_ = lean_usize_dec_eq(v___x_401_, v___x_402_);
if (v___x_403_ == 0)
{
lean_object* v___x_12613__overap_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
lean_inc(v_binderName_379_);
lean_del_object(v___x_399_);
lean_del_object(v___x_394_);
lean_dec_ref_known(v_e_281_, 3);
v___x_12613__overap_404_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v___x_298_, v___x_289_, v_binderName_379_, v_binderInfo_382_, v_fst_386_, v_fst_396_);
v___x_405_ = lean_box(v_a_285_);
lean_inc_ref(v_a_286_);
v___x_406_ = lean_apply_4(v___x_12613__overap_404_, v_snd_397_, v___x_405_, v_a_286_, v_a_392_);
return v___x_406_;
}
else
{
size_t v___x_407_; size_t v___x_408_; uint8_t v___x_409_; 
v___x_407_ = lean_ptr_addr(v_body_381_);
v___x_408_ = lean_ptr_addr(v_fst_396_);
v___x_409_ = lean_usize_dec_eq(v___x_407_, v___x_408_);
if (v___x_409_ == 0)
{
lean_object* v___x_12618__overap_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
lean_inc(v_binderName_379_);
lean_del_object(v___x_399_);
lean_del_object(v___x_394_);
lean_dec_ref_known(v_e_281_, 3);
v___x_12618__overap_410_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v___x_298_, v___x_289_, v_binderName_379_, v_binderInfo_382_, v_fst_386_, v_fst_396_);
v___x_411_ = lean_box(v_a_285_);
lean_inc_ref(v_a_286_);
v___x_412_ = lean_apply_4(v___x_12618__overap_410_, v_snd_397_, v___x_411_, v_a_286_, v_a_392_);
return v___x_412_;
}
else
{
lean_object* v___x_414_; 
lean_dec(v_fst_396_);
lean_dec(v_fst_386_);
lean_dec_ref_known(v___x_298_, 3);
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 0, v_e_281_);
v___x_414_ = v___x_399_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_e_281_);
lean_ctor_set(v_reuseFailAlloc_418_, 1, v_snd_397_);
v___x_414_ = v_reuseFailAlloc_418_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
lean_object* v___x_416_; 
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 0, v___x_414_);
v___x_416_ = v___x_394_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v___x_414_);
lean_ctor_set(v_reuseFailAlloc_417_, 1, v_a_392_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_386_);
lean_dec_ref_known(v_e_281_, 3);
lean_dec_ref_known(v___x_298_, 3);
return v___x_390_;
}
}
else
{
lean_dec_ref_known(v_e_281_, 3);
lean_dec_ref_known(v___x_298_, 3);
lean_dec_ref(v_fn_283_);
lean_dec(v_offset_282_);
return v___x_383_;
}
}
case 8:
{
lean_object* v_declName_421_; lean_object* v_type_422_; lean_object* v_value_423_; lean_object* v_body_424_; uint8_t v_nondep_425_; lean_object* v___x_426_; 
v_declName_421_ = lean_ctor_get(v_e_281_, 0);
v_type_422_ = lean_ctor_get(v_e_281_, 1);
v_value_423_ = lean_ctor_get(v_e_281_, 2);
v_body_424_ = lean_ctor_get(v_e_281_, 3);
v_nondep_425_ = lean_ctor_get_uint8(v_e_281_, sizeof(void*)*4 + 8);
lean_inc_ref(v_fn_283_);
lean_inc(v_offset_282_);
lean_inc_ref(v_type_422_);
v___x_426_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_type_422_, v_offset_282_, v_fn_283_, v_a_284_, v_a_285_, v_a_286_, v_a_287_);
if (lean_obj_tag(v___x_426_) == 0)
{
lean_object* v_a_427_; lean_object* v_a_428_; lean_object* v_fst_429_; lean_object* v_snd_430_; lean_object* v___x_431_; 
v_a_427_ = lean_ctor_get(v___x_426_, 0);
lean_inc(v_a_427_);
v_a_428_ = lean_ctor_get(v___x_426_, 1);
lean_inc(v_a_428_);
lean_dec_ref_known(v___x_426_, 2);
v_fst_429_ = lean_ctor_get(v_a_427_, 0);
lean_inc(v_fst_429_);
v_snd_430_ = lean_ctor_get(v_a_427_, 1);
lean_inc(v_snd_430_);
lean_dec(v_a_427_);
lean_inc_ref(v_fn_283_);
lean_inc(v_offset_282_);
lean_inc_ref(v_value_423_);
v___x_431_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_value_423_, v_offset_282_, v_fn_283_, v_snd_430_, v_a_285_, v_a_286_, v_a_428_);
if (lean_obj_tag(v___x_431_) == 0)
{
lean_object* v_a_432_; lean_object* v_a_433_; lean_object* v_fst_434_; lean_object* v_snd_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v_a_432_ = lean_ctor_get(v___x_431_, 0);
lean_inc(v_a_432_);
v_a_433_ = lean_ctor_get(v___x_431_, 1);
lean_inc(v_a_433_);
lean_dec_ref_known(v___x_431_, 2);
v_fst_434_ = lean_ctor_get(v_a_432_, 0);
lean_inc(v_fst_434_);
v_snd_435_ = lean_ctor_get(v_a_432_, 1);
lean_inc(v_snd_435_);
lean_dec(v_a_432_);
v___x_436_ = lean_unsigned_to_nat(1u);
v___x_437_ = lean_nat_add(v_offset_282_, v___x_436_);
lean_dec(v_offset_282_);
lean_inc_ref(v_body_424_);
v___x_438_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_body_424_, v___x_437_, v_fn_283_, v_snd_435_, v_a_285_, v_a_286_, v_a_433_);
if (lean_obj_tag(v___x_438_) == 0)
{
lean_object* v_a_439_; lean_object* v_a_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_474_; 
v_a_439_ = lean_ctor_get(v___x_438_, 0);
v_a_440_ = lean_ctor_get(v___x_438_, 1);
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_474_ == 0)
{
v___x_442_ = v___x_438_;
v_isShared_443_ = v_isSharedCheck_474_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_a_440_);
lean_inc(v_a_439_);
lean_dec(v___x_438_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_474_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v_fst_444_; lean_object* v_snd_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_473_; 
v_fst_444_ = lean_ctor_get(v_a_439_, 0);
v_snd_445_ = lean_ctor_get(v_a_439_, 1);
v_isSharedCheck_473_ = !lean_is_exclusive(v_a_439_);
if (v_isSharedCheck_473_ == 0)
{
v___x_447_ = v_a_439_;
v_isShared_448_ = v_isSharedCheck_473_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_snd_445_);
lean_inc(v_fst_444_);
lean_dec(v_a_439_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_473_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
size_t v___x_449_; size_t v___x_450_; uint8_t v___x_451_; 
v___x_449_ = lean_ptr_addr(v_type_422_);
v___x_450_ = lean_ptr_addr(v_fst_429_);
v___x_451_ = lean_usize_dec_eq(v___x_449_, v___x_450_);
if (v___x_451_ == 0)
{
lean_object* v___x_12951__overap_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
lean_inc(v_declName_421_);
lean_del_object(v___x_447_);
lean_del_object(v___x_442_);
lean_dec_ref_known(v_e_281_, 4);
v___x_12951__overap_452_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v___x_298_, v___x_289_, v_declName_421_, v_fst_429_, v_fst_434_, v_fst_444_, v_nondep_425_);
v___x_453_ = lean_box(v_a_285_);
lean_inc_ref(v_a_286_);
v___x_454_ = lean_apply_4(v___x_12951__overap_452_, v_snd_445_, v___x_453_, v_a_286_, v_a_440_);
return v___x_454_;
}
else
{
size_t v___x_455_; size_t v___x_456_; uint8_t v___x_457_; 
v___x_455_ = lean_ptr_addr(v_value_423_);
v___x_456_ = lean_ptr_addr(v_fst_434_);
v___x_457_ = lean_usize_dec_eq(v___x_455_, v___x_456_);
if (v___x_457_ == 0)
{
lean_object* v___x_12956__overap_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
lean_inc(v_declName_421_);
lean_del_object(v___x_447_);
lean_del_object(v___x_442_);
lean_dec_ref_known(v_e_281_, 4);
v___x_12956__overap_458_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v___x_298_, v___x_289_, v_declName_421_, v_fst_429_, v_fst_434_, v_fst_444_, v_nondep_425_);
v___x_459_ = lean_box(v_a_285_);
lean_inc_ref(v_a_286_);
v___x_460_ = lean_apply_4(v___x_12956__overap_458_, v_snd_445_, v___x_459_, v_a_286_, v_a_440_);
return v___x_460_;
}
else
{
size_t v___x_461_; size_t v___x_462_; uint8_t v___x_463_; 
v___x_461_ = lean_ptr_addr(v_body_424_);
v___x_462_ = lean_ptr_addr(v_fst_444_);
v___x_463_ = lean_usize_dec_eq(v___x_461_, v___x_462_);
if (v___x_463_ == 0)
{
lean_object* v___x_12961__overap_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
lean_inc(v_declName_421_);
lean_del_object(v___x_447_);
lean_del_object(v___x_442_);
lean_dec_ref_known(v_e_281_, 4);
v___x_12961__overap_464_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v___x_298_, v___x_289_, v_declName_421_, v_fst_429_, v_fst_434_, v_fst_444_, v_nondep_425_);
v___x_465_ = lean_box(v_a_285_);
lean_inc_ref(v_a_286_);
v___x_466_ = lean_apply_4(v___x_12961__overap_464_, v_snd_445_, v___x_465_, v_a_286_, v_a_440_);
return v___x_466_;
}
else
{
lean_object* v___x_468_; 
lean_dec(v_fst_444_);
lean_dec(v_fst_434_);
lean_dec(v_fst_429_);
lean_dec_ref_known(v___x_298_, 3);
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 0, v_e_281_);
v___x_468_ = v___x_447_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v_e_281_);
lean_ctor_set(v_reuseFailAlloc_472_, 1, v_snd_445_);
v___x_468_ = v_reuseFailAlloc_472_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
lean_object* v___x_470_; 
if (v_isShared_443_ == 0)
{
lean_ctor_set(v___x_442_, 0, v___x_468_);
v___x_470_ = v___x_442_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v___x_468_);
lean_ctor_set(v_reuseFailAlloc_471_, 1, v_a_440_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
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
lean_dec(v_fst_434_);
lean_dec(v_fst_429_);
lean_dec_ref_known(v_e_281_, 4);
lean_dec_ref_known(v___x_298_, 3);
return v___x_438_;
}
}
else
{
lean_dec(v_fst_429_);
lean_dec_ref_known(v_e_281_, 4);
lean_dec_ref_known(v___x_298_, 3);
lean_dec_ref(v_fn_283_);
lean_dec(v_offset_282_);
return v___x_431_;
}
}
else
{
lean_dec_ref_known(v_e_281_, 4);
lean_dec_ref_known(v___x_298_, 3);
lean_dec_ref(v_fn_283_);
lean_dec(v_offset_282_);
return v___x_426_;
}
}
case 10:
{
lean_object* v_data_475_; lean_object* v_expr_476_; lean_object* v___x_477_; 
v_data_475_ = lean_ctor_get(v_e_281_, 0);
v_expr_476_ = lean_ctor_get(v_e_281_, 1);
lean_inc_ref(v_expr_476_);
v___x_477_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_expr_476_, v_offset_282_, v_fn_283_, v_a_284_, v_a_285_, v_a_286_, v_a_287_);
if (lean_obj_tag(v___x_477_) == 0)
{
lean_object* v_a_478_; lean_object* v_a_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_501_; 
v_a_478_ = lean_ctor_get(v___x_477_, 0);
v_a_479_ = lean_ctor_get(v___x_477_, 1);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_477_);
if (v_isSharedCheck_501_ == 0)
{
v___x_481_ = v___x_477_;
v_isShared_482_ = v_isSharedCheck_501_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_a_479_);
lean_inc(v_a_478_);
lean_dec(v___x_477_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_501_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v_fst_483_; lean_object* v_snd_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_500_; 
v_fst_483_ = lean_ctor_get(v_a_478_, 0);
v_snd_484_ = lean_ctor_get(v_a_478_, 1);
v_isSharedCheck_500_ = !lean_is_exclusive(v_a_478_);
if (v_isSharedCheck_500_ == 0)
{
v___x_486_ = v_a_478_;
v_isShared_487_ = v_isSharedCheck_500_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_snd_484_);
lean_inc(v_fst_483_);
lean_dec(v_a_478_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_500_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
size_t v___x_488_; size_t v___x_489_; uint8_t v___x_490_; 
v___x_488_ = lean_ptr_addr(v_expr_476_);
v___x_489_ = lean_ptr_addr(v_fst_483_);
v___x_490_ = lean_usize_dec_eq(v___x_488_, v___x_489_);
if (v___x_490_ == 0)
{
lean_object* v___x_13248__overap_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
lean_inc(v_data_475_);
lean_del_object(v___x_486_);
lean_del_object(v___x_481_);
lean_dec_ref_known(v_e_281_, 2);
v___x_13248__overap_491_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg(v___x_298_, v___x_289_, v_data_475_, v_fst_483_);
v___x_492_ = lean_box(v_a_285_);
lean_inc_ref(v_a_286_);
v___x_493_ = lean_apply_4(v___x_13248__overap_491_, v_snd_484_, v___x_492_, v_a_286_, v_a_479_);
return v___x_493_;
}
else
{
lean_object* v___x_495_; 
lean_dec(v_fst_483_);
lean_dec_ref_known(v___x_298_, 3);
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 0, v_e_281_);
v___x_495_ = v___x_486_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_e_281_);
lean_ctor_set(v_reuseFailAlloc_499_, 1, v_snd_484_);
v___x_495_ = v_reuseFailAlloc_499_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
lean_object* v___x_497_; 
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 0, v___x_495_);
v___x_497_ = v___x_481_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v___x_495_);
lean_ctor_set(v_reuseFailAlloc_498_, 1, v_a_479_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_281_, 2);
lean_dec_ref_known(v___x_298_, 3);
return v___x_477_;
}
}
case 11:
{
lean_object* v_typeName_502_; lean_object* v_idx_503_; lean_object* v_struct_504_; lean_object* v___x_505_; 
v_typeName_502_ = lean_ctor_get(v_e_281_, 0);
v_idx_503_ = lean_ctor_get(v_e_281_, 1);
v_struct_504_ = lean_ctor_get(v_e_281_, 2);
lean_inc_ref(v_struct_504_);
v___x_505_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_struct_504_, v_offset_282_, v_fn_283_, v_a_284_, v_a_285_, v_a_286_, v_a_287_);
if (lean_obj_tag(v___x_505_) == 0)
{
lean_object* v_a_506_; lean_object* v_a_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_529_; 
v_a_506_ = lean_ctor_get(v___x_505_, 0);
v_a_507_ = lean_ctor_get(v___x_505_, 1);
v_isSharedCheck_529_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_529_ == 0)
{
v___x_509_ = v___x_505_;
v_isShared_510_ = v_isSharedCheck_529_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_a_507_);
lean_inc(v_a_506_);
lean_dec(v___x_505_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_529_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v_fst_511_; lean_object* v_snd_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_528_; 
v_fst_511_ = lean_ctor_get(v_a_506_, 0);
v_snd_512_ = lean_ctor_get(v_a_506_, 1);
v_isSharedCheck_528_ = !lean_is_exclusive(v_a_506_);
if (v_isSharedCheck_528_ == 0)
{
v___x_514_ = v_a_506_;
v_isShared_515_ = v_isSharedCheck_528_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_snd_512_);
lean_inc(v_fst_511_);
lean_dec(v_a_506_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_528_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
size_t v___x_516_; size_t v___x_517_; uint8_t v___x_518_; 
v___x_516_ = lean_ptr_addr(v_struct_504_);
v___x_517_ = lean_ptr_addr(v_fst_511_);
v___x_518_ = lean_usize_dec_eq(v___x_516_, v___x_517_);
if (v___x_518_ == 0)
{
lean_object* v___x_13435__overap_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
lean_inc(v_idx_503_);
lean_inc(v_typeName_502_);
lean_del_object(v___x_514_);
lean_del_object(v___x_509_);
lean_dec_ref_known(v_e_281_, 3);
v___x_13435__overap_519_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg(v___x_298_, v___x_289_, v_typeName_502_, v_idx_503_, v_fst_511_);
v___x_520_ = lean_box(v_a_285_);
lean_inc_ref(v_a_286_);
v___x_521_ = lean_apply_4(v___x_13435__overap_519_, v_snd_512_, v___x_520_, v_a_286_, v_a_507_);
return v___x_521_;
}
else
{
lean_object* v___x_523_; 
lean_dec(v_fst_511_);
lean_dec_ref_known(v___x_298_, 3);
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 0, v_e_281_);
v___x_523_ = v___x_514_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v_e_281_);
lean_ctor_set(v_reuseFailAlloc_527_, 1, v_snd_512_);
v___x_523_ = v_reuseFailAlloc_527_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
lean_object* v___x_525_; 
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 0, v___x_523_);
v___x_525_ = v___x_509_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v___x_523_);
lean_ctor_set(v_reuseFailAlloc_526_, 1, v_a_507_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_281_, 3);
lean_dec_ref_known(v___x_298_, 3);
return v___x_505_;
}
}
default: 
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_11862__overap_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
lean_dec_ref_known(v___x_298_, 3);
lean_dec_ref(v_fn_283_);
lean_dec(v_offset_282_);
lean_dec_ref(v_e_281_);
v___x_530_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__23, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__23_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__23);
v___x_531_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__27, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__27_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__27);
v___x_11862__overap_532_ = l_panic___redArg(v___x_530_, v___x_531_);
v___x_533_ = lean_box(v_a_285_);
lean_inc_ref(v_a_286_);
v___x_534_ = lean_apply_4(v___x_11862__overap_532_, v_a_284_, v___x_533_, v_a_286_, v_a_287_);
return v___x_534_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(lean_object* v_e_535_, lean_object* v_offset_536_, lean_object* v_f_537_, lean_object* v_a_538_, uint8_t v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_){
_start:
{
lean_object* v___f_542_; lean_object* v_key_543_; lean_object* v___f_544_; lean_object* v___x_545_; 
v___f_542_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__3));
lean_inc(v_offset_536_);
lean_inc_ref(v_e_535_);
v_key_543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_543_, 0, v_e_535_);
lean_ctor_set(v_key_543_, 1, v_offset_536_);
v___f_544_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__5, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__5_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__5);
lean_inc_ref(v_key_543_);
v___x_545_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_544_, v___f_542_, v_a_538_, v_key_543_);
if (lean_obj_tag(v___x_545_) == 1)
{
lean_object* v_val_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
lean_dec_ref_known(v_key_543_, 2);
lean_dec_ref(v_f_537_);
lean_dec(v_offset_536_);
lean_dec_ref(v_e_535_);
v_val_546_ = lean_ctor_get(v___x_545_, 0);
lean_inc(v_val_546_);
lean_dec_ref_known(v___x_545_, 1);
v___x_547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_547_, 0, v_val_546_);
lean_ctor_set(v___x_547_, 1, v_a_538_);
v___x_548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
lean_ctor_set(v___x_548_, 1, v_a_541_);
return v___x_548_;
}
else
{
lean_object* v___x_549_; lean_object* v___x_550_; 
lean_dec(v___x_545_);
v___x_549_ = lean_box(v_a_539_);
lean_inc_ref(v_f_537_);
lean_inc_ref(v_a_540_);
lean_inc(v_offset_536_);
lean_inc_ref(v_e_535_);
v___x_550_ = lean_apply_5(v_f_537_, v_e_535_, v_offset_536_, v___x_549_, v_a_540_, v_a_541_);
if (lean_obj_tag(v___x_550_) == 0)
{
lean_object* v_a_551_; 
v_a_551_ = lean_ctor_get(v___x_550_, 0);
lean_inc(v_a_551_);
if (lean_obj_tag(v_a_551_) == 1)
{
lean_object* v_a_552_; lean_object* v_val_553_; lean_object* v___x_554_; 
lean_dec_ref(v_f_537_);
lean_dec(v_offset_536_);
lean_dec_ref(v_e_535_);
v_a_552_ = lean_ctor_get(v___x_550_, 1);
lean_inc(v_a_552_);
lean_dec_ref_known(v___x_550_, 2);
v_val_553_ = lean_ctor_get(v_a_551_, 0);
lean_inc(v_val_553_);
lean_dec_ref_known(v_a_551_, 1);
v___x_554_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(v_key_543_, v_val_553_, v_a_538_, v_a_552_);
return v___x_554_;
}
else
{
lean_dec(v_a_551_);
switch(lean_obj_tag(v_e_535_))
{
case 9:
{
lean_object* v_a_555_; lean_object* v___x_556_; 
lean_dec_ref(v_f_537_);
lean_dec(v_offset_536_);
v_a_555_ = lean_ctor_get(v___x_550_, 1);
lean_inc(v_a_555_);
lean_dec_ref_known(v___x_550_, 2);
v___x_556_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(v_key_543_, v_e_535_, v_a_538_, v_a_555_);
return v___x_556_;
}
case 2:
{
lean_object* v_a_557_; lean_object* v___x_558_; 
lean_dec_ref(v_f_537_);
lean_dec(v_offset_536_);
v_a_557_ = lean_ctor_get(v___x_550_, 1);
lean_inc(v_a_557_);
lean_dec_ref_known(v___x_550_, 2);
v___x_558_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(v_key_543_, v_e_535_, v_a_538_, v_a_557_);
return v___x_558_;
}
case 0:
{
lean_object* v_a_559_; lean_object* v___x_560_; 
lean_dec_ref(v_f_537_);
lean_dec(v_offset_536_);
v_a_559_ = lean_ctor_get(v___x_550_, 1);
lean_inc(v_a_559_);
lean_dec_ref_known(v___x_550_, 2);
v___x_560_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(v_key_543_, v_e_535_, v_a_538_, v_a_559_);
return v___x_560_;
}
case 1:
{
lean_object* v_a_561_; lean_object* v___x_562_; 
lean_dec_ref(v_f_537_);
lean_dec(v_offset_536_);
v_a_561_ = lean_ctor_get(v___x_550_, 1);
lean_inc(v_a_561_);
lean_dec_ref_known(v___x_550_, 2);
v___x_562_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(v_key_543_, v_e_535_, v_a_538_, v_a_561_);
return v___x_562_;
}
case 4:
{
lean_object* v_a_563_; lean_object* v___x_564_; 
lean_dec_ref(v_f_537_);
lean_dec(v_offset_536_);
v_a_563_ = lean_ctor_get(v___x_550_, 1);
lean_inc(v_a_563_);
lean_dec_ref_known(v___x_550_, 2);
v___x_564_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(v_key_543_, v_e_535_, v_a_538_, v_a_563_);
return v___x_564_;
}
case 3:
{
lean_object* v_a_565_; lean_object* v___x_566_; 
lean_dec_ref(v_f_537_);
lean_dec(v_offset_536_);
v_a_565_ = lean_ctor_get(v___x_550_, 1);
lean_inc(v_a_565_);
lean_dec_ref_known(v___x_550_, 2);
v___x_566_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(v_key_543_, v_e_535_, v_a_538_, v_a_565_);
return v___x_566_;
}
default: 
{
lean_object* v_a_567_; lean_object* v___x_568_; 
v_a_567_ = lean_ctor_get(v___x_550_, 1);
lean_inc(v_a_567_);
lean_dec_ref_known(v___x_550_, 2);
v___x_568_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit(v_e_535_, v_offset_536_, v_f_537_, v_a_538_, v_a_539_, v_a_540_, v_a_567_);
if (lean_obj_tag(v___x_568_) == 0)
{
lean_object* v_a_569_; lean_object* v_a_570_; lean_object* v_fst_571_; lean_object* v_snd_572_; lean_object* v___x_573_; 
v_a_569_ = lean_ctor_get(v___x_568_, 0);
lean_inc(v_a_569_);
v_a_570_ = lean_ctor_get(v___x_568_, 1);
lean_inc(v_a_570_);
lean_dec_ref_known(v___x_568_, 2);
v_fst_571_ = lean_ctor_get(v_a_569_, 0);
lean_inc(v_fst_571_);
v_snd_572_ = lean_ctor_get(v_a_569_, 1);
lean_inc(v_snd_572_);
lean_dec(v_a_569_);
v___x_573_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(v_key_543_, v_fst_571_, v_snd_572_, v_a_570_);
return v___x_573_;
}
else
{
lean_dec_ref_known(v_key_543_, 2);
return v___x_568_;
}
}
}
}
}
else
{
lean_object* v_a_574_; lean_object* v_a_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_582_; 
lean_dec_ref_known(v_key_543_, 2);
lean_dec_ref(v_a_538_);
lean_dec_ref(v_f_537_);
lean_dec(v_offset_536_);
lean_dec_ref(v_e_535_);
v_a_574_ = lean_ctor_get(v___x_550_, 0);
v_a_575_ = lean_ctor_get(v___x_550_, 1);
v_isSharedCheck_582_ = !lean_is_exclusive(v___x_550_);
if (v_isSharedCheck_582_ == 0)
{
v___x_577_ = v___x_550_;
v_isShared_578_ = v_isSharedCheck_582_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_a_575_);
lean_inc(v_a_574_);
lean_dec(v___x_550_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_582_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___x_580_; 
if (v_isShared_578_ == 0)
{
v___x_580_ = v___x_577_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v_a_574_);
lean_ctor_set(v_reuseFailAlloc_581_, 1, v_a_575_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
return v___x_580_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___boxed(lean_object* v_e_583_, lean_object* v_offset_584_, lean_object* v_f_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_){
_start:
{
uint8_t v_a_boxed_590_; lean_object* v_res_591_; 
v_a_boxed_590_ = lean_unbox(v_a_587_);
v_res_591_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_e_583_, v_offset_584_, v_f_585_, v_a_586_, v_a_boxed_590_, v_a_588_, v_a_589_);
lean_dec_ref(v_a_588_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___boxed(lean_object* v_e_592_, lean_object* v_offset_593_, lean_object* v_fn_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_){
_start:
{
uint8_t v_a_boxed_599_; lean_object* v_res_600_; 
v_a_boxed_599_ = lean_unbox(v_a_596_);
v_res_600_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit(v_e_592_, v_offset_593_, v_fn_594_, v_a_595_, v_a_boxed_599_, v_a_597_, v_a_598_);
lean_dec_ref(v_a_597_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild_match__4_splitter___redArg(lean_object* v_____do__lift_601_, lean_object* v_h__1_602_, lean_object* v_h__2_603_){
_start:
{
if (lean_obj_tag(v_____do__lift_601_) == 1)
{
lean_object* v_val_604_; lean_object* v___x_605_; 
lean_dec(v_h__2_603_);
v_val_604_ = lean_ctor_get(v_____do__lift_601_, 0);
lean_inc(v_val_604_);
lean_dec_ref_known(v_____do__lift_601_, 1);
v___x_605_ = lean_apply_1(v_h__1_602_, v_val_604_);
return v___x_605_;
}
else
{
lean_object* v___x_606_; 
lean_dec(v_h__1_602_);
v___x_606_ = lean_apply_2(v_h__2_603_, v_____do__lift_601_, lean_box(0));
return v___x_606_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild_match__4_splitter(lean_object* v_motive_607_, lean_object* v_____do__lift_608_, lean_object* v_h__1_609_, lean_object* v_h__2_610_){
_start:
{
if (lean_obj_tag(v_____do__lift_608_) == 1)
{
lean_object* v_val_611_; lean_object* v___x_612_; 
lean_dec(v_h__2_610_);
v_val_611_ = lean_ctor_get(v_____do__lift_608_, 0);
lean_inc(v_val_611_);
lean_dec_ref_known(v_____do__lift_608_, 1);
v___x_612_ = lean_apply_1(v_h__1_609_, v_val_611_);
return v___x_612_;
}
else
{
lean_object* v___x_613_; 
lean_dec(v_h__1_609_);
v___x_613_ = lean_apply_2(v_h__2_610_, v_____do__lift_608_, lean_box(0));
return v___x_613_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild_match__1_splitter___redArg(lean_object* v_e_614_, lean_object* v_h__1_615_, lean_object* v_h__2_616_, lean_object* v_h__3_617_, lean_object* v_h__4_618_, lean_object* v_h__5_619_, lean_object* v_h__6_620_, lean_object* v_h__7_621_){
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
lean_dec_ref_known(v_e_614_, 1);
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
lean_dec_ref_known(v_e_614_, 1);
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
lean_dec_ref_known(v_e_614_, 1);
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
lean_dec_ref_known(v_e_614_, 1);
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
lean_dec_ref_known(v_e_614_, 2);
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
lean_dec_ref_known(v_e_614_, 1);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild_match__1_splitter(lean_object* v_motive_636_, lean_object* v_e_637_, lean_object* v_h__1_638_, lean_object* v_h__2_639_, lean_object* v_h__3_640_, lean_object* v_h__4_641_, lean_object* v_h__5_642_, lean_object* v_h__6_643_, lean_object* v_h__7_644_){
_start:
{
switch(lean_obj_tag(v_e_637_))
{
case 9:
{
lean_object* v_a_645_; lean_object* v___x_646_; 
lean_dec(v_h__7_644_);
lean_dec(v_h__6_643_);
lean_dec(v_h__5_642_);
lean_dec(v_h__4_641_);
lean_dec(v_h__3_640_);
lean_dec(v_h__2_639_);
v_a_645_ = lean_ctor_get(v_e_637_, 0);
lean_inc_ref(v_a_645_);
lean_dec_ref_known(v_e_637_, 1);
v___x_646_ = lean_apply_1(v_h__1_638_, v_a_645_);
return v___x_646_;
}
case 2:
{
lean_object* v_mvarId_647_; lean_object* v___x_648_; 
lean_dec(v_h__7_644_);
lean_dec(v_h__6_643_);
lean_dec(v_h__5_642_);
lean_dec(v_h__4_641_);
lean_dec(v_h__3_640_);
lean_dec(v_h__1_638_);
v_mvarId_647_ = lean_ctor_get(v_e_637_, 0);
lean_inc(v_mvarId_647_);
lean_dec_ref_known(v_e_637_, 1);
v___x_648_ = lean_apply_1(v_h__2_639_, v_mvarId_647_);
return v___x_648_;
}
case 0:
{
lean_object* v_deBruijnIndex_649_; lean_object* v___x_650_; 
lean_dec(v_h__7_644_);
lean_dec(v_h__6_643_);
lean_dec(v_h__5_642_);
lean_dec(v_h__4_641_);
lean_dec(v_h__2_639_);
lean_dec(v_h__1_638_);
v_deBruijnIndex_649_ = lean_ctor_get(v_e_637_, 0);
lean_inc(v_deBruijnIndex_649_);
lean_dec_ref_known(v_e_637_, 1);
v___x_650_ = lean_apply_1(v_h__3_640_, v_deBruijnIndex_649_);
return v___x_650_;
}
case 1:
{
lean_object* v_fvarId_651_; lean_object* v___x_652_; 
lean_dec(v_h__7_644_);
lean_dec(v_h__6_643_);
lean_dec(v_h__5_642_);
lean_dec(v_h__3_640_);
lean_dec(v_h__2_639_);
lean_dec(v_h__1_638_);
v_fvarId_651_ = lean_ctor_get(v_e_637_, 0);
lean_inc(v_fvarId_651_);
lean_dec_ref_known(v_e_637_, 1);
v___x_652_ = lean_apply_1(v_h__4_641_, v_fvarId_651_);
return v___x_652_;
}
case 4:
{
lean_object* v_declName_653_; lean_object* v_us_654_; lean_object* v___x_655_; 
lean_dec(v_h__7_644_);
lean_dec(v_h__6_643_);
lean_dec(v_h__4_641_);
lean_dec(v_h__3_640_);
lean_dec(v_h__2_639_);
lean_dec(v_h__1_638_);
v_declName_653_ = lean_ctor_get(v_e_637_, 0);
lean_inc(v_declName_653_);
v_us_654_ = lean_ctor_get(v_e_637_, 1);
lean_inc(v_us_654_);
lean_dec_ref_known(v_e_637_, 2);
v___x_655_ = lean_apply_2(v_h__5_642_, v_declName_653_, v_us_654_);
return v___x_655_;
}
case 3:
{
lean_object* v_u_656_; lean_object* v___x_657_; 
lean_dec(v_h__7_644_);
lean_dec(v_h__5_642_);
lean_dec(v_h__4_641_);
lean_dec(v_h__3_640_);
lean_dec(v_h__2_639_);
lean_dec(v_h__1_638_);
v_u_656_ = lean_ctor_get(v_e_637_, 0);
lean_inc(v_u_656_);
lean_dec_ref_known(v_e_637_, 1);
v___x_657_ = lean_apply_1(v_h__6_643_, v_u_656_);
return v___x_657_;
}
default: 
{
lean_object* v___x_658_; 
lean_dec(v_h__6_643_);
lean_dec(v_h__5_642_);
lean_dec(v_h__4_641_);
lean_dec(v_h__3_640_);
lean_dec(v_h__2_639_);
lean_dec(v_h__1_638_);
v___x_658_ = lean_apply_7(v_h__7_644_, v_e_637_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_658_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit_match__1_splitter___redArg(lean_object* v_e_659_, lean_object* v_h__1_660_, lean_object* v_h__2_661_, lean_object* v_h__3_662_, lean_object* v_h__4_663_, lean_object* v_h__5_664_, lean_object* v_h__6_665_, lean_object* v_h__7_666_, lean_object* v_h__8_667_, lean_object* v_h__9_668_, lean_object* v_h__10_669_, lean_object* v_h__11_670_, lean_object* v_h__12_671_){
_start:
{
switch(lean_obj_tag(v_e_659_))
{
case 0:
{
lean_object* v_deBruijnIndex_672_; lean_object* v___x_673_; 
lean_dec(v_h__12_671_);
lean_dec(v_h__11_670_);
lean_dec(v_h__10_669_);
lean_dec(v_h__9_668_);
lean_dec(v_h__8_667_);
lean_dec(v_h__7_666_);
lean_dec(v_h__6_665_);
lean_dec(v_h__5_664_);
lean_dec(v_h__4_663_);
lean_dec(v_h__2_661_);
lean_dec(v_h__1_660_);
v_deBruijnIndex_672_ = lean_ctor_get(v_e_659_, 0);
lean_inc(v_deBruijnIndex_672_);
lean_dec_ref_known(v_e_659_, 1);
v___x_673_ = lean_apply_1(v_h__3_662_, v_deBruijnIndex_672_);
return v___x_673_;
}
case 1:
{
lean_object* v_fvarId_674_; lean_object* v___x_675_; 
lean_dec(v_h__12_671_);
lean_dec(v_h__11_670_);
lean_dec(v_h__10_669_);
lean_dec(v_h__9_668_);
lean_dec(v_h__8_667_);
lean_dec(v_h__7_666_);
lean_dec(v_h__6_665_);
lean_dec(v_h__5_664_);
lean_dec(v_h__3_662_);
lean_dec(v_h__2_661_);
lean_dec(v_h__1_660_);
v_fvarId_674_ = lean_ctor_get(v_e_659_, 0);
lean_inc(v_fvarId_674_);
lean_dec_ref_known(v_e_659_, 1);
v___x_675_ = lean_apply_1(v_h__4_663_, v_fvarId_674_);
return v___x_675_;
}
case 2:
{
lean_object* v_mvarId_676_; lean_object* v___x_677_; 
lean_dec(v_h__12_671_);
lean_dec(v_h__11_670_);
lean_dec(v_h__10_669_);
lean_dec(v_h__9_668_);
lean_dec(v_h__8_667_);
lean_dec(v_h__7_666_);
lean_dec(v_h__6_665_);
lean_dec(v_h__5_664_);
lean_dec(v_h__4_663_);
lean_dec(v_h__3_662_);
lean_dec(v_h__1_660_);
v_mvarId_676_ = lean_ctor_get(v_e_659_, 0);
lean_inc(v_mvarId_676_);
lean_dec_ref_known(v_e_659_, 1);
v___x_677_ = lean_apply_1(v_h__2_661_, v_mvarId_676_);
return v___x_677_;
}
case 3:
{
lean_object* v_u_678_; lean_object* v___x_679_; 
lean_dec(v_h__12_671_);
lean_dec(v_h__11_670_);
lean_dec(v_h__10_669_);
lean_dec(v_h__9_668_);
lean_dec(v_h__8_667_);
lean_dec(v_h__7_666_);
lean_dec(v_h__5_664_);
lean_dec(v_h__4_663_);
lean_dec(v_h__3_662_);
lean_dec(v_h__2_661_);
lean_dec(v_h__1_660_);
v_u_678_ = lean_ctor_get(v_e_659_, 0);
lean_inc(v_u_678_);
lean_dec_ref_known(v_e_659_, 1);
v___x_679_ = lean_apply_1(v_h__6_665_, v_u_678_);
return v___x_679_;
}
case 4:
{
lean_object* v_declName_680_; lean_object* v_us_681_; lean_object* v___x_682_; 
lean_dec(v_h__12_671_);
lean_dec(v_h__11_670_);
lean_dec(v_h__10_669_);
lean_dec(v_h__9_668_);
lean_dec(v_h__8_667_);
lean_dec(v_h__7_666_);
lean_dec(v_h__6_665_);
lean_dec(v_h__4_663_);
lean_dec(v_h__3_662_);
lean_dec(v_h__2_661_);
lean_dec(v_h__1_660_);
v_declName_680_ = lean_ctor_get(v_e_659_, 0);
lean_inc(v_declName_680_);
v_us_681_ = lean_ctor_get(v_e_659_, 1);
lean_inc(v_us_681_);
lean_dec_ref_known(v_e_659_, 2);
v___x_682_ = lean_apply_2(v_h__5_664_, v_declName_680_, v_us_681_);
return v___x_682_;
}
case 5:
{
lean_object* v_fn_683_; lean_object* v_arg_684_; lean_object* v___x_685_; 
lean_dec(v_h__12_671_);
lean_dec(v_h__11_670_);
lean_dec(v_h__10_669_);
lean_dec(v_h__9_668_);
lean_dec(v_h__8_667_);
lean_dec(v_h__6_665_);
lean_dec(v_h__5_664_);
lean_dec(v_h__4_663_);
lean_dec(v_h__3_662_);
lean_dec(v_h__2_661_);
lean_dec(v_h__1_660_);
v_fn_683_ = lean_ctor_get(v_e_659_, 0);
lean_inc_ref(v_fn_683_);
v_arg_684_ = lean_ctor_get(v_e_659_, 1);
lean_inc_ref(v_arg_684_);
lean_dec_ref_known(v_e_659_, 2);
v___x_685_ = lean_apply_2(v_h__7_666_, v_fn_683_, v_arg_684_);
return v___x_685_;
}
case 6:
{
lean_object* v_binderName_686_; lean_object* v_binderType_687_; lean_object* v_body_688_; uint8_t v_binderInfo_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
lean_dec(v_h__12_671_);
lean_dec(v_h__10_669_);
lean_dec(v_h__9_668_);
lean_dec(v_h__8_667_);
lean_dec(v_h__7_666_);
lean_dec(v_h__6_665_);
lean_dec(v_h__5_664_);
lean_dec(v_h__4_663_);
lean_dec(v_h__3_662_);
lean_dec(v_h__2_661_);
lean_dec(v_h__1_660_);
v_binderName_686_ = lean_ctor_get(v_e_659_, 0);
lean_inc(v_binderName_686_);
v_binderType_687_ = lean_ctor_get(v_e_659_, 1);
lean_inc_ref(v_binderType_687_);
v_body_688_ = lean_ctor_get(v_e_659_, 2);
lean_inc_ref(v_body_688_);
v_binderInfo_689_ = lean_ctor_get_uint8(v_e_659_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_659_, 3);
v___x_690_ = lean_box(v_binderInfo_689_);
v___x_691_ = lean_apply_4(v_h__11_670_, v_binderName_686_, v_binderType_687_, v_body_688_, v___x_690_);
return v___x_691_;
}
case 7:
{
lean_object* v_binderName_692_; lean_object* v_binderType_693_; lean_object* v_body_694_; uint8_t v_binderInfo_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
lean_dec(v_h__12_671_);
lean_dec(v_h__11_670_);
lean_dec(v_h__9_668_);
lean_dec(v_h__8_667_);
lean_dec(v_h__7_666_);
lean_dec(v_h__6_665_);
lean_dec(v_h__5_664_);
lean_dec(v_h__4_663_);
lean_dec(v_h__3_662_);
lean_dec(v_h__2_661_);
lean_dec(v_h__1_660_);
v_binderName_692_ = lean_ctor_get(v_e_659_, 0);
lean_inc(v_binderName_692_);
v_binderType_693_ = lean_ctor_get(v_e_659_, 1);
lean_inc_ref(v_binderType_693_);
v_body_694_ = lean_ctor_get(v_e_659_, 2);
lean_inc_ref(v_body_694_);
v_binderInfo_695_ = lean_ctor_get_uint8(v_e_659_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_659_, 3);
v___x_696_ = lean_box(v_binderInfo_695_);
v___x_697_ = lean_apply_4(v_h__10_669_, v_binderName_692_, v_binderType_693_, v_body_694_, v___x_696_);
return v___x_697_;
}
case 8:
{
lean_object* v_declName_698_; lean_object* v_type_699_; lean_object* v_value_700_; lean_object* v_body_701_; uint8_t v_nondep_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
lean_dec(v_h__11_670_);
lean_dec(v_h__10_669_);
lean_dec(v_h__9_668_);
lean_dec(v_h__8_667_);
lean_dec(v_h__7_666_);
lean_dec(v_h__6_665_);
lean_dec(v_h__5_664_);
lean_dec(v_h__4_663_);
lean_dec(v_h__3_662_);
lean_dec(v_h__2_661_);
lean_dec(v_h__1_660_);
v_declName_698_ = lean_ctor_get(v_e_659_, 0);
lean_inc(v_declName_698_);
v_type_699_ = lean_ctor_get(v_e_659_, 1);
lean_inc_ref(v_type_699_);
v_value_700_ = lean_ctor_get(v_e_659_, 2);
lean_inc_ref(v_value_700_);
v_body_701_ = lean_ctor_get(v_e_659_, 3);
lean_inc_ref(v_body_701_);
v_nondep_702_ = lean_ctor_get_uint8(v_e_659_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_659_, 4);
v___x_703_ = lean_box(v_nondep_702_);
v___x_704_ = lean_apply_5(v_h__12_671_, v_declName_698_, v_type_699_, v_value_700_, v_body_701_, v___x_703_);
return v___x_704_;
}
case 9:
{
lean_object* v_a_705_; lean_object* v___x_706_; 
lean_dec(v_h__12_671_);
lean_dec(v_h__11_670_);
lean_dec(v_h__10_669_);
lean_dec(v_h__9_668_);
lean_dec(v_h__8_667_);
lean_dec(v_h__7_666_);
lean_dec(v_h__6_665_);
lean_dec(v_h__5_664_);
lean_dec(v_h__4_663_);
lean_dec(v_h__3_662_);
lean_dec(v_h__2_661_);
v_a_705_ = lean_ctor_get(v_e_659_, 0);
lean_inc_ref(v_a_705_);
lean_dec_ref_known(v_e_659_, 1);
v___x_706_ = lean_apply_1(v_h__1_660_, v_a_705_);
return v___x_706_;
}
case 10:
{
lean_object* v_data_707_; lean_object* v_expr_708_; lean_object* v___x_709_; 
lean_dec(v_h__12_671_);
lean_dec(v_h__11_670_);
lean_dec(v_h__10_669_);
lean_dec(v_h__9_668_);
lean_dec(v_h__7_666_);
lean_dec(v_h__6_665_);
lean_dec(v_h__5_664_);
lean_dec(v_h__4_663_);
lean_dec(v_h__3_662_);
lean_dec(v_h__2_661_);
lean_dec(v_h__1_660_);
v_data_707_ = lean_ctor_get(v_e_659_, 0);
lean_inc(v_data_707_);
v_expr_708_ = lean_ctor_get(v_e_659_, 1);
lean_inc_ref(v_expr_708_);
lean_dec_ref_known(v_e_659_, 2);
v___x_709_ = lean_apply_2(v_h__8_667_, v_data_707_, v_expr_708_);
return v___x_709_;
}
default: 
{
lean_object* v_typeName_710_; lean_object* v_idx_711_; lean_object* v_struct_712_; lean_object* v___x_713_; 
lean_dec(v_h__12_671_);
lean_dec(v_h__11_670_);
lean_dec(v_h__10_669_);
lean_dec(v_h__8_667_);
lean_dec(v_h__7_666_);
lean_dec(v_h__6_665_);
lean_dec(v_h__5_664_);
lean_dec(v_h__4_663_);
lean_dec(v_h__3_662_);
lean_dec(v_h__2_661_);
lean_dec(v_h__1_660_);
v_typeName_710_ = lean_ctor_get(v_e_659_, 0);
lean_inc(v_typeName_710_);
v_idx_711_ = lean_ctor_get(v_e_659_, 1);
lean_inc(v_idx_711_);
v_struct_712_ = lean_ctor_get(v_e_659_, 2);
lean_inc_ref(v_struct_712_);
lean_dec_ref_known(v_e_659_, 3);
v___x_713_ = lean_apply_3(v_h__9_668_, v_typeName_710_, v_idx_711_, v_struct_712_);
return v___x_713_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit_match__1_splitter(lean_object* v_motive_714_, lean_object* v_e_715_, lean_object* v_h__1_716_, lean_object* v_h__2_717_, lean_object* v_h__3_718_, lean_object* v_h__4_719_, lean_object* v_h__5_720_, lean_object* v_h__6_721_, lean_object* v_h__7_722_, lean_object* v_h__8_723_, lean_object* v_h__9_724_, lean_object* v_h__10_725_, lean_object* v_h__11_726_, lean_object* v_h__12_727_){
_start:
{
switch(lean_obj_tag(v_e_715_))
{
case 0:
{
lean_object* v_deBruijnIndex_728_; lean_object* v___x_729_; 
lean_dec(v_h__12_727_);
lean_dec(v_h__11_726_);
lean_dec(v_h__10_725_);
lean_dec(v_h__9_724_);
lean_dec(v_h__8_723_);
lean_dec(v_h__7_722_);
lean_dec(v_h__6_721_);
lean_dec(v_h__5_720_);
lean_dec(v_h__4_719_);
lean_dec(v_h__2_717_);
lean_dec(v_h__1_716_);
v_deBruijnIndex_728_ = lean_ctor_get(v_e_715_, 0);
lean_inc(v_deBruijnIndex_728_);
lean_dec_ref_known(v_e_715_, 1);
v___x_729_ = lean_apply_1(v_h__3_718_, v_deBruijnIndex_728_);
return v___x_729_;
}
case 1:
{
lean_object* v_fvarId_730_; lean_object* v___x_731_; 
lean_dec(v_h__12_727_);
lean_dec(v_h__11_726_);
lean_dec(v_h__10_725_);
lean_dec(v_h__9_724_);
lean_dec(v_h__8_723_);
lean_dec(v_h__7_722_);
lean_dec(v_h__6_721_);
lean_dec(v_h__5_720_);
lean_dec(v_h__3_718_);
lean_dec(v_h__2_717_);
lean_dec(v_h__1_716_);
v_fvarId_730_ = lean_ctor_get(v_e_715_, 0);
lean_inc(v_fvarId_730_);
lean_dec_ref_known(v_e_715_, 1);
v___x_731_ = lean_apply_1(v_h__4_719_, v_fvarId_730_);
return v___x_731_;
}
case 2:
{
lean_object* v_mvarId_732_; lean_object* v___x_733_; 
lean_dec(v_h__12_727_);
lean_dec(v_h__11_726_);
lean_dec(v_h__10_725_);
lean_dec(v_h__9_724_);
lean_dec(v_h__8_723_);
lean_dec(v_h__7_722_);
lean_dec(v_h__6_721_);
lean_dec(v_h__5_720_);
lean_dec(v_h__4_719_);
lean_dec(v_h__3_718_);
lean_dec(v_h__1_716_);
v_mvarId_732_ = lean_ctor_get(v_e_715_, 0);
lean_inc(v_mvarId_732_);
lean_dec_ref_known(v_e_715_, 1);
v___x_733_ = lean_apply_1(v_h__2_717_, v_mvarId_732_);
return v___x_733_;
}
case 3:
{
lean_object* v_u_734_; lean_object* v___x_735_; 
lean_dec(v_h__12_727_);
lean_dec(v_h__11_726_);
lean_dec(v_h__10_725_);
lean_dec(v_h__9_724_);
lean_dec(v_h__8_723_);
lean_dec(v_h__7_722_);
lean_dec(v_h__5_720_);
lean_dec(v_h__4_719_);
lean_dec(v_h__3_718_);
lean_dec(v_h__2_717_);
lean_dec(v_h__1_716_);
v_u_734_ = lean_ctor_get(v_e_715_, 0);
lean_inc(v_u_734_);
lean_dec_ref_known(v_e_715_, 1);
v___x_735_ = lean_apply_1(v_h__6_721_, v_u_734_);
return v___x_735_;
}
case 4:
{
lean_object* v_declName_736_; lean_object* v_us_737_; lean_object* v___x_738_; 
lean_dec(v_h__12_727_);
lean_dec(v_h__11_726_);
lean_dec(v_h__10_725_);
lean_dec(v_h__9_724_);
lean_dec(v_h__8_723_);
lean_dec(v_h__7_722_);
lean_dec(v_h__6_721_);
lean_dec(v_h__4_719_);
lean_dec(v_h__3_718_);
lean_dec(v_h__2_717_);
lean_dec(v_h__1_716_);
v_declName_736_ = lean_ctor_get(v_e_715_, 0);
lean_inc(v_declName_736_);
v_us_737_ = lean_ctor_get(v_e_715_, 1);
lean_inc(v_us_737_);
lean_dec_ref_known(v_e_715_, 2);
v___x_738_ = lean_apply_2(v_h__5_720_, v_declName_736_, v_us_737_);
return v___x_738_;
}
case 5:
{
lean_object* v_fn_739_; lean_object* v_arg_740_; lean_object* v___x_741_; 
lean_dec(v_h__12_727_);
lean_dec(v_h__11_726_);
lean_dec(v_h__10_725_);
lean_dec(v_h__9_724_);
lean_dec(v_h__8_723_);
lean_dec(v_h__6_721_);
lean_dec(v_h__5_720_);
lean_dec(v_h__4_719_);
lean_dec(v_h__3_718_);
lean_dec(v_h__2_717_);
lean_dec(v_h__1_716_);
v_fn_739_ = lean_ctor_get(v_e_715_, 0);
lean_inc_ref(v_fn_739_);
v_arg_740_ = lean_ctor_get(v_e_715_, 1);
lean_inc_ref(v_arg_740_);
lean_dec_ref_known(v_e_715_, 2);
v___x_741_ = lean_apply_2(v_h__7_722_, v_fn_739_, v_arg_740_);
return v___x_741_;
}
case 6:
{
lean_object* v_binderName_742_; lean_object* v_binderType_743_; lean_object* v_body_744_; uint8_t v_binderInfo_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
lean_dec(v_h__12_727_);
lean_dec(v_h__10_725_);
lean_dec(v_h__9_724_);
lean_dec(v_h__8_723_);
lean_dec(v_h__7_722_);
lean_dec(v_h__6_721_);
lean_dec(v_h__5_720_);
lean_dec(v_h__4_719_);
lean_dec(v_h__3_718_);
lean_dec(v_h__2_717_);
lean_dec(v_h__1_716_);
v_binderName_742_ = lean_ctor_get(v_e_715_, 0);
lean_inc(v_binderName_742_);
v_binderType_743_ = lean_ctor_get(v_e_715_, 1);
lean_inc_ref(v_binderType_743_);
v_body_744_ = lean_ctor_get(v_e_715_, 2);
lean_inc_ref(v_body_744_);
v_binderInfo_745_ = lean_ctor_get_uint8(v_e_715_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_715_, 3);
v___x_746_ = lean_box(v_binderInfo_745_);
v___x_747_ = lean_apply_4(v_h__11_726_, v_binderName_742_, v_binderType_743_, v_body_744_, v___x_746_);
return v___x_747_;
}
case 7:
{
lean_object* v_binderName_748_; lean_object* v_binderType_749_; lean_object* v_body_750_; uint8_t v_binderInfo_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
lean_dec(v_h__12_727_);
lean_dec(v_h__11_726_);
lean_dec(v_h__9_724_);
lean_dec(v_h__8_723_);
lean_dec(v_h__7_722_);
lean_dec(v_h__6_721_);
lean_dec(v_h__5_720_);
lean_dec(v_h__4_719_);
lean_dec(v_h__3_718_);
lean_dec(v_h__2_717_);
lean_dec(v_h__1_716_);
v_binderName_748_ = lean_ctor_get(v_e_715_, 0);
lean_inc(v_binderName_748_);
v_binderType_749_ = lean_ctor_get(v_e_715_, 1);
lean_inc_ref(v_binderType_749_);
v_body_750_ = lean_ctor_get(v_e_715_, 2);
lean_inc_ref(v_body_750_);
v_binderInfo_751_ = lean_ctor_get_uint8(v_e_715_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_715_, 3);
v___x_752_ = lean_box(v_binderInfo_751_);
v___x_753_ = lean_apply_4(v_h__10_725_, v_binderName_748_, v_binderType_749_, v_body_750_, v___x_752_);
return v___x_753_;
}
case 8:
{
lean_object* v_declName_754_; lean_object* v_type_755_; lean_object* v_value_756_; lean_object* v_body_757_; uint8_t v_nondep_758_; lean_object* v___x_759_; lean_object* v___x_760_; 
lean_dec(v_h__11_726_);
lean_dec(v_h__10_725_);
lean_dec(v_h__9_724_);
lean_dec(v_h__8_723_);
lean_dec(v_h__7_722_);
lean_dec(v_h__6_721_);
lean_dec(v_h__5_720_);
lean_dec(v_h__4_719_);
lean_dec(v_h__3_718_);
lean_dec(v_h__2_717_);
lean_dec(v_h__1_716_);
v_declName_754_ = lean_ctor_get(v_e_715_, 0);
lean_inc(v_declName_754_);
v_type_755_ = lean_ctor_get(v_e_715_, 1);
lean_inc_ref(v_type_755_);
v_value_756_ = lean_ctor_get(v_e_715_, 2);
lean_inc_ref(v_value_756_);
v_body_757_ = lean_ctor_get(v_e_715_, 3);
lean_inc_ref(v_body_757_);
v_nondep_758_ = lean_ctor_get_uint8(v_e_715_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_715_, 4);
v___x_759_ = lean_box(v_nondep_758_);
v___x_760_ = lean_apply_5(v_h__12_727_, v_declName_754_, v_type_755_, v_value_756_, v_body_757_, v___x_759_);
return v___x_760_;
}
case 9:
{
lean_object* v_a_761_; lean_object* v___x_762_; 
lean_dec(v_h__12_727_);
lean_dec(v_h__11_726_);
lean_dec(v_h__10_725_);
lean_dec(v_h__9_724_);
lean_dec(v_h__8_723_);
lean_dec(v_h__7_722_);
lean_dec(v_h__6_721_);
lean_dec(v_h__5_720_);
lean_dec(v_h__4_719_);
lean_dec(v_h__3_718_);
lean_dec(v_h__2_717_);
v_a_761_ = lean_ctor_get(v_e_715_, 0);
lean_inc_ref(v_a_761_);
lean_dec_ref_known(v_e_715_, 1);
v___x_762_ = lean_apply_1(v_h__1_716_, v_a_761_);
return v___x_762_;
}
case 10:
{
lean_object* v_data_763_; lean_object* v_expr_764_; lean_object* v___x_765_; 
lean_dec(v_h__12_727_);
lean_dec(v_h__11_726_);
lean_dec(v_h__10_725_);
lean_dec(v_h__9_724_);
lean_dec(v_h__7_722_);
lean_dec(v_h__6_721_);
lean_dec(v_h__5_720_);
lean_dec(v_h__4_719_);
lean_dec(v_h__3_718_);
lean_dec(v_h__2_717_);
lean_dec(v_h__1_716_);
v_data_763_ = lean_ctor_get(v_e_715_, 0);
lean_inc(v_data_763_);
v_expr_764_ = lean_ctor_get(v_e_715_, 1);
lean_inc_ref(v_expr_764_);
lean_dec_ref_known(v_e_715_, 2);
v___x_765_ = lean_apply_2(v_h__8_723_, v_data_763_, v_expr_764_);
return v___x_765_;
}
default: 
{
lean_object* v_typeName_766_; lean_object* v_idx_767_; lean_object* v_struct_768_; lean_object* v___x_769_; 
lean_dec(v_h__12_727_);
lean_dec(v_h__11_726_);
lean_dec(v_h__10_725_);
lean_dec(v_h__8_723_);
lean_dec(v_h__7_722_);
lean_dec(v_h__6_721_);
lean_dec(v_h__5_720_);
lean_dec(v_h__4_719_);
lean_dec(v_h__3_718_);
lean_dec(v_h__2_717_);
lean_dec(v_h__1_716_);
v_typeName_766_ = lean_ctor_get(v_e_715_, 0);
lean_inc(v_typeName_766_);
v_idx_767_ = lean_ctor_get(v_e_715_, 1);
lean_inc(v_idx_767_);
v_struct_768_ = lean_ctor_get(v_e_715_, 2);
lean_inc_ref(v_struct_768_);
lean_dec_ref_known(v_e_715_, 3);
v___x_769_ = lean_apply_3(v_h__9_724_, v_typeName_766_, v_idx_767_, v_struct_768_);
return v___x_769_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Sym_replaceS_x27___closed__0(void){
_start:
{
lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_770_ = lean_box(0);
v___x_771_ = lean_unsigned_to_nat(16u);
v___x_772_ = lean_mk_array(v___x_771_, v___x_770_);
return v___x_772_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_replaceS_x27___closed__1(void){
_start:
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_773_ = lean_obj_once(&l_Lean_Meta_Sym_replaceS_x27___closed__0, &l_Lean_Meta_Sym_replaceS_x27___closed__0_once, _init_l_Lean_Meta_Sym_replaceS_x27___closed__0);
v___x_774_ = lean_unsigned_to_nat(0u);
v___x_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_775_, 0, v___x_774_);
lean_ctor_set(v___x_775_, 1, v___x_773_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_replaceS_x27(lean_object* v_e_776_, lean_object* v_f_777_, uint8_t v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_){
_start:
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_781_ = lean_unsigned_to_nat(0u);
v___x_782_ = lean_box(v_a_778_);
lean_inc_ref(v_f_777_);
lean_inc_ref(v_a_779_);
lean_inc_ref(v_e_776_);
v___x_783_ = lean_apply_5(v_f_777_, v_e_776_, v___x_781_, v___x_782_, v_a_779_, v_a_780_);
if (lean_obj_tag(v___x_783_) == 0)
{
lean_object* v_a_784_; 
v_a_784_ = lean_ctor_get(v___x_783_, 0);
lean_inc(v_a_784_);
if (lean_obj_tag(v_a_784_) == 1)
{
lean_object* v_a_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_793_; 
lean_dec_ref(v_f_777_);
lean_dec_ref(v_e_776_);
v_a_785_ = lean_ctor_get(v___x_783_, 1);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_793_ == 0)
{
lean_object* v_unused_794_; 
v_unused_794_ = lean_ctor_get(v___x_783_, 0);
lean_dec(v_unused_794_);
v___x_787_ = v___x_783_;
v_isShared_788_ = v_isSharedCheck_793_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_a_785_);
lean_dec(v___x_783_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_793_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v_val_789_; lean_object* v___x_791_; 
v_val_789_ = lean_ctor_get(v_a_784_, 0);
lean_inc(v_val_789_);
lean_dec_ref_known(v_a_784_, 1);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 0, v_val_789_);
v___x_791_ = v___x_787_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_val_789_);
lean_ctor_set(v_reuseFailAlloc_792_, 1, v_a_785_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
else
{
lean_dec(v_a_784_);
switch(lean_obj_tag(v_e_776_))
{
case 9:
{
lean_object* v_a_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_802_; 
lean_dec_ref(v_f_777_);
v_a_795_ = lean_ctor_get(v___x_783_, 1);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_802_ == 0)
{
lean_object* v_unused_803_; 
v_unused_803_ = lean_ctor_get(v___x_783_, 0);
lean_dec(v_unused_803_);
v___x_797_ = v___x_783_;
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_dec(v___x_783_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_800_; 
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 0, v_e_776_);
v___x_800_ = v___x_797_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_e_776_);
lean_ctor_set(v_reuseFailAlloc_801_, 1, v_a_795_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
case 2:
{
lean_object* v_a_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_811_; 
lean_dec_ref(v_f_777_);
v_a_804_ = lean_ctor_get(v___x_783_, 1);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_811_ == 0)
{
lean_object* v_unused_812_; 
v_unused_812_ = lean_ctor_get(v___x_783_, 0);
lean_dec(v_unused_812_);
v___x_806_ = v___x_783_;
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_a_804_);
lean_dec(v___x_783_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_809_; 
if (v_isShared_807_ == 0)
{
lean_ctor_set(v___x_806_, 0, v_e_776_);
v___x_809_ = v___x_806_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_e_776_);
lean_ctor_set(v_reuseFailAlloc_810_, 1, v_a_804_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
}
case 0:
{
lean_object* v_a_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_820_; 
lean_dec_ref(v_f_777_);
v_a_813_ = lean_ctor_get(v___x_783_, 1);
v_isSharedCheck_820_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_820_ == 0)
{
lean_object* v_unused_821_; 
v_unused_821_ = lean_ctor_get(v___x_783_, 0);
lean_dec(v_unused_821_);
v___x_815_ = v___x_783_;
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_a_813_);
lean_dec(v___x_783_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_818_; 
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 0, v_e_776_);
v___x_818_ = v___x_815_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_e_776_);
lean_ctor_set(v_reuseFailAlloc_819_, 1, v_a_813_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
}
case 1:
{
lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_829_; 
lean_dec_ref(v_f_777_);
v_a_822_ = lean_ctor_get(v___x_783_, 1);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_829_ == 0)
{
lean_object* v_unused_830_; 
v_unused_830_ = lean_ctor_get(v___x_783_, 0);
lean_dec(v_unused_830_);
v___x_824_ = v___x_783_;
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v___x_783_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_827_; 
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 0, v_e_776_);
v___x_827_ = v___x_824_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_e_776_);
lean_ctor_set(v_reuseFailAlloc_828_, 1, v_a_822_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
}
case 4:
{
lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_838_; 
lean_dec_ref(v_f_777_);
v_a_831_ = lean_ctor_get(v___x_783_, 1);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_838_ == 0)
{
lean_object* v_unused_839_; 
v_unused_839_ = lean_ctor_get(v___x_783_, 0);
lean_dec(v_unused_839_);
v___x_833_ = v___x_783_;
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_dec(v___x_783_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_836_; 
if (v_isShared_834_ == 0)
{
lean_ctor_set(v___x_833_, 0, v_e_776_);
v___x_836_ = v___x_833_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_e_776_);
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
case 3:
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_847_; 
lean_dec_ref(v_f_777_);
v_a_840_ = lean_ctor_get(v___x_783_, 1);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_847_ == 0)
{
lean_object* v_unused_848_; 
v_unused_848_ = lean_ctor_get(v___x_783_, 0);
lean_dec(v_unused_848_);
v___x_842_ = v___x_783_;
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_783_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_845_; 
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 0, v_e_776_);
v___x_845_ = v___x_842_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_e_776_);
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
default: 
{
lean_object* v_a_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v_a_849_ = lean_ctor_get(v___x_783_, 1);
lean_inc(v_a_849_);
lean_dec_ref_known(v___x_783_, 2);
v___x_850_ = lean_obj_once(&l_Lean_Meta_Sym_replaceS_x27___closed__1, &l_Lean_Meta_Sym_replaceS_x27___closed__1_once, _init_l_Lean_Meta_Sym_replaceS_x27___closed__1);
v___x_851_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit(v_e_776_, v___x_781_, v_f_777_, v___x_850_, v_a_778_, v_a_779_, v_a_849_);
if (lean_obj_tag(v___x_851_) == 0)
{
lean_object* v_a_852_; lean_object* v_a_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_861_; 
v_a_852_ = lean_ctor_get(v___x_851_, 0);
v_a_853_ = lean_ctor_get(v___x_851_, 1);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_861_ == 0)
{
v___x_855_ = v___x_851_;
v_isShared_856_ = v_isSharedCheck_861_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_a_853_);
lean_inc(v_a_852_);
lean_dec(v___x_851_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_861_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v_fst_857_; lean_object* v___x_859_; 
v_fst_857_ = lean_ctor_get(v_a_852_, 0);
lean_inc(v_fst_857_);
lean_dec(v_a_852_);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 0, v_fst_857_);
v___x_859_ = v___x_855_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_fst_857_);
lean_ctor_set(v_reuseFailAlloc_860_, 1, v_a_853_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
else
{
lean_object* v_a_862_; lean_object* v_a_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_870_; 
v_a_862_ = lean_ctor_get(v___x_851_, 0);
v_a_863_ = lean_ctor_get(v___x_851_, 1);
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_870_ == 0)
{
v___x_865_ = v___x_851_;
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_a_863_);
lean_inc(v_a_862_);
lean_dec(v___x_851_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_868_; 
if (v_isShared_866_ == 0)
{
v___x_868_ = v___x_865_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_a_862_);
lean_ctor_set(v_reuseFailAlloc_869_, 1, v_a_863_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_871_; lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_879_; 
lean_dec_ref(v_f_777_);
lean_dec_ref(v_e_776_);
v_a_871_ = lean_ctor_get(v___x_783_, 0);
v_a_872_ = lean_ctor_get(v___x_783_, 1);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_879_ == 0)
{
v___x_874_ = v___x_783_;
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_inc(v_a_871_);
lean_dec(v___x_783_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_877_; 
if (v_isShared_875_ == 0)
{
v___x_877_ = v___x_874_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_a_871_);
lean_ctor_set(v_reuseFailAlloc_878_, 1, v_a_872_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_replaceS_x27___boxed(lean_object* v_e_880_, lean_object* v_f_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_){
_start:
{
uint8_t v_a_boxed_885_; lean_object* v_res_886_; 
v_a_boxed_885_ = lean_unbox(v_a_882_);
v_res_886_ = l_Lean_Meta_Sym_replaceS_x27(v_e_880_, v_f_881_, v_a_boxed_885_, v_a_883_, v_a_884_);
lean_dec_ref(v_a_883_);
return v_res_886_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_replaceS___closed__0(void){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = l_Lean_Meta_Sym_instInhabitedSymM(lean_box(0));
return v___x_887_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_replaceS___closed__3(void){
_start:
{
lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_890_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__26));
v___x_891_ = lean_unsigned_to_nat(16u);
v___x_892_ = lean_unsigned_to_nat(62u);
v___x_893_ = ((lean_object*)(l_Lean_Meta_Sym_replaceS___closed__2));
v___x_894_ = ((lean_object*)(l_Lean_Meta_Sym_replaceS___closed__1));
v___x_895_ = l_mkPanicMessageWithDecl(v___x_894_, v___x_893_, v___x_892_, v___x_891_, v___x_890_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_replaceS(lean_object* v_e_896_, lean_object* v_f_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_){
_start:
{
lean_object* v___x_905_; lean_object* v___x_906_; uint8_t v_debug_907_; lean_object* v_env_908_; lean_object* v___x_909_; lean_object* v___x_910_; uint8_t v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_905_ = lean_st_ref_get(v_a_899_);
v___x_906_ = lean_st_ref_get(v_a_903_);
v_debug_907_ = lean_ctor_get_uint8(v___x_905_, sizeof(void*)*11);
lean_dec(v___x_905_);
v_env_908_ = lean_ctor_get(v___x_906_, 0);
lean_inc_ref(v_env_908_);
lean_dec(v___x_906_);
v___x_909_ = lean_box(v_debug_907_);
v___x_910_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_replaceS_x27___boxed), 5, 3);
lean_closure_set(v___x_910_, 0, v_e_896_);
lean_closure_set(v___x_910_, 1, v_f_897_);
lean_closure_set(v___x_910_, 2, v___x_909_);
v___x_911_ = 0;
v___x_912_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_912_, 0, v_env_908_);
lean_ctor_set_uint8(v___x_912_, sizeof(void*)*1, v___x_911_);
lean_ctor_set_uint8(v___x_912_, sizeof(void*)*1 + 1, v___x_911_);
v___x_913_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___x_910_, v___x_912_, v_a_899_);
if (lean_obj_tag(v___x_913_) == 0)
{
lean_object* v_a_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_926_; 
v_a_914_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_926_ == 0)
{
v___x_916_ = v___x_913_;
v_isShared_917_ = v_isSharedCheck_926_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_a_914_);
lean_dec(v___x_913_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_926_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
if (lean_obj_tag(v_a_914_) == 0)
{
lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_27__overap_920_; lean_object* v___x_921_; 
lean_dec_ref_known(v_a_914_, 1);
lean_del_object(v___x_916_);
v___x_918_ = lean_obj_once(&l_Lean_Meta_Sym_replaceS___closed__0, &l_Lean_Meta_Sym_replaceS___closed__0_once, _init_l_Lean_Meta_Sym_replaceS___closed__0);
v___x_919_ = lean_obj_once(&l_Lean_Meta_Sym_replaceS___closed__3, &l_Lean_Meta_Sym_replaceS___closed__3_once, _init_l_Lean_Meta_Sym_replaceS___closed__3);
v___x_27__overap_920_ = l_panic___redArg(v___x_918_, v___x_919_);
lean_inc(v_a_903_);
lean_inc_ref(v_a_902_);
lean_inc(v_a_901_);
lean_inc_ref(v_a_900_);
lean_inc(v_a_899_);
lean_inc_ref(v_a_898_);
v___x_921_ = lean_apply_7(v___x_27__overap_920_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, lean_box(0));
return v___x_921_;
}
else
{
lean_object* v_a_922_; lean_object* v___x_924_; 
v_a_922_ = lean_ctor_get(v_a_914_, 0);
lean_inc(v_a_922_);
lean_dec_ref_known(v_a_914_, 1);
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 0, v_a_922_);
v___x_924_ = v___x_916_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v_a_922_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
}
}
}
}
else
{
lean_object* v_a_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_934_; 
v_a_927_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_934_ == 0)
{
v___x_929_ = v___x_913_;
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_a_927_);
lean_dec(v___x_913_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_932_; 
if (v_isShared_930_ == 0)
{
v___x_932_ = v___x_929_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_a_927_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_replaceS___boxed(lean_object* v_e_935_, lean_object* v_f_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l_Lean_Meta_Sym_replaceS(v_e_935_, v_f_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_);
lean_dec(v_a_942_);
lean_dec_ref(v_a_941_);
lean_dec(v_a_940_);
lean_dec_ref(v_a_939_);
lean_dec(v_a_938_);
lean_dec_ref(v_a_937_);
return v_res_944_;
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
