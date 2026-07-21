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
lean_object* v_key_4_; lean_object* v_tail_5_; uint8_t v___y_7_; lean_object* v_fst_9_; lean_object* v_snd_10_; lean_object* v_fst_11_; lean_object* v_snd_12_; size_t v___x_13_; size_t v___x_14_; uint8_t v___x_15_; 
v_key_4_ = lean_ctor_get(v_x_2_, 0);
v_tail_5_ = lean_ctor_get(v_x_2_, 2);
v_fst_9_ = lean_ctor_get(v_key_4_, 0);
v_snd_10_ = lean_ctor_get(v_key_4_, 1);
v_fst_11_ = lean_ctor_get(v_a_1_, 0);
v_snd_12_ = lean_ctor_get(v_a_1_, 1);
v___x_13_ = lean_ptr_addr(v_fst_9_);
v___x_14_ = lean_ptr_addr(v_fst_11_);
v___x_15_ = lean_usize_dec_eq(v___x_13_, v___x_14_);
if (v___x_15_ == 0)
{
v___y_7_ = v___x_15_;
goto v___jp_6_;
}
else
{
uint8_t v___x_16_; 
v___x_16_ = lean_nat_dec_eq(v_snd_10_, v_snd_12_);
v___y_7_ = v___x_16_;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg___boxed(lean_object* v_a_17_, lean_object* v_x_18_){
_start:
{
uint8_t v_res_19_; lean_object* v_r_20_; 
v_res_19_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_a_17_, v_x_18_);
lean_dec(v_x_18_);
lean_dec_ref(v_a_17_);
v_r_20_ = lean_box(v_res_19_);
return v_r_20_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_21_, lean_object* v_x_22_){
_start:
{
if (lean_obj_tag(v_x_22_) == 0)
{
return v_x_21_;
}
else
{
lean_object* v_key_23_; lean_object* v_value_24_; lean_object* v_tail_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_55_; 
v_key_23_ = lean_ctor_get(v_x_22_, 0);
v_value_24_ = lean_ctor_get(v_x_22_, 1);
v_tail_25_ = lean_ctor_get(v_x_22_, 2);
v_isSharedCheck_55_ = !lean_is_exclusive(v_x_22_);
if (v_isSharedCheck_55_ == 0)
{
v___x_27_ = v_x_22_;
v_isShared_28_ = v_isSharedCheck_55_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_tail_25_);
lean_inc(v_value_24_);
lean_inc(v_key_23_);
lean_dec(v_x_22_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_55_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
lean_object* v_fst_29_; lean_object* v_snd_30_; lean_object* v___x_31_; size_t v___x_32_; size_t v___x_33_; size_t v___x_34_; uint64_t v___x_35_; uint64_t v___x_36_; uint64_t v___x_37_; uint64_t v___x_38_; uint64_t v___x_39_; uint64_t v_fold_40_; uint64_t v___x_41_; uint64_t v___x_42_; uint64_t v___x_43_; size_t v___x_44_; size_t v___x_45_; size_t v___x_46_; size_t v___x_47_; size_t v___x_48_; lean_object* v___x_49_; lean_object* v___x_51_; 
v_fst_29_ = lean_ctor_get(v_key_23_, 0);
v_snd_30_ = lean_ctor_get(v_key_23_, 1);
v___x_31_ = lean_array_get_size(v_x_21_);
v___x_32_ = lean_ptr_addr(v_fst_29_);
v___x_33_ = ((size_t)3ULL);
v___x_34_ = lean_usize_shift_right(v___x_32_, v___x_33_);
v___x_35_ = lean_usize_to_uint64(v___x_34_);
v___x_36_ = lean_uint64_of_nat(v_snd_30_);
v___x_37_ = lean_uint64_mix_hash(v___x_35_, v___x_36_);
v___x_38_ = 32ULL;
v___x_39_ = lean_uint64_shift_right(v___x_37_, v___x_38_);
v_fold_40_ = lean_uint64_xor(v___x_37_, v___x_39_);
v___x_41_ = 16ULL;
v___x_42_ = lean_uint64_shift_right(v_fold_40_, v___x_41_);
v___x_43_ = lean_uint64_xor(v_fold_40_, v___x_42_);
v___x_44_ = lean_uint64_to_usize(v___x_43_);
v___x_45_ = lean_usize_of_nat(v___x_31_);
v___x_46_ = ((size_t)1ULL);
v___x_47_ = lean_usize_sub(v___x_45_, v___x_46_);
v___x_48_ = lean_usize_land(v___x_44_, v___x_47_);
v___x_49_ = lean_array_uget_borrowed(v_x_21_, v___x_48_);
lean_inc(v___x_49_);
if (v_isShared_28_ == 0)
{
lean_ctor_set(v___x_27_, 2, v___x_49_);
v___x_51_ = v___x_27_;
goto v_reusejp_50_;
}
else
{
lean_object* v_reuseFailAlloc_54_; 
v_reuseFailAlloc_54_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_54_, 0, v_key_23_);
lean_ctor_set(v_reuseFailAlloc_54_, 1, v_value_24_);
lean_ctor_set(v_reuseFailAlloc_54_, 2, v___x_49_);
v___x_51_ = v_reuseFailAlloc_54_;
goto v_reusejp_50_;
}
v_reusejp_50_:
{
lean_object* v___x_52_; 
v___x_52_ = lean_array_uset(v_x_21_, v___x_48_, v___x_51_);
v_x_21_ = v___x_52_;
v_x_22_ = v_tail_25_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2___redArg(lean_object* v_i_56_, lean_object* v_source_57_, lean_object* v_target_58_){
_start:
{
lean_object* v___x_59_; uint8_t v___x_60_; 
v___x_59_ = lean_array_get_size(v_source_57_);
v___x_60_ = lean_nat_dec_lt(v_i_56_, v___x_59_);
if (v___x_60_ == 0)
{
lean_dec_ref(v_source_57_);
lean_dec(v_i_56_);
return v_target_58_;
}
else
{
lean_object* v_es_61_; lean_object* v___x_62_; lean_object* v_source_63_; lean_object* v_target_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v_es_61_ = lean_array_fget(v_source_57_, v_i_56_);
v___x_62_ = lean_box(0);
v_source_63_ = lean_array_fset(v_source_57_, v_i_56_, v___x_62_);
v_target_64_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3___redArg(v_target_58_, v_es_61_);
v___x_65_ = lean_unsigned_to_nat(1u);
v___x_66_ = lean_nat_add(v_i_56_, v___x_65_);
lean_dec(v_i_56_);
v_i_56_ = v___x_66_;
v_source_57_ = v_source_63_;
v_target_58_ = v_target_64_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1___redArg(lean_object* v_data_68_){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v_nbuckets_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_69_ = lean_array_get_size(v_data_68_);
v___x_70_ = lean_unsigned_to_nat(2u);
v_nbuckets_71_ = lean_nat_mul(v___x_69_, v___x_70_);
v___x_72_ = lean_unsigned_to_nat(0u);
v___x_73_ = lean_box(0);
v___x_74_ = lean_mk_array(v_nbuckets_71_, v___x_73_);
v___x_75_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2___redArg(v___x_72_, v_data_68_, v___x_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(lean_object* v_a_76_, lean_object* v_b_77_, lean_object* v_x_78_){
_start:
{
if (lean_obj_tag(v_x_78_) == 0)
{
lean_dec(v_b_77_);
lean_dec_ref(v_a_76_);
return v_x_78_;
}
else
{
lean_object* v_key_79_; lean_object* v_value_80_; lean_object* v_tail_81_; lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_102_; 
v_key_79_ = lean_ctor_get(v_x_78_, 0);
v_value_80_ = lean_ctor_get(v_x_78_, 1);
v_tail_81_ = lean_ctor_get(v_x_78_, 2);
v_isSharedCheck_102_ = !lean_is_exclusive(v_x_78_);
if (v_isSharedCheck_102_ == 0)
{
v___x_83_ = v_x_78_;
v_isShared_84_ = v_isSharedCheck_102_;
goto v_resetjp_82_;
}
else
{
lean_inc(v_tail_81_);
lean_inc(v_value_80_);
lean_inc(v_key_79_);
lean_dec(v_x_78_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_102_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
uint8_t v___y_86_; lean_object* v_fst_94_; lean_object* v_snd_95_; lean_object* v_fst_96_; lean_object* v_snd_97_; size_t v___x_98_; size_t v___x_99_; uint8_t v___x_100_; 
v_fst_94_ = lean_ctor_get(v_key_79_, 0);
v_snd_95_ = lean_ctor_get(v_key_79_, 1);
v_fst_96_ = lean_ctor_get(v_a_76_, 0);
v_snd_97_ = lean_ctor_get(v_a_76_, 1);
v___x_98_ = lean_ptr_addr(v_fst_94_);
v___x_99_ = lean_ptr_addr(v_fst_96_);
v___x_100_ = lean_usize_dec_eq(v___x_98_, v___x_99_);
if (v___x_100_ == 0)
{
v___y_86_ = v___x_100_;
goto v___jp_85_;
}
else
{
uint8_t v___x_101_; 
v___x_101_ = lean_nat_dec_eq(v_snd_95_, v_snd_97_);
v___y_86_ = v___x_101_;
goto v___jp_85_;
}
v___jp_85_:
{
if (v___y_86_ == 0)
{
lean_object* v___x_87_; lean_object* v___x_89_; 
v___x_87_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(v_a_76_, v_b_77_, v_tail_81_);
if (v_isShared_84_ == 0)
{
lean_ctor_set(v___x_83_, 2, v___x_87_);
v___x_89_ = v___x_83_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_90_; 
v_reuseFailAlloc_90_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v_key_79_);
lean_ctor_set(v_reuseFailAlloc_90_, 1, v_value_80_);
lean_ctor_set(v_reuseFailAlloc_90_, 2, v___x_87_);
v___x_89_ = v_reuseFailAlloc_90_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
return v___x_89_;
}
}
else
{
lean_object* v___x_92_; 
lean_dec(v_value_80_);
lean_dec(v_key_79_);
if (v_isShared_84_ == 0)
{
lean_ctor_set(v___x_83_, 1, v_b_77_);
lean_ctor_set(v___x_83_, 0, v_a_76_);
v___x_92_ = v___x_83_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v_a_76_);
lean_ctor_set(v_reuseFailAlloc_93_, 1, v_b_77_);
lean_ctor_set(v_reuseFailAlloc_93_, 2, v_tail_81_);
v___x_92_ = v_reuseFailAlloc_93_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
return v___x_92_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0___redArg(lean_object* v_m_103_, lean_object* v_a_104_, lean_object* v_b_105_){
_start:
{
lean_object* v_size_106_; lean_object* v_buckets_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_157_; 
v_size_106_ = lean_ctor_get(v_m_103_, 0);
v_buckets_107_ = lean_ctor_get(v_m_103_, 1);
v_isSharedCheck_157_ = !lean_is_exclusive(v_m_103_);
if (v_isSharedCheck_157_ == 0)
{
v___x_109_ = v_m_103_;
v_isShared_110_ = v_isSharedCheck_157_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_buckets_107_);
lean_inc(v_size_106_);
lean_dec(v_m_103_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_157_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v_fst_111_; lean_object* v_snd_112_; lean_object* v___x_113_; size_t v___x_114_; size_t v___x_115_; size_t v___x_116_; uint64_t v___x_117_; uint64_t v___x_118_; uint64_t v___x_119_; uint64_t v___x_120_; uint64_t v___x_121_; uint64_t v_fold_122_; uint64_t v___x_123_; uint64_t v___x_124_; uint64_t v___x_125_; size_t v___x_126_; size_t v___x_127_; size_t v___x_128_; size_t v___x_129_; size_t v___x_130_; lean_object* v_bkt_131_; uint8_t v___x_132_; 
v_fst_111_ = lean_ctor_get(v_a_104_, 0);
v_snd_112_ = lean_ctor_get(v_a_104_, 1);
v___x_113_ = lean_array_get_size(v_buckets_107_);
v___x_114_ = lean_ptr_addr(v_fst_111_);
v___x_115_ = ((size_t)3ULL);
v___x_116_ = lean_usize_shift_right(v___x_114_, v___x_115_);
v___x_117_ = lean_usize_to_uint64(v___x_116_);
v___x_118_ = lean_uint64_of_nat(v_snd_112_);
v___x_119_ = lean_uint64_mix_hash(v___x_117_, v___x_118_);
v___x_120_ = 32ULL;
v___x_121_ = lean_uint64_shift_right(v___x_119_, v___x_120_);
v_fold_122_ = lean_uint64_xor(v___x_119_, v___x_121_);
v___x_123_ = 16ULL;
v___x_124_ = lean_uint64_shift_right(v_fold_122_, v___x_123_);
v___x_125_ = lean_uint64_xor(v_fold_122_, v___x_124_);
v___x_126_ = lean_uint64_to_usize(v___x_125_);
v___x_127_ = lean_usize_of_nat(v___x_113_);
v___x_128_ = ((size_t)1ULL);
v___x_129_ = lean_usize_sub(v___x_127_, v___x_128_);
v___x_130_ = lean_usize_land(v___x_126_, v___x_129_);
v_bkt_131_ = lean_array_uget_borrowed(v_buckets_107_, v___x_130_);
v___x_132_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_a_104_, v_bkt_131_);
if (v___x_132_ == 0)
{
lean_object* v___x_133_; lean_object* v_size_x27_134_; lean_object* v___x_135_; lean_object* v_buckets_x27_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; uint8_t v___x_142_; 
v___x_133_ = lean_unsigned_to_nat(1u);
v_size_x27_134_ = lean_nat_add(v_size_106_, v___x_133_);
lean_dec(v_size_106_);
lean_inc(v_bkt_131_);
v___x_135_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_135_, 0, v_a_104_);
lean_ctor_set(v___x_135_, 1, v_b_105_);
lean_ctor_set(v___x_135_, 2, v_bkt_131_);
v_buckets_x27_136_ = lean_array_uset(v_buckets_107_, v___x_130_, v___x_135_);
v___x_137_ = lean_unsigned_to_nat(4u);
v___x_138_ = lean_nat_mul(v_size_x27_134_, v___x_137_);
v___x_139_ = lean_unsigned_to_nat(3u);
v___x_140_ = lean_nat_div(v___x_138_, v___x_139_);
lean_dec(v___x_138_);
v___x_141_ = lean_array_get_size(v_buckets_x27_136_);
v___x_142_ = lean_nat_dec_le(v___x_140_, v___x_141_);
lean_dec(v___x_140_);
if (v___x_142_ == 0)
{
lean_object* v_val_143_; lean_object* v___x_145_; 
v_val_143_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1___redArg(v_buckets_x27_136_);
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 1, v_val_143_);
lean_ctor_set(v___x_109_, 0, v_size_x27_134_);
v___x_145_ = v___x_109_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_size_x27_134_);
lean_ctor_set(v_reuseFailAlloc_146_, 1, v_val_143_);
v___x_145_ = v_reuseFailAlloc_146_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
return v___x_145_;
}
}
else
{
lean_object* v___x_148_; 
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 1, v_buckets_x27_136_);
lean_ctor_set(v___x_109_, 0, v_size_x27_134_);
v___x_148_ = v___x_109_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v_size_x27_134_);
lean_ctor_set(v_reuseFailAlloc_149_, 1, v_buckets_x27_136_);
v___x_148_ = v_reuseFailAlloc_149_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
return v___x_148_;
}
}
}
else
{
lean_object* v___x_150_; lean_object* v_buckets_x27_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_155_; 
lean_inc(v_bkt_131_);
v___x_150_ = lean_box(0);
v_buckets_x27_151_ = lean_array_uset(v_buckets_107_, v___x_130_, v___x_150_);
v___x_152_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(v_a_104_, v_b_105_, v_bkt_131_);
v___x_153_ = lean_array_uset(v_buckets_x27_151_, v___x_130_, v___x_152_);
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 1, v___x_153_);
v___x_155_ = v___x_109_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v_size_106_);
lean_ctor_set(v_reuseFailAlloc_156_, 1, v___x_153_);
v___x_155_ = v_reuseFailAlloc_156_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
return v___x_155_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(lean_object* v_key_158_, lean_object* v_r_159_, lean_object* v_a_160_, lean_object* v_a_161_){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
lean_inc_ref(v_r_159_);
v___x_162_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_160_, v_key_158_, v_r_159_);
v___x_163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_163_, 0, v_r_159_);
lean_ctor_set(v___x_163_, 1, v___x_162_);
v___x_164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
lean_ctor_set(v___x_164_, 1, v_a_161_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(lean_object* v_key_165_, lean_object* v_r_166_, lean_object* v_a_167_, uint8_t v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(v_key_165_, v_r_166_, v_a_167_, v_a_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___boxed(lean_object* v_key_172_, lean_object* v_r_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_){
_start:
{
uint8_t v_a_boxed_178_; lean_object* v_res_179_; 
v_a_boxed_178_ = lean_unbox(v_a_175_);
v_res_179_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_172_, v_r_173_, v_a_174_, v_a_boxed_178_, v_a_176_, v_a_177_);
lean_dec_ref(v_a_176_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0(lean_object* v_00_u03b2_180_, lean_object* v_m_181_, lean_object* v_a_182_, lean_object* v_b_183_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0___redArg(v_m_181_, v_a_182_, v_b_183_);
return v___x_184_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0(lean_object* v_00_u03b2_185_, lean_object* v_a_186_, lean_object* v_x_187_){
_start:
{
uint8_t v___x_188_; 
v___x_188_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_a_186_, v_x_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0___boxed(lean_object* v_00_u03b2_189_, lean_object* v_a_190_, lean_object* v_x_191_){
_start:
{
uint8_t v_res_192_; lean_object* v_r_193_; 
v_res_192_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0(v_00_u03b2_189_, v_a_190_, v_x_191_);
lean_dec(v_x_191_);
lean_dec_ref(v_a_190_);
v_r_193_ = lean_box(v_res_192_);
return v_r_193_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1(lean_object* v_00_u03b2_194_, lean_object* v_data_195_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1___redArg(v_data_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__2(lean_object* v_00_u03b2_197_, lean_object* v_a_198_, lean_object* v_b_199_, lean_object* v_x_200_){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(v_a_198_, v_b_199_, v_x_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_202_, lean_object* v_i_203_, lean_object* v_source_204_, lean_object* v_target_205_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2___redArg(v_i_203_, v_source_204_, v_target_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_207_, lean_object* v_x_208_, lean_object* v_x_209_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3___redArg(v_x_208_, v_x_209_);
return v___x_210_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__4(void){
_start:
{
lean_object* v___x_217_; lean_object* v___f_218_; 
v___x_217_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___f_218_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_218_, 0, v___x_217_);
return v___f_218_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__5(void){
_start:
{
lean_object* v___f_219_; lean_object* v___f_220_; lean_object* v___f_221_; 
v___f_219_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__4, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__4_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__4);
v___f_220_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__0));
v___f_221_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_221_, 0, v___f_220_);
lean_closure_set(v___f_221_, 1, v___f_219_);
return v___f_221_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__10(void){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_241_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__9));
v___x_242_ = l_ReaderT_instMonad___redArg(v___x_241_);
return v___x_242_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11(void){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_243_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__10, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__10_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__10);
v___x_244_ = l_ReaderT_instMonad___redArg(v___x_243_);
return v___x_244_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20(void){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11);
v___x_246_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_246_, 0, lean_box(0));
lean_closure_set(v___x_246_, 1, lean_box(0));
lean_closure_set(v___x_246_, 2, v___x_245_);
return v___x_246_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__15(void){
_start:
{
lean_object* v___x_247_; lean_object* v___f_248_; 
v___x_247_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11);
v___f_248_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_248_, 0, v___x_247_);
return v___f_248_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__14(void){
_start:
{
lean_object* v___x_249_; lean_object* v___f_250_; 
v___x_249_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11);
v___f_250_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_250_, 0, v___x_249_);
return v___f_250_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__13(void){
_start:
{
lean_object* v___x_251_; lean_object* v___f_252_; 
v___x_251_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11);
v___f_252_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_252_, 0, v___x_251_);
return v___f_252_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__18(void){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_253_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11);
v___x_254_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_254_, 0, lean_box(0));
lean_closure_set(v___x_254_, 1, lean_box(0));
lean_closure_set(v___x_254_, 2, v___x_253_);
return v___x_254_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__12(void){
_start:
{
lean_object* v___x_255_; lean_object* v___f_256_; 
v___x_255_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11);
v___f_256_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_256_, 0, v___x_255_);
return v___f_256_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__16(void){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_257_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11);
v___x_258_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_258_, 0, lean_box(0));
lean_closure_set(v___x_258_, 1, lean_box(0));
lean_closure_set(v___x_258_, 2, v___x_257_);
return v___x_258_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__17(void){
_start:
{
lean_object* v___f_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v___f_259_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__12, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__12_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__12);
v___x_260_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__16, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__16_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__16);
v___x_261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_261_, 0, v___x_260_);
lean_ctor_set(v___x_261_, 1, v___f_259_);
return v___x_261_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__19(void){
_start:
{
lean_object* v___f_262_; lean_object* v___f_263_; lean_object* v___f_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___f_262_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__15, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__15_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__15);
v___f_263_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__14, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__14_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__14);
v___f_264_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__13, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__13_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__13);
v___x_265_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__18, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__18_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__18);
v___x_266_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__17, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__17_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__17);
v___x_267_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_267_, 0, v___x_266_);
lean_ctor_set(v___x_267_, 1, v___x_265_);
lean_ctor_set(v___x_267_, 2, v___f_264_);
lean_ctor_set(v___x_267_, 3, v___f_263_);
lean_ctor_set(v___x_267_, 4, v___f_262_);
return v___x_267_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__21(void){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_268_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20);
v___x_269_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__19, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__19_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__19);
v___x_270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_270_, 0, v___x_269_);
lean_ctor_set(v___x_270_, 1, v___x_268_);
return v___x_270_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__22(void){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_271_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11);
v___x_272_ = lean_alloc_closure((void*)(l_StateT_lift), 6, 3);
lean_closure_set(v___x_272_, 0, lean_box(0));
lean_closure_set(v___x_272_, 1, lean_box(0));
lean_closure_set(v___x_272_, 2, v___x_271_);
return v___x_272_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__23(void){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_273_ = l_Lean_instInhabitedExpr;
v___x_274_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__21, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__21_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__21);
v___x_275_ = l_instInhabitedOfMonad___redArg(v___x_274_, v___x_273_);
return v___x_275_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__27(void){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_279_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__26));
v___x_280_ = lean_unsigned_to_nat(67u);
v___x_281_ = lean_unsigned_to_nat(35u);
v___x_282_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__25));
v___x_283_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__24));
v___x_284_ = l_mkPanicMessageWithDecl(v___x_283_, v___x_282_, v___x_281_, v___x_280_, v___x_279_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit(lean_object* v_e_285_, lean_object* v_offset_286_, lean_object* v_fn_287_, lean_object* v_a_288_, uint8_t v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v_share1_295_; lean_object* v_assertShared_296_; lean_object* v_isDebugEnabled_297_; lean_object* v___x_298_; lean_object* v___f_299_; lean_object* v___f_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_292_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11);
v___x_293_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__21, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__21_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__21);
v___x_294_ = l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM;
v_share1_295_ = lean_ctor_get(v___x_294_, 0);
v_assertShared_296_ = lean_ctor_get(v___x_294_, 1);
v_isDebugEnabled_297_ = lean_ctor_get(v___x_294_, 2);
v___x_298_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__22, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__22_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__22);
lean_inc(v_share1_295_);
v___f_299_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_299_, 0, v_share1_295_);
lean_closure_set(v___f_299_, 1, v___x_298_);
lean_inc(v_assertShared_296_);
v___f_300_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift___redArg___lam__1), 3, 2);
lean_closure_set(v___f_300_, 0, v_assertShared_296_);
lean_closure_set(v___f_300_, 1, v___x_298_);
lean_inc(v_isDebugEnabled_297_);
v___x_301_ = lean_alloc_closure((void*)(l_StateT_lift), 6, 5);
lean_closure_set(v___x_301_, 0, lean_box(0));
lean_closure_set(v___x_301_, 1, lean_box(0));
lean_closure_set(v___x_301_, 2, v___x_292_);
lean_closure_set(v___x_301_, 3, lean_box(0));
lean_closure_set(v___x_301_, 4, v_isDebugEnabled_297_);
v___x_302_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_302_, 0, v___f_299_);
lean_ctor_set(v___x_302_, 1, v___f_300_);
lean_ctor_set(v___x_302_, 2, v___x_301_);
switch(lean_obj_tag(v_e_285_))
{
case 5:
{
lean_object* v_fn_303_; lean_object* v_arg_304_; lean_object* v___x_305_; 
v_fn_303_ = lean_ctor_get(v_e_285_, 0);
v_arg_304_ = lean_ctor_get(v_e_285_, 1);
lean_inc_ref(v_fn_287_);
lean_inc(v_offset_286_);
lean_inc_ref(v_fn_303_);
v___x_305_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_fn_303_, v_offset_286_, v_fn_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_);
if (lean_obj_tag(v___x_305_) == 0)
{
lean_object* v_a_306_; lean_object* v_a_307_; lean_object* v_fst_308_; lean_object* v_snd_309_; lean_object* v___x_310_; 
v_a_306_ = lean_ctor_get(v___x_305_, 0);
lean_inc(v_a_306_);
v_a_307_ = lean_ctor_get(v___x_305_, 1);
lean_inc(v_a_307_);
lean_dec_ref_known(v___x_305_, 2);
v_fst_308_ = lean_ctor_get(v_a_306_, 0);
lean_inc(v_fst_308_);
v_snd_309_ = lean_ctor_get(v_a_306_, 1);
lean_inc(v_snd_309_);
lean_dec(v_a_306_);
lean_inc_ref(v_arg_304_);
v___x_310_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_arg_304_, v_offset_286_, v_fn_287_, v_snd_309_, v_a_289_, v_a_290_, v_a_307_);
if (lean_obj_tag(v___x_310_) == 0)
{
lean_object* v_a_311_; lean_object* v_a_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_339_; 
v_a_311_ = lean_ctor_get(v___x_310_, 0);
v_a_312_ = lean_ctor_get(v___x_310_, 1);
v_isSharedCheck_339_ = !lean_is_exclusive(v___x_310_);
if (v_isSharedCheck_339_ == 0)
{
v___x_314_ = v___x_310_;
v_isShared_315_ = v_isSharedCheck_339_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_a_312_);
lean_inc(v_a_311_);
lean_dec(v___x_310_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_339_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v_fst_316_; lean_object* v_snd_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_338_; 
v_fst_316_ = lean_ctor_get(v_a_311_, 0);
v_snd_317_ = lean_ctor_get(v_a_311_, 1);
v_isSharedCheck_338_ = !lean_is_exclusive(v_a_311_);
if (v_isSharedCheck_338_ == 0)
{
v___x_319_ = v_a_311_;
v_isShared_320_ = v_isSharedCheck_338_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_snd_317_);
lean_inc(v_fst_316_);
lean_dec(v_a_311_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_338_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
uint8_t v___y_322_; size_t v___x_332_; size_t v___x_333_; uint8_t v___x_334_; 
v___x_332_ = lean_ptr_addr(v_fn_303_);
v___x_333_ = lean_ptr_addr(v_fst_308_);
v___x_334_ = lean_usize_dec_eq(v___x_332_, v___x_333_);
if (v___x_334_ == 0)
{
v___y_322_ = v___x_334_;
goto v___jp_321_;
}
else
{
size_t v___x_335_; size_t v___x_336_; uint8_t v___x_337_; 
v___x_335_ = lean_ptr_addr(v_arg_304_);
v___x_336_ = lean_ptr_addr(v_fst_316_);
v___x_337_ = lean_usize_dec_eq(v___x_335_, v___x_336_);
v___y_322_ = v___x_337_;
goto v___jp_321_;
}
v___jp_321_:
{
if (v___y_322_ == 0)
{
lean_object* v___x_11954__overap_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
lean_del_object(v___x_319_);
lean_del_object(v___x_314_);
lean_dec_ref_known(v_e_285_, 2);
v___x_11954__overap_323_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v___x_302_, v___x_293_, v_fst_308_, v_fst_316_);
v___x_324_ = lean_box(v_a_289_);
lean_inc_ref(v_a_290_);
v___x_325_ = lean_apply_4(v___x_11954__overap_323_, v_snd_317_, v___x_324_, v_a_290_, v_a_312_);
return v___x_325_;
}
else
{
lean_object* v___x_327_; 
lean_dec(v_fst_316_);
lean_dec(v_fst_308_);
lean_dec_ref_known(v___x_302_, 3);
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 0, v_e_285_);
v___x_327_ = v___x_319_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_e_285_);
lean_ctor_set(v_reuseFailAlloc_331_, 1, v_snd_317_);
v___x_327_ = v_reuseFailAlloc_331_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
lean_object* v___x_329_; 
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 0, v___x_327_);
v___x_329_ = v___x_314_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v___x_327_);
lean_ctor_set(v_reuseFailAlloc_330_, 1, v_a_312_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_308_);
lean_dec_ref_known(v_e_285_, 2);
lean_dec_ref_known(v___x_302_, 3);
return v___x_310_;
}
}
else
{
lean_dec_ref_known(v_e_285_, 2);
lean_dec_ref_known(v___x_302_, 3);
lean_dec_ref(v_fn_287_);
lean_dec(v_offset_286_);
return v___x_305_;
}
}
case 6:
{
lean_object* v_binderName_340_; lean_object* v_binderType_341_; lean_object* v_body_342_; uint8_t v_binderInfo_343_; lean_object* v___x_344_; 
v_binderName_340_ = lean_ctor_get(v_e_285_, 0);
v_binderType_341_ = lean_ctor_get(v_e_285_, 1);
v_body_342_ = lean_ctor_get(v_e_285_, 2);
v_binderInfo_343_ = lean_ctor_get_uint8(v_e_285_, sizeof(void*)*3 + 8);
lean_inc_ref(v_fn_287_);
lean_inc(v_offset_286_);
lean_inc_ref(v_binderType_341_);
v___x_344_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_binderType_341_, v_offset_286_, v_fn_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_);
if (lean_obj_tag(v___x_344_) == 0)
{
lean_object* v_a_345_; lean_object* v_a_346_; lean_object* v_fst_347_; lean_object* v_snd_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v_a_345_ = lean_ctor_get(v___x_344_, 0);
lean_inc(v_a_345_);
v_a_346_ = lean_ctor_get(v___x_344_, 1);
lean_inc(v_a_346_);
lean_dec_ref_known(v___x_344_, 2);
v_fst_347_ = lean_ctor_get(v_a_345_, 0);
lean_inc(v_fst_347_);
v_snd_348_ = lean_ctor_get(v_a_345_, 1);
lean_inc(v_snd_348_);
lean_dec(v_a_345_);
v___x_349_ = lean_unsigned_to_nat(1u);
v___x_350_ = lean_nat_add(v_offset_286_, v___x_349_);
lean_dec(v_offset_286_);
lean_inc_ref(v_body_342_);
v___x_351_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_body_342_, v___x_350_, v_fn_287_, v_snd_348_, v_a_289_, v_a_290_, v_a_346_);
if (lean_obj_tag(v___x_351_) == 0)
{
lean_object* v_a_352_; lean_object* v_a_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_380_; 
v_a_352_ = lean_ctor_get(v___x_351_, 0);
v_a_353_ = lean_ctor_get(v___x_351_, 1);
v_isSharedCheck_380_ = !lean_is_exclusive(v___x_351_);
if (v_isSharedCheck_380_ == 0)
{
v___x_355_ = v___x_351_;
v_isShared_356_ = v_isSharedCheck_380_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_a_353_);
lean_inc(v_a_352_);
lean_dec(v___x_351_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_380_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v_fst_357_; lean_object* v_snd_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_379_; 
v_fst_357_ = lean_ctor_get(v_a_352_, 0);
v_snd_358_ = lean_ctor_get(v_a_352_, 1);
v_isSharedCheck_379_ = !lean_is_exclusive(v_a_352_);
if (v_isSharedCheck_379_ == 0)
{
v___x_360_ = v_a_352_;
v_isShared_361_ = v_isSharedCheck_379_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_snd_358_);
lean_inc(v_fst_357_);
lean_dec(v_a_352_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_379_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
uint8_t v___y_363_; size_t v___x_373_; size_t v___x_374_; uint8_t v___x_375_; 
v___x_373_ = lean_ptr_addr(v_binderType_341_);
v___x_374_ = lean_ptr_addr(v_fst_347_);
v___x_375_ = lean_usize_dec_eq(v___x_373_, v___x_374_);
if (v___x_375_ == 0)
{
v___y_363_ = v___x_375_;
goto v___jp_362_;
}
else
{
size_t v___x_376_; size_t v___x_377_; uint8_t v___x_378_; 
v___x_376_ = lean_ptr_addr(v_body_342_);
v___x_377_ = lean_ptr_addr(v_fst_357_);
v___x_378_ = lean_usize_dec_eq(v___x_376_, v___x_377_);
v___y_363_ = v___x_378_;
goto v___jp_362_;
}
v___jp_362_:
{
if (v___y_363_ == 0)
{
lean_object* v___x_12238__overap_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
lean_inc(v_binderName_340_);
lean_del_object(v___x_360_);
lean_del_object(v___x_355_);
lean_dec_ref_known(v_e_285_, 3);
v___x_12238__overap_364_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v___x_302_, v___x_293_, v_binderName_340_, v_binderInfo_343_, v_fst_347_, v_fst_357_);
v___x_365_ = lean_box(v_a_289_);
lean_inc_ref(v_a_290_);
v___x_366_ = lean_apply_4(v___x_12238__overap_364_, v_snd_358_, v___x_365_, v_a_290_, v_a_353_);
return v___x_366_;
}
else
{
lean_object* v___x_368_; 
lean_dec(v_fst_357_);
lean_dec(v_fst_347_);
lean_dec_ref_known(v___x_302_, 3);
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 0, v_e_285_);
v___x_368_ = v___x_360_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_e_285_);
lean_ctor_set(v_reuseFailAlloc_372_, 1, v_snd_358_);
v___x_368_ = v_reuseFailAlloc_372_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
lean_object* v___x_370_; 
if (v_isShared_356_ == 0)
{
lean_ctor_set(v___x_355_, 0, v___x_368_);
v___x_370_ = v___x_355_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v___x_368_);
lean_ctor_set(v_reuseFailAlloc_371_, 1, v_a_353_);
v___x_370_ = v_reuseFailAlloc_371_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
return v___x_370_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_347_);
lean_dec_ref_known(v_e_285_, 3);
lean_dec_ref_known(v___x_302_, 3);
return v___x_351_;
}
}
else
{
lean_dec_ref_known(v_e_285_, 3);
lean_dec_ref_known(v___x_302_, 3);
lean_dec_ref(v_fn_287_);
lean_dec(v_offset_286_);
return v___x_344_;
}
}
case 7:
{
lean_object* v_binderName_381_; lean_object* v_binderType_382_; lean_object* v_body_383_; uint8_t v_binderInfo_384_; lean_object* v___x_385_; 
v_binderName_381_ = lean_ctor_get(v_e_285_, 0);
v_binderType_382_ = lean_ctor_get(v_e_285_, 1);
v_body_383_ = lean_ctor_get(v_e_285_, 2);
v_binderInfo_384_ = lean_ctor_get_uint8(v_e_285_, sizeof(void*)*3 + 8);
lean_inc_ref(v_fn_287_);
lean_inc(v_offset_286_);
lean_inc_ref(v_binderType_382_);
v___x_385_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_binderType_382_, v_offset_286_, v_fn_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_);
if (lean_obj_tag(v___x_385_) == 0)
{
lean_object* v_a_386_; lean_object* v_a_387_; lean_object* v_fst_388_; lean_object* v_snd_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v_a_386_ = lean_ctor_get(v___x_385_, 0);
lean_inc(v_a_386_);
v_a_387_ = lean_ctor_get(v___x_385_, 1);
lean_inc(v_a_387_);
lean_dec_ref_known(v___x_385_, 2);
v_fst_388_ = lean_ctor_get(v_a_386_, 0);
lean_inc(v_fst_388_);
v_snd_389_ = lean_ctor_get(v_a_386_, 1);
lean_inc(v_snd_389_);
lean_dec(v_a_386_);
v___x_390_ = lean_unsigned_to_nat(1u);
v___x_391_ = lean_nat_add(v_offset_286_, v___x_390_);
lean_dec(v_offset_286_);
lean_inc_ref(v_body_383_);
v___x_392_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_body_383_, v___x_391_, v_fn_287_, v_snd_389_, v_a_289_, v_a_290_, v_a_387_);
if (lean_obj_tag(v___x_392_) == 0)
{
lean_object* v_a_393_; lean_object* v_a_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_421_; 
v_a_393_ = lean_ctor_get(v___x_392_, 0);
v_a_394_ = lean_ctor_get(v___x_392_, 1);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_421_ == 0)
{
v___x_396_ = v___x_392_;
v_isShared_397_ = v_isSharedCheck_421_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_a_394_);
lean_inc(v_a_393_);
lean_dec(v___x_392_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_421_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v_fst_398_; lean_object* v_snd_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_420_; 
v_fst_398_ = lean_ctor_get(v_a_393_, 0);
v_snd_399_ = lean_ctor_get(v_a_393_, 1);
v_isSharedCheck_420_ = !lean_is_exclusive(v_a_393_);
if (v_isSharedCheck_420_ == 0)
{
v___x_401_ = v_a_393_;
v_isShared_402_ = v_isSharedCheck_420_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_snd_399_);
lean_inc(v_fst_398_);
lean_dec(v_a_393_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_420_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
uint8_t v___y_404_; size_t v___x_414_; size_t v___x_415_; uint8_t v___x_416_; 
v___x_414_ = lean_ptr_addr(v_binderType_382_);
v___x_415_ = lean_ptr_addr(v_fst_388_);
v___x_416_ = lean_usize_dec_eq(v___x_414_, v___x_415_);
if (v___x_416_ == 0)
{
v___y_404_ = v___x_416_;
goto v___jp_403_;
}
else
{
size_t v___x_417_; size_t v___x_418_; uint8_t v___x_419_; 
v___x_417_ = lean_ptr_addr(v_body_383_);
v___x_418_ = lean_ptr_addr(v_fst_398_);
v___x_419_ = lean_usize_dec_eq(v___x_417_, v___x_418_);
v___y_404_ = v___x_419_;
goto v___jp_403_;
}
v___jp_403_:
{
if (v___y_404_ == 0)
{
lean_object* v___x_12530__overap_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
lean_inc(v_binderName_381_);
lean_del_object(v___x_401_);
lean_del_object(v___x_396_);
lean_dec_ref_known(v_e_285_, 3);
v___x_12530__overap_405_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v___x_302_, v___x_293_, v_binderName_381_, v_binderInfo_384_, v_fst_388_, v_fst_398_);
v___x_406_ = lean_box(v_a_289_);
lean_inc_ref(v_a_290_);
v___x_407_ = lean_apply_4(v___x_12530__overap_405_, v_snd_399_, v___x_406_, v_a_290_, v_a_394_);
return v___x_407_;
}
else
{
lean_object* v___x_409_; 
lean_dec(v_fst_398_);
lean_dec(v_fst_388_);
lean_dec_ref_known(v___x_302_, 3);
if (v_isShared_402_ == 0)
{
lean_ctor_set(v___x_401_, 0, v_e_285_);
v___x_409_ = v___x_401_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_e_285_);
lean_ctor_set(v_reuseFailAlloc_413_, 1, v_snd_399_);
v___x_409_ = v_reuseFailAlloc_413_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
lean_object* v___x_411_; 
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 0, v___x_409_);
v___x_411_ = v___x_396_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v___x_409_);
lean_ctor_set(v_reuseFailAlloc_412_, 1, v_a_394_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_388_);
lean_dec_ref_known(v_e_285_, 3);
lean_dec_ref_known(v___x_302_, 3);
return v___x_392_;
}
}
else
{
lean_dec_ref_known(v_e_285_, 3);
lean_dec_ref_known(v___x_302_, 3);
lean_dec_ref(v_fn_287_);
lean_dec(v_offset_286_);
return v___x_385_;
}
}
case 8:
{
lean_object* v_declName_422_; lean_object* v_type_423_; lean_object* v_value_424_; lean_object* v_body_425_; uint8_t v_nondep_426_; lean_object* v___x_427_; 
v_declName_422_ = lean_ctor_get(v_e_285_, 0);
v_type_423_ = lean_ctor_get(v_e_285_, 1);
v_value_424_ = lean_ctor_get(v_e_285_, 2);
v_body_425_ = lean_ctor_get(v_e_285_, 3);
v_nondep_426_ = lean_ctor_get_uint8(v_e_285_, sizeof(void*)*4 + 8);
lean_inc_ref(v_fn_287_);
lean_inc(v_offset_286_);
lean_inc_ref(v_type_423_);
v___x_427_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_type_423_, v_offset_286_, v_fn_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_);
if (lean_obj_tag(v___x_427_) == 0)
{
lean_object* v_a_428_; lean_object* v_a_429_; lean_object* v_fst_430_; lean_object* v_snd_431_; lean_object* v___x_432_; 
v_a_428_ = lean_ctor_get(v___x_427_, 0);
lean_inc(v_a_428_);
v_a_429_ = lean_ctor_get(v___x_427_, 1);
lean_inc(v_a_429_);
lean_dec_ref_known(v___x_427_, 2);
v_fst_430_ = lean_ctor_get(v_a_428_, 0);
lean_inc(v_fst_430_);
v_snd_431_ = lean_ctor_get(v_a_428_, 1);
lean_inc(v_snd_431_);
lean_dec(v_a_428_);
lean_inc_ref(v_fn_287_);
lean_inc(v_offset_286_);
lean_inc_ref(v_value_424_);
v___x_432_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_value_424_, v_offset_286_, v_fn_287_, v_snd_431_, v_a_289_, v_a_290_, v_a_429_);
if (lean_obj_tag(v___x_432_) == 0)
{
lean_object* v_a_433_; lean_object* v_a_434_; lean_object* v_fst_435_; lean_object* v_snd_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v_a_433_ = lean_ctor_get(v___x_432_, 0);
lean_inc(v_a_433_);
v_a_434_ = lean_ctor_get(v___x_432_, 1);
lean_inc(v_a_434_);
lean_dec_ref_known(v___x_432_, 2);
v_fst_435_ = lean_ctor_get(v_a_433_, 0);
lean_inc(v_fst_435_);
v_snd_436_ = lean_ctor_get(v_a_433_, 1);
lean_inc(v_snd_436_);
lean_dec(v_a_433_);
v___x_437_ = lean_unsigned_to_nat(1u);
v___x_438_ = lean_nat_add(v_offset_286_, v___x_437_);
lean_dec(v_offset_286_);
lean_inc_ref(v_body_425_);
v___x_439_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_body_425_, v___x_438_, v_fn_287_, v_snd_436_, v_a_289_, v_a_290_, v_a_434_);
if (lean_obj_tag(v___x_439_) == 0)
{
lean_object* v_a_440_; lean_object* v_a_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_474_; 
v_a_440_ = lean_ctor_get(v___x_439_, 0);
v_a_441_ = lean_ctor_get(v___x_439_, 1);
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_474_ == 0)
{
v___x_443_ = v___x_439_;
v_isShared_444_ = v_isSharedCheck_474_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_a_441_);
lean_inc(v_a_440_);
lean_dec(v___x_439_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_474_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v_fst_445_; lean_object* v_snd_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_473_; 
v_fst_445_ = lean_ctor_get(v_a_440_, 0);
v_snd_446_ = lean_ctor_get(v_a_440_, 1);
v_isSharedCheck_473_ = !lean_is_exclusive(v_a_440_);
if (v_isSharedCheck_473_ == 0)
{
v___x_448_ = v_a_440_;
v_isShared_449_ = v_isSharedCheck_473_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_snd_446_);
lean_inc(v_fst_445_);
lean_dec(v_a_440_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_473_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
uint8_t v___y_451_; size_t v___x_467_; size_t v___x_468_; uint8_t v___x_469_; 
v___x_467_ = lean_ptr_addr(v_type_423_);
v___x_468_ = lean_ptr_addr(v_fst_430_);
v___x_469_ = lean_usize_dec_eq(v___x_467_, v___x_468_);
if (v___x_469_ == 0)
{
v___y_451_ = v___x_469_;
goto v___jp_450_;
}
else
{
size_t v___x_470_; size_t v___x_471_; uint8_t v___x_472_; 
v___x_470_ = lean_ptr_addr(v_value_424_);
v___x_471_ = lean_ptr_addr(v_fst_435_);
v___x_472_ = lean_usize_dec_eq(v___x_470_, v___x_471_);
v___y_451_ = v___x_472_;
goto v___jp_450_;
}
v___jp_450_:
{
if (v___y_451_ == 0)
{
lean_object* v___x_12867__overap_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
lean_inc(v_declName_422_);
lean_del_object(v___x_448_);
lean_del_object(v___x_443_);
lean_dec_ref_known(v_e_285_, 4);
v___x_12867__overap_452_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v___x_302_, v___x_293_, v_declName_422_, v_fst_430_, v_fst_435_, v_fst_445_, v_nondep_426_);
v___x_453_ = lean_box(v_a_289_);
lean_inc_ref(v_a_290_);
v___x_454_ = lean_apply_4(v___x_12867__overap_452_, v_snd_446_, v___x_453_, v_a_290_, v_a_441_);
return v___x_454_;
}
else
{
size_t v___x_455_; size_t v___x_456_; uint8_t v___x_457_; 
v___x_455_ = lean_ptr_addr(v_body_425_);
v___x_456_ = lean_ptr_addr(v_fst_445_);
v___x_457_ = lean_usize_dec_eq(v___x_455_, v___x_456_);
if (v___x_457_ == 0)
{
lean_object* v___x_12872__overap_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
lean_inc(v_declName_422_);
lean_del_object(v___x_448_);
lean_del_object(v___x_443_);
lean_dec_ref_known(v_e_285_, 4);
v___x_12872__overap_458_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v___x_302_, v___x_293_, v_declName_422_, v_fst_430_, v_fst_435_, v_fst_445_, v_nondep_426_);
v___x_459_ = lean_box(v_a_289_);
lean_inc_ref(v_a_290_);
v___x_460_ = lean_apply_4(v___x_12872__overap_458_, v_snd_446_, v___x_459_, v_a_290_, v_a_441_);
return v___x_460_;
}
else
{
lean_object* v___x_462_; 
lean_dec(v_fst_445_);
lean_dec(v_fst_435_);
lean_dec(v_fst_430_);
lean_dec_ref_known(v___x_302_, 3);
if (v_isShared_449_ == 0)
{
lean_ctor_set(v___x_448_, 0, v_e_285_);
v___x_462_ = v___x_448_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_e_285_);
lean_ctor_set(v_reuseFailAlloc_466_, 1, v_snd_446_);
v___x_462_ = v_reuseFailAlloc_466_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
lean_object* v___x_464_; 
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 0, v___x_462_);
v___x_464_ = v___x_443_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v___x_462_);
lean_ctor_set(v_reuseFailAlloc_465_, 1, v_a_441_);
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
}
else
{
lean_dec(v_fst_435_);
lean_dec(v_fst_430_);
lean_dec_ref_known(v_e_285_, 4);
lean_dec_ref_known(v___x_302_, 3);
return v___x_439_;
}
}
else
{
lean_dec(v_fst_430_);
lean_dec_ref_known(v_e_285_, 4);
lean_dec_ref_known(v___x_302_, 3);
lean_dec_ref(v_fn_287_);
lean_dec(v_offset_286_);
return v___x_432_;
}
}
else
{
lean_dec_ref_known(v_e_285_, 4);
lean_dec_ref_known(v___x_302_, 3);
lean_dec_ref(v_fn_287_);
lean_dec(v_offset_286_);
return v___x_427_;
}
}
case 10:
{
lean_object* v_data_475_; lean_object* v_expr_476_; lean_object* v___x_477_; 
v_data_475_ = lean_ctor_get(v_e_285_, 0);
v_expr_476_ = lean_ctor_get(v_e_285_, 1);
lean_inc_ref(v_expr_476_);
v___x_477_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_expr_476_, v_offset_286_, v_fn_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_);
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
lean_object* v___x_13158__overap_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
lean_inc(v_data_475_);
lean_del_object(v___x_486_);
lean_del_object(v___x_481_);
lean_dec_ref_known(v_e_285_, 2);
v___x_13158__overap_491_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg(v___x_302_, v___x_293_, v_data_475_, v_fst_483_);
v___x_492_ = lean_box(v_a_289_);
lean_inc_ref(v_a_290_);
v___x_493_ = lean_apply_4(v___x_13158__overap_491_, v_snd_484_, v___x_492_, v_a_290_, v_a_479_);
return v___x_493_;
}
else
{
lean_object* v___x_495_; 
lean_dec(v_fst_483_);
lean_dec_ref_known(v___x_302_, 3);
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 0, v_e_285_);
v___x_495_ = v___x_486_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_e_285_);
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
lean_dec_ref_known(v_e_285_, 2);
lean_dec_ref_known(v___x_302_, 3);
return v___x_477_;
}
}
case 11:
{
lean_object* v_typeName_502_; lean_object* v_idx_503_; lean_object* v_struct_504_; lean_object* v___x_505_; 
v_typeName_502_ = lean_ctor_get(v_e_285_, 0);
v_idx_503_ = lean_ctor_get(v_e_285_, 1);
v_struct_504_ = lean_ctor_get(v_e_285_, 2);
lean_inc_ref(v_struct_504_);
v___x_505_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_struct_504_, v_offset_286_, v_fn_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_);
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
lean_object* v___x_13341__overap_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
lean_inc(v_idx_503_);
lean_inc(v_typeName_502_);
lean_del_object(v___x_514_);
lean_del_object(v___x_509_);
lean_dec_ref_known(v_e_285_, 3);
v___x_13341__overap_519_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg(v___x_302_, v___x_293_, v_typeName_502_, v_idx_503_, v_fst_511_);
v___x_520_ = lean_box(v_a_289_);
lean_inc_ref(v_a_290_);
v___x_521_ = lean_apply_4(v___x_13341__overap_519_, v_snd_512_, v___x_520_, v_a_290_, v_a_507_);
return v___x_521_;
}
else
{
lean_object* v___x_523_; 
lean_dec(v_fst_511_);
lean_dec_ref_known(v___x_302_, 3);
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 0, v_e_285_);
v___x_523_ = v___x_514_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v_e_285_);
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
lean_dec_ref_known(v_e_285_, 3);
lean_dec_ref_known(v___x_302_, 3);
return v___x_505_;
}
}
default: 
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_11780__overap_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
lean_dec_ref_known(v___x_302_, 3);
lean_dec_ref(v_fn_287_);
lean_dec(v_offset_286_);
lean_dec_ref(v_e_285_);
v___x_530_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__23, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__23_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__23);
v___x_531_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__27, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__27_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__27);
v___x_11780__overap_532_ = l_panic___redArg(v___x_530_, v___x_531_);
v___x_533_ = lean_box(v_a_289_);
lean_inc_ref(v_a_290_);
v___x_534_ = lean_apply_4(v___x_11780__overap_532_, v_a_288_, v___x_533_, v_a_290_, v_a_291_);
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
