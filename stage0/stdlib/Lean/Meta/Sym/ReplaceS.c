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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v_nbuckets_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_68_ = lean_array_get_size(v_data_67_);
v___x_69_ = lean_unsigned_to_nat(2u);
v_nbuckets_70_ = lean_nat_mul(v___x_68_, v___x_69_);
v___x_71_ = lean_unsigned_to_nat(0u);
v___x_72_ = lean_box(0);
v___x_73_ = lean_mk_array(v_nbuckets_70_, v___x_72_);
v___x_74_ = lean_array_propagate_mark(v_data_67_, v___x_73_);
v___x_75_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2___redArg(v___x_71_, v_data_67_, v___x_74_);
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
lean_object* v_key_79_; lean_object* v_value_80_; lean_object* v_tail_81_; lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_99_; 
v_key_79_ = lean_ctor_get(v_x_78_, 0);
v_value_80_ = lean_ctor_get(v_x_78_, 1);
v_tail_81_ = lean_ctor_get(v_x_78_, 2);
v_isSharedCheck_99_ = !lean_is_exclusive(v_x_78_);
if (v_isSharedCheck_99_ == 0)
{
v___x_83_ = v_x_78_;
v_isShared_84_ = v_isSharedCheck_99_;
goto v_resetjp_82_;
}
else
{
lean_inc(v_tail_81_);
lean_inc(v_value_80_);
lean_inc(v_key_79_);
lean_dec(v_x_78_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_99_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v_fst_90_; lean_object* v_snd_91_; lean_object* v_fst_92_; lean_object* v_snd_93_; size_t v___x_94_; size_t v___x_95_; uint8_t v___x_96_; 
v_fst_90_ = lean_ctor_get(v_key_79_, 0);
v_snd_91_ = lean_ctor_get(v_key_79_, 1);
v_fst_92_ = lean_ctor_get(v_a_76_, 0);
v_snd_93_ = lean_ctor_get(v_a_76_, 1);
v___x_94_ = lean_ptr_addr(v_fst_90_);
v___x_95_ = lean_ptr_addr(v_fst_92_);
v___x_96_ = lean_usize_dec_eq(v___x_94_, v___x_95_);
if (v___x_96_ == 0)
{
goto v___jp_85_;
}
else
{
uint8_t v___x_97_; 
v___x_97_ = lean_nat_dec_eq(v_snd_91_, v_snd_93_);
if (v___x_97_ == 0)
{
goto v___jp_85_;
}
else
{
lean_object* v___x_98_; 
lean_del_object(v___x_83_);
lean_dec(v_value_80_);
lean_dec(v_key_79_);
v___x_98_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_98_, 0, v_a_76_);
lean_ctor_set(v___x_98_, 1, v_b_77_);
lean_ctor_set(v___x_98_, 2, v_tail_81_);
return v___x_98_;
}
}
v___jp_85_:
{
lean_object* v___x_86_; lean_object* v___x_88_; 
v___x_86_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(v_a_76_, v_b_77_, v_tail_81_);
if (v_isShared_84_ == 0)
{
lean_ctor_set(v___x_83_, 2, v___x_86_);
v___x_88_ = v___x_83_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v_key_79_);
lean_ctor_set(v_reuseFailAlloc_89_, 1, v_value_80_);
lean_ctor_set(v_reuseFailAlloc_89_, 2, v___x_86_);
v___x_88_ = v_reuseFailAlloc_89_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
return v___x_88_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0___redArg(lean_object* v_m_100_, lean_object* v_a_101_, lean_object* v_b_102_){
_start:
{
lean_object* v_size_103_; lean_object* v_buckets_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_154_; 
v_size_103_ = lean_ctor_get(v_m_100_, 0);
v_buckets_104_ = lean_ctor_get(v_m_100_, 1);
v_isSharedCheck_154_ = !lean_is_exclusive(v_m_100_);
if (v_isSharedCheck_154_ == 0)
{
v___x_106_ = v_m_100_;
v_isShared_107_ = v_isSharedCheck_154_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_buckets_104_);
lean_inc(v_size_103_);
lean_dec(v_m_100_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_154_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v_fst_108_; lean_object* v_snd_109_; lean_object* v___x_110_; size_t v___x_111_; size_t v___x_112_; size_t v___x_113_; uint64_t v___x_114_; uint64_t v___x_115_; uint64_t v___x_116_; uint64_t v___x_117_; uint64_t v___x_118_; uint64_t v_fold_119_; uint64_t v___x_120_; uint64_t v___x_121_; uint64_t v___x_122_; size_t v___x_123_; size_t v___x_124_; size_t v___x_125_; size_t v___x_126_; size_t v___x_127_; lean_object* v_bkt_128_; uint8_t v___x_129_; 
v_fst_108_ = lean_ctor_get(v_a_101_, 0);
v_snd_109_ = lean_ctor_get(v_a_101_, 1);
v___x_110_ = lean_array_get_size(v_buckets_104_);
v___x_111_ = lean_ptr_addr(v_fst_108_);
v___x_112_ = ((size_t)3ULL);
v___x_113_ = lean_usize_shift_right(v___x_111_, v___x_112_);
v___x_114_ = lean_usize_to_uint64(v___x_113_);
v___x_115_ = lean_uint64_of_nat(v_snd_109_);
v___x_116_ = lean_uint64_mix_hash(v___x_114_, v___x_115_);
v___x_117_ = 32ULL;
v___x_118_ = lean_uint64_shift_right(v___x_116_, v___x_117_);
v_fold_119_ = lean_uint64_xor(v___x_116_, v___x_118_);
v___x_120_ = 16ULL;
v___x_121_ = lean_uint64_shift_right(v_fold_119_, v___x_120_);
v___x_122_ = lean_uint64_xor(v_fold_119_, v___x_121_);
v___x_123_ = lean_uint64_to_usize(v___x_122_);
v___x_124_ = lean_usize_of_nat(v___x_110_);
v___x_125_ = ((size_t)1ULL);
v___x_126_ = lean_usize_sub(v___x_124_, v___x_125_);
v___x_127_ = lean_usize_land(v___x_123_, v___x_126_);
v_bkt_128_ = lean_array_uget_borrowed(v_buckets_104_, v___x_127_);
v___x_129_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_a_101_, v_bkt_128_);
if (v___x_129_ == 0)
{
lean_object* v___x_130_; lean_object* v_size_x27_131_; lean_object* v___x_132_; lean_object* v_buckets_x27_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; uint8_t v___x_139_; 
v___x_130_ = lean_unsigned_to_nat(1u);
v_size_x27_131_ = lean_nat_add(v_size_103_, v___x_130_);
lean_dec(v_size_103_);
lean_inc(v_bkt_128_);
v___x_132_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_132_, 0, v_a_101_);
lean_ctor_set(v___x_132_, 1, v_b_102_);
lean_ctor_set(v___x_132_, 2, v_bkt_128_);
v_buckets_x27_133_ = lean_array_uset(v_buckets_104_, v___x_127_, v___x_132_);
v___x_134_ = lean_unsigned_to_nat(4u);
v___x_135_ = lean_nat_mul(v_size_x27_131_, v___x_134_);
v___x_136_ = lean_unsigned_to_nat(3u);
v___x_137_ = lean_nat_div(v___x_135_, v___x_136_);
lean_dec(v___x_135_);
v___x_138_ = lean_array_get_size(v_buckets_x27_133_);
v___x_139_ = lean_nat_dec_le(v___x_137_, v___x_138_);
lean_dec(v___x_137_);
if (v___x_139_ == 0)
{
lean_object* v_val_140_; lean_object* v___x_142_; 
v_val_140_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1___redArg(v_buckets_x27_133_);
if (v_isShared_107_ == 0)
{
lean_ctor_set(v___x_106_, 1, v_val_140_);
lean_ctor_set(v___x_106_, 0, v_size_x27_131_);
v___x_142_ = v___x_106_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v_size_x27_131_);
lean_ctor_set(v_reuseFailAlloc_143_, 1, v_val_140_);
v___x_142_ = v_reuseFailAlloc_143_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
return v___x_142_;
}
}
else
{
lean_object* v___x_145_; 
if (v_isShared_107_ == 0)
{
lean_ctor_set(v___x_106_, 1, v_buckets_x27_133_);
lean_ctor_set(v___x_106_, 0, v_size_x27_131_);
v___x_145_ = v___x_106_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_size_x27_131_);
lean_ctor_set(v_reuseFailAlloc_146_, 1, v_buckets_x27_133_);
v___x_145_ = v_reuseFailAlloc_146_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
return v___x_145_;
}
}
}
else
{
lean_object* v___x_147_; lean_object* v_buckets_x27_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_152_; 
lean_inc(v_bkt_128_);
v___x_147_ = lean_box(0);
v_buckets_x27_148_ = lean_array_uset(v_buckets_104_, v___x_127_, v___x_147_);
v___x_149_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(v_a_101_, v_b_102_, v_bkt_128_);
v___x_150_ = lean_array_uset(v_buckets_x27_148_, v___x_127_, v___x_149_);
if (v_isShared_107_ == 0)
{
lean_ctor_set(v___x_106_, 1, v___x_150_);
v___x_152_ = v___x_106_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v_size_103_);
lean_ctor_set(v_reuseFailAlloc_153_, 1, v___x_150_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
return v___x_152_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(lean_object* v_key_155_, lean_object* v_r_156_, lean_object* v_a_157_, lean_object* v_a_158_){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
lean_inc_ref(v_r_156_);
v___x_159_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_157_, v_key_155_, v_r_156_);
v___x_160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_160_, 0, v_r_156_);
lean_ctor_set(v___x_160_, 1, v___x_159_);
v___x_161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_161_, 0, v___x_160_);
lean_ctor_set(v___x_161_, 1, v_a_158_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(lean_object* v_key_162_, lean_object* v_r_163_, lean_object* v_a_164_, uint8_t v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(v_key_162_, v_r_163_, v_a_164_, v_a_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___boxed(lean_object* v_key_169_, lean_object* v_r_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_){
_start:
{
uint8_t v_a_boxed_175_; lean_object* v_res_176_; 
v_a_boxed_175_ = lean_unbox(v_a_172_);
v_res_176_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_169_, v_r_170_, v_a_171_, v_a_boxed_175_, v_a_173_, v_a_174_);
lean_dec_ref(v_a_173_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0(lean_object* v_00_u03b2_177_, lean_object* v_m_178_, lean_object* v_a_179_, lean_object* v_b_180_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0___redArg(v_m_178_, v_a_179_, v_b_180_);
return v___x_181_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0(lean_object* v_00_u03b2_182_, lean_object* v_a_183_, lean_object* v_x_184_){
_start:
{
uint8_t v___x_185_; 
v___x_185_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_a_183_, v_x_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0___boxed(lean_object* v_00_u03b2_186_, lean_object* v_a_187_, lean_object* v_x_188_){
_start:
{
uint8_t v_res_189_; lean_object* v_r_190_; 
v_res_189_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0(v_00_u03b2_186_, v_a_187_, v_x_188_);
lean_dec(v_x_188_);
lean_dec_ref(v_a_187_);
v_r_190_ = lean_box(v_res_189_);
return v_r_190_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1(lean_object* v_00_u03b2_191_, lean_object* v_data_192_){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1___redArg(v_data_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__2(lean_object* v_00_u03b2_194_, lean_object* v_a_195_, lean_object* v_b_196_, lean_object* v_x_197_){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(v_a_195_, v_b_196_, v_x_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_199_, lean_object* v_i_200_, lean_object* v_source_201_, lean_object* v_target_202_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2___redArg(v_i_200_, v_source_201_, v_target_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_204_, lean_object* v_x_205_, lean_object* v_x_206_){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3___redArg(v_x_205_, v_x_206_);
return v___x_207_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__4(void){
_start:
{
lean_object* v___x_214_; lean_object* v___f_215_; 
v___x_214_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___f_215_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_215_, 0, v___x_214_);
return v___f_215_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__5(void){
_start:
{
lean_object* v___f_216_; lean_object* v___f_217_; lean_object* v___f_218_; 
v___f_216_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__4, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__4_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__4);
v___f_217_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__0));
v___f_218_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_218_, 0, v___f_217_);
lean_closure_set(v___f_218_, 1, v___f_216_);
return v___f_218_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__10(void){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_238_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__9));
v___x_239_ = l_ReaderT_instMonad___redArg(v___x_238_);
return v___x_239_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11(void){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_240_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__10, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__10_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__10);
v___x_241_ = l_ReaderT_instMonad___redArg(v___x_240_);
return v___x_241_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20(void){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_242_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11);
v___x_243_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_243_, 0, lean_box(0));
lean_closure_set(v___x_243_, 1, lean_box(0));
lean_closure_set(v___x_243_, 2, v___x_242_);
return v___x_243_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__15(void){
_start:
{
lean_object* v___x_244_; lean_object* v___f_245_; 
v___x_244_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11);
v___f_245_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_245_, 0, v___x_244_);
return v___f_245_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__14(void){
_start:
{
lean_object* v___x_246_; lean_object* v___f_247_; 
v___x_246_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11);
v___f_247_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_247_, 0, v___x_246_);
return v___f_247_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__13(void){
_start:
{
lean_object* v___x_248_; lean_object* v___f_249_; 
v___x_248_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11);
v___f_249_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_249_, 0, v___x_248_);
return v___f_249_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__18(void){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_250_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11);
v___x_251_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_251_, 0, lean_box(0));
lean_closure_set(v___x_251_, 1, lean_box(0));
lean_closure_set(v___x_251_, 2, v___x_250_);
return v___x_251_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__12(void){
_start:
{
lean_object* v___x_252_; lean_object* v___f_253_; 
v___x_252_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11);
v___f_253_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_253_, 0, v___x_252_);
return v___f_253_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__16(void){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_254_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11);
v___x_255_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_255_, 0, lean_box(0));
lean_closure_set(v___x_255_, 1, lean_box(0));
lean_closure_set(v___x_255_, 2, v___x_254_);
return v___x_255_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__17(void){
_start:
{
lean_object* v___f_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v___f_256_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__12, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__12_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__12);
v___x_257_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__16, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__16_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__16);
v___x_258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_258_, 0, v___x_257_);
lean_ctor_set(v___x_258_, 1, v___f_256_);
return v___x_258_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__19(void){
_start:
{
lean_object* v___f_259_; lean_object* v___f_260_; lean_object* v___f_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v___f_259_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__15, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__15_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__15);
v___f_260_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__14, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__14_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__14);
v___f_261_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__13, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__13_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__13);
v___x_262_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__18, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__18_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__18);
v___x_263_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__17, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__17_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__17);
v___x_264_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
lean_ctor_set(v___x_264_, 1, v___x_262_);
lean_ctor_set(v___x_264_, 2, v___f_261_);
lean_ctor_set(v___x_264_, 3, v___f_260_);
lean_ctor_set(v___x_264_, 4, v___f_259_);
return v___x_264_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__21(void){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_265_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__20);
v___x_266_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__19, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__19_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__19);
v___x_267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_267_, 0, v___x_266_);
lean_ctor_set(v___x_267_, 1, v___x_265_);
return v___x_267_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__22(void){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_268_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11);
v___x_269_ = lean_alloc_closure((void*)(l_StateT_lift), 6, 3);
lean_closure_set(v___x_269_, 0, lean_box(0));
lean_closure_set(v___x_269_, 1, lean_box(0));
lean_closure_set(v___x_269_, 2, v___x_268_);
return v___x_269_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__23(void){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_270_ = l_Lean_instInhabitedExpr;
v___x_271_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__21, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__21_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__21);
v___x_272_ = l_instInhabitedOfMonad___redArg(v___x_271_, v___x_270_);
return v___x_272_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__27(void){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_276_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__26));
v___x_277_ = lean_unsigned_to_nat(67u);
v___x_278_ = lean_unsigned_to_nat(35u);
v___x_279_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__25));
v___x_280_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__24));
v___x_281_ = l_mkPanicMessageWithDecl(v___x_280_, v___x_279_, v___x_278_, v___x_277_, v___x_276_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit(lean_object* v_e_282_, lean_object* v_offset_283_, lean_object* v_fn_284_, lean_object* v_a_285_, uint8_t v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v_share1_292_; lean_object* v_assertShared_293_; lean_object* v_isDebugEnabled_294_; lean_object* v___x_295_; lean_object* v___f_296_; lean_object* v___f_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_289_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__11);
v___x_290_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__21, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__21_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__21);
v___x_291_ = l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM;
v_share1_292_ = lean_ctor_get(v___x_291_, 0);
v_assertShared_293_ = lean_ctor_get(v___x_291_, 1);
v_isDebugEnabled_294_ = lean_ctor_get(v___x_291_, 2);
v___x_295_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__22, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__22_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__22);
lean_inc(v_share1_292_);
v___f_296_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_296_, 0, v_share1_292_);
lean_closure_set(v___f_296_, 1, v___x_295_);
lean_inc(v_assertShared_293_);
v___f_297_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift___redArg___lam__1), 3, 2);
lean_closure_set(v___f_297_, 0, v_assertShared_293_);
lean_closure_set(v___f_297_, 1, v___x_295_);
lean_inc(v_isDebugEnabled_294_);
v___x_298_ = lean_alloc_closure((void*)(l_StateT_lift), 6, 5);
lean_closure_set(v___x_298_, 0, lean_box(0));
lean_closure_set(v___x_298_, 1, lean_box(0));
lean_closure_set(v___x_298_, 2, v___x_289_);
lean_closure_set(v___x_298_, 3, lean_box(0));
lean_closure_set(v___x_298_, 4, v_isDebugEnabled_294_);
v___x_299_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_299_, 0, v___f_296_);
lean_ctor_set(v___x_299_, 1, v___f_297_);
lean_ctor_set(v___x_299_, 2, v___x_298_);
switch(lean_obj_tag(v_e_282_))
{
case 5:
{
lean_object* v_fn_300_; lean_object* v_arg_301_; lean_object* v___x_302_; 
v_fn_300_ = lean_ctor_get(v_e_282_, 0);
v_arg_301_ = lean_ctor_get(v_e_282_, 1);
lean_inc_ref(v_fn_284_);
lean_inc(v_offset_283_);
lean_inc_ref(v_fn_300_);
v___x_302_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_fn_300_, v_offset_283_, v_fn_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_);
if (lean_obj_tag(v___x_302_) == 0)
{
lean_object* v_a_303_; lean_object* v_a_304_; lean_object* v_fst_305_; lean_object* v_snd_306_; lean_object* v___x_307_; 
v_a_303_ = lean_ctor_get(v___x_302_, 0);
lean_inc(v_a_303_);
v_a_304_ = lean_ctor_get(v___x_302_, 1);
lean_inc(v_a_304_);
lean_dec_ref_known(v___x_302_, 2);
v_fst_305_ = lean_ctor_get(v_a_303_, 0);
lean_inc(v_fst_305_);
v_snd_306_ = lean_ctor_get(v_a_303_, 1);
lean_inc(v_snd_306_);
lean_dec(v_a_303_);
lean_inc_ref(v_arg_301_);
v___x_307_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_arg_301_, v_offset_283_, v_fn_284_, v_snd_306_, v_a_286_, v_a_287_, v_a_304_);
if (lean_obj_tag(v___x_307_) == 0)
{
lean_object* v_a_308_; lean_object* v_a_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_337_; 
v_a_308_ = lean_ctor_get(v___x_307_, 0);
v_a_309_ = lean_ctor_get(v___x_307_, 1);
v_isSharedCheck_337_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_337_ == 0)
{
v___x_311_ = v___x_307_;
v_isShared_312_ = v_isSharedCheck_337_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_a_309_);
lean_inc(v_a_308_);
lean_dec(v___x_307_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_337_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v_fst_313_; lean_object* v_snd_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_336_; 
v_fst_313_ = lean_ctor_get(v_a_308_, 0);
v_snd_314_ = lean_ctor_get(v_a_308_, 1);
v_isSharedCheck_336_ = !lean_is_exclusive(v_a_308_);
if (v_isSharedCheck_336_ == 0)
{
v___x_316_ = v_a_308_;
v_isShared_317_ = v_isSharedCheck_336_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_snd_314_);
lean_inc(v_fst_313_);
lean_dec(v_a_308_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_336_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
size_t v___x_318_; size_t v___x_319_; uint8_t v___x_320_; 
v___x_318_ = lean_ptr_addr(v_fn_300_);
v___x_319_ = lean_ptr_addr(v_fst_305_);
v___x_320_ = lean_usize_dec_eq(v___x_318_, v___x_319_);
if (v___x_320_ == 0)
{
lean_object* v___x_12039__overap_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
lean_del_object(v___x_316_);
lean_del_object(v___x_311_);
lean_dec_ref_known(v_e_282_, 2);
v___x_12039__overap_321_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v___x_299_, v___x_290_, v_fst_305_, v_fst_313_);
v___x_322_ = lean_box(v_a_286_);
lean_inc_ref(v_a_287_);
v___x_323_ = lean_apply_4(v___x_12039__overap_321_, v_snd_314_, v___x_322_, v_a_287_, v_a_309_);
return v___x_323_;
}
else
{
size_t v___x_324_; size_t v___x_325_; uint8_t v___x_326_; 
v___x_324_ = lean_ptr_addr(v_arg_301_);
v___x_325_ = lean_ptr_addr(v_fst_313_);
v___x_326_ = lean_usize_dec_eq(v___x_324_, v___x_325_);
if (v___x_326_ == 0)
{
lean_object* v___x_12044__overap_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
lean_del_object(v___x_316_);
lean_del_object(v___x_311_);
lean_dec_ref_known(v_e_282_, 2);
v___x_12044__overap_327_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v___x_299_, v___x_290_, v_fst_305_, v_fst_313_);
v___x_328_ = lean_box(v_a_286_);
lean_inc_ref(v_a_287_);
v___x_329_ = lean_apply_4(v___x_12044__overap_327_, v_snd_314_, v___x_328_, v_a_287_, v_a_309_);
return v___x_329_;
}
else
{
lean_object* v___x_331_; 
lean_dec(v_fst_313_);
lean_dec(v_fst_305_);
lean_dec_ref_known(v___x_299_, 3);
if (v_isShared_317_ == 0)
{
lean_ctor_set(v___x_316_, 0, v_e_282_);
v___x_331_ = v___x_316_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v_e_282_);
lean_ctor_set(v_reuseFailAlloc_335_, 1, v_snd_314_);
v___x_331_ = v_reuseFailAlloc_335_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
lean_object* v___x_333_; 
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 0, v___x_331_);
v___x_333_ = v___x_311_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v___x_331_);
lean_ctor_set(v_reuseFailAlloc_334_, 1, v_a_309_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_305_);
lean_dec_ref_known(v_e_282_, 2);
lean_dec_ref_known(v___x_299_, 3);
return v___x_307_;
}
}
else
{
lean_dec_ref_known(v_e_282_, 2);
lean_dec_ref_known(v___x_299_, 3);
lean_dec_ref(v_fn_284_);
lean_dec(v_offset_283_);
return v___x_302_;
}
}
case 6:
{
lean_object* v_binderName_338_; lean_object* v_binderType_339_; lean_object* v_body_340_; uint8_t v_binderInfo_341_; lean_object* v___x_342_; 
v_binderName_338_ = lean_ctor_get(v_e_282_, 0);
v_binderType_339_ = lean_ctor_get(v_e_282_, 1);
v_body_340_ = lean_ctor_get(v_e_282_, 2);
v_binderInfo_341_ = lean_ctor_get_uint8(v_e_282_, sizeof(void*)*3 + 8);
lean_inc_ref(v_fn_284_);
lean_inc(v_offset_283_);
lean_inc_ref(v_binderType_339_);
v___x_342_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_binderType_339_, v_offset_283_, v_fn_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_);
if (lean_obj_tag(v___x_342_) == 0)
{
lean_object* v_a_343_; lean_object* v_a_344_; lean_object* v_fst_345_; lean_object* v_snd_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v_a_343_ = lean_ctor_get(v___x_342_, 0);
lean_inc(v_a_343_);
v_a_344_ = lean_ctor_get(v___x_342_, 1);
lean_inc(v_a_344_);
lean_dec_ref_known(v___x_342_, 2);
v_fst_345_ = lean_ctor_get(v_a_343_, 0);
lean_inc(v_fst_345_);
v_snd_346_ = lean_ctor_get(v_a_343_, 1);
lean_inc(v_snd_346_);
lean_dec(v_a_343_);
v___x_347_ = lean_unsigned_to_nat(1u);
v___x_348_ = lean_nat_add(v_offset_283_, v___x_347_);
lean_dec(v_offset_283_);
lean_inc_ref(v_body_340_);
v___x_349_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_body_340_, v___x_348_, v_fn_284_, v_snd_346_, v_a_286_, v_a_287_, v_a_344_);
if (lean_obj_tag(v___x_349_) == 0)
{
lean_object* v_a_350_; lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_379_; 
v_a_350_ = lean_ctor_get(v___x_349_, 0);
v_a_351_ = lean_ctor_get(v___x_349_, 1);
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_349_);
if (v_isSharedCheck_379_ == 0)
{
v___x_353_ = v___x_349_;
v_isShared_354_ = v_isSharedCheck_379_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_inc(v_a_350_);
lean_dec(v___x_349_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_379_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v_fst_355_; lean_object* v_snd_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_378_; 
v_fst_355_ = lean_ctor_get(v_a_350_, 0);
v_snd_356_ = lean_ctor_get(v_a_350_, 1);
v_isSharedCheck_378_ = !lean_is_exclusive(v_a_350_);
if (v_isSharedCheck_378_ == 0)
{
v___x_358_ = v_a_350_;
v_isShared_359_ = v_isSharedCheck_378_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_snd_356_);
lean_inc(v_fst_355_);
lean_dec(v_a_350_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_378_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
size_t v___x_360_; size_t v___x_361_; uint8_t v___x_362_; 
v___x_360_ = lean_ptr_addr(v_binderType_339_);
v___x_361_ = lean_ptr_addr(v_fst_345_);
v___x_362_ = lean_usize_dec_eq(v___x_360_, v___x_361_);
if (v___x_362_ == 0)
{
lean_object* v___x_12320__overap_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
lean_inc(v_binderName_338_);
lean_del_object(v___x_358_);
lean_del_object(v___x_353_);
lean_dec_ref_known(v_e_282_, 3);
v___x_12320__overap_363_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v___x_299_, v___x_290_, v_binderName_338_, v_binderInfo_341_, v_fst_345_, v_fst_355_);
v___x_364_ = lean_box(v_a_286_);
lean_inc_ref(v_a_287_);
v___x_365_ = lean_apply_4(v___x_12320__overap_363_, v_snd_356_, v___x_364_, v_a_287_, v_a_351_);
return v___x_365_;
}
else
{
size_t v___x_366_; size_t v___x_367_; uint8_t v___x_368_; 
v___x_366_ = lean_ptr_addr(v_body_340_);
v___x_367_ = lean_ptr_addr(v_fst_355_);
v___x_368_ = lean_usize_dec_eq(v___x_366_, v___x_367_);
if (v___x_368_ == 0)
{
lean_object* v___x_12325__overap_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
lean_inc(v_binderName_338_);
lean_del_object(v___x_358_);
lean_del_object(v___x_353_);
lean_dec_ref_known(v_e_282_, 3);
v___x_12325__overap_369_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v___x_299_, v___x_290_, v_binderName_338_, v_binderInfo_341_, v_fst_345_, v_fst_355_);
v___x_370_ = lean_box(v_a_286_);
lean_inc_ref(v_a_287_);
v___x_371_ = lean_apply_4(v___x_12325__overap_369_, v_snd_356_, v___x_370_, v_a_287_, v_a_351_);
return v___x_371_;
}
else
{
lean_object* v___x_373_; 
lean_dec(v_fst_355_);
lean_dec(v_fst_345_);
lean_dec_ref_known(v___x_299_, 3);
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 0, v_e_282_);
v___x_373_ = v___x_358_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_e_282_);
lean_ctor_set(v_reuseFailAlloc_377_, 1, v_snd_356_);
v___x_373_ = v_reuseFailAlloc_377_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
lean_object* v___x_375_; 
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 0, v___x_373_);
v___x_375_ = v___x_353_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v___x_373_);
lean_ctor_set(v_reuseFailAlloc_376_, 1, v_a_351_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
return v___x_375_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_345_);
lean_dec_ref_known(v_e_282_, 3);
lean_dec_ref_known(v___x_299_, 3);
return v___x_349_;
}
}
else
{
lean_dec_ref_known(v_e_282_, 3);
lean_dec_ref_known(v___x_299_, 3);
lean_dec_ref(v_fn_284_);
lean_dec(v_offset_283_);
return v___x_342_;
}
}
case 7:
{
lean_object* v_binderName_380_; lean_object* v_binderType_381_; lean_object* v_body_382_; uint8_t v_binderInfo_383_; lean_object* v___x_384_; 
v_binderName_380_ = lean_ctor_get(v_e_282_, 0);
v_binderType_381_ = lean_ctor_get(v_e_282_, 1);
v_body_382_ = lean_ctor_get(v_e_282_, 2);
v_binderInfo_383_ = lean_ctor_get_uint8(v_e_282_, sizeof(void*)*3 + 8);
lean_inc_ref(v_fn_284_);
lean_inc(v_offset_283_);
lean_inc_ref(v_binderType_381_);
v___x_384_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_binderType_381_, v_offset_283_, v_fn_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_);
if (lean_obj_tag(v___x_384_) == 0)
{
lean_object* v_a_385_; lean_object* v_a_386_; lean_object* v_fst_387_; lean_object* v_snd_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
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
v___x_389_ = lean_unsigned_to_nat(1u);
v___x_390_ = lean_nat_add(v_offset_283_, v___x_389_);
lean_dec(v_offset_283_);
lean_inc_ref(v_body_382_);
v___x_391_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_body_382_, v___x_390_, v_fn_284_, v_snd_388_, v_a_286_, v_a_287_, v_a_386_);
if (lean_obj_tag(v___x_391_) == 0)
{
lean_object* v_a_392_; lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_421_; 
v_a_392_ = lean_ctor_get(v___x_391_, 0);
v_a_393_ = lean_ctor_get(v___x_391_, 1);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_421_ == 0)
{
v___x_395_ = v___x_391_;
v_isShared_396_ = v_isSharedCheck_421_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_inc(v_a_392_);
lean_dec(v___x_391_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_421_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v_fst_397_; lean_object* v_snd_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_420_; 
v_fst_397_ = lean_ctor_get(v_a_392_, 0);
v_snd_398_ = lean_ctor_get(v_a_392_, 1);
v_isSharedCheck_420_ = !lean_is_exclusive(v_a_392_);
if (v_isSharedCheck_420_ == 0)
{
v___x_400_ = v_a_392_;
v_isShared_401_ = v_isSharedCheck_420_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_snd_398_);
lean_inc(v_fst_397_);
lean_dec(v_a_392_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_420_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
size_t v___x_402_; size_t v___x_403_; uint8_t v___x_404_; 
v___x_402_ = lean_ptr_addr(v_binderType_381_);
v___x_403_ = lean_ptr_addr(v_fst_387_);
v___x_404_ = lean_usize_dec_eq(v___x_402_, v___x_403_);
if (v___x_404_ == 0)
{
lean_object* v___x_12613__overap_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
lean_inc(v_binderName_380_);
lean_del_object(v___x_400_);
lean_del_object(v___x_395_);
lean_dec_ref_known(v_e_282_, 3);
v___x_12613__overap_405_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v___x_299_, v___x_290_, v_binderName_380_, v_binderInfo_383_, v_fst_387_, v_fst_397_);
v___x_406_ = lean_box(v_a_286_);
lean_inc_ref(v_a_287_);
v___x_407_ = lean_apply_4(v___x_12613__overap_405_, v_snd_398_, v___x_406_, v_a_287_, v_a_393_);
return v___x_407_;
}
else
{
size_t v___x_408_; size_t v___x_409_; uint8_t v___x_410_; 
v___x_408_ = lean_ptr_addr(v_body_382_);
v___x_409_ = lean_ptr_addr(v_fst_397_);
v___x_410_ = lean_usize_dec_eq(v___x_408_, v___x_409_);
if (v___x_410_ == 0)
{
lean_object* v___x_12618__overap_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
lean_inc(v_binderName_380_);
lean_del_object(v___x_400_);
lean_del_object(v___x_395_);
lean_dec_ref_known(v_e_282_, 3);
v___x_12618__overap_411_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v___x_299_, v___x_290_, v_binderName_380_, v_binderInfo_383_, v_fst_387_, v_fst_397_);
v___x_412_ = lean_box(v_a_286_);
lean_inc_ref(v_a_287_);
v___x_413_ = lean_apply_4(v___x_12618__overap_411_, v_snd_398_, v___x_412_, v_a_287_, v_a_393_);
return v___x_413_;
}
else
{
lean_object* v___x_415_; 
lean_dec(v_fst_397_);
lean_dec(v_fst_387_);
lean_dec_ref_known(v___x_299_, 3);
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 0, v_e_282_);
v___x_415_ = v___x_400_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_e_282_);
lean_ctor_set(v_reuseFailAlloc_419_, 1, v_snd_398_);
v___x_415_ = v_reuseFailAlloc_419_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
lean_object* v___x_417_; 
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 0, v___x_415_);
v___x_417_ = v___x_395_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v___x_415_);
lean_ctor_set(v_reuseFailAlloc_418_, 1, v_a_393_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
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
lean_dec_ref_known(v_e_282_, 3);
lean_dec_ref_known(v___x_299_, 3);
return v___x_391_;
}
}
else
{
lean_dec_ref_known(v_e_282_, 3);
lean_dec_ref_known(v___x_299_, 3);
lean_dec_ref(v_fn_284_);
lean_dec(v_offset_283_);
return v___x_384_;
}
}
case 8:
{
lean_object* v_declName_422_; lean_object* v_type_423_; lean_object* v_value_424_; lean_object* v_body_425_; uint8_t v_nondep_426_; lean_object* v___x_427_; 
v_declName_422_ = lean_ctor_get(v_e_282_, 0);
v_type_423_ = lean_ctor_get(v_e_282_, 1);
v_value_424_ = lean_ctor_get(v_e_282_, 2);
v_body_425_ = lean_ctor_get(v_e_282_, 3);
v_nondep_426_ = lean_ctor_get_uint8(v_e_282_, sizeof(void*)*4 + 8);
lean_inc_ref(v_fn_284_);
lean_inc(v_offset_283_);
lean_inc_ref(v_type_423_);
v___x_427_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_type_423_, v_offset_283_, v_fn_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_);
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
lean_inc_ref(v_fn_284_);
lean_inc(v_offset_283_);
lean_inc_ref(v_value_424_);
v___x_432_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_value_424_, v_offset_283_, v_fn_284_, v_snd_431_, v_a_286_, v_a_287_, v_a_429_);
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
v___x_438_ = lean_nat_add(v_offset_283_, v___x_437_);
lean_dec(v_offset_283_);
lean_inc_ref(v_body_425_);
v___x_439_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_body_425_, v___x_438_, v_fn_284_, v_snd_436_, v_a_286_, v_a_287_, v_a_434_);
if (lean_obj_tag(v___x_439_) == 0)
{
lean_object* v_a_440_; lean_object* v_a_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_475_; 
v_a_440_ = lean_ctor_get(v___x_439_, 0);
v_a_441_ = lean_ctor_get(v___x_439_, 1);
v_isSharedCheck_475_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_475_ == 0)
{
v___x_443_ = v___x_439_;
v_isShared_444_ = v_isSharedCheck_475_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_a_441_);
lean_inc(v_a_440_);
lean_dec(v___x_439_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_475_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v_fst_445_; lean_object* v_snd_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_474_; 
v_fst_445_ = lean_ctor_get(v_a_440_, 0);
v_snd_446_ = lean_ctor_get(v_a_440_, 1);
v_isSharedCheck_474_ = !lean_is_exclusive(v_a_440_);
if (v_isSharedCheck_474_ == 0)
{
v___x_448_ = v_a_440_;
v_isShared_449_ = v_isSharedCheck_474_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_snd_446_);
lean_inc(v_fst_445_);
lean_dec(v_a_440_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_474_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
size_t v___x_450_; size_t v___x_451_; uint8_t v___x_452_; 
v___x_450_ = lean_ptr_addr(v_type_423_);
v___x_451_ = lean_ptr_addr(v_fst_430_);
v___x_452_ = lean_usize_dec_eq(v___x_450_, v___x_451_);
if (v___x_452_ == 0)
{
lean_object* v___x_12951__overap_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
lean_inc(v_declName_422_);
lean_del_object(v___x_448_);
lean_del_object(v___x_443_);
lean_dec_ref_known(v_e_282_, 4);
v___x_12951__overap_453_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v___x_299_, v___x_290_, v_declName_422_, v_fst_430_, v_fst_435_, v_fst_445_, v_nondep_426_);
v___x_454_ = lean_box(v_a_286_);
lean_inc_ref(v_a_287_);
v___x_455_ = lean_apply_4(v___x_12951__overap_453_, v_snd_446_, v___x_454_, v_a_287_, v_a_441_);
return v___x_455_;
}
else
{
size_t v___x_456_; size_t v___x_457_; uint8_t v___x_458_; 
v___x_456_ = lean_ptr_addr(v_value_424_);
v___x_457_ = lean_ptr_addr(v_fst_435_);
v___x_458_ = lean_usize_dec_eq(v___x_456_, v___x_457_);
if (v___x_458_ == 0)
{
lean_object* v___x_12956__overap_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
lean_inc(v_declName_422_);
lean_del_object(v___x_448_);
lean_del_object(v___x_443_);
lean_dec_ref_known(v_e_282_, 4);
v___x_12956__overap_459_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v___x_299_, v___x_290_, v_declName_422_, v_fst_430_, v_fst_435_, v_fst_445_, v_nondep_426_);
v___x_460_ = lean_box(v_a_286_);
lean_inc_ref(v_a_287_);
v___x_461_ = lean_apply_4(v___x_12956__overap_459_, v_snd_446_, v___x_460_, v_a_287_, v_a_441_);
return v___x_461_;
}
else
{
size_t v___x_462_; size_t v___x_463_; uint8_t v___x_464_; 
v___x_462_ = lean_ptr_addr(v_body_425_);
v___x_463_ = lean_ptr_addr(v_fst_445_);
v___x_464_ = lean_usize_dec_eq(v___x_462_, v___x_463_);
if (v___x_464_ == 0)
{
lean_object* v___x_12961__overap_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
lean_inc(v_declName_422_);
lean_del_object(v___x_448_);
lean_del_object(v___x_443_);
lean_dec_ref_known(v_e_282_, 4);
v___x_12961__overap_465_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v___x_299_, v___x_290_, v_declName_422_, v_fst_430_, v_fst_435_, v_fst_445_, v_nondep_426_);
v___x_466_ = lean_box(v_a_286_);
lean_inc_ref(v_a_287_);
v___x_467_ = lean_apply_4(v___x_12961__overap_465_, v_snd_446_, v___x_466_, v_a_287_, v_a_441_);
return v___x_467_;
}
else
{
lean_object* v___x_469_; 
lean_dec(v_fst_445_);
lean_dec(v_fst_435_);
lean_dec(v_fst_430_);
lean_dec_ref_known(v___x_299_, 3);
if (v_isShared_449_ == 0)
{
lean_ctor_set(v___x_448_, 0, v_e_282_);
v___x_469_ = v___x_448_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v_e_282_);
lean_ctor_set(v_reuseFailAlloc_473_, 1, v_snd_446_);
v___x_469_ = v_reuseFailAlloc_473_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
lean_object* v___x_471_; 
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 0, v___x_469_);
v___x_471_ = v___x_443_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v___x_469_);
lean_ctor_set(v_reuseFailAlloc_472_, 1, v_a_441_);
v___x_471_ = v_reuseFailAlloc_472_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
return v___x_471_;
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
lean_dec_ref_known(v_e_282_, 4);
lean_dec_ref_known(v___x_299_, 3);
return v___x_439_;
}
}
else
{
lean_dec(v_fst_430_);
lean_dec_ref_known(v_e_282_, 4);
lean_dec_ref_known(v___x_299_, 3);
lean_dec_ref(v_fn_284_);
lean_dec(v_offset_283_);
return v___x_432_;
}
}
else
{
lean_dec_ref_known(v_e_282_, 4);
lean_dec_ref_known(v___x_299_, 3);
lean_dec_ref(v_fn_284_);
lean_dec(v_offset_283_);
return v___x_427_;
}
}
case 10:
{
lean_object* v_data_476_; lean_object* v_expr_477_; lean_object* v___x_478_; 
v_data_476_ = lean_ctor_get(v_e_282_, 0);
v_expr_477_ = lean_ctor_get(v_e_282_, 1);
lean_inc_ref(v_expr_477_);
v___x_478_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_expr_477_, v_offset_283_, v_fn_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_);
if (lean_obj_tag(v___x_478_) == 0)
{
lean_object* v_a_479_; lean_object* v_a_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_502_; 
v_a_479_ = lean_ctor_get(v___x_478_, 0);
v_a_480_ = lean_ctor_get(v___x_478_, 1);
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_502_ == 0)
{
v___x_482_ = v___x_478_;
v_isShared_483_ = v_isSharedCheck_502_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_a_480_);
lean_inc(v_a_479_);
lean_dec(v___x_478_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_502_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v_fst_484_; lean_object* v_snd_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_501_; 
v_fst_484_ = lean_ctor_get(v_a_479_, 0);
v_snd_485_ = lean_ctor_get(v_a_479_, 1);
v_isSharedCheck_501_ = !lean_is_exclusive(v_a_479_);
if (v_isSharedCheck_501_ == 0)
{
v___x_487_ = v_a_479_;
v_isShared_488_ = v_isSharedCheck_501_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_snd_485_);
lean_inc(v_fst_484_);
lean_dec(v_a_479_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_501_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
size_t v___x_489_; size_t v___x_490_; uint8_t v___x_491_; 
v___x_489_ = lean_ptr_addr(v_expr_477_);
v___x_490_ = lean_ptr_addr(v_fst_484_);
v___x_491_ = lean_usize_dec_eq(v___x_489_, v___x_490_);
if (v___x_491_ == 0)
{
lean_object* v___x_13248__overap_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
lean_inc(v_data_476_);
lean_del_object(v___x_487_);
lean_del_object(v___x_482_);
lean_dec_ref_known(v_e_282_, 2);
v___x_13248__overap_492_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg(v___x_299_, v___x_290_, v_data_476_, v_fst_484_);
v___x_493_ = lean_box(v_a_286_);
lean_inc_ref(v_a_287_);
v___x_494_ = lean_apply_4(v___x_13248__overap_492_, v_snd_485_, v___x_493_, v_a_287_, v_a_480_);
return v___x_494_;
}
else
{
lean_object* v___x_496_; 
lean_dec(v_fst_484_);
lean_dec_ref_known(v___x_299_, 3);
if (v_isShared_488_ == 0)
{
lean_ctor_set(v___x_487_, 0, v_e_282_);
v___x_496_ = v___x_487_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_e_282_);
lean_ctor_set(v_reuseFailAlloc_500_, 1, v_snd_485_);
v___x_496_ = v_reuseFailAlloc_500_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
lean_object* v___x_498_; 
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 0, v___x_496_);
v___x_498_ = v___x_482_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v___x_496_);
lean_ctor_set(v_reuseFailAlloc_499_, 1, v_a_480_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
return v___x_498_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_282_, 2);
lean_dec_ref_known(v___x_299_, 3);
return v___x_478_;
}
}
case 11:
{
lean_object* v_typeName_503_; lean_object* v_idx_504_; lean_object* v_struct_505_; lean_object* v___x_506_; 
v_typeName_503_ = lean_ctor_get(v_e_282_, 0);
v_idx_504_ = lean_ctor_get(v_e_282_, 1);
v_struct_505_ = lean_ctor_get(v_e_282_, 2);
lean_inc_ref(v_struct_505_);
v___x_506_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_struct_505_, v_offset_283_, v_fn_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_);
if (lean_obj_tag(v___x_506_) == 0)
{
lean_object* v_a_507_; lean_object* v_a_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_530_; 
v_a_507_ = lean_ctor_get(v___x_506_, 0);
v_a_508_ = lean_ctor_get(v___x_506_, 1);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_506_);
if (v_isSharedCheck_530_ == 0)
{
v___x_510_ = v___x_506_;
v_isShared_511_ = v_isSharedCheck_530_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_a_508_);
lean_inc(v_a_507_);
lean_dec(v___x_506_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_530_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v_fst_512_; lean_object* v_snd_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_529_; 
v_fst_512_ = lean_ctor_get(v_a_507_, 0);
v_snd_513_ = lean_ctor_get(v_a_507_, 1);
v_isSharedCheck_529_ = !lean_is_exclusive(v_a_507_);
if (v_isSharedCheck_529_ == 0)
{
v___x_515_ = v_a_507_;
v_isShared_516_ = v_isSharedCheck_529_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_snd_513_);
lean_inc(v_fst_512_);
lean_dec(v_a_507_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_529_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
size_t v___x_517_; size_t v___x_518_; uint8_t v___x_519_; 
v___x_517_ = lean_ptr_addr(v_struct_505_);
v___x_518_ = lean_ptr_addr(v_fst_512_);
v___x_519_ = lean_usize_dec_eq(v___x_517_, v___x_518_);
if (v___x_519_ == 0)
{
lean_object* v___x_13435__overap_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
lean_inc(v_idx_504_);
lean_inc(v_typeName_503_);
lean_del_object(v___x_515_);
lean_del_object(v___x_510_);
lean_dec_ref_known(v_e_282_, 3);
v___x_13435__overap_520_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg(v___x_299_, v___x_290_, v_typeName_503_, v_idx_504_, v_fst_512_);
v___x_521_ = lean_box(v_a_286_);
lean_inc_ref(v_a_287_);
v___x_522_ = lean_apply_4(v___x_13435__overap_520_, v_snd_513_, v___x_521_, v_a_287_, v_a_508_);
return v___x_522_;
}
else
{
lean_object* v___x_524_; 
lean_dec(v_fst_512_);
lean_dec_ref_known(v___x_299_, 3);
if (v_isShared_516_ == 0)
{
lean_ctor_set(v___x_515_, 0, v_e_282_);
v___x_524_ = v___x_515_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_e_282_);
lean_ctor_set(v_reuseFailAlloc_528_, 1, v_snd_513_);
v___x_524_ = v_reuseFailAlloc_528_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
lean_object* v___x_526_; 
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 0, v___x_524_);
v___x_526_ = v___x_510_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v___x_524_);
lean_ctor_set(v_reuseFailAlloc_527_, 1, v_a_508_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_282_, 3);
lean_dec_ref_known(v___x_299_, 3);
return v___x_506_;
}
}
default: 
{
lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_11862__overap_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
lean_dec_ref_known(v___x_299_, 3);
lean_dec_ref(v_fn_284_);
lean_dec(v_offset_283_);
lean_dec_ref(v_e_282_);
v___x_531_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__23, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__23_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__23);
v___x_532_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__27, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__27_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__27);
v___x_11862__overap_533_ = l_panic___redArg(v___x_531_, v___x_532_);
v___x_534_ = lean_box(v_a_286_);
lean_inc_ref(v_a_287_);
v___x_535_ = lean_apply_4(v___x_11862__overap_533_, v_a_285_, v___x_534_, v_a_287_, v_a_288_);
return v___x_535_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(lean_object* v_e_536_, lean_object* v_offset_537_, lean_object* v_f_538_, lean_object* v_a_539_, uint8_t v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_){
_start:
{
lean_object* v___f_543_; lean_object* v_key_544_; lean_object* v___f_545_; lean_object* v___x_546_; 
v___f_543_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__3));
lean_inc(v_offset_537_);
lean_inc_ref(v_e_536_);
v_key_544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_544_, 0, v_e_536_);
lean_ctor_set(v_key_544_, 1, v_offset_537_);
v___f_545_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__5, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__5_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__5);
lean_inc_ref(v_key_544_);
v___x_546_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_545_, v___f_543_, v_a_539_, v_key_544_);
if (lean_obj_tag(v___x_546_) == 1)
{
lean_object* v_val_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
lean_dec_ref_known(v_key_544_, 2);
lean_dec_ref(v_f_538_);
lean_dec(v_offset_537_);
lean_dec_ref(v_e_536_);
v_val_547_ = lean_ctor_get(v___x_546_, 0);
lean_inc(v_val_547_);
lean_dec_ref_known(v___x_546_, 1);
v___x_548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_548_, 0, v_val_547_);
lean_ctor_set(v___x_548_, 1, v_a_539_);
v___x_549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_549_, 0, v___x_548_);
lean_ctor_set(v___x_549_, 1, v_a_542_);
return v___x_549_;
}
else
{
lean_object* v___x_550_; lean_object* v___x_551_; 
lean_dec(v___x_546_);
v___x_550_ = lean_box(v_a_540_);
lean_inc_ref(v_f_538_);
lean_inc_ref(v_a_541_);
lean_inc(v_offset_537_);
lean_inc_ref(v_e_536_);
v___x_551_ = lean_apply_5(v_f_538_, v_e_536_, v_offset_537_, v___x_550_, v_a_541_, v_a_542_);
if (lean_obj_tag(v___x_551_) == 0)
{
lean_object* v_a_552_; 
v_a_552_ = lean_ctor_get(v___x_551_, 0);
lean_inc(v_a_552_);
if (lean_obj_tag(v_a_552_) == 1)
{
lean_object* v_a_553_; lean_object* v_val_554_; lean_object* v___x_555_; 
lean_dec_ref(v_f_538_);
lean_dec(v_offset_537_);
lean_dec_ref(v_e_536_);
v_a_553_ = lean_ctor_get(v___x_551_, 1);
lean_inc(v_a_553_);
lean_dec_ref_known(v___x_551_, 2);
v_val_554_ = lean_ctor_get(v_a_552_, 0);
lean_inc(v_val_554_);
lean_dec_ref_known(v_a_552_, 1);
v___x_555_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(v_key_544_, v_val_554_, v_a_539_, v_a_553_);
return v___x_555_;
}
else
{
lean_dec(v_a_552_);
switch(lean_obj_tag(v_e_536_))
{
case 9:
{
lean_object* v_a_556_; lean_object* v___x_557_; 
lean_dec_ref(v_f_538_);
lean_dec(v_offset_537_);
v_a_556_ = lean_ctor_get(v___x_551_, 1);
lean_inc(v_a_556_);
lean_dec_ref_known(v___x_551_, 2);
v___x_557_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(v_key_544_, v_e_536_, v_a_539_, v_a_556_);
return v___x_557_;
}
case 2:
{
lean_object* v_a_558_; lean_object* v___x_559_; 
lean_dec_ref(v_f_538_);
lean_dec(v_offset_537_);
v_a_558_ = lean_ctor_get(v___x_551_, 1);
lean_inc(v_a_558_);
lean_dec_ref_known(v___x_551_, 2);
v___x_559_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(v_key_544_, v_e_536_, v_a_539_, v_a_558_);
return v___x_559_;
}
case 0:
{
lean_object* v_a_560_; lean_object* v___x_561_; 
lean_dec_ref(v_f_538_);
lean_dec(v_offset_537_);
v_a_560_ = lean_ctor_get(v___x_551_, 1);
lean_inc(v_a_560_);
lean_dec_ref_known(v___x_551_, 2);
v___x_561_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(v_key_544_, v_e_536_, v_a_539_, v_a_560_);
return v___x_561_;
}
case 1:
{
lean_object* v_a_562_; lean_object* v___x_563_; 
lean_dec_ref(v_f_538_);
lean_dec(v_offset_537_);
v_a_562_ = lean_ctor_get(v___x_551_, 1);
lean_inc(v_a_562_);
lean_dec_ref_known(v___x_551_, 2);
v___x_563_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(v_key_544_, v_e_536_, v_a_539_, v_a_562_);
return v___x_563_;
}
case 4:
{
lean_object* v_a_564_; lean_object* v___x_565_; 
lean_dec_ref(v_f_538_);
lean_dec(v_offset_537_);
v_a_564_ = lean_ctor_get(v___x_551_, 1);
lean_inc(v_a_564_);
lean_dec_ref_known(v___x_551_, 2);
v___x_565_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(v_key_544_, v_e_536_, v_a_539_, v_a_564_);
return v___x_565_;
}
case 3:
{
lean_object* v_a_566_; lean_object* v___x_567_; 
lean_dec_ref(v_f_538_);
lean_dec(v_offset_537_);
v_a_566_ = lean_ctor_get(v___x_551_, 1);
lean_inc(v_a_566_);
lean_dec_ref_known(v___x_551_, 2);
v___x_567_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(v_key_544_, v_e_536_, v_a_539_, v_a_566_);
return v___x_567_;
}
default: 
{
lean_object* v_a_568_; lean_object* v___x_569_; 
v_a_568_ = lean_ctor_get(v___x_551_, 1);
lean_inc(v_a_568_);
lean_dec_ref_known(v___x_551_, 2);
v___x_569_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit(v_e_536_, v_offset_537_, v_f_538_, v_a_539_, v_a_540_, v_a_541_, v_a_568_);
if (lean_obj_tag(v___x_569_) == 0)
{
lean_object* v_a_570_; lean_object* v_a_571_; lean_object* v_fst_572_; lean_object* v_snd_573_; lean_object* v___x_574_; 
v_a_570_ = lean_ctor_get(v___x_569_, 0);
lean_inc(v_a_570_);
v_a_571_ = lean_ctor_get(v___x_569_, 1);
lean_inc(v_a_571_);
lean_dec_ref_known(v___x_569_, 2);
v_fst_572_ = lean_ctor_get(v_a_570_, 0);
lean_inc(v_fst_572_);
v_snd_573_ = lean_ctor_get(v_a_570_, 1);
lean_inc(v_snd_573_);
lean_dec(v_a_570_);
v___x_574_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(v_key_544_, v_fst_572_, v_snd_573_, v_a_571_);
return v___x_574_;
}
else
{
lean_dec_ref_known(v_key_544_, 2);
return v___x_569_;
}
}
}
}
}
else
{
lean_object* v_a_575_; lean_object* v_a_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_583_; 
lean_dec_ref_known(v_key_544_, 2);
lean_dec_ref(v_a_539_);
lean_dec_ref(v_f_538_);
lean_dec(v_offset_537_);
lean_dec_ref(v_e_536_);
v_a_575_ = lean_ctor_get(v___x_551_, 0);
v_a_576_ = lean_ctor_get(v___x_551_, 1);
v_isSharedCheck_583_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_583_ == 0)
{
v___x_578_ = v___x_551_;
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_a_576_);
lean_inc(v_a_575_);
lean_dec(v___x_551_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_581_; 
if (v_isShared_579_ == 0)
{
v___x_581_ = v___x_578_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_a_575_);
lean_ctor_set(v_reuseFailAlloc_582_, 1, v_a_576_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
return v___x_581_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___boxed(lean_object* v_e_584_, lean_object* v_offset_585_, lean_object* v_f_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_){
_start:
{
uint8_t v_a_boxed_591_; lean_object* v_res_592_; 
v_a_boxed_591_ = lean_unbox(v_a_588_);
v_res_592_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_e_584_, v_offset_585_, v_f_586_, v_a_587_, v_a_boxed_591_, v_a_589_, v_a_590_);
lean_dec_ref(v_a_589_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___boxed(lean_object* v_e_593_, lean_object* v_offset_594_, lean_object* v_fn_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_){
_start:
{
uint8_t v_a_boxed_600_; lean_object* v_res_601_; 
v_a_boxed_600_ = lean_unbox(v_a_597_);
v_res_601_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit(v_e_593_, v_offset_594_, v_fn_595_, v_a_596_, v_a_boxed_600_, v_a_598_, v_a_599_);
lean_dec_ref(v_a_598_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild_match__4_splitter___redArg(lean_object* v_____do__lift_602_, lean_object* v_h__1_603_, lean_object* v_h__2_604_){
_start:
{
if (lean_obj_tag(v_____do__lift_602_) == 1)
{
lean_object* v_val_605_; lean_object* v___x_606_; 
lean_dec(v_h__2_604_);
v_val_605_ = lean_ctor_get(v_____do__lift_602_, 0);
lean_inc(v_val_605_);
lean_dec_ref_known(v_____do__lift_602_, 1);
v___x_606_ = lean_apply_1(v_h__1_603_, v_val_605_);
return v___x_606_;
}
else
{
lean_object* v___x_607_; 
lean_dec(v_h__1_603_);
v___x_607_ = lean_apply_2(v_h__2_604_, v_____do__lift_602_, lean_box(0));
return v___x_607_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild_match__4_splitter(lean_object* v_motive_608_, lean_object* v_____do__lift_609_, lean_object* v_h__1_610_, lean_object* v_h__2_611_){
_start:
{
if (lean_obj_tag(v_____do__lift_609_) == 1)
{
lean_object* v_val_612_; lean_object* v___x_613_; 
lean_dec(v_h__2_611_);
v_val_612_ = lean_ctor_get(v_____do__lift_609_, 0);
lean_inc(v_val_612_);
lean_dec_ref_known(v_____do__lift_609_, 1);
v___x_613_ = lean_apply_1(v_h__1_610_, v_val_612_);
return v___x_613_;
}
else
{
lean_object* v___x_614_; 
lean_dec(v_h__1_610_);
v___x_614_ = lean_apply_2(v_h__2_611_, v_____do__lift_609_, lean_box(0));
return v___x_614_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild_match__1_splitter___redArg(lean_object* v_e_615_, lean_object* v_h__1_616_, lean_object* v_h__2_617_, lean_object* v_h__3_618_, lean_object* v_h__4_619_, lean_object* v_h__5_620_, lean_object* v_h__6_621_, lean_object* v_h__7_622_){
_start:
{
switch(lean_obj_tag(v_e_615_))
{
case 9:
{
lean_object* v_a_623_; lean_object* v___x_624_; 
lean_dec(v_h__7_622_);
lean_dec(v_h__6_621_);
lean_dec(v_h__5_620_);
lean_dec(v_h__4_619_);
lean_dec(v_h__3_618_);
lean_dec(v_h__2_617_);
v_a_623_ = lean_ctor_get(v_e_615_, 0);
lean_inc_ref(v_a_623_);
lean_dec_ref_known(v_e_615_, 1);
v___x_624_ = lean_apply_1(v_h__1_616_, v_a_623_);
return v___x_624_;
}
case 2:
{
lean_object* v_mvarId_625_; lean_object* v___x_626_; 
lean_dec(v_h__7_622_);
lean_dec(v_h__6_621_);
lean_dec(v_h__5_620_);
lean_dec(v_h__4_619_);
lean_dec(v_h__3_618_);
lean_dec(v_h__1_616_);
v_mvarId_625_ = lean_ctor_get(v_e_615_, 0);
lean_inc(v_mvarId_625_);
lean_dec_ref_known(v_e_615_, 1);
v___x_626_ = lean_apply_1(v_h__2_617_, v_mvarId_625_);
return v___x_626_;
}
case 0:
{
lean_object* v_deBruijnIndex_627_; lean_object* v___x_628_; 
lean_dec(v_h__7_622_);
lean_dec(v_h__6_621_);
lean_dec(v_h__5_620_);
lean_dec(v_h__4_619_);
lean_dec(v_h__2_617_);
lean_dec(v_h__1_616_);
v_deBruijnIndex_627_ = lean_ctor_get(v_e_615_, 0);
lean_inc(v_deBruijnIndex_627_);
lean_dec_ref_known(v_e_615_, 1);
v___x_628_ = lean_apply_1(v_h__3_618_, v_deBruijnIndex_627_);
return v___x_628_;
}
case 1:
{
lean_object* v_fvarId_629_; lean_object* v___x_630_; 
lean_dec(v_h__7_622_);
lean_dec(v_h__6_621_);
lean_dec(v_h__5_620_);
lean_dec(v_h__3_618_);
lean_dec(v_h__2_617_);
lean_dec(v_h__1_616_);
v_fvarId_629_ = lean_ctor_get(v_e_615_, 0);
lean_inc(v_fvarId_629_);
lean_dec_ref_known(v_e_615_, 1);
v___x_630_ = lean_apply_1(v_h__4_619_, v_fvarId_629_);
return v___x_630_;
}
case 4:
{
lean_object* v_declName_631_; lean_object* v_us_632_; lean_object* v___x_633_; 
lean_dec(v_h__7_622_);
lean_dec(v_h__6_621_);
lean_dec(v_h__4_619_);
lean_dec(v_h__3_618_);
lean_dec(v_h__2_617_);
lean_dec(v_h__1_616_);
v_declName_631_ = lean_ctor_get(v_e_615_, 0);
lean_inc(v_declName_631_);
v_us_632_ = lean_ctor_get(v_e_615_, 1);
lean_inc(v_us_632_);
lean_dec_ref_known(v_e_615_, 2);
v___x_633_ = lean_apply_2(v_h__5_620_, v_declName_631_, v_us_632_);
return v___x_633_;
}
case 3:
{
lean_object* v_u_634_; lean_object* v___x_635_; 
lean_dec(v_h__7_622_);
lean_dec(v_h__5_620_);
lean_dec(v_h__4_619_);
lean_dec(v_h__3_618_);
lean_dec(v_h__2_617_);
lean_dec(v_h__1_616_);
v_u_634_ = lean_ctor_get(v_e_615_, 0);
lean_inc(v_u_634_);
lean_dec_ref_known(v_e_615_, 1);
v___x_635_ = lean_apply_1(v_h__6_621_, v_u_634_);
return v___x_635_;
}
default: 
{
lean_object* v___x_636_; 
lean_dec(v_h__6_621_);
lean_dec(v_h__5_620_);
lean_dec(v_h__4_619_);
lean_dec(v_h__3_618_);
lean_dec(v_h__2_617_);
lean_dec(v_h__1_616_);
v___x_636_ = lean_apply_7(v_h__7_622_, v_e_615_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_636_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild_match__1_splitter(lean_object* v_motive_637_, lean_object* v_e_638_, lean_object* v_h__1_639_, lean_object* v_h__2_640_, lean_object* v_h__3_641_, lean_object* v_h__4_642_, lean_object* v_h__5_643_, lean_object* v_h__6_644_, lean_object* v_h__7_645_){
_start:
{
switch(lean_obj_tag(v_e_638_))
{
case 9:
{
lean_object* v_a_646_; lean_object* v___x_647_; 
lean_dec(v_h__7_645_);
lean_dec(v_h__6_644_);
lean_dec(v_h__5_643_);
lean_dec(v_h__4_642_);
lean_dec(v_h__3_641_);
lean_dec(v_h__2_640_);
v_a_646_ = lean_ctor_get(v_e_638_, 0);
lean_inc_ref(v_a_646_);
lean_dec_ref_known(v_e_638_, 1);
v___x_647_ = lean_apply_1(v_h__1_639_, v_a_646_);
return v___x_647_;
}
case 2:
{
lean_object* v_mvarId_648_; lean_object* v___x_649_; 
lean_dec(v_h__7_645_);
lean_dec(v_h__6_644_);
lean_dec(v_h__5_643_);
lean_dec(v_h__4_642_);
lean_dec(v_h__3_641_);
lean_dec(v_h__1_639_);
v_mvarId_648_ = lean_ctor_get(v_e_638_, 0);
lean_inc(v_mvarId_648_);
lean_dec_ref_known(v_e_638_, 1);
v___x_649_ = lean_apply_1(v_h__2_640_, v_mvarId_648_);
return v___x_649_;
}
case 0:
{
lean_object* v_deBruijnIndex_650_; lean_object* v___x_651_; 
lean_dec(v_h__7_645_);
lean_dec(v_h__6_644_);
lean_dec(v_h__5_643_);
lean_dec(v_h__4_642_);
lean_dec(v_h__2_640_);
lean_dec(v_h__1_639_);
v_deBruijnIndex_650_ = lean_ctor_get(v_e_638_, 0);
lean_inc(v_deBruijnIndex_650_);
lean_dec_ref_known(v_e_638_, 1);
v___x_651_ = lean_apply_1(v_h__3_641_, v_deBruijnIndex_650_);
return v___x_651_;
}
case 1:
{
lean_object* v_fvarId_652_; lean_object* v___x_653_; 
lean_dec(v_h__7_645_);
lean_dec(v_h__6_644_);
lean_dec(v_h__5_643_);
lean_dec(v_h__3_641_);
lean_dec(v_h__2_640_);
lean_dec(v_h__1_639_);
v_fvarId_652_ = lean_ctor_get(v_e_638_, 0);
lean_inc(v_fvarId_652_);
lean_dec_ref_known(v_e_638_, 1);
v___x_653_ = lean_apply_1(v_h__4_642_, v_fvarId_652_);
return v___x_653_;
}
case 4:
{
lean_object* v_declName_654_; lean_object* v_us_655_; lean_object* v___x_656_; 
lean_dec(v_h__7_645_);
lean_dec(v_h__6_644_);
lean_dec(v_h__4_642_);
lean_dec(v_h__3_641_);
lean_dec(v_h__2_640_);
lean_dec(v_h__1_639_);
v_declName_654_ = lean_ctor_get(v_e_638_, 0);
lean_inc(v_declName_654_);
v_us_655_ = lean_ctor_get(v_e_638_, 1);
lean_inc(v_us_655_);
lean_dec_ref_known(v_e_638_, 2);
v___x_656_ = lean_apply_2(v_h__5_643_, v_declName_654_, v_us_655_);
return v___x_656_;
}
case 3:
{
lean_object* v_u_657_; lean_object* v___x_658_; 
lean_dec(v_h__7_645_);
lean_dec(v_h__5_643_);
lean_dec(v_h__4_642_);
lean_dec(v_h__3_641_);
lean_dec(v_h__2_640_);
lean_dec(v_h__1_639_);
v_u_657_ = lean_ctor_get(v_e_638_, 0);
lean_inc(v_u_657_);
lean_dec_ref_known(v_e_638_, 1);
v___x_658_ = lean_apply_1(v_h__6_644_, v_u_657_);
return v___x_658_;
}
default: 
{
lean_object* v___x_659_; 
lean_dec(v_h__6_644_);
lean_dec(v_h__5_643_);
lean_dec(v_h__4_642_);
lean_dec(v_h__3_641_);
lean_dec(v_h__2_640_);
lean_dec(v_h__1_639_);
v___x_659_ = lean_apply_7(v_h__7_645_, v_e_638_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_659_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit_match__1_splitter___redArg(lean_object* v_e_660_, lean_object* v_h__1_661_, lean_object* v_h__2_662_, lean_object* v_h__3_663_, lean_object* v_h__4_664_, lean_object* v_h__5_665_, lean_object* v_h__6_666_, lean_object* v_h__7_667_, lean_object* v_h__8_668_, lean_object* v_h__9_669_, lean_object* v_h__10_670_, lean_object* v_h__11_671_, lean_object* v_h__12_672_){
_start:
{
switch(lean_obj_tag(v_e_660_))
{
case 0:
{
lean_object* v_deBruijnIndex_673_; lean_object* v___x_674_; 
lean_dec(v_h__12_672_);
lean_dec(v_h__11_671_);
lean_dec(v_h__10_670_);
lean_dec(v_h__9_669_);
lean_dec(v_h__8_668_);
lean_dec(v_h__7_667_);
lean_dec(v_h__6_666_);
lean_dec(v_h__5_665_);
lean_dec(v_h__4_664_);
lean_dec(v_h__2_662_);
lean_dec(v_h__1_661_);
v_deBruijnIndex_673_ = lean_ctor_get(v_e_660_, 0);
lean_inc(v_deBruijnIndex_673_);
lean_dec_ref_known(v_e_660_, 1);
v___x_674_ = lean_apply_1(v_h__3_663_, v_deBruijnIndex_673_);
return v___x_674_;
}
case 1:
{
lean_object* v_fvarId_675_; lean_object* v___x_676_; 
lean_dec(v_h__12_672_);
lean_dec(v_h__11_671_);
lean_dec(v_h__10_670_);
lean_dec(v_h__9_669_);
lean_dec(v_h__8_668_);
lean_dec(v_h__7_667_);
lean_dec(v_h__6_666_);
lean_dec(v_h__5_665_);
lean_dec(v_h__3_663_);
lean_dec(v_h__2_662_);
lean_dec(v_h__1_661_);
v_fvarId_675_ = lean_ctor_get(v_e_660_, 0);
lean_inc(v_fvarId_675_);
lean_dec_ref_known(v_e_660_, 1);
v___x_676_ = lean_apply_1(v_h__4_664_, v_fvarId_675_);
return v___x_676_;
}
case 2:
{
lean_object* v_mvarId_677_; lean_object* v___x_678_; 
lean_dec(v_h__12_672_);
lean_dec(v_h__11_671_);
lean_dec(v_h__10_670_);
lean_dec(v_h__9_669_);
lean_dec(v_h__8_668_);
lean_dec(v_h__7_667_);
lean_dec(v_h__6_666_);
lean_dec(v_h__5_665_);
lean_dec(v_h__4_664_);
lean_dec(v_h__3_663_);
lean_dec(v_h__1_661_);
v_mvarId_677_ = lean_ctor_get(v_e_660_, 0);
lean_inc(v_mvarId_677_);
lean_dec_ref_known(v_e_660_, 1);
v___x_678_ = lean_apply_1(v_h__2_662_, v_mvarId_677_);
return v___x_678_;
}
case 3:
{
lean_object* v_u_679_; lean_object* v___x_680_; 
lean_dec(v_h__12_672_);
lean_dec(v_h__11_671_);
lean_dec(v_h__10_670_);
lean_dec(v_h__9_669_);
lean_dec(v_h__8_668_);
lean_dec(v_h__7_667_);
lean_dec(v_h__5_665_);
lean_dec(v_h__4_664_);
lean_dec(v_h__3_663_);
lean_dec(v_h__2_662_);
lean_dec(v_h__1_661_);
v_u_679_ = lean_ctor_get(v_e_660_, 0);
lean_inc(v_u_679_);
lean_dec_ref_known(v_e_660_, 1);
v___x_680_ = lean_apply_1(v_h__6_666_, v_u_679_);
return v___x_680_;
}
case 4:
{
lean_object* v_declName_681_; lean_object* v_us_682_; lean_object* v___x_683_; 
lean_dec(v_h__12_672_);
lean_dec(v_h__11_671_);
lean_dec(v_h__10_670_);
lean_dec(v_h__9_669_);
lean_dec(v_h__8_668_);
lean_dec(v_h__7_667_);
lean_dec(v_h__6_666_);
lean_dec(v_h__4_664_);
lean_dec(v_h__3_663_);
lean_dec(v_h__2_662_);
lean_dec(v_h__1_661_);
v_declName_681_ = lean_ctor_get(v_e_660_, 0);
lean_inc(v_declName_681_);
v_us_682_ = lean_ctor_get(v_e_660_, 1);
lean_inc(v_us_682_);
lean_dec_ref_known(v_e_660_, 2);
v___x_683_ = lean_apply_2(v_h__5_665_, v_declName_681_, v_us_682_);
return v___x_683_;
}
case 5:
{
lean_object* v_fn_684_; lean_object* v_arg_685_; lean_object* v___x_686_; 
lean_dec(v_h__12_672_);
lean_dec(v_h__11_671_);
lean_dec(v_h__10_670_);
lean_dec(v_h__9_669_);
lean_dec(v_h__8_668_);
lean_dec(v_h__6_666_);
lean_dec(v_h__5_665_);
lean_dec(v_h__4_664_);
lean_dec(v_h__3_663_);
lean_dec(v_h__2_662_);
lean_dec(v_h__1_661_);
v_fn_684_ = lean_ctor_get(v_e_660_, 0);
lean_inc_ref(v_fn_684_);
v_arg_685_ = lean_ctor_get(v_e_660_, 1);
lean_inc_ref(v_arg_685_);
lean_dec_ref_known(v_e_660_, 2);
v___x_686_ = lean_apply_2(v_h__7_667_, v_fn_684_, v_arg_685_);
return v___x_686_;
}
case 6:
{
lean_object* v_binderName_687_; lean_object* v_binderType_688_; lean_object* v_body_689_; uint8_t v_binderInfo_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
lean_dec(v_h__12_672_);
lean_dec(v_h__10_670_);
lean_dec(v_h__9_669_);
lean_dec(v_h__8_668_);
lean_dec(v_h__7_667_);
lean_dec(v_h__6_666_);
lean_dec(v_h__5_665_);
lean_dec(v_h__4_664_);
lean_dec(v_h__3_663_);
lean_dec(v_h__2_662_);
lean_dec(v_h__1_661_);
v_binderName_687_ = lean_ctor_get(v_e_660_, 0);
lean_inc(v_binderName_687_);
v_binderType_688_ = lean_ctor_get(v_e_660_, 1);
lean_inc_ref(v_binderType_688_);
v_body_689_ = lean_ctor_get(v_e_660_, 2);
lean_inc_ref(v_body_689_);
v_binderInfo_690_ = lean_ctor_get_uint8(v_e_660_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_660_, 3);
v___x_691_ = lean_box(v_binderInfo_690_);
v___x_692_ = lean_apply_4(v_h__11_671_, v_binderName_687_, v_binderType_688_, v_body_689_, v___x_691_);
return v___x_692_;
}
case 7:
{
lean_object* v_binderName_693_; lean_object* v_binderType_694_; lean_object* v_body_695_; uint8_t v_binderInfo_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
lean_dec(v_h__12_672_);
lean_dec(v_h__11_671_);
lean_dec(v_h__9_669_);
lean_dec(v_h__8_668_);
lean_dec(v_h__7_667_);
lean_dec(v_h__6_666_);
lean_dec(v_h__5_665_);
lean_dec(v_h__4_664_);
lean_dec(v_h__3_663_);
lean_dec(v_h__2_662_);
lean_dec(v_h__1_661_);
v_binderName_693_ = lean_ctor_get(v_e_660_, 0);
lean_inc(v_binderName_693_);
v_binderType_694_ = lean_ctor_get(v_e_660_, 1);
lean_inc_ref(v_binderType_694_);
v_body_695_ = lean_ctor_get(v_e_660_, 2);
lean_inc_ref(v_body_695_);
v_binderInfo_696_ = lean_ctor_get_uint8(v_e_660_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_660_, 3);
v___x_697_ = lean_box(v_binderInfo_696_);
v___x_698_ = lean_apply_4(v_h__10_670_, v_binderName_693_, v_binderType_694_, v_body_695_, v___x_697_);
return v___x_698_;
}
case 8:
{
lean_object* v_declName_699_; lean_object* v_type_700_; lean_object* v_value_701_; lean_object* v_body_702_; uint8_t v_nondep_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
lean_dec(v_h__11_671_);
lean_dec(v_h__10_670_);
lean_dec(v_h__9_669_);
lean_dec(v_h__8_668_);
lean_dec(v_h__7_667_);
lean_dec(v_h__6_666_);
lean_dec(v_h__5_665_);
lean_dec(v_h__4_664_);
lean_dec(v_h__3_663_);
lean_dec(v_h__2_662_);
lean_dec(v_h__1_661_);
v_declName_699_ = lean_ctor_get(v_e_660_, 0);
lean_inc(v_declName_699_);
v_type_700_ = lean_ctor_get(v_e_660_, 1);
lean_inc_ref(v_type_700_);
v_value_701_ = lean_ctor_get(v_e_660_, 2);
lean_inc_ref(v_value_701_);
v_body_702_ = lean_ctor_get(v_e_660_, 3);
lean_inc_ref(v_body_702_);
v_nondep_703_ = lean_ctor_get_uint8(v_e_660_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_660_, 4);
v___x_704_ = lean_box(v_nondep_703_);
v___x_705_ = lean_apply_5(v_h__12_672_, v_declName_699_, v_type_700_, v_value_701_, v_body_702_, v___x_704_);
return v___x_705_;
}
case 9:
{
lean_object* v_a_706_; lean_object* v___x_707_; 
lean_dec(v_h__12_672_);
lean_dec(v_h__11_671_);
lean_dec(v_h__10_670_);
lean_dec(v_h__9_669_);
lean_dec(v_h__8_668_);
lean_dec(v_h__7_667_);
lean_dec(v_h__6_666_);
lean_dec(v_h__5_665_);
lean_dec(v_h__4_664_);
lean_dec(v_h__3_663_);
lean_dec(v_h__2_662_);
v_a_706_ = lean_ctor_get(v_e_660_, 0);
lean_inc_ref(v_a_706_);
lean_dec_ref_known(v_e_660_, 1);
v___x_707_ = lean_apply_1(v_h__1_661_, v_a_706_);
return v___x_707_;
}
case 10:
{
lean_object* v_data_708_; lean_object* v_expr_709_; lean_object* v___x_710_; 
lean_dec(v_h__12_672_);
lean_dec(v_h__11_671_);
lean_dec(v_h__10_670_);
lean_dec(v_h__9_669_);
lean_dec(v_h__7_667_);
lean_dec(v_h__6_666_);
lean_dec(v_h__5_665_);
lean_dec(v_h__4_664_);
lean_dec(v_h__3_663_);
lean_dec(v_h__2_662_);
lean_dec(v_h__1_661_);
v_data_708_ = lean_ctor_get(v_e_660_, 0);
lean_inc(v_data_708_);
v_expr_709_ = lean_ctor_get(v_e_660_, 1);
lean_inc_ref(v_expr_709_);
lean_dec_ref_known(v_e_660_, 2);
v___x_710_ = lean_apply_2(v_h__8_668_, v_data_708_, v_expr_709_);
return v___x_710_;
}
default: 
{
lean_object* v_typeName_711_; lean_object* v_idx_712_; lean_object* v_struct_713_; lean_object* v___x_714_; 
lean_dec(v_h__12_672_);
lean_dec(v_h__11_671_);
lean_dec(v_h__10_670_);
lean_dec(v_h__8_668_);
lean_dec(v_h__7_667_);
lean_dec(v_h__6_666_);
lean_dec(v_h__5_665_);
lean_dec(v_h__4_664_);
lean_dec(v_h__3_663_);
lean_dec(v_h__2_662_);
lean_dec(v_h__1_661_);
v_typeName_711_ = lean_ctor_get(v_e_660_, 0);
lean_inc(v_typeName_711_);
v_idx_712_ = lean_ctor_get(v_e_660_, 1);
lean_inc(v_idx_712_);
v_struct_713_ = lean_ctor_get(v_e_660_, 2);
lean_inc_ref(v_struct_713_);
lean_dec_ref_known(v_e_660_, 3);
v___x_714_ = lean_apply_3(v_h__9_669_, v_typeName_711_, v_idx_712_, v_struct_713_);
return v___x_714_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit_match__1_splitter(lean_object* v_motive_715_, lean_object* v_e_716_, lean_object* v_h__1_717_, lean_object* v_h__2_718_, lean_object* v_h__3_719_, lean_object* v_h__4_720_, lean_object* v_h__5_721_, lean_object* v_h__6_722_, lean_object* v_h__7_723_, lean_object* v_h__8_724_, lean_object* v_h__9_725_, lean_object* v_h__10_726_, lean_object* v_h__11_727_, lean_object* v_h__12_728_){
_start:
{
switch(lean_obj_tag(v_e_716_))
{
case 0:
{
lean_object* v_deBruijnIndex_729_; lean_object* v___x_730_; 
lean_dec(v_h__12_728_);
lean_dec(v_h__11_727_);
lean_dec(v_h__10_726_);
lean_dec(v_h__9_725_);
lean_dec(v_h__8_724_);
lean_dec(v_h__7_723_);
lean_dec(v_h__6_722_);
lean_dec(v_h__5_721_);
lean_dec(v_h__4_720_);
lean_dec(v_h__2_718_);
lean_dec(v_h__1_717_);
v_deBruijnIndex_729_ = lean_ctor_get(v_e_716_, 0);
lean_inc(v_deBruijnIndex_729_);
lean_dec_ref_known(v_e_716_, 1);
v___x_730_ = lean_apply_1(v_h__3_719_, v_deBruijnIndex_729_);
return v___x_730_;
}
case 1:
{
lean_object* v_fvarId_731_; lean_object* v___x_732_; 
lean_dec(v_h__12_728_);
lean_dec(v_h__11_727_);
lean_dec(v_h__10_726_);
lean_dec(v_h__9_725_);
lean_dec(v_h__8_724_);
lean_dec(v_h__7_723_);
lean_dec(v_h__6_722_);
lean_dec(v_h__5_721_);
lean_dec(v_h__3_719_);
lean_dec(v_h__2_718_);
lean_dec(v_h__1_717_);
v_fvarId_731_ = lean_ctor_get(v_e_716_, 0);
lean_inc(v_fvarId_731_);
lean_dec_ref_known(v_e_716_, 1);
v___x_732_ = lean_apply_1(v_h__4_720_, v_fvarId_731_);
return v___x_732_;
}
case 2:
{
lean_object* v_mvarId_733_; lean_object* v___x_734_; 
lean_dec(v_h__12_728_);
lean_dec(v_h__11_727_);
lean_dec(v_h__10_726_);
lean_dec(v_h__9_725_);
lean_dec(v_h__8_724_);
lean_dec(v_h__7_723_);
lean_dec(v_h__6_722_);
lean_dec(v_h__5_721_);
lean_dec(v_h__4_720_);
lean_dec(v_h__3_719_);
lean_dec(v_h__1_717_);
v_mvarId_733_ = lean_ctor_get(v_e_716_, 0);
lean_inc(v_mvarId_733_);
lean_dec_ref_known(v_e_716_, 1);
v___x_734_ = lean_apply_1(v_h__2_718_, v_mvarId_733_);
return v___x_734_;
}
case 3:
{
lean_object* v_u_735_; lean_object* v___x_736_; 
lean_dec(v_h__12_728_);
lean_dec(v_h__11_727_);
lean_dec(v_h__10_726_);
lean_dec(v_h__9_725_);
lean_dec(v_h__8_724_);
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
case 4:
{
lean_object* v_declName_737_; lean_object* v_us_738_; lean_object* v___x_739_; 
lean_dec(v_h__12_728_);
lean_dec(v_h__11_727_);
lean_dec(v_h__10_726_);
lean_dec(v_h__9_725_);
lean_dec(v_h__8_724_);
lean_dec(v_h__7_723_);
lean_dec(v_h__6_722_);
lean_dec(v_h__4_720_);
lean_dec(v_h__3_719_);
lean_dec(v_h__2_718_);
lean_dec(v_h__1_717_);
v_declName_737_ = lean_ctor_get(v_e_716_, 0);
lean_inc(v_declName_737_);
v_us_738_ = lean_ctor_get(v_e_716_, 1);
lean_inc(v_us_738_);
lean_dec_ref_known(v_e_716_, 2);
v___x_739_ = lean_apply_2(v_h__5_721_, v_declName_737_, v_us_738_);
return v___x_739_;
}
case 5:
{
lean_object* v_fn_740_; lean_object* v_arg_741_; lean_object* v___x_742_; 
lean_dec(v_h__12_728_);
lean_dec(v_h__11_727_);
lean_dec(v_h__10_726_);
lean_dec(v_h__9_725_);
lean_dec(v_h__8_724_);
lean_dec(v_h__6_722_);
lean_dec(v_h__5_721_);
lean_dec(v_h__4_720_);
lean_dec(v_h__3_719_);
lean_dec(v_h__2_718_);
lean_dec(v_h__1_717_);
v_fn_740_ = lean_ctor_get(v_e_716_, 0);
lean_inc_ref(v_fn_740_);
v_arg_741_ = lean_ctor_get(v_e_716_, 1);
lean_inc_ref(v_arg_741_);
lean_dec_ref_known(v_e_716_, 2);
v___x_742_ = lean_apply_2(v_h__7_723_, v_fn_740_, v_arg_741_);
return v___x_742_;
}
case 6:
{
lean_object* v_binderName_743_; lean_object* v_binderType_744_; lean_object* v_body_745_; uint8_t v_binderInfo_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
lean_dec(v_h__12_728_);
lean_dec(v_h__10_726_);
lean_dec(v_h__9_725_);
lean_dec(v_h__8_724_);
lean_dec(v_h__7_723_);
lean_dec(v_h__6_722_);
lean_dec(v_h__5_721_);
lean_dec(v_h__4_720_);
lean_dec(v_h__3_719_);
lean_dec(v_h__2_718_);
lean_dec(v_h__1_717_);
v_binderName_743_ = lean_ctor_get(v_e_716_, 0);
lean_inc(v_binderName_743_);
v_binderType_744_ = lean_ctor_get(v_e_716_, 1);
lean_inc_ref(v_binderType_744_);
v_body_745_ = lean_ctor_get(v_e_716_, 2);
lean_inc_ref(v_body_745_);
v_binderInfo_746_ = lean_ctor_get_uint8(v_e_716_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_716_, 3);
v___x_747_ = lean_box(v_binderInfo_746_);
v___x_748_ = lean_apply_4(v_h__11_727_, v_binderName_743_, v_binderType_744_, v_body_745_, v___x_747_);
return v___x_748_;
}
case 7:
{
lean_object* v_binderName_749_; lean_object* v_binderType_750_; lean_object* v_body_751_; uint8_t v_binderInfo_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
lean_dec(v_h__12_728_);
lean_dec(v_h__11_727_);
lean_dec(v_h__9_725_);
lean_dec(v_h__8_724_);
lean_dec(v_h__7_723_);
lean_dec(v_h__6_722_);
lean_dec(v_h__5_721_);
lean_dec(v_h__4_720_);
lean_dec(v_h__3_719_);
lean_dec(v_h__2_718_);
lean_dec(v_h__1_717_);
v_binderName_749_ = lean_ctor_get(v_e_716_, 0);
lean_inc(v_binderName_749_);
v_binderType_750_ = lean_ctor_get(v_e_716_, 1);
lean_inc_ref(v_binderType_750_);
v_body_751_ = lean_ctor_get(v_e_716_, 2);
lean_inc_ref(v_body_751_);
v_binderInfo_752_ = lean_ctor_get_uint8(v_e_716_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_716_, 3);
v___x_753_ = lean_box(v_binderInfo_752_);
v___x_754_ = lean_apply_4(v_h__10_726_, v_binderName_749_, v_binderType_750_, v_body_751_, v___x_753_);
return v___x_754_;
}
case 8:
{
lean_object* v_declName_755_; lean_object* v_type_756_; lean_object* v_value_757_; lean_object* v_body_758_; uint8_t v_nondep_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
lean_dec(v_h__11_727_);
lean_dec(v_h__10_726_);
lean_dec(v_h__9_725_);
lean_dec(v_h__8_724_);
lean_dec(v_h__7_723_);
lean_dec(v_h__6_722_);
lean_dec(v_h__5_721_);
lean_dec(v_h__4_720_);
lean_dec(v_h__3_719_);
lean_dec(v_h__2_718_);
lean_dec(v_h__1_717_);
v_declName_755_ = lean_ctor_get(v_e_716_, 0);
lean_inc(v_declName_755_);
v_type_756_ = lean_ctor_get(v_e_716_, 1);
lean_inc_ref(v_type_756_);
v_value_757_ = lean_ctor_get(v_e_716_, 2);
lean_inc_ref(v_value_757_);
v_body_758_ = lean_ctor_get(v_e_716_, 3);
lean_inc_ref(v_body_758_);
v_nondep_759_ = lean_ctor_get_uint8(v_e_716_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_716_, 4);
v___x_760_ = lean_box(v_nondep_759_);
v___x_761_ = lean_apply_5(v_h__12_728_, v_declName_755_, v_type_756_, v_value_757_, v_body_758_, v___x_760_);
return v___x_761_;
}
case 9:
{
lean_object* v_a_762_; lean_object* v___x_763_; 
lean_dec(v_h__12_728_);
lean_dec(v_h__11_727_);
lean_dec(v_h__10_726_);
lean_dec(v_h__9_725_);
lean_dec(v_h__8_724_);
lean_dec(v_h__7_723_);
lean_dec(v_h__6_722_);
lean_dec(v_h__5_721_);
lean_dec(v_h__4_720_);
lean_dec(v_h__3_719_);
lean_dec(v_h__2_718_);
v_a_762_ = lean_ctor_get(v_e_716_, 0);
lean_inc_ref(v_a_762_);
lean_dec_ref_known(v_e_716_, 1);
v___x_763_ = lean_apply_1(v_h__1_717_, v_a_762_);
return v___x_763_;
}
case 10:
{
lean_object* v_data_764_; lean_object* v_expr_765_; lean_object* v___x_766_; 
lean_dec(v_h__12_728_);
lean_dec(v_h__11_727_);
lean_dec(v_h__10_726_);
lean_dec(v_h__9_725_);
lean_dec(v_h__7_723_);
lean_dec(v_h__6_722_);
lean_dec(v_h__5_721_);
lean_dec(v_h__4_720_);
lean_dec(v_h__3_719_);
lean_dec(v_h__2_718_);
lean_dec(v_h__1_717_);
v_data_764_ = lean_ctor_get(v_e_716_, 0);
lean_inc(v_data_764_);
v_expr_765_ = lean_ctor_get(v_e_716_, 1);
lean_inc_ref(v_expr_765_);
lean_dec_ref_known(v_e_716_, 2);
v___x_766_ = lean_apply_2(v_h__8_724_, v_data_764_, v_expr_765_);
return v___x_766_;
}
default: 
{
lean_object* v_typeName_767_; lean_object* v_idx_768_; lean_object* v_struct_769_; lean_object* v___x_770_; 
lean_dec(v_h__12_728_);
lean_dec(v_h__11_727_);
lean_dec(v_h__10_726_);
lean_dec(v_h__8_724_);
lean_dec(v_h__7_723_);
lean_dec(v_h__6_722_);
lean_dec(v_h__5_721_);
lean_dec(v_h__4_720_);
lean_dec(v_h__3_719_);
lean_dec(v_h__2_718_);
lean_dec(v_h__1_717_);
v_typeName_767_ = lean_ctor_get(v_e_716_, 0);
lean_inc(v_typeName_767_);
v_idx_768_ = lean_ctor_get(v_e_716_, 1);
lean_inc(v_idx_768_);
v_struct_769_ = lean_ctor_get(v_e_716_, 2);
lean_inc_ref(v_struct_769_);
lean_dec_ref_known(v_e_716_, 3);
v___x_770_ = lean_apply_3(v_h__9_725_, v_typeName_767_, v_idx_768_, v_struct_769_);
return v___x_770_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Sym_replaceS_x27___closed__0(void){
_start:
{
lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_771_ = lean_box(0);
v___x_772_ = lean_unsigned_to_nat(16u);
v___x_773_ = lean_mk_array(v___x_772_, v___x_771_);
return v___x_773_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_replaceS_x27___closed__1(void){
_start:
{
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_774_ = lean_obj_once(&l_Lean_Meta_Sym_replaceS_x27___closed__0, &l_Lean_Meta_Sym_replaceS_x27___closed__0_once, _init_l_Lean_Meta_Sym_replaceS_x27___closed__0);
v___x_775_ = lean_unsigned_to_nat(0u);
v___x_776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_776_, 0, v___x_775_);
lean_ctor_set(v___x_776_, 1, v___x_774_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_replaceS_x27(lean_object* v_e_777_, lean_object* v_f_778_, uint8_t v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_){
_start:
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_782_ = lean_unsigned_to_nat(0u);
v___x_783_ = lean_box(v_a_779_);
lean_inc_ref(v_f_778_);
lean_inc_ref(v_a_780_);
lean_inc_ref(v_e_777_);
v___x_784_ = lean_apply_5(v_f_778_, v_e_777_, v___x_782_, v___x_783_, v_a_780_, v_a_781_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_object* v_a_785_; 
v_a_785_ = lean_ctor_get(v___x_784_, 0);
lean_inc(v_a_785_);
if (lean_obj_tag(v_a_785_) == 1)
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_794_; 
lean_dec_ref(v_f_778_);
lean_dec_ref(v_e_777_);
v_a_786_ = lean_ctor_get(v___x_784_, 1);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_794_ == 0)
{
lean_object* v_unused_795_; 
v_unused_795_ = lean_ctor_get(v___x_784_, 0);
lean_dec(v_unused_795_);
v___x_788_ = v___x_784_;
v_isShared_789_ = v_isSharedCheck_794_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_784_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_794_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v_val_790_; lean_object* v___x_792_; 
v_val_790_ = lean_ctor_get(v_a_785_, 0);
lean_inc(v_val_790_);
lean_dec_ref_known(v_a_785_, 1);
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 0, v_val_790_);
v___x_792_ = v___x_788_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_val_790_);
lean_ctor_set(v_reuseFailAlloc_793_, 1, v_a_786_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
else
{
lean_dec(v_a_785_);
switch(lean_obj_tag(v_e_777_))
{
case 9:
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_803_; 
lean_dec_ref(v_f_778_);
v_a_796_ = lean_ctor_get(v___x_784_, 1);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_803_ == 0)
{
lean_object* v_unused_804_; 
v_unused_804_ = lean_ctor_get(v___x_784_, 0);
lean_dec(v_unused_804_);
v___x_798_ = v___x_784_;
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___x_784_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_801_; 
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 0, v_e_777_);
v___x_801_ = v___x_798_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_e_777_);
lean_ctor_set(v_reuseFailAlloc_802_, 1, v_a_796_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
case 2:
{
lean_object* v_a_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_812_; 
lean_dec_ref(v_f_778_);
v_a_805_ = lean_ctor_get(v___x_784_, 1);
v_isSharedCheck_812_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_812_ == 0)
{
lean_object* v_unused_813_; 
v_unused_813_ = lean_ctor_get(v___x_784_, 0);
lean_dec(v_unused_813_);
v___x_807_ = v___x_784_;
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_a_805_);
lean_dec(v___x_784_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_810_; 
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 0, v_e_777_);
v___x_810_ = v___x_807_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_e_777_);
lean_ctor_set(v_reuseFailAlloc_811_, 1, v_a_805_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
case 0:
{
lean_object* v_a_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_821_; 
lean_dec_ref(v_f_778_);
v_a_814_ = lean_ctor_get(v___x_784_, 1);
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_821_ == 0)
{
lean_object* v_unused_822_; 
v_unused_822_ = lean_ctor_get(v___x_784_, 0);
lean_dec(v_unused_822_);
v___x_816_ = v___x_784_;
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_a_814_);
lean_dec(v___x_784_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_819_; 
if (v_isShared_817_ == 0)
{
lean_ctor_set(v___x_816_, 0, v_e_777_);
v___x_819_ = v___x_816_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_e_777_);
lean_ctor_set(v_reuseFailAlloc_820_, 1, v_a_814_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
case 1:
{
lean_object* v_a_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_830_; 
lean_dec_ref(v_f_778_);
v_a_823_ = lean_ctor_get(v___x_784_, 1);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_830_ == 0)
{
lean_object* v_unused_831_; 
v_unused_831_ = lean_ctor_get(v___x_784_, 0);
lean_dec(v_unused_831_);
v___x_825_ = v___x_784_;
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_a_823_);
lean_dec(v___x_784_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_828_; 
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 0, v_e_777_);
v___x_828_ = v___x_825_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_e_777_);
lean_ctor_set(v_reuseFailAlloc_829_, 1, v_a_823_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
case 4:
{
lean_object* v_a_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_839_; 
lean_dec_ref(v_f_778_);
v_a_832_ = lean_ctor_get(v___x_784_, 1);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_839_ == 0)
{
lean_object* v_unused_840_; 
v_unused_840_ = lean_ctor_get(v___x_784_, 0);
lean_dec(v_unused_840_);
v___x_834_ = v___x_784_;
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_a_832_);
lean_dec(v___x_784_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_837_; 
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 0, v_e_777_);
v___x_837_ = v___x_834_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_e_777_);
lean_ctor_set(v_reuseFailAlloc_838_, 1, v_a_832_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
case 3:
{
lean_object* v_a_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_848_; 
lean_dec_ref(v_f_778_);
v_a_841_ = lean_ctor_get(v___x_784_, 1);
v_isSharedCheck_848_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_848_ == 0)
{
lean_object* v_unused_849_; 
v_unused_849_ = lean_ctor_get(v___x_784_, 0);
lean_dec(v_unused_849_);
v___x_843_ = v___x_784_;
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_a_841_);
lean_dec(v___x_784_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_846_; 
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 0, v_e_777_);
v___x_846_ = v___x_843_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_e_777_);
lean_ctor_set(v_reuseFailAlloc_847_, 1, v_a_841_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
default: 
{
lean_object* v_a_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
v_a_850_ = lean_ctor_get(v___x_784_, 1);
lean_inc(v_a_850_);
lean_dec_ref_known(v___x_784_, 2);
v___x_851_ = lean_obj_once(&l_Lean_Meta_Sym_replaceS_x27___closed__1, &l_Lean_Meta_Sym_replaceS_x27___closed__1_once, _init_l_Lean_Meta_Sym_replaceS_x27___closed__1);
v___x_852_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit(v_e_777_, v___x_782_, v_f_778_, v___x_851_, v_a_779_, v_a_780_, v_a_850_);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_object* v_a_853_; lean_object* v_a_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_862_; 
v_a_853_ = lean_ctor_get(v___x_852_, 0);
v_a_854_ = lean_ctor_get(v___x_852_, 1);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_862_ == 0)
{
v___x_856_ = v___x_852_;
v_isShared_857_ = v_isSharedCheck_862_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_a_854_);
lean_inc(v_a_853_);
lean_dec(v___x_852_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_862_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v_fst_858_; lean_object* v___x_860_; 
v_fst_858_ = lean_ctor_get(v_a_853_, 0);
lean_inc(v_fst_858_);
lean_dec(v_a_853_);
if (v_isShared_857_ == 0)
{
lean_ctor_set(v___x_856_, 0, v_fst_858_);
v___x_860_ = v___x_856_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_fst_858_);
lean_ctor_set(v_reuseFailAlloc_861_, 1, v_a_854_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
else
{
lean_object* v_a_863_; lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_871_; 
v_a_863_ = lean_ctor_get(v___x_852_, 0);
v_a_864_ = lean_ctor_get(v___x_852_, 1);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_871_ == 0)
{
v___x_866_ = v___x_852_;
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_inc(v_a_863_);
lean_dec(v___x_852_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_869_; 
if (v_isShared_867_ == 0)
{
v___x_869_ = v___x_866_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_a_863_);
lean_ctor_set(v_reuseFailAlloc_870_, 1, v_a_864_);
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
}
else
{
lean_object* v_a_872_; lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_880_; 
lean_dec_ref(v_f_778_);
lean_dec_ref(v_e_777_);
v_a_872_ = lean_ctor_get(v___x_784_, 0);
v_a_873_ = lean_ctor_get(v___x_784_, 1);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_880_ == 0)
{
v___x_875_ = v___x_784_;
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_inc(v_a_872_);
lean_dec(v___x_784_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_878_; 
if (v_isShared_876_ == 0)
{
v___x_878_ = v___x_875_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_a_872_);
lean_ctor_set(v_reuseFailAlloc_879_, 1, v_a_873_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_replaceS_x27___boxed(lean_object* v_e_881_, lean_object* v_f_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_){
_start:
{
uint8_t v_a_boxed_886_; lean_object* v_res_887_; 
v_a_boxed_886_ = lean_unbox(v_a_883_);
v_res_887_ = l_Lean_Meta_Sym_replaceS_x27(v_e_881_, v_f_882_, v_a_boxed_886_, v_a_884_, v_a_885_);
lean_dec_ref(v_a_884_);
return v_res_887_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_replaceS___closed__0(void){
_start:
{
lean_object* v___x_888_; 
v___x_888_ = l_Lean_Meta_Sym_instInhabitedSymM(lean_box(0));
return v___x_888_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_replaceS___closed__3(void){
_start:
{
lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_891_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__26));
v___x_892_ = lean_unsigned_to_nat(16u);
v___x_893_ = lean_unsigned_to_nat(62u);
v___x_894_ = ((lean_object*)(l_Lean_Meta_Sym_replaceS___closed__2));
v___x_895_ = ((lean_object*)(l_Lean_Meta_Sym_replaceS___closed__1));
v___x_896_ = l_mkPanicMessageWithDecl(v___x_895_, v___x_894_, v___x_893_, v___x_892_, v___x_891_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_replaceS(lean_object* v_e_897_, lean_object* v_f_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; uint8_t v_debug_908_; lean_object* v_env_909_; lean_object* v___x_910_; lean_object* v___x_911_; uint8_t v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_906_ = lean_st_ref_get(v_a_900_);
v___x_907_ = lean_st_ref_get(v_a_904_);
v_debug_908_ = lean_ctor_get_uint8(v___x_906_, sizeof(void*)*11);
lean_dec(v___x_906_);
v_env_909_ = lean_ctor_get(v___x_907_, 0);
lean_inc_ref(v_env_909_);
lean_dec(v___x_907_);
v___x_910_ = lean_box(v_debug_908_);
v___x_911_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_replaceS_x27___boxed), 5, 3);
lean_closure_set(v___x_911_, 0, v_e_897_);
lean_closure_set(v___x_911_, 1, v_f_898_);
lean_closure_set(v___x_911_, 2, v___x_910_);
v___x_912_ = 0;
v___x_913_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_913_, 0, v_env_909_);
lean_ctor_set_uint8(v___x_913_, sizeof(void*)*1, v___x_912_);
lean_ctor_set_uint8(v___x_913_, sizeof(void*)*1 + 1, v___x_912_);
v___x_914_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___x_911_, v___x_913_, v_a_900_);
if (lean_obj_tag(v___x_914_) == 0)
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_927_; 
v_a_915_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_927_ == 0)
{
v___x_917_ = v___x_914_;
v_isShared_918_ = v_isSharedCheck_927_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_914_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_927_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
if (lean_obj_tag(v_a_915_) == 0)
{
lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_27__overap_921_; lean_object* v___x_922_; 
lean_dec_ref_known(v_a_915_, 1);
lean_del_object(v___x_917_);
v___x_919_ = lean_obj_once(&l_Lean_Meta_Sym_replaceS___closed__0, &l_Lean_Meta_Sym_replaceS___closed__0_once, _init_l_Lean_Meta_Sym_replaceS___closed__0);
v___x_920_ = lean_obj_once(&l_Lean_Meta_Sym_replaceS___closed__3, &l_Lean_Meta_Sym_replaceS___closed__3_once, _init_l_Lean_Meta_Sym_replaceS___closed__3);
v___x_27__overap_921_ = l_panic___redArg(v___x_919_, v___x_920_);
lean_inc(v_a_904_);
lean_inc_ref(v_a_903_);
lean_inc(v_a_902_);
lean_inc_ref(v_a_901_);
lean_inc(v_a_900_);
lean_inc_ref(v_a_899_);
v___x_922_ = lean_apply_7(v___x_27__overap_921_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, lean_box(0));
return v___x_922_;
}
else
{
lean_object* v_a_923_; lean_object* v___x_925_; 
v_a_923_ = lean_ctor_get(v_a_915_, 0);
lean_inc(v_a_923_);
lean_dec_ref_known(v_a_915_, 1);
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 0, v_a_923_);
v___x_925_ = v___x_917_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_a_923_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
}
else
{
lean_object* v_a_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_935_; 
v_a_928_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_935_ == 0)
{
v___x_930_ = v___x_914_;
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_a_928_);
lean_dec(v___x_914_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_933_; 
if (v_isShared_931_ == 0)
{
v___x_933_ = v___x_930_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_a_928_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_replaceS___boxed(lean_object* v_e_936_, lean_object* v_f_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_Lean_Meta_Sym_replaceS(v_e_936_, v_f_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_);
lean_dec(v_a_943_);
lean_dec_ref(v_a_942_);
lean_dec(v_a_941_);
lean_dec_ref(v_a_940_);
lean_dec(v_a_939_);
lean_dec_ref(v_a_938_);
return v_res_945_;
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
