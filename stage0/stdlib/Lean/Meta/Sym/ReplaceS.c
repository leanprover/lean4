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
lean_object* l_EStateM_instMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg();
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
static const lean_closure_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___redArg___lam__2, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__2_value;
static const lean_closure_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___redArg___lam__1, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__1_value;
static const lean_closure_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_pure, .m_arity = 5, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__5 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__5_value;
static const lean_closure_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___redArg___lam__0, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
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
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(lean_object* v_a_1_, lean_object* v_x_2_){
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
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1_ = stack[0].m_obj;
lean_object* v_x_2_ = stack[1].m_obj;
uint8_t v_res_16_;
v_res_16_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_a_1_, v_x_2_);
stack->m_num = v_res_16_;
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
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v_nbuckets_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_69_ = lean_array_get_size(v_data_68_);
v___x_70_ = lean_unsigned_to_nat(2u);
v_nbuckets_71_ = lean_nat_mul(v___x_69_, v___x_70_);
v___x_72_ = lean_unsigned_to_nat(0u);
v___x_73_ = lean_box(0);
v___x_74_ = lean_mk_array(v_nbuckets_71_, v___x_73_);
v___x_75_ = lean_array_propagate_mark(v_data_68_, v___x_74_);
v___x_76_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2___redArg(v___x_72_, v_data_68_, v___x_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(lean_object* v_a_77_, lean_object* v_b_78_, lean_object* v_x_79_){
_start:
{
if (lean_obj_tag(v_x_79_) == 0)
{
lean_dec(v_b_78_);
lean_dec_ref(v_a_77_);
return v_x_79_;
}
else
{
lean_object* v_key_80_; lean_object* v_value_81_; lean_object* v_tail_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_100_; 
v_key_80_ = lean_ctor_get(v_x_79_, 0);
v_value_81_ = lean_ctor_get(v_x_79_, 1);
v_tail_82_ = lean_ctor_get(v_x_79_, 2);
v_isSharedCheck_100_ = !lean_is_exclusive(v_x_79_);
if (v_isSharedCheck_100_ == 0)
{
v___x_84_ = v_x_79_;
v_isShared_85_ = v_isSharedCheck_100_;
goto v_resetjp_83_;
}
else
{
lean_inc(v_tail_82_);
lean_inc(v_value_81_);
lean_inc(v_key_80_);
lean_dec(v_x_79_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_100_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
lean_object* v_fst_91_; lean_object* v_snd_92_; lean_object* v_fst_93_; lean_object* v_snd_94_; size_t v___x_95_; size_t v___x_96_; uint8_t v___x_97_; 
v_fst_91_ = lean_ctor_get(v_key_80_, 0);
v_snd_92_ = lean_ctor_get(v_key_80_, 1);
v_fst_93_ = lean_ctor_get(v_a_77_, 0);
v_snd_94_ = lean_ctor_get(v_a_77_, 1);
v___x_95_ = lean_ptr_addr(v_fst_91_);
v___x_96_ = lean_ptr_addr(v_fst_93_);
v___x_97_ = lean_usize_dec_eq(v___x_95_, v___x_96_);
if (v___x_97_ == 0)
{
goto v___jp_86_;
}
else
{
uint8_t v___x_98_; 
v___x_98_ = lean_nat_dec_eq(v_snd_92_, v_snd_94_);
if (v___x_98_ == 0)
{
goto v___jp_86_;
}
else
{
lean_object* v___x_99_; 
lean_del_object(v___x_84_);
lean_dec(v_value_81_);
lean_dec(v_key_80_);
v___x_99_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_99_, 0, v_a_77_);
lean_ctor_set(v___x_99_, 1, v_b_78_);
lean_ctor_set(v___x_99_, 2, v_tail_82_);
return v___x_99_;
}
}
v___jp_86_:
{
lean_object* v___x_87_; lean_object* v___x_89_; 
v___x_87_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(v_a_77_, v_b_78_, v_tail_82_);
if (v_isShared_85_ == 0)
{
lean_ctor_set(v___x_84_, 2, v___x_87_);
v___x_89_ = v___x_84_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_90_; 
v_reuseFailAlloc_90_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v_key_80_);
lean_ctor_set(v_reuseFailAlloc_90_, 1, v_value_81_);
lean_ctor_set(v_reuseFailAlloc_90_, 2, v___x_87_);
v___x_89_ = v_reuseFailAlloc_90_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
return v___x_89_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0___redArg(lean_object* v_m_101_, lean_object* v_a_102_, lean_object* v_b_103_){
_start:
{
lean_object* v_size_104_; lean_object* v_buckets_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_155_; 
v_size_104_ = lean_ctor_get(v_m_101_, 0);
v_buckets_105_ = lean_ctor_get(v_m_101_, 1);
v_isSharedCheck_155_ = !lean_is_exclusive(v_m_101_);
if (v_isSharedCheck_155_ == 0)
{
v___x_107_ = v_m_101_;
v_isShared_108_ = v_isSharedCheck_155_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_buckets_105_);
lean_inc(v_size_104_);
lean_dec(v_m_101_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_155_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v_fst_109_; lean_object* v_snd_110_; lean_object* v___x_111_; size_t v___x_112_; size_t v___x_113_; size_t v___x_114_; uint64_t v___x_115_; uint64_t v___x_116_; uint64_t v___x_117_; uint64_t v___x_118_; uint64_t v___x_119_; uint64_t v_fold_120_; uint64_t v___x_121_; uint64_t v___x_122_; uint64_t v___x_123_; size_t v___x_124_; size_t v___x_125_; size_t v___x_126_; size_t v___x_127_; size_t v___x_128_; lean_object* v_bkt_129_; uint8_t v___x_130_; 
v_fst_109_ = lean_ctor_get(v_a_102_, 0);
v_snd_110_ = lean_ctor_get(v_a_102_, 1);
v___x_111_ = lean_array_get_size(v_buckets_105_);
v___x_112_ = lean_ptr_addr(v_fst_109_);
v___x_113_ = ((size_t)3ULL);
v___x_114_ = lean_usize_shift_right(v___x_112_, v___x_113_);
v___x_115_ = lean_usize_to_uint64(v___x_114_);
v___x_116_ = lean_uint64_of_nat(v_snd_110_);
v___x_117_ = lean_uint64_mix_hash(v___x_115_, v___x_116_);
v___x_118_ = 32ULL;
v___x_119_ = lean_uint64_shift_right(v___x_117_, v___x_118_);
v_fold_120_ = lean_uint64_xor(v___x_117_, v___x_119_);
v___x_121_ = 16ULL;
v___x_122_ = lean_uint64_shift_right(v_fold_120_, v___x_121_);
v___x_123_ = lean_uint64_xor(v_fold_120_, v___x_122_);
v___x_124_ = lean_uint64_to_usize(v___x_123_);
v___x_125_ = lean_usize_of_nat(v___x_111_);
v___x_126_ = ((size_t)1ULL);
v___x_127_ = lean_usize_sub(v___x_125_, v___x_126_);
v___x_128_ = lean_usize_land(v___x_124_, v___x_127_);
v_bkt_129_ = lean_array_uget_borrowed(v_buckets_105_, v___x_128_);
v___x_130_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_a_102_, v_bkt_129_);
if (v___x_130_ == 0)
{
lean_object* v___x_131_; lean_object* v_size_x27_132_; lean_object* v___x_133_; lean_object* v_buckets_x27_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; uint8_t v___x_140_; 
v___x_131_ = lean_unsigned_to_nat(1u);
v_size_x27_132_ = lean_nat_add(v_size_104_, v___x_131_);
lean_dec(v_size_104_);
lean_inc(v_bkt_129_);
v___x_133_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_133_, 0, v_a_102_);
lean_ctor_set(v___x_133_, 1, v_b_103_);
lean_ctor_set(v___x_133_, 2, v_bkt_129_);
v_buckets_x27_134_ = lean_array_uset(v_buckets_105_, v___x_128_, v___x_133_);
v___x_135_ = lean_unsigned_to_nat(4u);
v___x_136_ = lean_nat_mul(v_size_x27_132_, v___x_135_);
v___x_137_ = lean_unsigned_to_nat(3u);
v___x_138_ = lean_nat_div(v___x_136_, v___x_137_);
lean_dec(v___x_136_);
v___x_139_ = lean_array_get_size(v_buckets_x27_134_);
v___x_140_ = lean_nat_dec_le(v___x_138_, v___x_139_);
lean_dec(v___x_138_);
if (v___x_140_ == 0)
{
lean_object* v_val_141_; lean_object* v___x_143_; 
v_val_141_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__1___redArg(v_buckets_x27_134_);
if (v_isShared_108_ == 0)
{
lean_ctor_set(v___x_107_, 1, v_val_141_);
lean_ctor_set(v___x_107_, 0, v_size_x27_132_);
v___x_143_ = v___x_107_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_size_x27_132_);
lean_ctor_set(v_reuseFailAlloc_144_, 1, v_val_141_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
return v___x_143_;
}
}
else
{
lean_object* v___x_146_; 
if (v_isShared_108_ == 0)
{
lean_ctor_set(v___x_107_, 1, v_buckets_x27_134_);
lean_ctor_set(v___x_107_, 0, v_size_x27_132_);
v___x_146_ = v___x_107_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v_size_x27_132_);
lean_ctor_set(v_reuseFailAlloc_147_, 1, v_buckets_x27_134_);
v___x_146_ = v_reuseFailAlloc_147_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
return v___x_146_;
}
}
}
else
{
lean_object* v___x_148_; lean_object* v_buckets_x27_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_153_; 
lean_inc(v_bkt_129_);
v___x_148_ = lean_box(0);
v_buckets_x27_149_ = lean_array_uset(v_buckets_105_, v___x_128_, v___x_148_);
v___x_150_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(v_a_102_, v_b_103_, v_bkt_129_);
v___x_151_ = lean_array_uset(v_buckets_x27_149_, v___x_128_, v___x_150_);
if (v_isShared_108_ == 0)
{
lean_ctor_set(v___x_107_, 1, v___x_151_);
v___x_153_ = v___x_107_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_size_104_);
lean_ctor_set(v_reuseFailAlloc_154_, 1, v___x_151_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
return v___x_153_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(lean_object* v_key_156_, lean_object* v_r_157_, lean_object* v_a_158_, lean_object* v_a_159_){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
lean_inc_ref(v_r_157_);
v___x_160_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_158_, v_key_156_, v_r_157_);
v___x_161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_161_, 0, v_r_157_);
lean_ctor_set(v___x_161_, 1, v___x_160_);
v___x_162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
lean_ctor_set(v___x_162_, 1, v_a_159_);
return v___x_162_;
}
}
lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(lean_object* v_key_163_, lean_object* v_r_164_, lean_object* v_a_165_, uint8_t v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(v_key_163_, v_r_164_, v_a_165_, v_a_168_);
return v___x_169_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_0interp(lean_interpreter_value* stack)
{
lean_object* v_key_163_ = stack[0].m_obj;
lean_object* v_r_164_ = stack[1].m_obj;
lean_object* v_a_165_ = stack[2].m_obj;
uint8_t v_a_166_ = stack[3].m_num;
lean_object* v_a_167_ = stack[4].m_obj;
lean_object* v_a_168_ = stack[5].m_obj;
lean_object* v_res_170_;
v_res_170_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_163_, v_r_164_, v_a_165_, v_a_166_, v_a_167_, v_a_168_);
stack->m_obj
 = v_res_170_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___boxed(lean_object* v_key_171_, lean_object* v_r_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_){
_start:
{
uint8_t v_a_boxed_177_; lean_object* v_res_178_; 
v_a_boxed_177_ = lean_unbox(v_a_174_);
v_res_178_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_171_, v_r_172_, v_a_173_, v_a_boxed_177_, v_a_175_, v_a_176_);
lean_dec_ref(v_a_175_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0(lean_object* v_00_u03b2_179_, lean_object* v_m_180_, lean_object* v_a_181_, lean_object* v_b_182_){
_start:
{
lean_object* v___x_183_; 
v___x_183_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0___redArg(v_m_180_, v_a_181_, v_b_182_);
return v___x_183_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0(lean_object* v_00_u03b2_184_, lean_object* v_a_185_, lean_object* v_x_186_){
_start:
{
uint8_t v___x_187_; 
v___x_187_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_a_185_, v_x_186_);
return v___x_187_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_185_ = stack[1].m_obj;
lean_object* v_x_186_ = stack[2].m_obj;
uint8_t v_res_188_;
v_res_188_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save_spec__0_spec__0(lean_box(0), v_a_185_, v_x_186_);
stack->m_num = v_res_188_;
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
lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit(lean_object* v_e_285_, lean_object* v_offset_286_, lean_object* v_fn_287_, lean_object* v_a_288_, uint8_t v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_){
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
lean_object* v_a_311_; lean_object* v_a_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_340_; 
v_a_311_ = lean_ctor_get(v___x_310_, 0);
v_a_312_ = lean_ctor_get(v___x_310_, 1);
v_isSharedCheck_340_ = !lean_is_exclusive(v___x_310_);
if (v_isSharedCheck_340_ == 0)
{
v___x_314_ = v___x_310_;
v_isShared_315_ = v_isSharedCheck_340_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_a_312_);
lean_inc(v_a_311_);
lean_dec(v___x_310_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_340_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v_fst_316_; lean_object* v_snd_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_339_; 
v_fst_316_ = lean_ctor_get(v_a_311_, 0);
v_snd_317_ = lean_ctor_get(v_a_311_, 1);
v_isSharedCheck_339_ = !lean_is_exclusive(v_a_311_);
if (v_isSharedCheck_339_ == 0)
{
v___x_319_ = v_a_311_;
v_isShared_320_ = v_isSharedCheck_339_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_snd_317_);
lean_inc(v_fst_316_);
lean_dec(v_a_311_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_339_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
size_t v___x_321_; size_t v___x_322_; uint8_t v___x_323_; 
v___x_321_ = lean_ptr_addr(v_fn_303_);
v___x_322_ = lean_ptr_addr(v_fst_308_);
v___x_323_ = lean_usize_dec_eq(v___x_321_, v___x_322_);
if (v___x_323_ == 0)
{
lean_object* v___x_13254__overap_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
lean_del_object(v___x_319_);
lean_del_object(v___x_314_);
lean_dec_ref_known(v_e_285_, 2);
v___x_13254__overap_324_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v___x_302_, v___x_293_, v_fst_308_, v_fst_316_);
v___x_325_ = lean_box(v_a_289_);
lean_inc_ref(v_a_290_);
v___x_326_ = lean_apply_4(v___x_13254__overap_324_, v_snd_317_, v___x_325_, v_a_290_, v_a_312_);
return v___x_326_;
}
else
{
size_t v___x_327_; size_t v___x_328_; uint8_t v___x_329_; 
v___x_327_ = lean_ptr_addr(v_arg_304_);
v___x_328_ = lean_ptr_addr(v_fst_316_);
v___x_329_ = lean_usize_dec_eq(v___x_327_, v___x_328_);
if (v___x_329_ == 0)
{
lean_object* v___x_13257__overap_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
lean_del_object(v___x_319_);
lean_del_object(v___x_314_);
lean_dec_ref_known(v_e_285_, 2);
v___x_13257__overap_330_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v___x_302_, v___x_293_, v_fst_308_, v_fst_316_);
v___x_331_ = lean_box(v_a_289_);
lean_inc_ref(v_a_290_);
v___x_332_ = lean_apply_4(v___x_13257__overap_330_, v_snd_317_, v___x_331_, v_a_290_, v_a_312_);
return v___x_332_;
}
else
{
lean_object* v___x_334_; 
lean_dec(v_fst_316_);
lean_dec(v_fst_308_);
lean_dec_ref_known(v___x_302_, 3);
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 0, v_e_285_);
v___x_334_ = v___x_319_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_e_285_);
lean_ctor_set(v_reuseFailAlloc_338_, 1, v_snd_317_);
v___x_334_ = v_reuseFailAlloc_338_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
lean_object* v___x_336_; 
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 0, v___x_334_);
v___x_336_ = v___x_314_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v___x_334_);
lean_ctor_set(v_reuseFailAlloc_337_, 1, v_a_312_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
return v___x_336_;
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
lean_object* v_binderName_341_; lean_object* v_binderType_342_; lean_object* v_body_343_; uint8_t v_binderInfo_344_; lean_object* v___x_345_; 
v_binderName_341_ = lean_ctor_get(v_e_285_, 0);
v_binderType_342_ = lean_ctor_get(v_e_285_, 1);
v_body_343_ = lean_ctor_get(v_e_285_, 2);
v_binderInfo_344_ = lean_ctor_get_uint8(v_e_285_, sizeof(void*)*3 + 8);
lean_inc_ref(v_fn_287_);
lean_inc(v_offset_286_);
lean_inc_ref(v_binderType_342_);
v___x_345_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_binderType_342_, v_offset_286_, v_fn_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_);
if (lean_obj_tag(v___x_345_) == 0)
{
lean_object* v_a_346_; lean_object* v_a_347_; lean_object* v_fst_348_; lean_object* v_snd_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v_a_346_ = lean_ctor_get(v___x_345_, 0);
lean_inc(v_a_346_);
v_a_347_ = lean_ctor_get(v___x_345_, 1);
lean_inc(v_a_347_);
lean_dec_ref_known(v___x_345_, 2);
v_fst_348_ = lean_ctor_get(v_a_346_, 0);
lean_inc(v_fst_348_);
v_snd_349_ = lean_ctor_get(v_a_346_, 1);
lean_inc(v_snd_349_);
lean_dec(v_a_346_);
v___x_350_ = lean_unsigned_to_nat(1u);
v___x_351_ = lean_nat_add(v_offset_286_, v___x_350_);
lean_dec(v_offset_286_);
lean_inc_ref(v_body_343_);
v___x_352_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_body_343_, v___x_351_, v_fn_287_, v_snd_349_, v_a_289_, v_a_290_, v_a_347_);
if (lean_obj_tag(v___x_352_) == 0)
{
lean_object* v_a_353_; lean_object* v_a_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_382_; 
v_a_353_ = lean_ctor_get(v___x_352_, 0);
v_a_354_ = lean_ctor_get(v___x_352_, 1);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_352_);
if (v_isSharedCheck_382_ == 0)
{
v___x_356_ = v___x_352_;
v_isShared_357_ = v_isSharedCheck_382_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_a_354_);
lean_inc(v_a_353_);
lean_dec(v___x_352_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_382_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v_fst_358_; lean_object* v_snd_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_381_; 
v_fst_358_ = lean_ctor_get(v_a_353_, 0);
v_snd_359_ = lean_ctor_get(v_a_353_, 1);
v_isSharedCheck_381_ = !lean_is_exclusive(v_a_353_);
if (v_isSharedCheck_381_ == 0)
{
v___x_361_ = v_a_353_;
v_isShared_362_ = v_isSharedCheck_381_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_snd_359_);
lean_inc(v_fst_358_);
lean_dec(v_a_353_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_381_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
size_t v___x_363_; size_t v___x_364_; uint8_t v___x_365_; 
v___x_363_ = lean_ptr_addr(v_binderType_342_);
v___x_364_ = lean_ptr_addr(v_fst_348_);
v___x_365_ = lean_usize_dec_eq(v___x_363_, v___x_364_);
if (v___x_365_ == 0)
{
lean_object* v___x_13260__overap_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
lean_inc(v_binderName_341_);
lean_del_object(v___x_361_);
lean_del_object(v___x_356_);
lean_dec_ref_known(v_e_285_, 3);
v___x_13260__overap_366_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v___x_302_, v___x_293_, v_binderName_341_, v_binderInfo_344_, v_fst_348_, v_fst_358_);
v___x_367_ = lean_box(v_a_289_);
lean_inc_ref(v_a_290_);
v___x_368_ = lean_apply_4(v___x_13260__overap_366_, v_snd_359_, v___x_367_, v_a_290_, v_a_354_);
return v___x_368_;
}
else
{
size_t v___x_369_; size_t v___x_370_; uint8_t v___x_371_; 
v___x_369_ = lean_ptr_addr(v_body_343_);
v___x_370_ = lean_ptr_addr(v_fst_358_);
v___x_371_ = lean_usize_dec_eq(v___x_369_, v___x_370_);
if (v___x_371_ == 0)
{
lean_object* v___x_13263__overap_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
lean_inc(v_binderName_341_);
lean_del_object(v___x_361_);
lean_del_object(v___x_356_);
lean_dec_ref_known(v_e_285_, 3);
v___x_13263__overap_372_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v___x_302_, v___x_293_, v_binderName_341_, v_binderInfo_344_, v_fst_348_, v_fst_358_);
v___x_373_ = lean_box(v_a_289_);
lean_inc_ref(v_a_290_);
v___x_374_ = lean_apply_4(v___x_13263__overap_372_, v_snd_359_, v___x_373_, v_a_290_, v_a_354_);
return v___x_374_;
}
else
{
lean_object* v___x_376_; 
lean_dec(v_fst_358_);
lean_dec(v_fst_348_);
lean_dec_ref_known(v___x_302_, 3);
if (v_isShared_362_ == 0)
{
lean_ctor_set(v___x_361_, 0, v_e_285_);
v___x_376_ = v___x_361_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_e_285_);
lean_ctor_set(v_reuseFailAlloc_380_, 1, v_snd_359_);
v___x_376_ = v_reuseFailAlloc_380_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
lean_object* v___x_378_; 
if (v_isShared_357_ == 0)
{
lean_ctor_set(v___x_356_, 0, v___x_376_);
v___x_378_ = v___x_356_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v___x_376_);
lean_ctor_set(v_reuseFailAlloc_379_, 1, v_a_354_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
return v___x_378_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_348_);
lean_dec_ref_known(v_e_285_, 3);
lean_dec_ref_known(v___x_302_, 3);
return v___x_352_;
}
}
else
{
lean_dec_ref_known(v_e_285_, 3);
lean_dec_ref_known(v___x_302_, 3);
lean_dec_ref(v_fn_287_);
lean_dec(v_offset_286_);
return v___x_345_;
}
}
case 7:
{
lean_object* v_binderName_383_; lean_object* v_binderType_384_; lean_object* v_body_385_; uint8_t v_binderInfo_386_; lean_object* v___x_387_; 
v_binderName_383_ = lean_ctor_get(v_e_285_, 0);
v_binderType_384_ = lean_ctor_get(v_e_285_, 1);
v_body_385_ = lean_ctor_get(v_e_285_, 2);
v_binderInfo_386_ = lean_ctor_get_uint8(v_e_285_, sizeof(void*)*3 + 8);
lean_inc_ref(v_fn_287_);
lean_inc(v_offset_286_);
lean_inc_ref(v_binderType_384_);
v___x_387_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_binderType_384_, v_offset_286_, v_fn_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_);
if (lean_obj_tag(v___x_387_) == 0)
{
lean_object* v_a_388_; lean_object* v_a_389_; lean_object* v_fst_390_; lean_object* v_snd_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v_a_388_ = lean_ctor_get(v___x_387_, 0);
lean_inc(v_a_388_);
v_a_389_ = lean_ctor_get(v___x_387_, 1);
lean_inc(v_a_389_);
lean_dec_ref_known(v___x_387_, 2);
v_fst_390_ = lean_ctor_get(v_a_388_, 0);
lean_inc(v_fst_390_);
v_snd_391_ = lean_ctor_get(v_a_388_, 1);
lean_inc(v_snd_391_);
lean_dec(v_a_388_);
v___x_392_ = lean_unsigned_to_nat(1u);
v___x_393_ = lean_nat_add(v_offset_286_, v___x_392_);
lean_dec(v_offset_286_);
lean_inc_ref(v_body_385_);
v___x_394_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_body_385_, v___x_393_, v_fn_287_, v_snd_391_, v_a_289_, v_a_290_, v_a_389_);
if (lean_obj_tag(v___x_394_) == 0)
{
lean_object* v_a_395_; lean_object* v_a_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_424_; 
v_a_395_ = lean_ctor_get(v___x_394_, 0);
v_a_396_ = lean_ctor_get(v___x_394_, 1);
v_isSharedCheck_424_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_424_ == 0)
{
v___x_398_ = v___x_394_;
v_isShared_399_ = v_isSharedCheck_424_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_a_396_);
lean_inc(v_a_395_);
lean_dec(v___x_394_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_424_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v_fst_400_; lean_object* v_snd_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_423_; 
v_fst_400_ = lean_ctor_get(v_a_395_, 0);
v_snd_401_ = lean_ctor_get(v_a_395_, 1);
v_isSharedCheck_423_ = !lean_is_exclusive(v_a_395_);
if (v_isSharedCheck_423_ == 0)
{
v___x_403_ = v_a_395_;
v_isShared_404_ = v_isSharedCheck_423_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_snd_401_);
lean_inc(v_fst_400_);
lean_dec(v_a_395_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_423_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
size_t v___x_405_; size_t v___x_406_; uint8_t v___x_407_; 
v___x_405_ = lean_ptr_addr(v_binderType_384_);
v___x_406_ = lean_ptr_addr(v_fst_390_);
v___x_407_ = lean_usize_dec_eq(v___x_405_, v___x_406_);
if (v___x_407_ == 0)
{
lean_object* v___x_13266__overap_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
lean_inc(v_binderName_383_);
lean_del_object(v___x_403_);
lean_del_object(v___x_398_);
lean_dec_ref_known(v_e_285_, 3);
v___x_13266__overap_408_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v___x_302_, v___x_293_, v_binderName_383_, v_binderInfo_386_, v_fst_390_, v_fst_400_);
v___x_409_ = lean_box(v_a_289_);
lean_inc_ref(v_a_290_);
v___x_410_ = lean_apply_4(v___x_13266__overap_408_, v_snd_401_, v___x_409_, v_a_290_, v_a_396_);
return v___x_410_;
}
else
{
size_t v___x_411_; size_t v___x_412_; uint8_t v___x_413_; 
v___x_411_ = lean_ptr_addr(v_body_385_);
v___x_412_ = lean_ptr_addr(v_fst_400_);
v___x_413_ = lean_usize_dec_eq(v___x_411_, v___x_412_);
if (v___x_413_ == 0)
{
lean_object* v___x_13269__overap_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
lean_inc(v_binderName_383_);
lean_del_object(v___x_403_);
lean_del_object(v___x_398_);
lean_dec_ref_known(v_e_285_, 3);
v___x_13269__overap_414_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v___x_302_, v___x_293_, v_binderName_383_, v_binderInfo_386_, v_fst_390_, v_fst_400_);
v___x_415_ = lean_box(v_a_289_);
lean_inc_ref(v_a_290_);
v___x_416_ = lean_apply_4(v___x_13269__overap_414_, v_snd_401_, v___x_415_, v_a_290_, v_a_396_);
return v___x_416_;
}
else
{
lean_object* v___x_418_; 
lean_dec(v_fst_400_);
lean_dec(v_fst_390_);
lean_dec_ref_known(v___x_302_, 3);
if (v_isShared_404_ == 0)
{
lean_ctor_set(v___x_403_, 0, v_e_285_);
v___x_418_ = v___x_403_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v_e_285_);
lean_ctor_set(v_reuseFailAlloc_422_, 1, v_snd_401_);
v___x_418_ = v_reuseFailAlloc_422_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
lean_object* v___x_420_; 
if (v_isShared_399_ == 0)
{
lean_ctor_set(v___x_398_, 0, v___x_418_);
v___x_420_ = v___x_398_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v___x_418_);
lean_ctor_set(v_reuseFailAlloc_421_, 1, v_a_396_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_390_);
lean_dec_ref_known(v_e_285_, 3);
lean_dec_ref_known(v___x_302_, 3);
return v___x_394_;
}
}
else
{
lean_dec_ref_known(v_e_285_, 3);
lean_dec_ref_known(v___x_302_, 3);
lean_dec_ref(v_fn_287_);
lean_dec(v_offset_286_);
return v___x_387_;
}
}
case 8:
{
lean_object* v_declName_425_; lean_object* v_type_426_; lean_object* v_value_427_; lean_object* v_body_428_; uint8_t v_nondep_429_; lean_object* v___x_430_; 
v_declName_425_ = lean_ctor_get(v_e_285_, 0);
v_type_426_ = lean_ctor_get(v_e_285_, 1);
v_value_427_ = lean_ctor_get(v_e_285_, 2);
v_body_428_ = lean_ctor_get(v_e_285_, 3);
v_nondep_429_ = lean_ctor_get_uint8(v_e_285_, sizeof(void*)*4 + 8);
lean_inc_ref(v_fn_287_);
lean_inc(v_offset_286_);
lean_inc_ref(v_type_426_);
v___x_430_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_type_426_, v_offset_286_, v_fn_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_);
if (lean_obj_tag(v___x_430_) == 0)
{
lean_object* v_a_431_; lean_object* v_a_432_; lean_object* v_fst_433_; lean_object* v_snd_434_; lean_object* v___x_435_; 
v_a_431_ = lean_ctor_get(v___x_430_, 0);
lean_inc(v_a_431_);
v_a_432_ = lean_ctor_get(v___x_430_, 1);
lean_inc(v_a_432_);
lean_dec_ref_known(v___x_430_, 2);
v_fst_433_ = lean_ctor_get(v_a_431_, 0);
lean_inc(v_fst_433_);
v_snd_434_ = lean_ctor_get(v_a_431_, 1);
lean_inc(v_snd_434_);
lean_dec(v_a_431_);
lean_inc_ref(v_fn_287_);
lean_inc(v_offset_286_);
lean_inc_ref(v_value_427_);
v___x_435_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_value_427_, v_offset_286_, v_fn_287_, v_snd_434_, v_a_289_, v_a_290_, v_a_432_);
if (lean_obj_tag(v___x_435_) == 0)
{
lean_object* v_a_436_; lean_object* v_a_437_; lean_object* v_fst_438_; lean_object* v_snd_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v_a_436_ = lean_ctor_get(v___x_435_, 0);
lean_inc(v_a_436_);
v_a_437_ = lean_ctor_get(v___x_435_, 1);
lean_inc(v_a_437_);
lean_dec_ref_known(v___x_435_, 2);
v_fst_438_ = lean_ctor_get(v_a_436_, 0);
lean_inc(v_fst_438_);
v_snd_439_ = lean_ctor_get(v_a_436_, 1);
lean_inc(v_snd_439_);
lean_dec(v_a_436_);
v___x_440_ = lean_unsigned_to_nat(1u);
v___x_441_ = lean_nat_add(v_offset_286_, v___x_440_);
lean_dec(v_offset_286_);
lean_inc_ref(v_body_428_);
v___x_442_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_body_428_, v___x_441_, v_fn_287_, v_snd_439_, v_a_289_, v_a_290_, v_a_437_);
if (lean_obj_tag(v___x_442_) == 0)
{
lean_object* v_a_443_; lean_object* v_a_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_478_; 
v_a_443_ = lean_ctor_get(v___x_442_, 0);
v_a_444_ = lean_ctor_get(v___x_442_, 1);
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_478_ == 0)
{
v___x_446_ = v___x_442_;
v_isShared_447_ = v_isSharedCheck_478_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_a_444_);
lean_inc(v_a_443_);
lean_dec(v___x_442_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_478_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v_fst_448_; lean_object* v_snd_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_477_; 
v_fst_448_ = lean_ctor_get(v_a_443_, 0);
v_snd_449_ = lean_ctor_get(v_a_443_, 1);
v_isSharedCheck_477_ = !lean_is_exclusive(v_a_443_);
if (v_isSharedCheck_477_ == 0)
{
v___x_451_ = v_a_443_;
v_isShared_452_ = v_isSharedCheck_477_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_snd_449_);
lean_inc(v_fst_448_);
lean_dec(v_a_443_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_477_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
size_t v___x_453_; size_t v___x_454_; uint8_t v___x_455_; 
v___x_453_ = lean_ptr_addr(v_type_426_);
v___x_454_ = lean_ptr_addr(v_fst_433_);
v___x_455_ = lean_usize_dec_eq(v___x_453_, v___x_454_);
if (v___x_455_ == 0)
{
lean_object* v___x_13272__overap_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
lean_inc(v_declName_425_);
lean_del_object(v___x_451_);
lean_del_object(v___x_446_);
lean_dec_ref_known(v_e_285_, 4);
v___x_13272__overap_456_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v___x_302_, v___x_293_, v_declName_425_, v_fst_433_, v_fst_438_, v_fst_448_, v_nondep_429_);
v___x_457_ = lean_box(v_a_289_);
lean_inc_ref(v_a_290_);
v___x_458_ = lean_apply_4(v___x_13272__overap_456_, v_snd_449_, v___x_457_, v_a_290_, v_a_444_);
return v___x_458_;
}
else
{
size_t v___x_459_; size_t v___x_460_; uint8_t v___x_461_; 
v___x_459_ = lean_ptr_addr(v_value_427_);
v___x_460_ = lean_ptr_addr(v_fst_438_);
v___x_461_ = lean_usize_dec_eq(v___x_459_, v___x_460_);
if (v___x_461_ == 0)
{
lean_object* v___x_13275__overap_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
lean_inc(v_declName_425_);
lean_del_object(v___x_451_);
lean_del_object(v___x_446_);
lean_dec_ref_known(v_e_285_, 4);
v___x_13275__overap_462_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v___x_302_, v___x_293_, v_declName_425_, v_fst_433_, v_fst_438_, v_fst_448_, v_nondep_429_);
v___x_463_ = lean_box(v_a_289_);
lean_inc_ref(v_a_290_);
v___x_464_ = lean_apply_4(v___x_13275__overap_462_, v_snd_449_, v___x_463_, v_a_290_, v_a_444_);
return v___x_464_;
}
else
{
size_t v___x_465_; size_t v___x_466_; uint8_t v___x_467_; 
v___x_465_ = lean_ptr_addr(v_body_428_);
v___x_466_ = lean_ptr_addr(v_fst_448_);
v___x_467_ = lean_usize_dec_eq(v___x_465_, v___x_466_);
if (v___x_467_ == 0)
{
lean_object* v___x_13278__overap_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
lean_inc(v_declName_425_);
lean_del_object(v___x_451_);
lean_del_object(v___x_446_);
lean_dec_ref_known(v_e_285_, 4);
v___x_13278__overap_468_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v___x_302_, v___x_293_, v_declName_425_, v_fst_433_, v_fst_438_, v_fst_448_, v_nondep_429_);
v___x_469_ = lean_box(v_a_289_);
lean_inc_ref(v_a_290_);
v___x_470_ = lean_apply_4(v___x_13278__overap_468_, v_snd_449_, v___x_469_, v_a_290_, v_a_444_);
return v___x_470_;
}
else
{
lean_object* v___x_472_; 
lean_dec(v_fst_448_);
lean_dec(v_fst_438_);
lean_dec(v_fst_433_);
lean_dec_ref_known(v___x_302_, 3);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 0, v_e_285_);
v___x_472_ = v___x_451_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v_e_285_);
lean_ctor_set(v_reuseFailAlloc_476_, 1, v_snd_449_);
v___x_472_ = v_reuseFailAlloc_476_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
lean_object* v___x_474_; 
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 0, v___x_472_);
v___x_474_ = v___x_446_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v___x_472_);
lean_ctor_set(v_reuseFailAlloc_475_, 1, v_a_444_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
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
lean_dec(v_fst_438_);
lean_dec(v_fst_433_);
lean_dec_ref_known(v_e_285_, 4);
lean_dec_ref_known(v___x_302_, 3);
return v___x_442_;
}
}
else
{
lean_dec(v_fst_433_);
lean_dec_ref_known(v_e_285_, 4);
lean_dec_ref_known(v___x_302_, 3);
lean_dec_ref(v_fn_287_);
lean_dec(v_offset_286_);
return v___x_435_;
}
}
else
{
lean_dec_ref_known(v_e_285_, 4);
lean_dec_ref_known(v___x_302_, 3);
lean_dec_ref(v_fn_287_);
lean_dec(v_offset_286_);
return v___x_430_;
}
}
case 10:
{
lean_object* v_data_479_; lean_object* v_expr_480_; lean_object* v___x_481_; 
v_data_479_ = lean_ctor_get(v_e_285_, 0);
v_expr_480_ = lean_ctor_get(v_e_285_, 1);
lean_inc_ref(v_expr_480_);
v___x_481_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_expr_480_, v_offset_286_, v_fn_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_);
if (lean_obj_tag(v___x_481_) == 0)
{
lean_object* v_a_482_; lean_object* v_a_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_505_; 
v_a_482_ = lean_ctor_get(v___x_481_, 0);
v_a_483_ = lean_ctor_get(v___x_481_, 1);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_505_ == 0)
{
v___x_485_ = v___x_481_;
v_isShared_486_ = v_isSharedCheck_505_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_a_483_);
lean_inc(v_a_482_);
lean_dec(v___x_481_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_505_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v_fst_487_; lean_object* v_snd_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_504_; 
v_fst_487_ = lean_ctor_get(v_a_482_, 0);
v_snd_488_ = lean_ctor_get(v_a_482_, 1);
v_isSharedCheck_504_ = !lean_is_exclusive(v_a_482_);
if (v_isSharedCheck_504_ == 0)
{
v___x_490_ = v_a_482_;
v_isShared_491_ = v_isSharedCheck_504_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_snd_488_);
lean_inc(v_fst_487_);
lean_dec(v_a_482_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_504_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
size_t v___x_492_; size_t v___x_493_; uint8_t v___x_494_; 
v___x_492_ = lean_ptr_addr(v_expr_480_);
v___x_493_ = lean_ptr_addr(v_fst_487_);
v___x_494_ = lean_usize_dec_eq(v___x_492_, v___x_493_);
if (v___x_494_ == 0)
{
lean_object* v___x_13281__overap_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
lean_inc(v_data_479_);
lean_del_object(v___x_490_);
lean_del_object(v___x_485_);
lean_dec_ref_known(v_e_285_, 2);
v___x_13281__overap_495_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg(v___x_302_, v___x_293_, v_data_479_, v_fst_487_);
v___x_496_ = lean_box(v_a_289_);
lean_inc_ref(v_a_290_);
v___x_497_ = lean_apply_4(v___x_13281__overap_495_, v_snd_488_, v___x_496_, v_a_290_, v_a_483_);
return v___x_497_;
}
else
{
lean_object* v___x_499_; 
lean_dec(v_fst_487_);
lean_dec_ref_known(v___x_302_, 3);
if (v_isShared_491_ == 0)
{
lean_ctor_set(v___x_490_, 0, v_e_285_);
v___x_499_ = v___x_490_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_e_285_);
lean_ctor_set(v_reuseFailAlloc_503_, 1, v_snd_488_);
v___x_499_ = v_reuseFailAlloc_503_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
lean_object* v___x_501_; 
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 0, v___x_499_);
v___x_501_ = v___x_485_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v___x_499_);
lean_ctor_set(v_reuseFailAlloc_502_, 1, v_a_483_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
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
return v___x_481_;
}
}
case 11:
{
lean_object* v_typeName_506_; lean_object* v_idx_507_; lean_object* v_struct_508_; lean_object* v___x_509_; 
v_typeName_506_ = lean_ctor_get(v_e_285_, 0);
v_idx_507_ = lean_ctor_get(v_e_285_, 1);
v_struct_508_ = lean_ctor_get(v_e_285_, 2);
lean_inc_ref(v_struct_508_);
v___x_509_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_struct_508_, v_offset_286_, v_fn_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_);
if (lean_obj_tag(v___x_509_) == 0)
{
lean_object* v_a_510_; lean_object* v_a_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_533_; 
v_a_510_ = lean_ctor_get(v___x_509_, 0);
v_a_511_ = lean_ctor_get(v___x_509_, 1);
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_509_);
if (v_isSharedCheck_533_ == 0)
{
v___x_513_ = v___x_509_;
v_isShared_514_ = v_isSharedCheck_533_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_a_511_);
lean_inc(v_a_510_);
lean_dec(v___x_509_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_533_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v_fst_515_; lean_object* v_snd_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_532_; 
v_fst_515_ = lean_ctor_get(v_a_510_, 0);
v_snd_516_ = lean_ctor_get(v_a_510_, 1);
v_isSharedCheck_532_ = !lean_is_exclusive(v_a_510_);
if (v_isSharedCheck_532_ == 0)
{
v___x_518_ = v_a_510_;
v_isShared_519_ = v_isSharedCheck_532_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_snd_516_);
lean_inc(v_fst_515_);
lean_dec(v_a_510_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_532_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
size_t v___x_520_; size_t v___x_521_; uint8_t v___x_522_; 
v___x_520_ = lean_ptr_addr(v_struct_508_);
v___x_521_ = lean_ptr_addr(v_fst_515_);
v___x_522_ = lean_usize_dec_eq(v___x_520_, v___x_521_);
if (v___x_522_ == 0)
{
lean_object* v___x_13284__overap_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
lean_inc(v_idx_507_);
lean_inc(v_typeName_506_);
lean_del_object(v___x_518_);
lean_del_object(v___x_513_);
lean_dec_ref_known(v_e_285_, 3);
v___x_13284__overap_523_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg(v___x_302_, v___x_293_, v_typeName_506_, v_idx_507_, v_fst_515_);
v___x_524_ = lean_box(v_a_289_);
lean_inc_ref(v_a_290_);
v___x_525_ = lean_apply_4(v___x_13284__overap_523_, v_snd_516_, v___x_524_, v_a_290_, v_a_511_);
return v___x_525_;
}
else
{
lean_object* v___x_527_; 
lean_dec(v_fst_515_);
lean_dec_ref_known(v___x_302_, 3);
if (v_isShared_519_ == 0)
{
lean_ctor_set(v___x_518_, 0, v_e_285_);
v___x_527_ = v___x_518_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_e_285_);
lean_ctor_set(v_reuseFailAlloc_531_, 1, v_snd_516_);
v___x_527_ = v_reuseFailAlloc_531_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
lean_object* v___x_529_; 
if (v_isShared_514_ == 0)
{
lean_ctor_set(v___x_513_, 0, v___x_527_);
v___x_529_ = v___x_513_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v___x_527_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v_a_511_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
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
return v___x_509_;
}
}
default: 
{
lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_13286__overap_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
lean_dec_ref_known(v___x_302_, 3);
lean_dec_ref(v_fn_287_);
lean_dec(v_offset_286_);
lean_dec_ref(v_e_285_);
v___x_534_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__23, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__23_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__23);
v___x_535_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__27, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__27_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__27);
v___x_13286__overap_536_ = l_panic___redArg(v___x_534_, v___x_535_);
v___x_537_ = lean_box(v_a_289_);
lean_inc_ref(v_a_290_);
v___x_538_ = lean_apply_4(v___x_13286__overap_536_, v_a_288_, v___x_537_, v_a_290_, v_a_291_);
return v___x_538_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_285_ = stack[0].m_obj;
lean_object* v_offset_286_ = stack[1].m_obj;
lean_object* v_fn_287_ = stack[2].m_obj;
lean_object* v_a_288_ = stack[3].m_obj;
uint8_t v_a_289_ = stack[4].m_num;
lean_object* v_a_290_ = stack[5].m_obj;
lean_object* v_a_291_ = stack[6].m_obj;
lean_object* v_res_539_;
v_res_539_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit(v_e_285_, v_offset_286_, v_fn_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_);
stack->m_obj
 = v_res_539_;
}
lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(lean_object* v_e_540_, lean_object* v_offset_541_, lean_object* v_f_542_, lean_object* v_a_543_, uint8_t v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_){
_start:
{
lean_object* v___f_547_; lean_object* v_key_548_; lean_object* v___f_549_; lean_object* v___x_550_; 
v___f_547_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__3));
lean_inc(v_offset_541_);
lean_inc_ref(v_e_540_);
v_key_548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_548_, 0, v_e_540_);
lean_ctor_set(v_key_548_, 1, v_offset_541_);
v___f_549_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__5, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__5_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___closed__5);
lean_inc_ref(v_key_548_);
v___x_550_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_549_, v___f_547_, v_a_543_, v_key_548_);
if (lean_obj_tag(v___x_550_) == 1)
{
lean_object* v_val_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
lean_dec_ref_known(v_key_548_, 2);
lean_dec_ref(v_f_542_);
lean_dec(v_offset_541_);
lean_dec_ref(v_e_540_);
v_val_551_ = lean_ctor_get(v___x_550_, 0);
lean_inc(v_val_551_);
lean_dec_ref_known(v___x_550_, 1);
v___x_552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_552_, 0, v_val_551_);
lean_ctor_set(v___x_552_, 1, v_a_543_);
v___x_553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_553_, 0, v___x_552_);
lean_ctor_set(v___x_553_, 1, v_a_546_);
return v___x_553_;
}
else
{
lean_object* v___x_554_; lean_object* v___x_555_; 
lean_dec(v___x_550_);
v___x_554_ = lean_box(v_a_544_);
lean_inc_ref(v_f_542_);
lean_inc_ref(v_a_545_);
lean_inc(v_offset_541_);
lean_inc_ref(v_e_540_);
v___x_555_ = lean_apply_5(v_f_542_, v_e_540_, v_offset_541_, v___x_554_, v_a_545_, v_a_546_);
if (lean_obj_tag(v___x_555_) == 0)
{
lean_object* v_a_556_; 
v_a_556_ = lean_ctor_get(v___x_555_, 0);
lean_inc(v_a_556_);
if (lean_obj_tag(v_a_556_) == 1)
{
lean_object* v_a_557_; lean_object* v_val_558_; lean_object* v___x_559_; 
lean_dec_ref(v_f_542_);
lean_dec(v_offset_541_);
lean_dec_ref(v_e_540_);
v_a_557_ = lean_ctor_get(v___x_555_, 1);
lean_inc(v_a_557_);
lean_dec_ref_known(v___x_555_, 2);
v_val_558_ = lean_ctor_get(v_a_556_, 0);
lean_inc(v_val_558_);
lean_dec_ref_known(v_a_556_, 1);
v___x_559_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(v_key_548_, v_val_558_, v_a_543_, v_a_557_);
return v___x_559_;
}
else
{
lean_dec(v_a_556_);
switch(lean_obj_tag(v_e_540_))
{
case 9:
{
lean_object* v_a_560_; lean_object* v___x_561_; 
lean_dec_ref(v_f_542_);
lean_dec(v_offset_541_);
v_a_560_ = lean_ctor_get(v___x_555_, 1);
lean_inc(v_a_560_);
lean_dec_ref_known(v___x_555_, 2);
v___x_561_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(v_key_548_, v_e_540_, v_a_543_, v_a_560_);
return v___x_561_;
}
case 2:
{
lean_object* v_a_562_; lean_object* v___x_563_; 
lean_dec_ref(v_f_542_);
lean_dec(v_offset_541_);
v_a_562_ = lean_ctor_get(v___x_555_, 1);
lean_inc(v_a_562_);
lean_dec_ref_known(v___x_555_, 2);
v___x_563_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(v_key_548_, v_e_540_, v_a_543_, v_a_562_);
return v___x_563_;
}
case 0:
{
lean_object* v_a_564_; lean_object* v___x_565_; 
lean_dec_ref(v_f_542_);
lean_dec(v_offset_541_);
v_a_564_ = lean_ctor_get(v___x_555_, 1);
lean_inc(v_a_564_);
lean_dec_ref_known(v___x_555_, 2);
v___x_565_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(v_key_548_, v_e_540_, v_a_543_, v_a_564_);
return v___x_565_;
}
case 1:
{
lean_object* v_a_566_; lean_object* v___x_567_; 
lean_dec_ref(v_f_542_);
lean_dec(v_offset_541_);
v_a_566_ = lean_ctor_get(v___x_555_, 1);
lean_inc(v_a_566_);
lean_dec_ref_known(v___x_555_, 2);
v___x_567_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(v_key_548_, v_e_540_, v_a_543_, v_a_566_);
return v___x_567_;
}
case 4:
{
lean_object* v_a_568_; lean_object* v___x_569_; 
lean_dec_ref(v_f_542_);
lean_dec(v_offset_541_);
v_a_568_ = lean_ctor_get(v___x_555_, 1);
lean_inc(v_a_568_);
lean_dec_ref_known(v___x_555_, 2);
v___x_569_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(v_key_548_, v_e_540_, v_a_543_, v_a_568_);
return v___x_569_;
}
case 3:
{
lean_object* v_a_570_; lean_object* v___x_571_; 
lean_dec_ref(v_f_542_);
lean_dec(v_offset_541_);
v_a_570_ = lean_ctor_get(v___x_555_, 1);
lean_inc(v_a_570_);
lean_dec_ref_known(v___x_555_, 2);
v___x_571_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(v_key_548_, v_e_540_, v_a_543_, v_a_570_);
return v___x_571_;
}
default: 
{
lean_object* v_a_572_; lean_object* v___x_573_; 
v_a_572_ = lean_ctor_get(v___x_555_, 1);
lean_inc(v_a_572_);
lean_dec_ref_known(v___x_555_, 2);
v___x_573_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit(v_e_540_, v_offset_541_, v_f_542_, v_a_543_, v_a_544_, v_a_545_, v_a_572_);
if (lean_obj_tag(v___x_573_) == 0)
{
lean_object* v_a_574_; lean_object* v_a_575_; lean_object* v_fst_576_; lean_object* v_snd_577_; lean_object* v___x_578_; 
v_a_574_ = lean_ctor_get(v___x_573_, 0);
lean_inc(v_a_574_);
v_a_575_ = lean_ctor_get(v___x_573_, 1);
lean_inc(v_a_575_);
lean_dec_ref_known(v___x_573_, 2);
v_fst_576_ = lean_ctor_get(v_a_574_, 0);
lean_inc(v_fst_576_);
v_snd_577_ = lean_ctor_get(v_a_574_, 1);
lean_inc(v_snd_577_);
lean_dec(v_a_574_);
v___x_578_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save___redArg(v_key_548_, v_fst_576_, v_snd_577_, v_a_575_);
return v___x_578_;
}
else
{
lean_dec_ref_known(v_key_548_, 2);
return v___x_573_;
}
}
}
}
}
else
{
lean_object* v_a_579_; lean_object* v_a_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_587_; 
lean_dec_ref_known(v_key_548_, 2);
lean_dec_ref(v_a_543_);
lean_dec_ref(v_f_542_);
lean_dec(v_offset_541_);
lean_dec_ref(v_e_540_);
v_a_579_ = lean_ctor_get(v___x_555_, 0);
v_a_580_ = lean_ctor_get(v___x_555_, 1);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_587_ == 0)
{
v___x_582_ = v___x_555_;
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_a_580_);
lean_inc(v_a_579_);
lean_dec(v___x_555_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_585_; 
if (v_isShared_583_ == 0)
{
v___x_585_ = v___x_582_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_a_579_);
lean_ctor_set(v_reuseFailAlloc_586_, 1, v_a_580_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_540_ = stack[0].m_obj;
lean_object* v_offset_541_ = stack[1].m_obj;
lean_object* v_f_542_ = stack[2].m_obj;
lean_object* v_a_543_ = stack[3].m_obj;
uint8_t v_a_544_ = stack[4].m_num;
lean_object* v_a_545_ = stack[5].m_obj;
lean_object* v_a_546_ = stack[6].m_obj;
lean_object* v_res_588_;
v_res_588_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_e_540_, v_offset_541_, v_f_542_, v_a_543_, v_a_544_, v_a_545_, v_a_546_);
stack->m_obj
 = v_res_588_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___boxed(lean_object* v_e_589_, lean_object* v_offset_590_, lean_object* v_f_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_){
_start:
{
uint8_t v_a_boxed_596_; lean_object* v_res_597_; 
v_a_boxed_596_ = lean_unbox(v_a_593_);
v_res_597_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild(v_e_589_, v_offset_590_, v_f_591_, v_a_592_, v_a_boxed_596_, v_a_594_, v_a_595_);
lean_dec_ref(v_a_594_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___boxed(lean_object* v_e_598_, lean_object* v_offset_599_, lean_object* v_fn_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_){
_start:
{
uint8_t v_a_boxed_605_; lean_object* v_res_606_; 
v_a_boxed_605_ = lean_unbox(v_a_602_);
v_res_606_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit(v_e_598_, v_offset_599_, v_fn_600_, v_a_601_, v_a_boxed_605_, v_a_603_, v_a_604_);
lean_dec_ref(v_a_603_);
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild_match__4_splitter___redArg(lean_object* v_____do__lift_607_, lean_object* v_h__1_608_, lean_object* v_h__2_609_){
_start:
{
if (lean_obj_tag(v_____do__lift_607_) == 1)
{
lean_object* v_val_610_; lean_object* v___x_611_; 
lean_dec(v_h__2_609_);
v_val_610_ = lean_ctor_get(v_____do__lift_607_, 0);
lean_inc(v_val_610_);
lean_dec_ref_known(v_____do__lift_607_, 1);
v___x_611_ = lean_apply_1(v_h__1_608_, v_val_610_);
return v___x_611_;
}
else
{
lean_object* v___x_612_; 
lean_dec(v_h__1_608_);
v___x_612_ = lean_apply_2(v_h__2_609_, v_____do__lift_607_, lean_box(0));
return v___x_612_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild_match__4_splitter(lean_object* v_motive_613_, lean_object* v_____do__lift_614_, lean_object* v_h__1_615_, lean_object* v_h__2_616_){
_start:
{
if (lean_obj_tag(v_____do__lift_614_) == 1)
{
lean_object* v_val_617_; lean_object* v___x_618_; 
lean_dec(v_h__2_616_);
v_val_617_ = lean_ctor_get(v_____do__lift_614_, 0);
lean_inc(v_val_617_);
lean_dec_ref_known(v_____do__lift_614_, 1);
v___x_618_ = lean_apply_1(v_h__1_615_, v_val_617_);
return v___x_618_;
}
else
{
lean_object* v___x_619_; 
lean_dec(v_h__1_615_);
v___x_619_ = lean_apply_2(v_h__2_616_, v_____do__lift_614_, lean_box(0));
return v___x_619_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild_match__1_splitter___redArg(lean_object* v_e_620_, lean_object* v_h__1_621_, lean_object* v_h__2_622_, lean_object* v_h__3_623_, lean_object* v_h__4_624_, lean_object* v_h__5_625_, lean_object* v_h__6_626_, lean_object* v_h__7_627_){
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
lean_dec_ref_known(v_e_620_, 1);
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
lean_dec_ref_known(v_e_620_, 1);
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
lean_dec_ref_known(v_e_620_, 1);
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
lean_dec_ref_known(v_e_620_, 1);
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
lean_dec_ref_known(v_e_620_, 2);
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
lean_dec_ref_known(v_e_620_, 1);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild_match__1_splitter(lean_object* v_motive_642_, lean_object* v_e_643_, lean_object* v_h__1_644_, lean_object* v_h__2_645_, lean_object* v_h__3_646_, lean_object* v_h__4_647_, lean_object* v_h__5_648_, lean_object* v_h__6_649_, lean_object* v_h__7_650_){
_start:
{
switch(lean_obj_tag(v_e_643_))
{
case 9:
{
lean_object* v_a_651_; lean_object* v___x_652_; 
lean_dec(v_h__7_650_);
lean_dec(v_h__6_649_);
lean_dec(v_h__5_648_);
lean_dec(v_h__4_647_);
lean_dec(v_h__3_646_);
lean_dec(v_h__2_645_);
v_a_651_ = lean_ctor_get(v_e_643_, 0);
lean_inc_ref(v_a_651_);
lean_dec_ref_known(v_e_643_, 1);
v___x_652_ = lean_apply_1(v_h__1_644_, v_a_651_);
return v___x_652_;
}
case 2:
{
lean_object* v_mvarId_653_; lean_object* v___x_654_; 
lean_dec(v_h__7_650_);
lean_dec(v_h__6_649_);
lean_dec(v_h__5_648_);
lean_dec(v_h__4_647_);
lean_dec(v_h__3_646_);
lean_dec(v_h__1_644_);
v_mvarId_653_ = lean_ctor_get(v_e_643_, 0);
lean_inc(v_mvarId_653_);
lean_dec_ref_known(v_e_643_, 1);
v___x_654_ = lean_apply_1(v_h__2_645_, v_mvarId_653_);
return v___x_654_;
}
case 0:
{
lean_object* v_deBruijnIndex_655_; lean_object* v___x_656_; 
lean_dec(v_h__7_650_);
lean_dec(v_h__6_649_);
lean_dec(v_h__5_648_);
lean_dec(v_h__4_647_);
lean_dec(v_h__2_645_);
lean_dec(v_h__1_644_);
v_deBruijnIndex_655_ = lean_ctor_get(v_e_643_, 0);
lean_inc(v_deBruijnIndex_655_);
lean_dec_ref_known(v_e_643_, 1);
v___x_656_ = lean_apply_1(v_h__3_646_, v_deBruijnIndex_655_);
return v___x_656_;
}
case 1:
{
lean_object* v_fvarId_657_; lean_object* v___x_658_; 
lean_dec(v_h__7_650_);
lean_dec(v_h__6_649_);
lean_dec(v_h__5_648_);
lean_dec(v_h__3_646_);
lean_dec(v_h__2_645_);
lean_dec(v_h__1_644_);
v_fvarId_657_ = lean_ctor_get(v_e_643_, 0);
lean_inc(v_fvarId_657_);
lean_dec_ref_known(v_e_643_, 1);
v___x_658_ = lean_apply_1(v_h__4_647_, v_fvarId_657_);
return v___x_658_;
}
case 4:
{
lean_object* v_declName_659_; lean_object* v_us_660_; lean_object* v___x_661_; 
lean_dec(v_h__7_650_);
lean_dec(v_h__6_649_);
lean_dec(v_h__4_647_);
lean_dec(v_h__3_646_);
lean_dec(v_h__2_645_);
lean_dec(v_h__1_644_);
v_declName_659_ = lean_ctor_get(v_e_643_, 0);
lean_inc(v_declName_659_);
v_us_660_ = lean_ctor_get(v_e_643_, 1);
lean_inc(v_us_660_);
lean_dec_ref_known(v_e_643_, 2);
v___x_661_ = lean_apply_2(v_h__5_648_, v_declName_659_, v_us_660_);
return v___x_661_;
}
case 3:
{
lean_object* v_u_662_; lean_object* v___x_663_; 
lean_dec(v_h__7_650_);
lean_dec(v_h__5_648_);
lean_dec(v_h__4_647_);
lean_dec(v_h__3_646_);
lean_dec(v_h__2_645_);
lean_dec(v_h__1_644_);
v_u_662_ = lean_ctor_get(v_e_643_, 0);
lean_inc(v_u_662_);
lean_dec_ref_known(v_e_643_, 1);
v___x_663_ = lean_apply_1(v_h__6_649_, v_u_662_);
return v___x_663_;
}
default: 
{
lean_object* v___x_664_; 
lean_dec(v_h__6_649_);
lean_dec(v_h__5_648_);
lean_dec(v_h__4_647_);
lean_dec(v_h__3_646_);
lean_dec(v_h__2_645_);
lean_dec(v_h__1_644_);
v___x_664_ = lean_apply_7(v_h__7_650_, v_e_643_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_664_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit_match__1_splitter___redArg(lean_object* v_e_665_, lean_object* v_h__1_666_, lean_object* v_h__2_667_, lean_object* v_h__3_668_, lean_object* v_h__4_669_, lean_object* v_h__5_670_, lean_object* v_h__6_671_, lean_object* v_h__7_672_, lean_object* v_h__8_673_, lean_object* v_h__9_674_, lean_object* v_h__10_675_, lean_object* v_h__11_676_, lean_object* v_h__12_677_){
_start:
{
switch(lean_obj_tag(v_e_665_))
{
case 0:
{
lean_object* v_deBruijnIndex_678_; lean_object* v___x_679_; 
lean_dec(v_h__12_677_);
lean_dec(v_h__11_676_);
lean_dec(v_h__10_675_);
lean_dec(v_h__9_674_);
lean_dec(v_h__8_673_);
lean_dec(v_h__7_672_);
lean_dec(v_h__6_671_);
lean_dec(v_h__5_670_);
lean_dec(v_h__4_669_);
lean_dec(v_h__2_667_);
lean_dec(v_h__1_666_);
v_deBruijnIndex_678_ = lean_ctor_get(v_e_665_, 0);
lean_inc(v_deBruijnIndex_678_);
lean_dec_ref_known(v_e_665_, 1);
v___x_679_ = lean_apply_1(v_h__3_668_, v_deBruijnIndex_678_);
return v___x_679_;
}
case 1:
{
lean_object* v_fvarId_680_; lean_object* v___x_681_; 
lean_dec(v_h__12_677_);
lean_dec(v_h__11_676_);
lean_dec(v_h__10_675_);
lean_dec(v_h__9_674_);
lean_dec(v_h__8_673_);
lean_dec(v_h__7_672_);
lean_dec(v_h__6_671_);
lean_dec(v_h__5_670_);
lean_dec(v_h__3_668_);
lean_dec(v_h__2_667_);
lean_dec(v_h__1_666_);
v_fvarId_680_ = lean_ctor_get(v_e_665_, 0);
lean_inc(v_fvarId_680_);
lean_dec_ref_known(v_e_665_, 1);
v___x_681_ = lean_apply_1(v_h__4_669_, v_fvarId_680_);
return v___x_681_;
}
case 2:
{
lean_object* v_mvarId_682_; lean_object* v___x_683_; 
lean_dec(v_h__12_677_);
lean_dec(v_h__11_676_);
lean_dec(v_h__10_675_);
lean_dec(v_h__9_674_);
lean_dec(v_h__8_673_);
lean_dec(v_h__7_672_);
lean_dec(v_h__6_671_);
lean_dec(v_h__5_670_);
lean_dec(v_h__4_669_);
lean_dec(v_h__3_668_);
lean_dec(v_h__1_666_);
v_mvarId_682_ = lean_ctor_get(v_e_665_, 0);
lean_inc(v_mvarId_682_);
lean_dec_ref_known(v_e_665_, 1);
v___x_683_ = lean_apply_1(v_h__2_667_, v_mvarId_682_);
return v___x_683_;
}
case 3:
{
lean_object* v_u_684_; lean_object* v___x_685_; 
lean_dec(v_h__12_677_);
lean_dec(v_h__11_676_);
lean_dec(v_h__10_675_);
lean_dec(v_h__9_674_);
lean_dec(v_h__8_673_);
lean_dec(v_h__7_672_);
lean_dec(v_h__5_670_);
lean_dec(v_h__4_669_);
lean_dec(v_h__3_668_);
lean_dec(v_h__2_667_);
lean_dec(v_h__1_666_);
v_u_684_ = lean_ctor_get(v_e_665_, 0);
lean_inc(v_u_684_);
lean_dec_ref_known(v_e_665_, 1);
v___x_685_ = lean_apply_1(v_h__6_671_, v_u_684_);
return v___x_685_;
}
case 4:
{
lean_object* v_declName_686_; lean_object* v_us_687_; lean_object* v___x_688_; 
lean_dec(v_h__12_677_);
lean_dec(v_h__11_676_);
lean_dec(v_h__10_675_);
lean_dec(v_h__9_674_);
lean_dec(v_h__8_673_);
lean_dec(v_h__7_672_);
lean_dec(v_h__6_671_);
lean_dec(v_h__4_669_);
lean_dec(v_h__3_668_);
lean_dec(v_h__2_667_);
lean_dec(v_h__1_666_);
v_declName_686_ = lean_ctor_get(v_e_665_, 0);
lean_inc(v_declName_686_);
v_us_687_ = lean_ctor_get(v_e_665_, 1);
lean_inc(v_us_687_);
lean_dec_ref_known(v_e_665_, 2);
v___x_688_ = lean_apply_2(v_h__5_670_, v_declName_686_, v_us_687_);
return v___x_688_;
}
case 5:
{
lean_object* v_fn_689_; lean_object* v_arg_690_; lean_object* v___x_691_; 
lean_dec(v_h__12_677_);
lean_dec(v_h__11_676_);
lean_dec(v_h__10_675_);
lean_dec(v_h__9_674_);
lean_dec(v_h__8_673_);
lean_dec(v_h__6_671_);
lean_dec(v_h__5_670_);
lean_dec(v_h__4_669_);
lean_dec(v_h__3_668_);
lean_dec(v_h__2_667_);
lean_dec(v_h__1_666_);
v_fn_689_ = lean_ctor_get(v_e_665_, 0);
lean_inc_ref(v_fn_689_);
v_arg_690_ = lean_ctor_get(v_e_665_, 1);
lean_inc_ref(v_arg_690_);
lean_dec_ref_known(v_e_665_, 2);
v___x_691_ = lean_apply_2(v_h__7_672_, v_fn_689_, v_arg_690_);
return v___x_691_;
}
case 6:
{
lean_object* v_binderName_692_; lean_object* v_binderType_693_; lean_object* v_body_694_; uint8_t v_binderInfo_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
lean_dec(v_h__12_677_);
lean_dec(v_h__10_675_);
lean_dec(v_h__9_674_);
lean_dec(v_h__8_673_);
lean_dec(v_h__7_672_);
lean_dec(v_h__6_671_);
lean_dec(v_h__5_670_);
lean_dec(v_h__4_669_);
lean_dec(v_h__3_668_);
lean_dec(v_h__2_667_);
lean_dec(v_h__1_666_);
v_binderName_692_ = lean_ctor_get(v_e_665_, 0);
lean_inc(v_binderName_692_);
v_binderType_693_ = lean_ctor_get(v_e_665_, 1);
lean_inc_ref(v_binderType_693_);
v_body_694_ = lean_ctor_get(v_e_665_, 2);
lean_inc_ref(v_body_694_);
v_binderInfo_695_ = lean_ctor_get_uint8(v_e_665_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_665_, 3);
v___x_696_ = lean_box(v_binderInfo_695_);
v___x_697_ = lean_apply_4(v_h__11_676_, v_binderName_692_, v_binderType_693_, v_body_694_, v___x_696_);
return v___x_697_;
}
case 7:
{
lean_object* v_binderName_698_; lean_object* v_binderType_699_; lean_object* v_body_700_; uint8_t v_binderInfo_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
lean_dec(v_h__12_677_);
lean_dec(v_h__11_676_);
lean_dec(v_h__9_674_);
lean_dec(v_h__8_673_);
lean_dec(v_h__7_672_);
lean_dec(v_h__6_671_);
lean_dec(v_h__5_670_);
lean_dec(v_h__4_669_);
lean_dec(v_h__3_668_);
lean_dec(v_h__2_667_);
lean_dec(v_h__1_666_);
v_binderName_698_ = lean_ctor_get(v_e_665_, 0);
lean_inc(v_binderName_698_);
v_binderType_699_ = lean_ctor_get(v_e_665_, 1);
lean_inc_ref(v_binderType_699_);
v_body_700_ = lean_ctor_get(v_e_665_, 2);
lean_inc_ref(v_body_700_);
v_binderInfo_701_ = lean_ctor_get_uint8(v_e_665_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_665_, 3);
v___x_702_ = lean_box(v_binderInfo_701_);
v___x_703_ = lean_apply_4(v_h__10_675_, v_binderName_698_, v_binderType_699_, v_body_700_, v___x_702_);
return v___x_703_;
}
case 8:
{
lean_object* v_declName_704_; lean_object* v_type_705_; lean_object* v_value_706_; lean_object* v_body_707_; uint8_t v_nondep_708_; lean_object* v___x_709_; lean_object* v___x_710_; 
lean_dec(v_h__11_676_);
lean_dec(v_h__10_675_);
lean_dec(v_h__9_674_);
lean_dec(v_h__8_673_);
lean_dec(v_h__7_672_);
lean_dec(v_h__6_671_);
lean_dec(v_h__5_670_);
lean_dec(v_h__4_669_);
lean_dec(v_h__3_668_);
lean_dec(v_h__2_667_);
lean_dec(v_h__1_666_);
v_declName_704_ = lean_ctor_get(v_e_665_, 0);
lean_inc(v_declName_704_);
v_type_705_ = lean_ctor_get(v_e_665_, 1);
lean_inc_ref(v_type_705_);
v_value_706_ = lean_ctor_get(v_e_665_, 2);
lean_inc_ref(v_value_706_);
v_body_707_ = lean_ctor_get(v_e_665_, 3);
lean_inc_ref(v_body_707_);
v_nondep_708_ = lean_ctor_get_uint8(v_e_665_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_665_, 4);
v___x_709_ = lean_box(v_nondep_708_);
v___x_710_ = lean_apply_5(v_h__12_677_, v_declName_704_, v_type_705_, v_value_706_, v_body_707_, v___x_709_);
return v___x_710_;
}
case 9:
{
lean_object* v_a_711_; lean_object* v___x_712_; 
lean_dec(v_h__12_677_);
lean_dec(v_h__11_676_);
lean_dec(v_h__10_675_);
lean_dec(v_h__9_674_);
lean_dec(v_h__8_673_);
lean_dec(v_h__7_672_);
lean_dec(v_h__6_671_);
lean_dec(v_h__5_670_);
lean_dec(v_h__4_669_);
lean_dec(v_h__3_668_);
lean_dec(v_h__2_667_);
v_a_711_ = lean_ctor_get(v_e_665_, 0);
lean_inc_ref(v_a_711_);
lean_dec_ref_known(v_e_665_, 1);
v___x_712_ = lean_apply_1(v_h__1_666_, v_a_711_);
return v___x_712_;
}
case 10:
{
lean_object* v_data_713_; lean_object* v_expr_714_; lean_object* v___x_715_; 
lean_dec(v_h__12_677_);
lean_dec(v_h__11_676_);
lean_dec(v_h__10_675_);
lean_dec(v_h__9_674_);
lean_dec(v_h__7_672_);
lean_dec(v_h__6_671_);
lean_dec(v_h__5_670_);
lean_dec(v_h__4_669_);
lean_dec(v_h__3_668_);
lean_dec(v_h__2_667_);
lean_dec(v_h__1_666_);
v_data_713_ = lean_ctor_get(v_e_665_, 0);
lean_inc(v_data_713_);
v_expr_714_ = lean_ctor_get(v_e_665_, 1);
lean_inc_ref(v_expr_714_);
lean_dec_ref_known(v_e_665_, 2);
v___x_715_ = lean_apply_2(v_h__8_673_, v_data_713_, v_expr_714_);
return v___x_715_;
}
default: 
{
lean_object* v_typeName_716_; lean_object* v_idx_717_; lean_object* v_struct_718_; lean_object* v___x_719_; 
lean_dec(v_h__12_677_);
lean_dec(v_h__11_676_);
lean_dec(v_h__10_675_);
lean_dec(v_h__8_673_);
lean_dec(v_h__7_672_);
lean_dec(v_h__6_671_);
lean_dec(v_h__5_670_);
lean_dec(v_h__4_669_);
lean_dec(v_h__3_668_);
lean_dec(v_h__2_667_);
lean_dec(v_h__1_666_);
v_typeName_716_ = lean_ctor_get(v_e_665_, 0);
lean_inc(v_typeName_716_);
v_idx_717_ = lean_ctor_get(v_e_665_, 1);
lean_inc(v_idx_717_);
v_struct_718_ = lean_ctor_get(v_e_665_, 2);
lean_inc_ref(v_struct_718_);
lean_dec_ref_known(v_e_665_, 3);
v___x_719_ = lean_apply_3(v_h__9_674_, v_typeName_716_, v_idx_717_, v_struct_718_);
return v___x_719_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit_match__1_splitter(lean_object* v_motive_720_, lean_object* v_e_721_, lean_object* v_h__1_722_, lean_object* v_h__2_723_, lean_object* v_h__3_724_, lean_object* v_h__4_725_, lean_object* v_h__5_726_, lean_object* v_h__6_727_, lean_object* v_h__7_728_, lean_object* v_h__8_729_, lean_object* v_h__9_730_, lean_object* v_h__10_731_, lean_object* v_h__11_732_, lean_object* v_h__12_733_){
_start:
{
switch(lean_obj_tag(v_e_721_))
{
case 0:
{
lean_object* v_deBruijnIndex_734_; lean_object* v___x_735_; 
lean_dec(v_h__12_733_);
lean_dec(v_h__11_732_);
lean_dec(v_h__10_731_);
lean_dec(v_h__9_730_);
lean_dec(v_h__8_729_);
lean_dec(v_h__7_728_);
lean_dec(v_h__6_727_);
lean_dec(v_h__5_726_);
lean_dec(v_h__4_725_);
lean_dec(v_h__2_723_);
lean_dec(v_h__1_722_);
v_deBruijnIndex_734_ = lean_ctor_get(v_e_721_, 0);
lean_inc(v_deBruijnIndex_734_);
lean_dec_ref_known(v_e_721_, 1);
v___x_735_ = lean_apply_1(v_h__3_724_, v_deBruijnIndex_734_);
return v___x_735_;
}
case 1:
{
lean_object* v_fvarId_736_; lean_object* v___x_737_; 
lean_dec(v_h__12_733_);
lean_dec(v_h__11_732_);
lean_dec(v_h__10_731_);
lean_dec(v_h__9_730_);
lean_dec(v_h__8_729_);
lean_dec(v_h__7_728_);
lean_dec(v_h__6_727_);
lean_dec(v_h__5_726_);
lean_dec(v_h__3_724_);
lean_dec(v_h__2_723_);
lean_dec(v_h__1_722_);
v_fvarId_736_ = lean_ctor_get(v_e_721_, 0);
lean_inc(v_fvarId_736_);
lean_dec_ref_known(v_e_721_, 1);
v___x_737_ = lean_apply_1(v_h__4_725_, v_fvarId_736_);
return v___x_737_;
}
case 2:
{
lean_object* v_mvarId_738_; lean_object* v___x_739_; 
lean_dec(v_h__12_733_);
lean_dec(v_h__11_732_);
lean_dec(v_h__10_731_);
lean_dec(v_h__9_730_);
lean_dec(v_h__8_729_);
lean_dec(v_h__7_728_);
lean_dec(v_h__6_727_);
lean_dec(v_h__5_726_);
lean_dec(v_h__4_725_);
lean_dec(v_h__3_724_);
lean_dec(v_h__1_722_);
v_mvarId_738_ = lean_ctor_get(v_e_721_, 0);
lean_inc(v_mvarId_738_);
lean_dec_ref_known(v_e_721_, 1);
v___x_739_ = lean_apply_1(v_h__2_723_, v_mvarId_738_);
return v___x_739_;
}
case 3:
{
lean_object* v_u_740_; lean_object* v___x_741_; 
lean_dec(v_h__12_733_);
lean_dec(v_h__11_732_);
lean_dec(v_h__10_731_);
lean_dec(v_h__9_730_);
lean_dec(v_h__8_729_);
lean_dec(v_h__7_728_);
lean_dec(v_h__5_726_);
lean_dec(v_h__4_725_);
lean_dec(v_h__3_724_);
lean_dec(v_h__2_723_);
lean_dec(v_h__1_722_);
v_u_740_ = lean_ctor_get(v_e_721_, 0);
lean_inc(v_u_740_);
lean_dec_ref_known(v_e_721_, 1);
v___x_741_ = lean_apply_1(v_h__6_727_, v_u_740_);
return v___x_741_;
}
case 4:
{
lean_object* v_declName_742_; lean_object* v_us_743_; lean_object* v___x_744_; 
lean_dec(v_h__12_733_);
lean_dec(v_h__11_732_);
lean_dec(v_h__10_731_);
lean_dec(v_h__9_730_);
lean_dec(v_h__8_729_);
lean_dec(v_h__7_728_);
lean_dec(v_h__6_727_);
lean_dec(v_h__4_725_);
lean_dec(v_h__3_724_);
lean_dec(v_h__2_723_);
lean_dec(v_h__1_722_);
v_declName_742_ = lean_ctor_get(v_e_721_, 0);
lean_inc(v_declName_742_);
v_us_743_ = lean_ctor_get(v_e_721_, 1);
lean_inc(v_us_743_);
lean_dec_ref_known(v_e_721_, 2);
v___x_744_ = lean_apply_2(v_h__5_726_, v_declName_742_, v_us_743_);
return v___x_744_;
}
case 5:
{
lean_object* v_fn_745_; lean_object* v_arg_746_; lean_object* v___x_747_; 
lean_dec(v_h__12_733_);
lean_dec(v_h__11_732_);
lean_dec(v_h__10_731_);
lean_dec(v_h__9_730_);
lean_dec(v_h__8_729_);
lean_dec(v_h__6_727_);
lean_dec(v_h__5_726_);
lean_dec(v_h__4_725_);
lean_dec(v_h__3_724_);
lean_dec(v_h__2_723_);
lean_dec(v_h__1_722_);
v_fn_745_ = lean_ctor_get(v_e_721_, 0);
lean_inc_ref(v_fn_745_);
v_arg_746_ = lean_ctor_get(v_e_721_, 1);
lean_inc_ref(v_arg_746_);
lean_dec_ref_known(v_e_721_, 2);
v___x_747_ = lean_apply_2(v_h__7_728_, v_fn_745_, v_arg_746_);
return v___x_747_;
}
case 6:
{
lean_object* v_binderName_748_; lean_object* v_binderType_749_; lean_object* v_body_750_; uint8_t v_binderInfo_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
lean_dec(v_h__12_733_);
lean_dec(v_h__10_731_);
lean_dec(v_h__9_730_);
lean_dec(v_h__8_729_);
lean_dec(v_h__7_728_);
lean_dec(v_h__6_727_);
lean_dec(v_h__5_726_);
lean_dec(v_h__4_725_);
lean_dec(v_h__3_724_);
lean_dec(v_h__2_723_);
lean_dec(v_h__1_722_);
v_binderName_748_ = lean_ctor_get(v_e_721_, 0);
lean_inc(v_binderName_748_);
v_binderType_749_ = lean_ctor_get(v_e_721_, 1);
lean_inc_ref(v_binderType_749_);
v_body_750_ = lean_ctor_get(v_e_721_, 2);
lean_inc_ref(v_body_750_);
v_binderInfo_751_ = lean_ctor_get_uint8(v_e_721_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_721_, 3);
v___x_752_ = lean_box(v_binderInfo_751_);
v___x_753_ = lean_apply_4(v_h__11_732_, v_binderName_748_, v_binderType_749_, v_body_750_, v___x_752_);
return v___x_753_;
}
case 7:
{
lean_object* v_binderName_754_; lean_object* v_binderType_755_; lean_object* v_body_756_; uint8_t v_binderInfo_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
lean_dec(v_h__12_733_);
lean_dec(v_h__11_732_);
lean_dec(v_h__9_730_);
lean_dec(v_h__8_729_);
lean_dec(v_h__7_728_);
lean_dec(v_h__6_727_);
lean_dec(v_h__5_726_);
lean_dec(v_h__4_725_);
lean_dec(v_h__3_724_);
lean_dec(v_h__2_723_);
lean_dec(v_h__1_722_);
v_binderName_754_ = lean_ctor_get(v_e_721_, 0);
lean_inc(v_binderName_754_);
v_binderType_755_ = lean_ctor_get(v_e_721_, 1);
lean_inc_ref(v_binderType_755_);
v_body_756_ = lean_ctor_get(v_e_721_, 2);
lean_inc_ref(v_body_756_);
v_binderInfo_757_ = lean_ctor_get_uint8(v_e_721_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_721_, 3);
v___x_758_ = lean_box(v_binderInfo_757_);
v___x_759_ = lean_apply_4(v_h__10_731_, v_binderName_754_, v_binderType_755_, v_body_756_, v___x_758_);
return v___x_759_;
}
case 8:
{
lean_object* v_declName_760_; lean_object* v_type_761_; lean_object* v_value_762_; lean_object* v_body_763_; uint8_t v_nondep_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
lean_dec(v_h__11_732_);
lean_dec(v_h__10_731_);
lean_dec(v_h__9_730_);
lean_dec(v_h__8_729_);
lean_dec(v_h__7_728_);
lean_dec(v_h__6_727_);
lean_dec(v_h__5_726_);
lean_dec(v_h__4_725_);
lean_dec(v_h__3_724_);
lean_dec(v_h__2_723_);
lean_dec(v_h__1_722_);
v_declName_760_ = lean_ctor_get(v_e_721_, 0);
lean_inc(v_declName_760_);
v_type_761_ = lean_ctor_get(v_e_721_, 1);
lean_inc_ref(v_type_761_);
v_value_762_ = lean_ctor_get(v_e_721_, 2);
lean_inc_ref(v_value_762_);
v_body_763_ = lean_ctor_get(v_e_721_, 3);
lean_inc_ref(v_body_763_);
v_nondep_764_ = lean_ctor_get_uint8(v_e_721_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_721_, 4);
v___x_765_ = lean_box(v_nondep_764_);
v___x_766_ = lean_apply_5(v_h__12_733_, v_declName_760_, v_type_761_, v_value_762_, v_body_763_, v___x_765_);
return v___x_766_;
}
case 9:
{
lean_object* v_a_767_; lean_object* v___x_768_; 
lean_dec(v_h__12_733_);
lean_dec(v_h__11_732_);
lean_dec(v_h__10_731_);
lean_dec(v_h__9_730_);
lean_dec(v_h__8_729_);
lean_dec(v_h__7_728_);
lean_dec(v_h__6_727_);
lean_dec(v_h__5_726_);
lean_dec(v_h__4_725_);
lean_dec(v_h__3_724_);
lean_dec(v_h__2_723_);
v_a_767_ = lean_ctor_get(v_e_721_, 0);
lean_inc_ref(v_a_767_);
lean_dec_ref_known(v_e_721_, 1);
v___x_768_ = lean_apply_1(v_h__1_722_, v_a_767_);
return v___x_768_;
}
case 10:
{
lean_object* v_data_769_; lean_object* v_expr_770_; lean_object* v___x_771_; 
lean_dec(v_h__12_733_);
lean_dec(v_h__11_732_);
lean_dec(v_h__10_731_);
lean_dec(v_h__9_730_);
lean_dec(v_h__7_728_);
lean_dec(v_h__6_727_);
lean_dec(v_h__5_726_);
lean_dec(v_h__4_725_);
lean_dec(v_h__3_724_);
lean_dec(v_h__2_723_);
lean_dec(v_h__1_722_);
v_data_769_ = lean_ctor_get(v_e_721_, 0);
lean_inc(v_data_769_);
v_expr_770_ = lean_ctor_get(v_e_721_, 1);
lean_inc_ref(v_expr_770_);
lean_dec_ref_known(v_e_721_, 2);
v___x_771_ = lean_apply_2(v_h__8_729_, v_data_769_, v_expr_770_);
return v___x_771_;
}
default: 
{
lean_object* v_typeName_772_; lean_object* v_idx_773_; lean_object* v_struct_774_; lean_object* v___x_775_; 
lean_dec(v_h__12_733_);
lean_dec(v_h__11_732_);
lean_dec(v_h__10_731_);
lean_dec(v_h__8_729_);
lean_dec(v_h__7_728_);
lean_dec(v_h__6_727_);
lean_dec(v_h__5_726_);
lean_dec(v_h__4_725_);
lean_dec(v_h__3_724_);
lean_dec(v_h__2_723_);
lean_dec(v_h__1_722_);
v_typeName_772_ = lean_ctor_get(v_e_721_, 0);
lean_inc(v_typeName_772_);
v_idx_773_ = lean_ctor_get(v_e_721_, 1);
lean_inc(v_idx_773_);
v_struct_774_ = lean_ctor_get(v_e_721_, 2);
lean_inc_ref(v_struct_774_);
lean_dec_ref_known(v_e_721_, 3);
v___x_775_ = lean_apply_3(v_h__9_730_, v_typeName_772_, v_idx_773_, v_struct_774_);
return v___x_775_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Sym_replaceS_x27___closed__0(void){
_start:
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_776_ = lean_box(0);
v___x_777_ = lean_unsigned_to_nat(16u);
v___x_778_ = lean_mk_array(v___x_777_, v___x_776_);
return v___x_778_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_replaceS_x27___closed__1(void){
_start:
{
lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_779_ = lean_obj_once(&l_Lean_Meta_Sym_replaceS_x27___closed__0, &l_Lean_Meta_Sym_replaceS_x27___closed__0_once, _init_l_Lean_Meta_Sym_replaceS_x27___closed__0);
v___x_780_ = lean_unsigned_to_nat(0u);
v___x_781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_781_, 0, v___x_780_);
lean_ctor_set(v___x_781_, 1, v___x_779_);
return v___x_781_;
}
}
lean_object* l_Lean_Meta_Sym_replaceS_x27(lean_object* v_e_782_, lean_object* v_f_783_, uint8_t v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_){
_start:
{
lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_787_ = lean_unsigned_to_nat(0u);
v___x_788_ = lean_box(v_a_784_);
lean_inc_ref(v_f_783_);
lean_inc_ref(v_a_785_);
lean_inc_ref(v_e_782_);
v___x_789_ = lean_apply_5(v_f_783_, v_e_782_, v___x_787_, v___x_788_, v_a_785_, v_a_786_);
if (lean_obj_tag(v___x_789_) == 0)
{
lean_object* v_a_790_; 
v_a_790_ = lean_ctor_get(v___x_789_, 0);
lean_inc(v_a_790_);
if (lean_obj_tag(v_a_790_) == 1)
{
lean_object* v_a_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_799_; 
lean_dec_ref(v_f_783_);
lean_dec_ref(v_e_782_);
v_a_791_ = lean_ctor_get(v___x_789_, 1);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_799_ == 0)
{
lean_object* v_unused_800_; 
v_unused_800_ = lean_ctor_get(v___x_789_, 0);
lean_dec(v_unused_800_);
v___x_793_ = v___x_789_;
v_isShared_794_ = v_isSharedCheck_799_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_a_791_);
lean_dec(v___x_789_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_799_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v_val_795_; lean_object* v___x_797_; 
v_val_795_ = lean_ctor_get(v_a_790_, 0);
lean_inc(v_val_795_);
lean_dec_ref_known(v_a_790_, 1);
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 0, v_val_795_);
v___x_797_ = v___x_793_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v_val_795_);
lean_ctor_set(v_reuseFailAlloc_798_, 1, v_a_791_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
return v___x_797_;
}
}
}
else
{
lean_dec(v_a_790_);
switch(lean_obj_tag(v_e_782_))
{
case 9:
{
lean_object* v_a_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_808_; 
lean_dec_ref(v_f_783_);
v_a_801_ = lean_ctor_get(v___x_789_, 1);
v_isSharedCheck_808_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_808_ == 0)
{
lean_object* v_unused_809_; 
v_unused_809_ = lean_ctor_get(v___x_789_, 0);
lean_dec(v_unused_809_);
v___x_803_ = v___x_789_;
v_isShared_804_ = v_isSharedCheck_808_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_a_801_);
lean_dec(v___x_789_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_808_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___x_806_; 
if (v_isShared_804_ == 0)
{
lean_ctor_set(v___x_803_, 0, v_e_782_);
v___x_806_ = v___x_803_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v_e_782_);
lean_ctor_set(v_reuseFailAlloc_807_, 1, v_a_801_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
return v___x_806_;
}
}
}
case 2:
{
lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_817_; 
lean_dec_ref(v_f_783_);
v_a_810_ = lean_ctor_get(v___x_789_, 1);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_817_ == 0)
{
lean_object* v_unused_818_; 
v_unused_818_ = lean_ctor_get(v___x_789_, 0);
lean_dec(v_unused_818_);
v___x_812_ = v___x_789_;
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___x_789_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_815_; 
if (v_isShared_813_ == 0)
{
lean_ctor_set(v___x_812_, 0, v_e_782_);
v___x_815_ = v___x_812_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_e_782_);
lean_ctor_set(v_reuseFailAlloc_816_, 1, v_a_810_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
case 0:
{
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_826_; 
lean_dec_ref(v_f_783_);
v_a_819_ = lean_ctor_get(v___x_789_, 1);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_826_ == 0)
{
lean_object* v_unused_827_; 
v_unused_827_ = lean_ctor_get(v___x_789_, 0);
lean_dec(v_unused_827_);
v___x_821_ = v___x_789_;
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_789_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_824_; 
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 0, v_e_782_);
v___x_824_ = v___x_821_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_e_782_);
lean_ctor_set(v_reuseFailAlloc_825_, 1, v_a_819_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
case 1:
{
lean_object* v_a_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_835_; 
lean_dec_ref(v_f_783_);
v_a_828_ = lean_ctor_get(v___x_789_, 1);
v_isSharedCheck_835_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_835_ == 0)
{
lean_object* v_unused_836_; 
v_unused_836_ = lean_ctor_get(v___x_789_, 0);
lean_dec(v_unused_836_);
v___x_830_ = v___x_789_;
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_a_828_);
lean_dec(v___x_789_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_833_; 
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 0, v_e_782_);
v___x_833_ = v___x_830_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_e_782_);
lean_ctor_set(v_reuseFailAlloc_834_, 1, v_a_828_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
}
case 4:
{
lean_object* v_a_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_844_; 
lean_dec_ref(v_f_783_);
v_a_837_ = lean_ctor_get(v___x_789_, 1);
v_isSharedCheck_844_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_844_ == 0)
{
lean_object* v_unused_845_; 
v_unused_845_ = lean_ctor_get(v___x_789_, 0);
lean_dec(v_unused_845_);
v___x_839_ = v___x_789_;
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_a_837_);
lean_dec(v___x_789_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_842_; 
if (v_isShared_840_ == 0)
{
lean_ctor_set(v___x_839_, 0, v_e_782_);
v___x_842_ = v___x_839_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_e_782_);
lean_ctor_set(v_reuseFailAlloc_843_, 1, v_a_837_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
}
case 3:
{
lean_object* v_a_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_853_; 
lean_dec_ref(v_f_783_);
v_a_846_ = lean_ctor_get(v___x_789_, 1);
v_isSharedCheck_853_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_853_ == 0)
{
lean_object* v_unused_854_; 
v_unused_854_ = lean_ctor_get(v___x_789_, 0);
lean_dec(v_unused_854_);
v___x_848_ = v___x_789_;
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_a_846_);
lean_dec(v___x_789_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_851_; 
if (v_isShared_849_ == 0)
{
lean_ctor_set(v___x_848_, 0, v_e_782_);
v___x_851_ = v___x_848_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_e_782_);
lean_ctor_set(v_reuseFailAlloc_852_, 1, v_a_846_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
}
default: 
{
lean_object* v_a_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
v_a_855_ = lean_ctor_get(v___x_789_, 1);
lean_inc(v_a_855_);
lean_dec_ref_known(v___x_789_, 2);
v___x_856_ = lean_obj_once(&l_Lean_Meta_Sym_replaceS_x27___closed__1, &l_Lean_Meta_Sym_replaceS_x27___closed__1_once, _init_l_Lean_Meta_Sym_replaceS_x27___closed__1);
v___x_857_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit(v_e_782_, v___x_787_, v_f_783_, v___x_856_, v_a_784_, v_a_785_, v_a_855_);
if (lean_obj_tag(v___x_857_) == 0)
{
lean_object* v_a_858_; lean_object* v_a_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_867_; 
v_a_858_ = lean_ctor_get(v___x_857_, 0);
v_a_859_ = lean_ctor_get(v___x_857_, 1);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_867_ == 0)
{
v___x_861_ = v___x_857_;
v_isShared_862_ = v_isSharedCheck_867_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_a_859_);
lean_inc(v_a_858_);
lean_dec(v___x_857_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_867_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v_fst_863_; lean_object* v___x_865_; 
v_fst_863_ = lean_ctor_get(v_a_858_, 0);
lean_inc(v_fst_863_);
lean_dec(v_a_858_);
if (v_isShared_862_ == 0)
{
lean_ctor_set(v___x_861_, 0, v_fst_863_);
v___x_865_ = v___x_861_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_fst_863_);
lean_ctor_set(v_reuseFailAlloc_866_, 1, v_a_859_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
else
{
lean_object* v_a_868_; lean_object* v_a_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_876_; 
v_a_868_ = lean_ctor_get(v___x_857_, 0);
v_a_869_ = lean_ctor_get(v___x_857_, 1);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_876_ == 0)
{
v___x_871_ = v___x_857_;
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_a_869_);
lean_inc(v_a_868_);
lean_dec(v___x_857_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_874_; 
if (v_isShared_872_ == 0)
{
v___x_874_ = v___x_871_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_a_868_);
lean_ctor_set(v_reuseFailAlloc_875_, 1, v_a_869_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_877_; lean_object* v_a_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_885_; 
lean_dec_ref(v_f_783_);
lean_dec_ref(v_e_782_);
v_a_877_ = lean_ctor_get(v___x_789_, 0);
v_a_878_ = lean_ctor_get(v___x_789_, 1);
v_isSharedCheck_885_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_885_ == 0)
{
v___x_880_ = v___x_789_;
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_a_878_);
lean_inc(v_a_877_);
lean_dec(v___x_789_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_883_; 
if (v_isShared_881_ == 0)
{
v___x_883_ = v___x_880_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_a_877_);
lean_ctor_set(v_reuseFailAlloc_884_, 1, v_a_878_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_replaceS_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_782_ = stack[0].m_obj;
lean_object* v_f_783_ = stack[1].m_obj;
uint8_t v_a_784_ = stack[2].m_num;
lean_object* v_a_785_ = stack[3].m_obj;
lean_object* v_a_786_ = stack[4].m_obj;
lean_object* v_res_886_;
v_res_886_ = l_Lean_Meta_Sym_replaceS_x27(v_e_782_, v_f_783_, v_a_784_, v_a_785_, v_a_786_);
stack->m_obj
 = v_res_886_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_replaceS_x27___boxed(lean_object* v_e_887_, lean_object* v_f_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_){
_start:
{
uint8_t v_a_boxed_892_; lean_object* v_res_893_; 
v_a_boxed_892_ = lean_unbox(v_a_889_);
v_res_893_ = l_Lean_Meta_Sym_replaceS_x27(v_e_887_, v_f_888_, v_a_boxed_892_, v_a_890_, v_a_891_);
lean_dec_ref(v_a_890_);
return v_res_893_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_replaceS___closed__0(void){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = l_Lean_Meta_Sym_instInhabitedSymM___redArg();
return v___x_894_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_replaceS___closed__3(void){
_start:
{
lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_897_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___closed__26));
v___x_898_ = lean_unsigned_to_nat(16u);
v___x_899_ = lean_unsigned_to_nat(62u);
v___x_900_ = ((lean_object*)(l_Lean_Meta_Sym_replaceS___closed__2));
v___x_901_ = ((lean_object*)(l_Lean_Meta_Sym_replaceS___closed__1));
v___x_902_ = l_mkPanicMessageWithDecl(v___x_901_, v___x_900_, v___x_899_, v___x_898_, v___x_897_);
return v___x_902_;
}
}
lean_object* l_Lean_Meta_Sym_replaceS(lean_object* v_e_903_, lean_object* v_f_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_){
_start:
{
lean_object* v___x_912_; lean_object* v___x_913_; uint8_t v_debug_914_; lean_object* v___x_915_; lean_object* v_env_916_; lean_object* v___x_917_; lean_object* v___x_918_; uint8_t v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_912_ = lean_obj_once(&l_Lean_Meta_Sym_replaceS___closed__0, &l_Lean_Meta_Sym_replaceS___closed__0_once, _init_l_Lean_Meta_Sym_replaceS___closed__0);
v___x_913_ = lean_st_ref_get(v_a_906_);
v_debug_914_ = lean_ctor_get_uint8(v___x_913_, sizeof(void*)*12);
lean_dec(v___x_913_);
v___x_915_ = lean_st_ref_get(v_a_910_);
v_env_916_ = lean_ctor_get(v___x_915_, 0);
lean_inc_ref(v_env_916_);
lean_dec(v___x_915_);
v___x_917_ = lean_box(v_debug_914_);
v___x_918_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_replaceS_x27___boxed), 5, 3);
lean_closure_set(v___x_918_, 0, v_e_903_);
lean_closure_set(v___x_918_, 1, v_f_904_);
lean_closure_set(v___x_918_, 2, v___x_917_);
v___x_919_ = 0;
v___x_920_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_920_, 0, v_env_916_);
lean_ctor_set_uint8(v___x_920_, sizeof(void*)*1, v___x_919_);
lean_ctor_set_uint8(v___x_920_, sizeof(void*)*1 + 1, v___x_919_);
v___x_921_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___x_918_, v___x_920_, v_a_906_);
if (lean_obj_tag(v___x_921_) == 0)
{
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_933_; 
v_a_922_ = lean_ctor_get(v___x_921_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_921_);
if (v_isSharedCheck_933_ == 0)
{
v___x_924_ = v___x_921_;
v_isShared_925_ = v_isSharedCheck_933_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v___x_921_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_933_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
if (lean_obj_tag(v_a_922_) == 0)
{
lean_object* v___x_926_; lean_object* v___x_36__overap_927_; lean_object* v___x_928_; 
lean_dec_ref_known(v_a_922_, 1);
lean_del_object(v___x_924_);
v___x_926_ = lean_obj_once(&l_Lean_Meta_Sym_replaceS___closed__3, &l_Lean_Meta_Sym_replaceS___closed__3_once, _init_l_Lean_Meta_Sym_replaceS___closed__3);
v___x_36__overap_927_ = l_panic___redArg(v___x_912_, v___x_926_);
lean_inc(v_a_910_);
lean_inc_ref(v_a_909_);
lean_inc(v_a_908_);
lean_inc_ref(v_a_907_);
lean_inc(v_a_906_);
lean_inc_ref(v_a_905_);
v___x_928_ = lean_apply_7(v___x_36__overap_927_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, lean_box(0));
return v___x_928_;
}
else
{
lean_object* v_a_929_; lean_object* v___x_931_; 
v_a_929_ = lean_ctor_get(v_a_922_, 0);
lean_inc(v_a_929_);
lean_dec_ref_known(v_a_922_, 1);
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 0, v_a_929_);
v___x_931_ = v___x_924_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_a_929_);
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
else
{
lean_object* v_a_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_941_; 
v_a_934_ = lean_ctor_get(v___x_921_, 0);
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_921_);
if (v_isSharedCheck_941_ == 0)
{
v___x_936_ = v___x_921_;
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_a_934_);
lean_dec(v___x_921_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_939_; 
if (v_isShared_937_ == 0)
{
v___x_939_ = v___x_936_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_a_934_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_replaceS_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_903_ = stack[0].m_obj;
lean_object* v_f_904_ = stack[1].m_obj;
lean_object* v_a_905_ = stack[2].m_obj;
lean_object* v_a_906_ = stack[3].m_obj;
lean_object* v_a_907_ = stack[4].m_obj;
lean_object* v_a_908_ = stack[5].m_obj;
lean_object* v_a_909_ = stack[6].m_obj;
lean_object* v_a_910_ = stack[7].m_obj;
lean_object* v_res_942_;
v_res_942_ = l_Lean_Meta_Sym_replaceS(v_e_903_, v_f_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_);
stack->m_obj
 = v_res_942_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_replaceS___boxed(lean_object* v_e_943_, lean_object* v_f_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l_Lean_Meta_Sym_replaceS(v_e_943_, v_f_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_, v_a_949_, v_a_950_);
lean_dec(v_a_950_);
lean_dec_ref(v_a_949_);
lean_dec(v_a_948_);
lean_dec_ref(v_a_947_);
lean_dec(v_a_946_);
lean_dec_ref(v_a_945_);
return v_res_952_;
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
