// Lean compiler output
// Module: Lean.Meta.Sym.InstantiateS
// Imports: public import Lean.Meta.Sym.SymM import Lean.Meta.Sym.LooseBVarsS import Init.Grind
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
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Sym_instBEqExprPtr___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instHashableExprPtr___lam__0___boxed(lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instInhabited___redArg___lam__0(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Builder_share1___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_liftLooseBVarsS_x27(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_looseBVarRange(lean_object*);
lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Builder_assertShared(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_seqRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Sym_runShareCommonM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instInhabitedSymM(lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_Lean_Expr_isBVar(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11_spec__12_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11_spec__12_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11_spec__12___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___lam__0, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8___closed__0_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___lam__1, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___lam__2, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8___closed__2_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_map, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8___closed__3 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8___closed__3_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_pure, .m_arity = 5, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8___closed__4 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8___closed__4_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_seqRight, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8___closed__5 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8___closed__5_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_bind, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8___closed__6 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8___closed__6_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__6(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "_private.Lean.Meta.Sym.ReplaceS.0.Lean.Meta.Sym.visit"};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Meta.Sym.ReplaceS"};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__0;
static lean_once_cell_t l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__1;
static lean_once_cell_t l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevRangeS___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_instantiateRevRangeS___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Meta.Sym.AlphaShareBuilder"};
static const lean_object* l_Lean_Meta_Sym_instantiateRevRangeS___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_instantiateRevRangeS___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_instantiateRevRangeS___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Lean.Meta.Sym.Internal.liftBuilderM"};
static const lean_object* l_Lean_Meta_Sym_instantiateRevRangeS___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_instantiateRevRangeS___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Sym_instantiateRevRangeS___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instantiateRevRangeS___closed__2;
static const lean_string_object l_Lean_Meta_Sym_instantiateRevRangeS___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Lean.Meta.Sym.InstantiateS"};
static const lean_object* l_Lean_Meta_Sym_instantiateRevRangeS___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_instantiateRevRangeS___closed__3_value;
static const lean_string_object l_Lean_Meta_Sym_instantiateRevRangeS___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Lean.Meta.Sym.instantiateRevRangeS"};
static const lean_object* l_Lean_Meta_Sym_instantiateRevRangeS___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_instantiateRevRangeS___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Sym_instantiateRevRangeS___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instantiateRevRangeS___closed__5;
static lean_once_cell_t l_Lean_Meta_Sym_instantiateRevRangeS___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instantiateRevRangeS___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevRangeS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevRangeS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11_spec__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11_spec__12_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11_spec__12_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_instBEqExprPtr___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1___closed__0_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_instHashableExprPtr___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 70, .m_data = "_private.Lean.Meta.Sym.InstantiateS.0.Lean.Meta.Sym.instantiateRangeS'"};
static const lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "application expected"};
static const lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Expr.updateAppS!"};
static const lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__2;
static const lean_string_object l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 86, .m_capacity = 86, .m_length = 85, .m_data = "_private.Lean.Meta.Sym.InstantiateS.0.Lean.Meta.Sym.instantiateRevBetaS'.visitAppBeta"};
static const lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "_private.Lean.Meta.Sym.InstantiateS.0.Lean.Meta.Sym.instantiateRevBetaS'.visit"};
static const lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevBetaS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevBetaS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_betaRevS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_betaRevS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_betaS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_betaS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___redArg(lean_object* v_idx_1_, lean_object* v___y_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = l_Lean_Expr_bvar___override(v_idx_1_);
v___x_4_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_3_, v___y_2_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0(lean_object* v_idx_5_, uint8_t v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___redArg(v_idx_5_, v___y_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___boxed(lean_object* v_idx_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_){
_start:
{
uint8_t v___y_26116__boxed_14_; lean_object* v_res_15_; 
v___y_26116__boxed_14_ = lean_unbox(v___y_11_);
v_res_15_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0(v_idx_10_, v___y_26116__boxed_14_, v___y_12_, v___y_13_);
lean_dec_ref(v___y_12_);
return v_res_15_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__0(void){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = l_Lean_Meta_Sym_instInhabitedSymM(lean_box(0));
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(lean_object* v_msg_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_){
_start:
{
lean_object* v___x_25_; lean_object* v___x_2973__overap_26_; lean_object* v___x_27_; 
v___x_25_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__0, &l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__0);
v___x_2973__overap_26_ = lean_panic_fn_borrowed(v___x_25_, v_msg_17_);
lean_inc(v___y_23_);
lean_inc_ref(v___y_22_);
lean_inc(v___y_21_);
lean_inc_ref(v___y_20_);
lean_inc(v___y_19_);
lean_inc_ref(v___y_18_);
v___x_27_ = lean_apply_7(v___x_2973__overap_26_, v___y_18_, v___y_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_, lean_box(0));
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___boxed(lean_object* v_msg_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(v_msg_28_, v___y_29_, v___y_30_, v___y_31_, v___y_32_, v___y_33_, v___y_34_);
lean_dec(v___y_34_);
lean_dec_ref(v___y_33_);
lean_dec(v___y_32_);
lean_dec_ref(v___y_31_);
lean_dec(v___y_30_);
lean_dec_ref(v___y_29_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__2(lean_object* v_f_37_, lean_object* v_a_38_, lean_object* v___y_39_, uint8_t v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_){
_start:
{
lean_object* v___y_44_; lean_object* v___y_45_; 
if (v___y_40_ == 0)
{
v___y_44_ = v___y_39_;
v___y_45_ = v___y_42_;
goto v___jp_43_;
}
else
{
lean_object* v___x_67_; 
v___x_67_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_f_37_, v___y_40_, v___y_41_, v___y_42_);
if (lean_obj_tag(v___x_67_) == 0)
{
lean_object* v_a_68_; lean_object* v___x_69_; 
v_a_68_ = lean_ctor_get(v___x_67_, 1);
lean_inc(v_a_68_);
lean_dec_ref_known(v___x_67_, 2);
v___x_69_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_a_38_, v___y_40_, v___y_41_, v_a_68_);
if (lean_obj_tag(v___x_69_) == 0)
{
lean_object* v_a_70_; 
v_a_70_ = lean_ctor_get(v___x_69_, 1);
lean_inc(v_a_70_);
lean_dec_ref_known(v___x_69_, 2);
v___y_44_ = v___y_39_;
v___y_45_ = v_a_70_;
goto v___jp_43_;
}
else
{
lean_object* v_a_71_; lean_object* v_a_72_; lean_object* v___x_74_; uint8_t v_isShared_75_; uint8_t v_isSharedCheck_79_; 
lean_dec_ref(v___y_39_);
lean_dec_ref(v_a_38_);
lean_dec_ref(v_f_37_);
v_a_71_ = lean_ctor_get(v___x_69_, 0);
v_a_72_ = lean_ctor_get(v___x_69_, 1);
v_isSharedCheck_79_ = !lean_is_exclusive(v___x_69_);
if (v_isSharedCheck_79_ == 0)
{
v___x_74_ = v___x_69_;
v_isShared_75_ = v_isSharedCheck_79_;
goto v_resetjp_73_;
}
else
{
lean_inc(v_a_72_);
lean_inc(v_a_71_);
lean_dec(v___x_69_);
v___x_74_ = lean_box(0);
v_isShared_75_ = v_isSharedCheck_79_;
goto v_resetjp_73_;
}
v_resetjp_73_:
{
lean_object* v___x_77_; 
if (v_isShared_75_ == 0)
{
v___x_77_ = v___x_74_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v_a_71_);
lean_ctor_set(v_reuseFailAlloc_78_, 1, v_a_72_);
v___x_77_ = v_reuseFailAlloc_78_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
return v___x_77_;
}
}
}
}
else
{
lean_object* v_a_80_; lean_object* v_a_81_; lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_88_; 
lean_dec_ref(v___y_39_);
lean_dec_ref(v_a_38_);
lean_dec_ref(v_f_37_);
v_a_80_ = lean_ctor_get(v___x_67_, 0);
v_a_81_ = lean_ctor_get(v___x_67_, 1);
v_isSharedCheck_88_ = !lean_is_exclusive(v___x_67_);
if (v_isSharedCheck_88_ == 0)
{
v___x_83_ = v___x_67_;
v_isShared_84_ = v_isSharedCheck_88_;
goto v_resetjp_82_;
}
else
{
lean_inc(v_a_81_);
lean_inc(v_a_80_);
lean_dec(v___x_67_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_88_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v___x_86_; 
if (v_isShared_84_ == 0)
{
v___x_86_ = v___x_83_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v_a_80_);
lean_ctor_set(v_reuseFailAlloc_87_, 1, v_a_81_);
v___x_86_ = v_reuseFailAlloc_87_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
return v___x_86_;
}
}
}
}
v___jp_43_:
{
lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_46_ = l_Lean_Expr_app___override(v_f_37_, v_a_38_);
v___x_47_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_46_, v___y_45_);
if (lean_obj_tag(v___x_47_) == 0)
{
lean_object* v_a_48_; lean_object* v_a_49_; lean_object* v___x_51_; uint8_t v_isShared_52_; uint8_t v_isSharedCheck_57_; 
v_a_48_ = lean_ctor_get(v___x_47_, 0);
v_a_49_ = lean_ctor_get(v___x_47_, 1);
v_isSharedCheck_57_ = !lean_is_exclusive(v___x_47_);
if (v_isSharedCheck_57_ == 0)
{
v___x_51_ = v___x_47_;
v_isShared_52_ = v_isSharedCheck_57_;
goto v_resetjp_50_;
}
else
{
lean_inc(v_a_49_);
lean_inc(v_a_48_);
lean_dec(v___x_47_);
v___x_51_ = lean_box(0);
v_isShared_52_ = v_isSharedCheck_57_;
goto v_resetjp_50_;
}
v_resetjp_50_:
{
lean_object* v___x_53_; lean_object* v___x_55_; 
v___x_53_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_53_, 0, v_a_48_);
lean_ctor_set(v___x_53_, 1, v___y_44_);
if (v_isShared_52_ == 0)
{
lean_ctor_set(v___x_51_, 0, v___x_53_);
v___x_55_ = v___x_51_;
goto v_reusejp_54_;
}
else
{
lean_object* v_reuseFailAlloc_56_; 
v_reuseFailAlloc_56_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_56_, 0, v___x_53_);
lean_ctor_set(v_reuseFailAlloc_56_, 1, v_a_49_);
v___x_55_ = v_reuseFailAlloc_56_;
goto v_reusejp_54_;
}
v_reusejp_54_:
{
return v___x_55_;
}
}
}
else
{
lean_object* v_a_58_; lean_object* v_a_59_; lean_object* v___x_61_; uint8_t v_isShared_62_; uint8_t v_isSharedCheck_66_; 
lean_dec_ref(v___y_44_);
v_a_58_ = lean_ctor_get(v___x_47_, 0);
v_a_59_ = lean_ctor_get(v___x_47_, 1);
v_isSharedCheck_66_ = !lean_is_exclusive(v___x_47_);
if (v_isSharedCheck_66_ == 0)
{
v___x_61_ = v___x_47_;
v_isShared_62_ = v_isSharedCheck_66_;
goto v_resetjp_60_;
}
else
{
lean_inc(v_a_59_);
lean_inc(v_a_58_);
lean_dec(v___x_47_);
v___x_61_ = lean_box(0);
v_isShared_62_ = v_isSharedCheck_66_;
goto v_resetjp_60_;
}
v_resetjp_60_:
{
lean_object* v___x_64_; 
if (v_isShared_62_ == 0)
{
v___x_64_ = v___x_61_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_65_; 
v_reuseFailAlloc_65_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_65_, 0, v_a_58_);
lean_ctor_set(v_reuseFailAlloc_65_, 1, v_a_59_);
v___x_64_ = v_reuseFailAlloc_65_;
goto v_reusejp_63_;
}
v_reusejp_63_:
{
return v___x_64_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__2___boxed(lean_object* v_f_89_, lean_object* v_a_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_){
_start:
{
uint8_t v___y_26156__boxed_95_; lean_object* v_res_96_; 
v___y_26156__boxed_95_ = lean_unbox(v___y_92_);
v_res_96_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__2(v_f_89_, v_a_90_, v___y_91_, v___y_26156__boxed_95_, v___y_93_, v___y_94_);
lean_dec_ref(v___y_93_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__4(lean_object* v_x_97_, uint8_t v_bi_98_, lean_object* v_t_99_, lean_object* v_b_100_, lean_object* v___y_101_, uint8_t v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_){
_start:
{
lean_object* v___y_106_; lean_object* v___y_107_; 
if (v___y_102_ == 0)
{
v___y_106_ = v___y_101_;
v___y_107_ = v___y_104_;
goto v___jp_105_;
}
else
{
lean_object* v___x_129_; 
v___x_129_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_99_, v___y_102_, v___y_103_, v___y_104_);
if (lean_obj_tag(v___x_129_) == 0)
{
lean_object* v_a_130_; lean_object* v___x_131_; 
v_a_130_ = lean_ctor_get(v___x_129_, 1);
lean_inc(v_a_130_);
lean_dec_ref_known(v___x_129_, 2);
v___x_131_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_100_, v___y_102_, v___y_103_, v_a_130_);
if (lean_obj_tag(v___x_131_) == 0)
{
lean_object* v_a_132_; 
v_a_132_ = lean_ctor_get(v___x_131_, 1);
lean_inc(v_a_132_);
lean_dec_ref_known(v___x_131_, 2);
v___y_106_ = v___y_101_;
v___y_107_ = v_a_132_;
goto v___jp_105_;
}
else
{
lean_object* v_a_133_; lean_object* v_a_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_141_; 
lean_dec_ref(v___y_101_);
lean_dec_ref(v_b_100_);
lean_dec_ref(v_t_99_);
lean_dec(v_x_97_);
v_a_133_ = lean_ctor_get(v___x_131_, 0);
v_a_134_ = lean_ctor_get(v___x_131_, 1);
v_isSharedCheck_141_ = !lean_is_exclusive(v___x_131_);
if (v_isSharedCheck_141_ == 0)
{
v___x_136_ = v___x_131_;
v_isShared_137_ = v_isSharedCheck_141_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_a_134_);
lean_inc(v_a_133_);
lean_dec(v___x_131_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_141_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v___x_139_; 
if (v_isShared_137_ == 0)
{
v___x_139_ = v___x_136_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v_a_133_);
lean_ctor_set(v_reuseFailAlloc_140_, 1, v_a_134_);
v___x_139_ = v_reuseFailAlloc_140_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
return v___x_139_;
}
}
}
}
else
{
lean_object* v_a_142_; lean_object* v_a_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_150_; 
lean_dec_ref(v___y_101_);
lean_dec_ref(v_b_100_);
lean_dec_ref(v_t_99_);
lean_dec(v_x_97_);
v_a_142_ = lean_ctor_get(v___x_129_, 0);
v_a_143_ = lean_ctor_get(v___x_129_, 1);
v_isSharedCheck_150_ = !lean_is_exclusive(v___x_129_);
if (v_isSharedCheck_150_ == 0)
{
v___x_145_ = v___x_129_;
v_isShared_146_ = v_isSharedCheck_150_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_a_143_);
lean_inc(v_a_142_);
lean_dec(v___x_129_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_150_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___x_148_; 
if (v_isShared_146_ == 0)
{
v___x_148_ = v___x_145_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v_a_142_);
lean_ctor_set(v_reuseFailAlloc_149_, 1, v_a_143_);
v___x_148_ = v_reuseFailAlloc_149_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
return v___x_148_;
}
}
}
}
v___jp_105_:
{
lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_108_ = l_Lean_Expr_forallE___override(v_x_97_, v_t_99_, v_b_100_, v_bi_98_);
v___x_109_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_108_, v___y_107_);
if (lean_obj_tag(v___x_109_) == 0)
{
lean_object* v_a_110_; lean_object* v_a_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_119_; 
v_a_110_ = lean_ctor_get(v___x_109_, 0);
v_a_111_ = lean_ctor_get(v___x_109_, 1);
v_isSharedCheck_119_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_119_ == 0)
{
v___x_113_ = v___x_109_;
v_isShared_114_ = v_isSharedCheck_119_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_a_111_);
lean_inc(v_a_110_);
lean_dec(v___x_109_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_119_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v___x_115_; lean_object* v___x_117_; 
v___x_115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_115_, 0, v_a_110_);
lean_ctor_set(v___x_115_, 1, v___y_106_);
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 0, v___x_115_);
v___x_117_ = v___x_113_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v___x_115_);
lean_ctor_set(v_reuseFailAlloc_118_, 1, v_a_111_);
v___x_117_ = v_reuseFailAlloc_118_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
return v___x_117_;
}
}
}
else
{
lean_object* v_a_120_; lean_object* v_a_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_128_; 
lean_dec_ref(v___y_106_);
v_a_120_ = lean_ctor_get(v___x_109_, 0);
v_a_121_ = lean_ctor_get(v___x_109_, 1);
v_isSharedCheck_128_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_128_ == 0)
{
v___x_123_ = v___x_109_;
v_isShared_124_ = v_isSharedCheck_128_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_a_121_);
lean_inc(v_a_120_);
lean_dec(v___x_109_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_128_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_126_; 
if (v_isShared_124_ == 0)
{
v___x_126_ = v___x_123_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v_a_120_);
lean_ctor_set(v_reuseFailAlloc_127_, 1, v_a_121_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
return v___x_126_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__4___boxed(lean_object* v_x_151_, lean_object* v_bi_152_, lean_object* v_t_153_, lean_object* v_b_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_){
_start:
{
uint8_t v_bi_boxed_159_; uint8_t v___y_26262__boxed_160_; lean_object* v_res_161_; 
v_bi_boxed_159_ = lean_unbox(v_bi_152_);
v___y_26262__boxed_160_ = lean_unbox(v___y_156_);
v_res_161_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__4(v_x_151_, v_bi_boxed_159_, v_t_153_, v_b_154_, v___y_155_, v___y_26262__boxed_160_, v___y_157_, v___y_158_);
lean_dec_ref(v___y_157_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__7(lean_object* v_structName_162_, lean_object* v_idx_163_, lean_object* v_struct_164_, lean_object* v___y_165_, uint8_t v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_){
_start:
{
lean_object* v___y_170_; lean_object* v___y_171_; 
if (v___y_166_ == 0)
{
v___y_170_ = v___y_165_;
v___y_171_ = v___y_168_;
goto v___jp_169_;
}
else
{
lean_object* v___x_193_; 
v___x_193_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_struct_164_, v___y_166_, v___y_167_, v___y_168_);
if (lean_obj_tag(v___x_193_) == 0)
{
lean_object* v_a_194_; 
v_a_194_ = lean_ctor_get(v___x_193_, 1);
lean_inc(v_a_194_);
lean_dec_ref_known(v___x_193_, 2);
v___y_170_ = v___y_165_;
v___y_171_ = v_a_194_;
goto v___jp_169_;
}
else
{
lean_object* v_a_195_; lean_object* v_a_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_203_; 
lean_dec_ref(v___y_165_);
lean_dec_ref(v_struct_164_);
lean_dec(v_idx_163_);
lean_dec(v_structName_162_);
v_a_195_ = lean_ctor_get(v___x_193_, 0);
v_a_196_ = lean_ctor_get(v___x_193_, 1);
v_isSharedCheck_203_ = !lean_is_exclusive(v___x_193_);
if (v_isSharedCheck_203_ == 0)
{
v___x_198_ = v___x_193_;
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_a_196_);
lean_inc(v_a_195_);
lean_dec(v___x_193_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_201_; 
if (v_isShared_199_ == 0)
{
v___x_201_ = v___x_198_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v_a_195_);
lean_ctor_set(v_reuseFailAlloc_202_, 1, v_a_196_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
return v___x_201_;
}
}
}
}
v___jp_169_:
{
lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_172_ = l_Lean_Expr_proj___override(v_structName_162_, v_idx_163_, v_struct_164_);
v___x_173_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_172_, v___y_171_);
if (lean_obj_tag(v___x_173_) == 0)
{
lean_object* v_a_174_; lean_object* v_a_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_183_; 
v_a_174_ = lean_ctor_get(v___x_173_, 0);
v_a_175_ = lean_ctor_get(v___x_173_, 1);
v_isSharedCheck_183_ = !lean_is_exclusive(v___x_173_);
if (v_isSharedCheck_183_ == 0)
{
v___x_177_ = v___x_173_;
v_isShared_178_ = v_isSharedCheck_183_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_a_175_);
lean_inc(v_a_174_);
lean_dec(v___x_173_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_183_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_179_; lean_object* v___x_181_; 
v___x_179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_179_, 0, v_a_174_);
lean_ctor_set(v___x_179_, 1, v___y_170_);
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 0, v___x_179_);
v___x_181_ = v___x_177_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v___x_179_);
lean_ctor_set(v_reuseFailAlloc_182_, 1, v_a_175_);
v___x_181_ = v_reuseFailAlloc_182_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
return v___x_181_;
}
}
}
else
{
lean_object* v_a_184_; lean_object* v_a_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_192_; 
lean_dec_ref(v___y_170_);
v_a_184_ = lean_ctor_get(v___x_173_, 0);
v_a_185_ = lean_ctor_get(v___x_173_, 1);
v_isSharedCheck_192_ = !lean_is_exclusive(v___x_173_);
if (v_isSharedCheck_192_ == 0)
{
v___x_187_ = v___x_173_;
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_a_185_);
lean_inc(v_a_184_);
lean_dec(v___x_173_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_190_; 
if (v_isShared_188_ == 0)
{
v___x_190_ = v___x_187_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v_a_184_);
lean_ctor_set(v_reuseFailAlloc_191_, 1, v_a_185_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__7___boxed(lean_object* v_structName_204_, lean_object* v_idx_205_, lean_object* v_struct_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_){
_start:
{
uint8_t v___y_26368__boxed_211_; lean_object* v_res_212_; 
v___y_26368__boxed_211_ = lean_unbox(v___y_208_);
v_res_212_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__7(v_structName_204_, v_idx_205_, v_struct_206_, v___y_207_, v___y_26368__boxed_211_, v___y_209_, v___y_210_);
lean_dec_ref(v___y_209_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11_spec__12_spec__13___redArg(lean_object* v_m_213_, lean_object* v_query_214_, lean_object* v_x_215_, lean_object* v_x_216_, lean_object* v_x_217_){
_start:
{
lean_object* v_zero_218_; uint8_t v_isZero_219_; 
v_zero_218_ = lean_unsigned_to_nat(0u);
v_isZero_219_ = lean_nat_dec_eq(v_x_216_, v_zero_218_);
if (v_isZero_219_ == 1)
{
lean_dec(v_x_217_);
lean_dec(v_x_216_);
if (lean_obj_tag(v_x_215_) == 0)
{
lean_object* v___x_220_; 
v___x_220_ = lean_box(2);
return v___x_220_;
}
else
{
lean_object* v_val_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_228_; 
v_val_221_ = lean_ctor_get(v_x_215_, 0);
v_isSharedCheck_228_ = !lean_is_exclusive(v_x_215_);
if (v_isSharedCheck_228_ == 0)
{
v___x_223_ = v_x_215_;
v_isShared_224_ = v_isSharedCheck_228_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_val_221_);
lean_dec(v_x_215_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_228_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___x_226_; 
if (v_isShared_224_ == 0)
{
v___x_226_ = v___x_223_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v_val_221_);
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
else
{
lean_object* v_keyArray_229_; lean_object* v_valueArray_230_; lean_object* v___x_231_; uint8_t v_isSome_232_; 
v_keyArray_229_ = lean_ctor_get(v_m_213_, 1);
v_valueArray_230_ = lean_ctor_get(v_m_213_, 2);
v___x_231_ = lean_array_fget_borrowed(v_keyArray_229_, v_x_217_);
v_isSome_232_ = lean_noption_is_some(v___x_231_);
if (v_isSome_232_ == 0)
{
lean_dec(v_x_216_);
if (lean_obj_tag(v_x_215_) == 0)
{
lean_object* v___x_233_; 
v___x_233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_233_, 0, v_x_217_);
return v___x_233_;
}
else
{
lean_object* v_val_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_241_; 
lean_dec(v_x_217_);
v_val_234_ = lean_ctor_get(v_x_215_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v_x_215_);
if (v_isSharedCheck_241_ == 0)
{
v___x_236_ = v_x_215_;
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_val_234_);
lean_dec(v_x_215_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v___x_239_; 
if (v_isShared_237_ == 0)
{
v___x_239_ = v___x_236_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_val_234_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
}
}
else
{
lean_object* v_one_242_; lean_object* v_n_243_; lean_object* v___y_245_; 
v_one_242_ = lean_unsigned_to_nat(1u);
v_n_243_ = lean_nat_sub(v_x_216_, v_one_242_);
lean_dec(v_x_216_);
if (v_isSome_232_ == 0)
{
goto v___jp_251_;
}
else
{
lean_object* v___x_253_; uint8_t v_isSome_254_; 
v___x_253_ = lean_array_fget_borrowed(v_valueArray_230_, v_x_217_);
v_isSome_254_ = lean_noption_is_some(v___x_253_);
if (v_isSome_254_ == 0)
{
goto v___jp_251_;
}
else
{
lean_object* v_val_255_; lean_object* v_fst_256_; lean_object* v_snd_257_; lean_object* v_fst_258_; lean_object* v_snd_259_; lean_object* v_val_260_; uint8_t v___y_262_; size_t v___x_269_; size_t v___x_270_; uint8_t v___x_271_; 
lean_inc(v___x_231_);
v_val_255_ = lean_noption_get(v___x_231_);
v_fst_256_ = lean_ctor_get(v_val_255_, 0);
lean_inc(v_fst_256_);
v_snd_257_ = lean_ctor_get(v_val_255_, 1);
lean_inc(v_snd_257_);
v_fst_258_ = lean_ctor_get(v_query_214_, 0);
v_snd_259_ = lean_ctor_get(v_query_214_, 1);
lean_inc(v___x_253_);
v_val_260_ = lean_noption_get(v___x_253_);
v___x_269_ = lean_ptr_addr(v_fst_256_);
lean_dec(v_fst_256_);
v___x_270_ = lean_ptr_addr(v_fst_258_);
v___x_271_ = lean_usize_dec_eq(v___x_269_, v___x_270_);
if (v___x_271_ == 0)
{
lean_dec(v_snd_257_);
v___y_262_ = v___x_271_;
goto v___jp_261_;
}
else
{
uint8_t v___x_272_; 
v___x_272_ = lean_nat_dec_eq(v_snd_257_, v_snd_259_);
lean_dec(v_snd_257_);
v___y_262_ = v___x_272_;
goto v___jp_261_;
}
v___jp_261_:
{
if (v___y_262_ == 0)
{
lean_object* v___x_263_; lean_object* v___x_264_; uint8_t v___x_265_; 
lean_dec(v_val_260_);
lean_dec(v_val_255_);
v___x_263_ = lean_array_get_size(v_keyArray_229_);
v___x_264_ = lean_nat_add(v_x_217_, v_one_242_);
lean_dec(v_x_217_);
v___x_265_ = lean_nat_dec_lt(v___x_264_, v___x_263_);
if (v___x_265_ == 0)
{
lean_dec(v___x_264_);
v_x_216_ = v_n_243_;
v_x_217_ = v_zero_218_;
goto _start;
}
else
{
v_x_216_ = v_n_243_;
v_x_217_ = v___x_264_;
goto _start;
}
}
else
{
lean_object* v___x_268_; 
lean_dec(v_n_243_);
lean_dec(v_x_215_);
v___x_268_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_268_, 0, v_x_217_);
lean_ctor_set(v___x_268_, 1, v_val_255_);
lean_ctor_set(v___x_268_, 2, v_val_260_);
return v___x_268_;
}
}
}
}
v___jp_244_:
{
lean_object* v___x_246_; lean_object* v___x_247_; uint8_t v___x_248_; 
v___x_246_ = lean_array_get_size(v_keyArray_229_);
v___x_247_ = lean_nat_add(v_x_217_, v_one_242_);
lean_dec(v_x_217_);
v___x_248_ = lean_nat_dec_lt(v___x_247_, v___x_246_);
if (v___x_248_ == 0)
{
lean_dec(v___x_247_);
v_x_215_ = v___y_245_;
v_x_216_ = v_n_243_;
v_x_217_ = v_zero_218_;
goto _start;
}
else
{
v_x_215_ = v___y_245_;
v_x_216_ = v_n_243_;
v_x_217_ = v___x_247_;
goto _start;
}
}
v___jp_251_:
{
if (lean_obj_tag(v_x_215_) == 0)
{
lean_object* v___x_252_; 
lean_inc(v_x_217_);
v___x_252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_252_, 0, v_x_217_);
v___y_245_ = v___x_252_;
goto v___jp_244_;
}
else
{
v___y_245_ = v_x_215_;
goto v___jp_244_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11_spec__12_spec__13___redArg___boxed(lean_object* v_m_273_, lean_object* v_query_274_, lean_object* v_x_275_, lean_object* v_x_276_, lean_object* v_x_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11_spec__12_spec__13___redArg(v_m_273_, v_query_274_, v_x_275_, v_x_276_, v_x_277_);
lean_dec_ref(v_query_274_);
lean_dec_ref(v_m_273_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11_spec__12___redArg(lean_object* v_m_279_, lean_object* v_query_280_){
_start:
{
lean_object* v_keyArray_281_; lean_object* v_fst_282_; lean_object* v_snd_283_; lean_object* v___x_284_; size_t v___x_285_; size_t v___x_286_; size_t v___x_287_; uint64_t v___x_288_; uint64_t v___x_289_; uint64_t v___x_290_; uint64_t v___x_291_; uint64_t v___x_292_; uint64_t v_fold_293_; uint64_t v___x_294_; uint64_t v___x_295_; uint64_t v___x_296_; size_t v___x_297_; size_t v___x_298_; size_t v___x_299_; size_t v___x_300_; size_t v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v_keyArray_281_ = lean_ctor_get(v_m_279_, 1);
v_fst_282_ = lean_ctor_get(v_query_280_, 0);
v_snd_283_ = lean_ctor_get(v_query_280_, 1);
v___x_284_ = lean_array_get_size(v_keyArray_281_);
v___x_285_ = lean_ptr_addr(v_fst_282_);
v___x_286_ = ((size_t)3ULL);
v___x_287_ = lean_usize_shift_right(v___x_285_, v___x_286_);
v___x_288_ = lean_usize_to_uint64(v___x_287_);
v___x_289_ = lean_uint64_of_nat(v_snd_283_);
v___x_290_ = lean_uint64_mix_hash(v___x_288_, v___x_289_);
v___x_291_ = 32ULL;
v___x_292_ = lean_uint64_shift_right(v___x_290_, v___x_291_);
v_fold_293_ = lean_uint64_xor(v___x_290_, v___x_292_);
v___x_294_ = 16ULL;
v___x_295_ = lean_uint64_shift_right(v_fold_293_, v___x_294_);
v___x_296_ = lean_uint64_xor(v_fold_293_, v___x_295_);
v___x_297_ = lean_uint64_to_usize(v___x_296_);
v___x_298_ = lean_usize_of_nat(v___x_284_);
v___x_299_ = ((size_t)1ULL);
v___x_300_ = lean_usize_sub(v___x_298_, v___x_299_);
v___x_301_ = lean_usize_land(v___x_297_, v___x_300_);
v___x_302_ = lean_usize_to_nat(v___x_301_);
v___x_303_ = lean_box(0);
v___x_304_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11_spec__12_spec__13___redArg(v_m_279_, v_query_280_, v___x_303_, v___x_284_, v___x_302_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11_spec__12___redArg___boxed(lean_object* v_m_305_, lean_object* v_query_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11_spec__12___redArg(v_m_305_, v_query_306_);
lean_dec_ref(v_query_306_);
lean_dec_ref(v_m_305_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11___redArg(lean_object* v_m_308_, lean_object* v_query_309_){
_start:
{
lean_object* v___x_310_; 
v___x_310_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11_spec__12___redArg(v_m_308_, v_query_309_);
if (lean_obj_tag(v___x_310_) == 0)
{
lean_object* v_index_311_; lean_object* v_key_312_; lean_object* v_value_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_320_; 
v_index_311_ = lean_ctor_get(v___x_310_, 0);
v_key_312_ = lean_ctor_get(v___x_310_, 1);
v_value_313_ = lean_ctor_get(v___x_310_, 2);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_310_);
if (v_isSharedCheck_320_ == 0)
{
v___x_315_ = v___x_310_;
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_value_313_);
lean_inc(v_key_312_);
lean_inc(v_index_311_);
lean_dec(v___x_310_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_318_; 
if (v_isShared_316_ == 0)
{
v___x_318_ = v___x_315_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_index_311_);
lean_ctor_set(v_reuseFailAlloc_319_, 1, v_key_312_);
lean_ctor_set(v_reuseFailAlloc_319_, 2, v_value_313_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
}
else
{
lean_object* v___x_321_; 
lean_dec(v___x_310_);
v___x_321_ = lean_box(1);
return v___x_321_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11___redArg___boxed(lean_object* v_m_322_, lean_object* v_query_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11___redArg(v_m_322_, v_query_323_);
lean_dec_ref(v_query_323_);
lean_dec_ref(v_m_322_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3___redArg(lean_object* v_m_325_, lean_object* v_a_326_){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11___redArg(v_m_325_, v_a_326_);
if (lean_obj_tag(v___x_327_) == 0)
{
lean_object* v_value_328_; lean_object* v___x_329_; 
v_value_328_ = lean_ctor_get(v___x_327_, 2);
lean_inc(v_value_328_);
lean_dec_ref_known(v___x_327_, 3);
v___x_329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_329_, 0, v_value_328_);
return v___x_329_;
}
else
{
lean_object* v___x_330_; 
v___x_330_ = lean_box(0);
return v___x_330_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_m_331_, lean_object* v_a_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3___redArg(v_m_331_, v_a_332_);
lean_dec_ref(v_a_332_);
lean_dec_ref(v_m_331_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__3(lean_object* v_x_334_, uint8_t v_bi_335_, lean_object* v_t_336_, lean_object* v_b_337_, lean_object* v___y_338_, uint8_t v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_){
_start:
{
lean_object* v___y_343_; lean_object* v___y_344_; 
if (v___y_339_ == 0)
{
v___y_343_ = v___y_338_;
v___y_344_ = v___y_341_;
goto v___jp_342_;
}
else
{
lean_object* v___x_366_; 
v___x_366_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_336_, v___y_339_, v___y_340_, v___y_341_);
if (lean_obj_tag(v___x_366_) == 0)
{
lean_object* v_a_367_; lean_object* v___x_368_; 
v_a_367_ = lean_ctor_get(v___x_366_, 1);
lean_inc(v_a_367_);
lean_dec_ref_known(v___x_366_, 2);
v___x_368_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_337_, v___y_339_, v___y_340_, v_a_367_);
if (lean_obj_tag(v___x_368_) == 0)
{
lean_object* v_a_369_; 
v_a_369_ = lean_ctor_get(v___x_368_, 1);
lean_inc(v_a_369_);
lean_dec_ref_known(v___x_368_, 2);
v___y_343_ = v___y_338_;
v___y_344_ = v_a_369_;
goto v___jp_342_;
}
else
{
lean_object* v_a_370_; lean_object* v_a_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_378_; 
lean_dec_ref(v___y_338_);
lean_dec_ref(v_b_337_);
lean_dec_ref(v_t_336_);
lean_dec(v_x_334_);
v_a_370_ = lean_ctor_get(v___x_368_, 0);
v_a_371_ = lean_ctor_get(v___x_368_, 1);
v_isSharedCheck_378_ = !lean_is_exclusive(v___x_368_);
if (v_isSharedCheck_378_ == 0)
{
v___x_373_ = v___x_368_;
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_a_371_);
lean_inc(v_a_370_);
lean_dec(v___x_368_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_376_; 
if (v_isShared_374_ == 0)
{
v___x_376_ = v___x_373_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_a_370_);
lean_ctor_set(v_reuseFailAlloc_377_, 1, v_a_371_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
}
}
else
{
lean_object* v_a_379_; lean_object* v_a_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_387_; 
lean_dec_ref(v___y_338_);
lean_dec_ref(v_b_337_);
lean_dec_ref(v_t_336_);
lean_dec(v_x_334_);
v_a_379_ = lean_ctor_get(v___x_366_, 0);
v_a_380_ = lean_ctor_get(v___x_366_, 1);
v_isSharedCheck_387_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_387_ == 0)
{
v___x_382_ = v___x_366_;
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_a_380_);
lean_inc(v_a_379_);
lean_dec(v___x_366_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_385_; 
if (v_isShared_383_ == 0)
{
v___x_385_ = v___x_382_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v_a_379_);
lean_ctor_set(v_reuseFailAlloc_386_, 1, v_a_380_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
}
}
}
}
v___jp_342_:
{
lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_345_ = l_Lean_Expr_lam___override(v_x_334_, v_t_336_, v_b_337_, v_bi_335_);
v___x_346_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_345_, v___y_344_);
if (lean_obj_tag(v___x_346_) == 0)
{
lean_object* v_a_347_; lean_object* v_a_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_356_; 
v_a_347_ = lean_ctor_get(v___x_346_, 0);
v_a_348_ = lean_ctor_get(v___x_346_, 1);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_356_ == 0)
{
v___x_350_ = v___x_346_;
v_isShared_351_ = v_isSharedCheck_356_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_a_348_);
lean_inc(v_a_347_);
lean_dec(v___x_346_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_356_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_352_; lean_object* v___x_354_; 
v___x_352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_352_, 0, v_a_347_);
lean_ctor_set(v___x_352_, 1, v___y_343_);
if (v_isShared_351_ == 0)
{
lean_ctor_set(v___x_350_, 0, v___x_352_);
v___x_354_ = v___x_350_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v___x_352_);
lean_ctor_set(v_reuseFailAlloc_355_, 1, v_a_348_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
}
else
{
lean_object* v_a_357_; lean_object* v_a_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_365_; 
lean_dec_ref(v___y_343_);
v_a_357_ = lean_ctor_get(v___x_346_, 0);
v_a_358_ = lean_ctor_get(v___x_346_, 1);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_365_ == 0)
{
v___x_360_ = v___x_346_;
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_a_358_);
lean_inc(v_a_357_);
lean_dec(v___x_346_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_363_; 
if (v_isShared_361_ == 0)
{
v___x_363_ = v___x_360_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v_a_357_);
lean_ctor_set(v_reuseFailAlloc_364_, 1, v_a_358_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__3___boxed(lean_object* v_x_388_, lean_object* v_bi_389_, lean_object* v_t_390_, lean_object* v_b_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_){
_start:
{
uint8_t v_bi_boxed_396_; uint8_t v___y_26635__boxed_397_; lean_object* v_res_398_; 
v_bi_boxed_396_ = lean_unbox(v_bi_389_);
v___y_26635__boxed_397_ = lean_unbox(v___y_393_);
v_res_398_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__3(v_x_388_, v_bi_boxed_396_, v_t_390_, v_b_391_, v___y_392_, v___y_26635__boxed_397_, v___y_394_, v___y_395_);
lean_dec_ref(v___y_394_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8(lean_object* v_msg_406_, lean_object* v___y_407_, uint8_t v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_){
_start:
{
lean_object* v___f_411_; lean_object* v___f_412_; lean_object* v___f_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___f_423_; lean_object* v___f_424_; lean_object* v___f_425_; lean_object* v___f_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_25524__overap_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v___f_411_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8___closed__0));
v___f_412_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8___closed__1));
v___f_413_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8___closed__2));
v___x_414_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8___closed__3));
v___x_415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_415_, 0, v___x_414_);
lean_ctor_set(v___x_415_, 1, v___f_411_);
v___x_416_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8___closed__4));
v___x_417_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8___closed__5));
v___x_418_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_418_, 0, v___x_415_);
lean_ctor_set(v___x_418_, 1, v___x_416_);
lean_ctor_set(v___x_418_, 2, v___f_412_);
lean_ctor_set(v___x_418_, 3, v___f_413_);
lean_ctor_set(v___x_418_, 4, v___x_417_);
v___x_419_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8___closed__6));
v___x_420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_420_, 0, v___x_418_);
lean_ctor_set(v___x_420_, 1, v___x_419_);
v___x_421_ = l_ReaderT_instMonad___redArg(v___x_420_);
v___x_422_ = l_ReaderT_instMonad___redArg(v___x_421_);
lean_inc_ref_n(v___x_422_, 6);
v___f_423_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_423_, 0, v___x_422_);
v___f_424_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_424_, 0, v___x_422_);
v___f_425_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_425_, 0, v___x_422_);
v___f_426_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_426_, 0, v___x_422_);
v___x_427_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_427_, 0, lean_box(0));
lean_closure_set(v___x_427_, 1, lean_box(0));
lean_closure_set(v___x_427_, 2, v___x_422_);
v___x_428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_428_, 0, v___x_427_);
lean_ctor_set(v___x_428_, 1, v___f_423_);
v___x_429_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_429_, 0, lean_box(0));
lean_closure_set(v___x_429_, 1, lean_box(0));
lean_closure_set(v___x_429_, 2, v___x_422_);
v___x_430_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_430_, 0, v___x_428_);
lean_ctor_set(v___x_430_, 1, v___x_429_);
lean_ctor_set(v___x_430_, 2, v___f_424_);
lean_ctor_set(v___x_430_, 3, v___f_425_);
lean_ctor_set(v___x_430_, 4, v___f_426_);
v___x_431_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_431_, 0, lean_box(0));
lean_closure_set(v___x_431_, 1, lean_box(0));
lean_closure_set(v___x_431_, 2, v___x_422_);
v___x_432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_432_, 0, v___x_430_);
lean_ctor_set(v___x_432_, 1, v___x_431_);
v___x_433_ = l_Lean_instInhabitedExpr;
v___x_434_ = l_instInhabitedOfMonad___redArg(v___x_432_, v___x_433_);
v___x_25524__overap_435_ = lean_panic_fn_borrowed(v___x_434_, v_msg_406_);
lean_dec(v___x_434_);
v___x_436_ = lean_box(v___y_408_);
lean_inc_ref(v___y_409_);
v___x_437_ = lean_apply_4(v___x_25524__overap_435_, v___y_407_, v___x_436_, v___y_409_, v___y_410_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8___boxed(lean_object* v_msg_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
uint8_t v___y_26755__boxed_443_; lean_object* v_res_444_; 
v___y_26755__boxed_443_ = lean_unbox(v___y_440_);
v_res_444_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8(v_msg_438_, v___y_439_, v___y_26755__boxed_443_, v___y_441_, v___y_442_);
lean_dec_ref(v___y_441_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__5(lean_object* v_x_445_, lean_object* v_t_446_, lean_object* v_v_447_, lean_object* v_b_448_, uint8_t v_nondep_449_, lean_object* v___y_450_, uint8_t v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_){
_start:
{
lean_object* v___y_455_; lean_object* v___y_456_; 
if (v___y_451_ == 0)
{
v___y_455_ = v___y_450_;
v___y_456_ = v___y_453_;
goto v___jp_454_;
}
else
{
lean_object* v___x_478_; 
v___x_478_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_446_, v___y_451_, v___y_452_, v___y_453_);
if (lean_obj_tag(v___x_478_) == 0)
{
lean_object* v_a_479_; lean_object* v___x_480_; 
v_a_479_ = lean_ctor_get(v___x_478_, 1);
lean_inc(v_a_479_);
lean_dec_ref_known(v___x_478_, 2);
v___x_480_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_v_447_, v___y_451_, v___y_452_, v_a_479_);
if (lean_obj_tag(v___x_480_) == 0)
{
lean_object* v_a_481_; lean_object* v___x_482_; 
v_a_481_ = lean_ctor_get(v___x_480_, 1);
lean_inc(v_a_481_);
lean_dec_ref_known(v___x_480_, 2);
v___x_482_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_448_, v___y_451_, v___y_452_, v_a_481_);
if (lean_obj_tag(v___x_482_) == 0)
{
lean_object* v_a_483_; 
v_a_483_ = lean_ctor_get(v___x_482_, 1);
lean_inc(v_a_483_);
lean_dec_ref_known(v___x_482_, 2);
v___y_455_ = v___y_450_;
v___y_456_ = v_a_483_;
goto v___jp_454_;
}
else
{
lean_object* v_a_484_; lean_object* v_a_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_492_; 
lean_dec_ref(v___y_450_);
lean_dec_ref(v_b_448_);
lean_dec_ref(v_v_447_);
lean_dec_ref(v_t_446_);
lean_dec(v_x_445_);
v_a_484_ = lean_ctor_get(v___x_482_, 0);
v_a_485_ = lean_ctor_get(v___x_482_, 1);
v_isSharedCheck_492_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_492_ == 0)
{
v___x_487_ = v___x_482_;
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_a_485_);
lean_inc(v_a_484_);
lean_dec(v___x_482_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_490_; 
if (v_isShared_488_ == 0)
{
v___x_490_ = v___x_487_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_a_484_);
lean_ctor_set(v_reuseFailAlloc_491_, 1, v_a_485_);
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
else
{
lean_object* v_a_493_; lean_object* v_a_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_501_; 
lean_dec_ref(v___y_450_);
lean_dec_ref(v_b_448_);
lean_dec_ref(v_v_447_);
lean_dec_ref(v_t_446_);
lean_dec(v_x_445_);
v_a_493_ = lean_ctor_get(v___x_480_, 0);
v_a_494_ = lean_ctor_get(v___x_480_, 1);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_480_);
if (v_isSharedCheck_501_ == 0)
{
v___x_496_ = v___x_480_;
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_a_494_);
lean_inc(v_a_493_);
lean_dec(v___x_480_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_499_; 
if (v_isShared_497_ == 0)
{
v___x_499_ = v___x_496_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_a_493_);
lean_ctor_set(v_reuseFailAlloc_500_, 1, v_a_494_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
}
else
{
lean_object* v_a_502_; lean_object* v_a_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_510_; 
lean_dec_ref(v___y_450_);
lean_dec_ref(v_b_448_);
lean_dec_ref(v_v_447_);
lean_dec_ref(v_t_446_);
lean_dec(v_x_445_);
v_a_502_ = lean_ctor_get(v___x_478_, 0);
v_a_503_ = lean_ctor_get(v___x_478_, 1);
v_isSharedCheck_510_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_510_ == 0)
{
v___x_505_ = v___x_478_;
v_isShared_506_ = v_isSharedCheck_510_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_a_503_);
lean_inc(v_a_502_);
lean_dec(v___x_478_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_510_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_508_; 
if (v_isShared_506_ == 0)
{
v___x_508_ = v___x_505_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v_a_502_);
lean_ctor_set(v_reuseFailAlloc_509_, 1, v_a_503_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
}
}
}
}
v___jp_454_:
{
lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_457_ = l_Lean_Expr_letE___override(v_x_445_, v_t_446_, v_v_447_, v_b_448_, v_nondep_449_);
v___x_458_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_457_, v___y_456_);
if (lean_obj_tag(v___x_458_) == 0)
{
lean_object* v_a_459_; lean_object* v_a_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_468_; 
v_a_459_ = lean_ctor_get(v___x_458_, 0);
v_a_460_ = lean_ctor_get(v___x_458_, 1);
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_468_ == 0)
{
v___x_462_ = v___x_458_;
v_isShared_463_ = v_isSharedCheck_468_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_a_460_);
lean_inc(v_a_459_);
lean_dec(v___x_458_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_468_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_464_; lean_object* v___x_466_; 
v___x_464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_464_, 0, v_a_459_);
lean_ctor_set(v___x_464_, 1, v___y_455_);
if (v_isShared_463_ == 0)
{
lean_ctor_set(v___x_462_, 0, v___x_464_);
v___x_466_ = v___x_462_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v___x_464_);
lean_ctor_set(v_reuseFailAlloc_467_, 1, v_a_460_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
}
else
{
lean_object* v_a_469_; lean_object* v_a_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_477_; 
lean_dec_ref(v___y_455_);
v_a_469_ = lean_ctor_get(v___x_458_, 0);
v_a_470_ = lean_ctor_get(v___x_458_, 1);
v_isSharedCheck_477_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_477_ == 0)
{
v___x_472_ = v___x_458_;
v_isShared_473_ = v_isSharedCheck_477_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_a_470_);
lean_inc(v_a_469_);
lean_dec(v___x_458_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_477_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_475_; 
if (v_isShared_473_ == 0)
{
v___x_475_ = v___x_472_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v_a_469_);
lean_ctor_set(v_reuseFailAlloc_476_, 1, v_a_470_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__5___boxed(lean_object* v_x_511_, lean_object* v_t_512_, lean_object* v_v_513_, lean_object* v_b_514_, lean_object* v_nondep_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_){
_start:
{
uint8_t v_nondep_boxed_520_; uint8_t v___y_26826__boxed_521_; lean_object* v_res_522_; 
v_nondep_boxed_520_ = lean_unbox(v_nondep_515_);
v___y_26826__boxed_521_ = lean_unbox(v___y_517_);
v_res_522_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__5(v_x_511_, v_t_512_, v_v_513_, v_b_514_, v_nondep_boxed_520_, v___y_516_, v___y_26826__boxed_521_, v___y_518_, v___y_519_);
lean_dec_ref(v___y_518_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__6(lean_object* v_d_523_, lean_object* v_e_524_, lean_object* v___y_525_, uint8_t v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_){
_start:
{
lean_object* v___y_530_; lean_object* v___y_531_; 
if (v___y_526_ == 0)
{
v___y_530_ = v___y_525_;
v___y_531_ = v___y_528_;
goto v___jp_529_;
}
else
{
lean_object* v___x_553_; 
v___x_553_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_e_524_, v___y_526_, v___y_527_, v___y_528_);
if (lean_obj_tag(v___x_553_) == 0)
{
lean_object* v_a_554_; 
v_a_554_ = lean_ctor_get(v___x_553_, 1);
lean_inc(v_a_554_);
lean_dec_ref_known(v___x_553_, 2);
v___y_530_ = v___y_525_;
v___y_531_ = v_a_554_;
goto v___jp_529_;
}
else
{
lean_object* v_a_555_; lean_object* v_a_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_563_; 
lean_dec_ref(v___y_525_);
lean_dec_ref(v_e_524_);
lean_dec(v_d_523_);
v_a_555_ = lean_ctor_get(v___x_553_, 0);
v_a_556_ = lean_ctor_get(v___x_553_, 1);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_563_ == 0)
{
v___x_558_ = v___x_553_;
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_a_556_);
lean_inc(v_a_555_);
lean_dec(v___x_553_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_561_; 
if (v_isShared_559_ == 0)
{
v___x_561_ = v___x_558_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_a_555_);
lean_ctor_set(v_reuseFailAlloc_562_, 1, v_a_556_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
}
v___jp_529_:
{
lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_532_ = l_Lean_Expr_mdata___override(v_d_523_, v_e_524_);
v___x_533_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_532_, v___y_531_);
if (lean_obj_tag(v___x_533_) == 0)
{
lean_object* v_a_534_; lean_object* v_a_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_543_; 
v_a_534_ = lean_ctor_get(v___x_533_, 0);
v_a_535_ = lean_ctor_get(v___x_533_, 1);
v_isSharedCheck_543_ = !lean_is_exclusive(v___x_533_);
if (v_isSharedCheck_543_ == 0)
{
v___x_537_ = v___x_533_;
v_isShared_538_ = v_isSharedCheck_543_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_a_535_);
lean_inc(v_a_534_);
lean_dec(v___x_533_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_543_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_539_; lean_object* v___x_541_; 
v___x_539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_539_, 0, v_a_534_);
lean_ctor_set(v___x_539_, 1, v___y_530_);
if (v_isShared_538_ == 0)
{
lean_ctor_set(v___x_537_, 0, v___x_539_);
v___x_541_ = v___x_537_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v___x_539_);
lean_ctor_set(v_reuseFailAlloc_542_, 1, v_a_535_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
return v___x_541_;
}
}
}
else
{
lean_object* v_a_544_; lean_object* v_a_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_552_; 
lean_dec_ref(v___y_530_);
v_a_544_ = lean_ctor_get(v___x_533_, 0);
v_a_545_ = lean_ctor_get(v___x_533_, 1);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_533_);
if (v_isSharedCheck_552_ == 0)
{
v___x_547_ = v___x_533_;
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_a_545_);
lean_inc(v_a_544_);
lean_dec(v___x_533_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_550_; 
if (v_isShared_548_ == 0)
{
v___x_550_ = v___x_547_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_a_544_);
lean_ctor_set(v_reuseFailAlloc_551_, 1, v_a_545_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__6___boxed(lean_object* v_d_564_, lean_object* v_e_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_){
_start:
{
uint8_t v___y_26955__boxed_570_; lean_object* v_res_571_; 
v___y_26955__boxed_570_ = lean_unbox(v___y_567_);
v_res_571_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__6(v_d_564_, v_e_565_, v___y_566_, v___y_26955__boxed_570_, v___y_568_, v___y_569_);
lean_dec_ref(v___y_568_);
return v_res_571_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__3(void){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_575_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__2));
v___x_576_ = lean_unsigned_to_nat(67u);
v___x_577_ = lean_unsigned_to_nat(35u);
v___x_578_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__1));
v___x_579_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__0));
v___x_580_ = l_mkPanicMessageWithDecl(v___x_579_, v___x_578_, v___x_577_, v___x_576_, v___x_575_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1(lean_object* v_beginIdx_581_, lean_object* v_n_582_, lean_object* v_subst_583_, lean_object* v_e_584_, lean_object* v_offset_585_, lean_object* v_a_586_, uint8_t v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_){
_start:
{
switch(lean_obj_tag(v_e_584_))
{
case 5:
{
lean_object* v_fn_590_; lean_object* v_arg_591_; lean_object* v___x_592_; 
v_fn_590_ = lean_ctor_get(v_e_584_, 0);
v_arg_591_ = lean_ctor_get(v_e_584_, 1);
lean_inc(v_offset_585_);
lean_inc_ref(v_fn_590_);
v___x_592_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(v_beginIdx_581_, v_n_582_, v_subst_583_, v_fn_590_, v_offset_585_, v_a_586_, v_a_587_, v_a_588_, v_a_589_);
if (lean_obj_tag(v___x_592_) == 0)
{
lean_object* v_a_593_; lean_object* v_a_594_; lean_object* v_fst_595_; lean_object* v_snd_596_; lean_object* v___x_597_; 
v_a_593_ = lean_ctor_get(v___x_592_, 0);
lean_inc(v_a_593_);
v_a_594_ = lean_ctor_get(v___x_592_, 1);
lean_inc(v_a_594_);
lean_dec_ref_known(v___x_592_, 2);
v_fst_595_ = lean_ctor_get(v_a_593_, 0);
lean_inc(v_fst_595_);
v_snd_596_ = lean_ctor_get(v_a_593_, 1);
lean_inc(v_snd_596_);
lean_dec(v_a_593_);
lean_inc_ref(v_arg_591_);
v___x_597_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(v_beginIdx_581_, v_n_582_, v_subst_583_, v_arg_591_, v_offset_585_, v_snd_596_, v_a_587_, v_a_588_, v_a_594_);
if (lean_obj_tag(v___x_597_) == 0)
{
lean_object* v_a_598_; lean_object* v_a_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_624_; 
v_a_598_ = lean_ctor_get(v___x_597_, 0);
v_a_599_ = lean_ctor_get(v___x_597_, 1);
v_isSharedCheck_624_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_624_ == 0)
{
v___x_601_ = v___x_597_;
v_isShared_602_ = v_isSharedCheck_624_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_a_599_);
lean_inc(v_a_598_);
lean_dec(v___x_597_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_624_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v_fst_603_; lean_object* v_snd_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_623_; 
v_fst_603_ = lean_ctor_get(v_a_598_, 0);
v_snd_604_ = lean_ctor_get(v_a_598_, 1);
v_isSharedCheck_623_ = !lean_is_exclusive(v_a_598_);
if (v_isSharedCheck_623_ == 0)
{
v___x_606_ = v_a_598_;
v_isShared_607_ = v_isSharedCheck_623_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_snd_604_);
lean_inc(v_fst_603_);
lean_dec(v_a_598_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_623_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
uint8_t v___y_609_; size_t v___x_617_; size_t v___x_618_; uint8_t v___x_619_; 
v___x_617_ = lean_ptr_addr(v_fn_590_);
v___x_618_ = lean_ptr_addr(v_fst_595_);
v___x_619_ = lean_usize_dec_eq(v___x_617_, v___x_618_);
if (v___x_619_ == 0)
{
v___y_609_ = v___x_619_;
goto v___jp_608_;
}
else
{
size_t v___x_620_; size_t v___x_621_; uint8_t v___x_622_; 
v___x_620_ = lean_ptr_addr(v_arg_591_);
v___x_621_ = lean_ptr_addr(v_fst_603_);
v___x_622_ = lean_usize_dec_eq(v___x_620_, v___x_621_);
v___y_609_ = v___x_622_;
goto v___jp_608_;
}
v___jp_608_:
{
if (v___y_609_ == 0)
{
lean_object* v___x_610_; 
lean_del_object(v___x_606_);
lean_del_object(v___x_601_);
lean_dec_ref_known(v_e_584_, 2);
v___x_610_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__2(v_fst_595_, v_fst_603_, v_snd_604_, v_a_587_, v_a_588_, v_a_599_);
return v___x_610_;
}
else
{
lean_object* v___x_612_; 
lean_dec(v_fst_603_);
lean_dec(v_fst_595_);
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 0, v_e_584_);
v___x_612_ = v___x_606_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_e_584_);
lean_ctor_set(v_reuseFailAlloc_616_, 1, v_snd_604_);
v___x_612_ = v_reuseFailAlloc_616_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
lean_object* v___x_614_; 
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 0, v___x_612_);
v___x_614_ = v___x_601_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v___x_612_);
lean_ctor_set(v_reuseFailAlloc_615_, 1, v_a_599_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_595_);
lean_dec_ref_known(v_e_584_, 2);
return v___x_597_;
}
}
else
{
lean_dec_ref_known(v_e_584_, 2);
lean_dec(v_offset_585_);
return v___x_592_;
}
}
case 6:
{
lean_object* v_binderName_625_; lean_object* v_binderType_626_; lean_object* v_body_627_; uint8_t v_binderInfo_628_; lean_object* v___x_629_; 
v_binderName_625_ = lean_ctor_get(v_e_584_, 0);
v_binderType_626_ = lean_ctor_get(v_e_584_, 1);
v_body_627_ = lean_ctor_get(v_e_584_, 2);
v_binderInfo_628_ = lean_ctor_get_uint8(v_e_584_, sizeof(void*)*3 + 8);
lean_inc(v_offset_585_);
lean_inc_ref(v_binderType_626_);
v___x_629_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(v_beginIdx_581_, v_n_582_, v_subst_583_, v_binderType_626_, v_offset_585_, v_a_586_, v_a_587_, v_a_588_, v_a_589_);
if (lean_obj_tag(v___x_629_) == 0)
{
lean_object* v_a_630_; lean_object* v_a_631_; lean_object* v_fst_632_; lean_object* v_snd_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v_a_630_ = lean_ctor_get(v___x_629_, 0);
lean_inc(v_a_630_);
v_a_631_ = lean_ctor_get(v___x_629_, 1);
lean_inc(v_a_631_);
lean_dec_ref_known(v___x_629_, 2);
v_fst_632_ = lean_ctor_get(v_a_630_, 0);
lean_inc(v_fst_632_);
v_snd_633_ = lean_ctor_get(v_a_630_, 1);
lean_inc(v_snd_633_);
lean_dec(v_a_630_);
v___x_634_ = lean_unsigned_to_nat(1u);
v___x_635_ = lean_nat_add(v_offset_585_, v___x_634_);
lean_dec(v_offset_585_);
lean_inc_ref(v_body_627_);
v___x_636_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(v_beginIdx_581_, v_n_582_, v_subst_583_, v_body_627_, v___x_635_, v_snd_633_, v_a_587_, v_a_588_, v_a_631_);
if (lean_obj_tag(v___x_636_) == 0)
{
lean_object* v_a_637_; lean_object* v_a_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_663_; 
v_a_637_ = lean_ctor_get(v___x_636_, 0);
v_a_638_ = lean_ctor_get(v___x_636_, 1);
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_663_ == 0)
{
v___x_640_ = v___x_636_;
v_isShared_641_ = v_isSharedCheck_663_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_a_638_);
lean_inc(v_a_637_);
lean_dec(v___x_636_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_663_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v_fst_642_; lean_object* v_snd_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_662_; 
v_fst_642_ = lean_ctor_get(v_a_637_, 0);
v_snd_643_ = lean_ctor_get(v_a_637_, 1);
v_isSharedCheck_662_ = !lean_is_exclusive(v_a_637_);
if (v_isSharedCheck_662_ == 0)
{
v___x_645_ = v_a_637_;
v_isShared_646_ = v_isSharedCheck_662_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_snd_643_);
lean_inc(v_fst_642_);
lean_dec(v_a_637_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_662_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
uint8_t v___y_648_; size_t v___x_656_; size_t v___x_657_; uint8_t v___x_658_; 
v___x_656_ = lean_ptr_addr(v_binderType_626_);
v___x_657_ = lean_ptr_addr(v_fst_632_);
v___x_658_ = lean_usize_dec_eq(v___x_656_, v___x_657_);
if (v___x_658_ == 0)
{
v___y_648_ = v___x_658_;
goto v___jp_647_;
}
else
{
size_t v___x_659_; size_t v___x_660_; uint8_t v___x_661_; 
v___x_659_ = lean_ptr_addr(v_body_627_);
v___x_660_ = lean_ptr_addr(v_fst_642_);
v___x_661_ = lean_usize_dec_eq(v___x_659_, v___x_660_);
v___y_648_ = v___x_661_;
goto v___jp_647_;
}
v___jp_647_:
{
if (v___y_648_ == 0)
{
lean_object* v___x_649_; 
lean_inc(v_binderName_625_);
lean_del_object(v___x_645_);
lean_del_object(v___x_640_);
lean_dec_ref_known(v_e_584_, 3);
v___x_649_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__3(v_binderName_625_, v_binderInfo_628_, v_fst_632_, v_fst_642_, v_snd_643_, v_a_587_, v_a_588_, v_a_638_);
return v___x_649_;
}
else
{
lean_object* v___x_651_; 
lean_dec(v_fst_642_);
lean_dec(v_fst_632_);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 0, v_e_584_);
v___x_651_ = v___x_645_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_e_584_);
lean_ctor_set(v_reuseFailAlloc_655_, 1, v_snd_643_);
v___x_651_ = v_reuseFailAlloc_655_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
lean_object* v___x_653_; 
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 0, v___x_651_);
v___x_653_ = v___x_640_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v___x_651_);
lean_ctor_set(v_reuseFailAlloc_654_, 1, v_a_638_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_632_);
lean_dec_ref_known(v_e_584_, 3);
return v___x_636_;
}
}
else
{
lean_dec_ref_known(v_e_584_, 3);
lean_dec(v_offset_585_);
return v___x_629_;
}
}
case 7:
{
lean_object* v_binderName_664_; lean_object* v_binderType_665_; lean_object* v_body_666_; uint8_t v_binderInfo_667_; lean_object* v___x_668_; 
v_binderName_664_ = lean_ctor_get(v_e_584_, 0);
v_binderType_665_ = lean_ctor_get(v_e_584_, 1);
v_body_666_ = lean_ctor_get(v_e_584_, 2);
v_binderInfo_667_ = lean_ctor_get_uint8(v_e_584_, sizeof(void*)*3 + 8);
lean_inc(v_offset_585_);
lean_inc_ref(v_binderType_665_);
v___x_668_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(v_beginIdx_581_, v_n_582_, v_subst_583_, v_binderType_665_, v_offset_585_, v_a_586_, v_a_587_, v_a_588_, v_a_589_);
if (lean_obj_tag(v___x_668_) == 0)
{
lean_object* v_a_669_; lean_object* v_a_670_; lean_object* v_fst_671_; lean_object* v_snd_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v_a_669_ = lean_ctor_get(v___x_668_, 0);
lean_inc(v_a_669_);
v_a_670_ = lean_ctor_get(v___x_668_, 1);
lean_inc(v_a_670_);
lean_dec_ref_known(v___x_668_, 2);
v_fst_671_ = lean_ctor_get(v_a_669_, 0);
lean_inc(v_fst_671_);
v_snd_672_ = lean_ctor_get(v_a_669_, 1);
lean_inc(v_snd_672_);
lean_dec(v_a_669_);
v___x_673_ = lean_unsigned_to_nat(1u);
v___x_674_ = lean_nat_add(v_offset_585_, v___x_673_);
lean_dec(v_offset_585_);
lean_inc_ref(v_body_666_);
v___x_675_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(v_beginIdx_581_, v_n_582_, v_subst_583_, v_body_666_, v___x_674_, v_snd_672_, v_a_587_, v_a_588_, v_a_670_);
if (lean_obj_tag(v___x_675_) == 0)
{
lean_object* v_a_676_; lean_object* v_a_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_702_; 
v_a_676_ = lean_ctor_get(v___x_675_, 0);
v_a_677_ = lean_ctor_get(v___x_675_, 1);
v_isSharedCheck_702_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_702_ == 0)
{
v___x_679_ = v___x_675_;
v_isShared_680_ = v_isSharedCheck_702_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_a_677_);
lean_inc(v_a_676_);
lean_dec(v___x_675_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_702_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v_fst_681_; lean_object* v_snd_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_701_; 
v_fst_681_ = lean_ctor_get(v_a_676_, 0);
v_snd_682_ = lean_ctor_get(v_a_676_, 1);
v_isSharedCheck_701_ = !lean_is_exclusive(v_a_676_);
if (v_isSharedCheck_701_ == 0)
{
v___x_684_ = v_a_676_;
v_isShared_685_ = v_isSharedCheck_701_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_snd_682_);
lean_inc(v_fst_681_);
lean_dec(v_a_676_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_701_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
uint8_t v___y_687_; size_t v___x_695_; size_t v___x_696_; uint8_t v___x_697_; 
v___x_695_ = lean_ptr_addr(v_binderType_665_);
v___x_696_ = lean_ptr_addr(v_fst_671_);
v___x_697_ = lean_usize_dec_eq(v___x_695_, v___x_696_);
if (v___x_697_ == 0)
{
v___y_687_ = v___x_697_;
goto v___jp_686_;
}
else
{
size_t v___x_698_; size_t v___x_699_; uint8_t v___x_700_; 
v___x_698_ = lean_ptr_addr(v_body_666_);
v___x_699_ = lean_ptr_addr(v_fst_681_);
v___x_700_ = lean_usize_dec_eq(v___x_698_, v___x_699_);
v___y_687_ = v___x_700_;
goto v___jp_686_;
}
v___jp_686_:
{
if (v___y_687_ == 0)
{
lean_object* v___x_688_; 
lean_inc(v_binderName_664_);
lean_del_object(v___x_684_);
lean_del_object(v___x_679_);
lean_dec_ref_known(v_e_584_, 3);
v___x_688_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__4(v_binderName_664_, v_binderInfo_667_, v_fst_671_, v_fst_681_, v_snd_682_, v_a_587_, v_a_588_, v_a_677_);
return v___x_688_;
}
else
{
lean_object* v___x_690_; 
lean_dec(v_fst_681_);
lean_dec(v_fst_671_);
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 0, v_e_584_);
v___x_690_ = v___x_684_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_e_584_);
lean_ctor_set(v_reuseFailAlloc_694_, 1, v_snd_682_);
v___x_690_ = v_reuseFailAlloc_694_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
lean_object* v___x_692_; 
if (v_isShared_680_ == 0)
{
lean_ctor_set(v___x_679_, 0, v___x_690_);
v___x_692_ = v___x_679_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v___x_690_);
lean_ctor_set(v_reuseFailAlloc_693_, 1, v_a_677_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
return v___x_692_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_671_);
lean_dec_ref_known(v_e_584_, 3);
return v___x_675_;
}
}
else
{
lean_dec_ref_known(v_e_584_, 3);
lean_dec(v_offset_585_);
return v___x_668_;
}
}
case 8:
{
lean_object* v_declName_703_; lean_object* v_type_704_; lean_object* v_value_705_; lean_object* v_body_706_; uint8_t v_nondep_707_; lean_object* v___x_708_; 
v_declName_703_ = lean_ctor_get(v_e_584_, 0);
v_type_704_ = lean_ctor_get(v_e_584_, 1);
v_value_705_ = lean_ctor_get(v_e_584_, 2);
v_body_706_ = lean_ctor_get(v_e_584_, 3);
v_nondep_707_ = lean_ctor_get_uint8(v_e_584_, sizeof(void*)*4 + 8);
lean_inc(v_offset_585_);
lean_inc_ref(v_type_704_);
v___x_708_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(v_beginIdx_581_, v_n_582_, v_subst_583_, v_type_704_, v_offset_585_, v_a_586_, v_a_587_, v_a_588_, v_a_589_);
if (lean_obj_tag(v___x_708_) == 0)
{
lean_object* v_a_709_; lean_object* v_a_710_; lean_object* v_fst_711_; lean_object* v_snd_712_; lean_object* v___x_713_; 
v_a_709_ = lean_ctor_get(v___x_708_, 0);
lean_inc(v_a_709_);
v_a_710_ = lean_ctor_get(v___x_708_, 1);
lean_inc(v_a_710_);
lean_dec_ref_known(v___x_708_, 2);
v_fst_711_ = lean_ctor_get(v_a_709_, 0);
lean_inc(v_fst_711_);
v_snd_712_ = lean_ctor_get(v_a_709_, 1);
lean_inc(v_snd_712_);
lean_dec(v_a_709_);
lean_inc(v_offset_585_);
lean_inc_ref(v_value_705_);
v___x_713_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(v_beginIdx_581_, v_n_582_, v_subst_583_, v_value_705_, v_offset_585_, v_snd_712_, v_a_587_, v_a_588_, v_a_710_);
if (lean_obj_tag(v___x_713_) == 0)
{
lean_object* v_a_714_; lean_object* v_a_715_; lean_object* v_fst_716_; lean_object* v_snd_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v_a_714_ = lean_ctor_get(v___x_713_, 0);
lean_inc(v_a_714_);
v_a_715_ = lean_ctor_get(v___x_713_, 1);
lean_inc(v_a_715_);
lean_dec_ref_known(v___x_713_, 2);
v_fst_716_ = lean_ctor_get(v_a_714_, 0);
lean_inc(v_fst_716_);
v_snd_717_ = lean_ctor_get(v_a_714_, 1);
lean_inc(v_snd_717_);
lean_dec(v_a_714_);
v___x_718_ = lean_unsigned_to_nat(1u);
v___x_719_ = lean_nat_add(v_offset_585_, v___x_718_);
lean_dec(v_offset_585_);
lean_inc_ref(v_body_706_);
v___x_720_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(v_beginIdx_581_, v_n_582_, v_subst_583_, v_body_706_, v___x_719_, v_snd_717_, v_a_587_, v_a_588_, v_a_715_);
if (lean_obj_tag(v___x_720_) == 0)
{
lean_object* v_a_721_; lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_751_; 
v_a_721_ = lean_ctor_get(v___x_720_, 0);
v_a_722_ = lean_ctor_get(v___x_720_, 1);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_751_ == 0)
{
v___x_724_ = v___x_720_;
v_isShared_725_ = v_isSharedCheck_751_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_inc(v_a_721_);
lean_dec(v___x_720_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_751_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v_fst_726_; lean_object* v_snd_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_750_; 
v_fst_726_ = lean_ctor_get(v_a_721_, 0);
v_snd_727_ = lean_ctor_get(v_a_721_, 1);
v_isSharedCheck_750_ = !lean_is_exclusive(v_a_721_);
if (v_isSharedCheck_750_ == 0)
{
v___x_729_ = v_a_721_;
v_isShared_730_ = v_isSharedCheck_750_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_snd_727_);
lean_inc(v_fst_726_);
lean_dec(v_a_721_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_750_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
uint8_t v___y_732_; size_t v___x_744_; size_t v___x_745_; uint8_t v___x_746_; 
v___x_744_ = lean_ptr_addr(v_type_704_);
v___x_745_ = lean_ptr_addr(v_fst_711_);
v___x_746_ = lean_usize_dec_eq(v___x_744_, v___x_745_);
if (v___x_746_ == 0)
{
v___y_732_ = v___x_746_;
goto v___jp_731_;
}
else
{
size_t v___x_747_; size_t v___x_748_; uint8_t v___x_749_; 
v___x_747_ = lean_ptr_addr(v_value_705_);
v___x_748_ = lean_ptr_addr(v_fst_716_);
v___x_749_ = lean_usize_dec_eq(v___x_747_, v___x_748_);
v___y_732_ = v___x_749_;
goto v___jp_731_;
}
v___jp_731_:
{
if (v___y_732_ == 0)
{
lean_object* v___x_733_; 
lean_inc(v_declName_703_);
lean_del_object(v___x_729_);
lean_del_object(v___x_724_);
lean_dec_ref_known(v_e_584_, 4);
v___x_733_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__5(v_declName_703_, v_fst_711_, v_fst_716_, v_fst_726_, v_nondep_707_, v_snd_727_, v_a_587_, v_a_588_, v_a_722_);
return v___x_733_;
}
else
{
size_t v___x_734_; size_t v___x_735_; uint8_t v___x_736_; 
v___x_734_ = lean_ptr_addr(v_body_706_);
v___x_735_ = lean_ptr_addr(v_fst_726_);
v___x_736_ = lean_usize_dec_eq(v___x_734_, v___x_735_);
if (v___x_736_ == 0)
{
lean_object* v___x_737_; 
lean_inc(v_declName_703_);
lean_del_object(v___x_729_);
lean_del_object(v___x_724_);
lean_dec_ref_known(v_e_584_, 4);
v___x_737_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__5(v_declName_703_, v_fst_711_, v_fst_716_, v_fst_726_, v_nondep_707_, v_snd_727_, v_a_587_, v_a_588_, v_a_722_);
return v___x_737_;
}
else
{
lean_object* v___x_739_; 
lean_dec(v_fst_726_);
lean_dec(v_fst_716_);
lean_dec(v_fst_711_);
if (v_isShared_730_ == 0)
{
lean_ctor_set(v___x_729_, 0, v_e_584_);
v___x_739_ = v___x_729_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_e_584_);
lean_ctor_set(v_reuseFailAlloc_743_, 1, v_snd_727_);
v___x_739_ = v_reuseFailAlloc_743_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
lean_object* v___x_741_; 
if (v_isShared_725_ == 0)
{
lean_ctor_set(v___x_724_, 0, v___x_739_);
v___x_741_ = v___x_724_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v___x_739_);
lean_ctor_set(v_reuseFailAlloc_742_, 1, v_a_722_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
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
lean_dec(v_fst_716_);
lean_dec(v_fst_711_);
lean_dec_ref_known(v_e_584_, 4);
return v___x_720_;
}
}
else
{
lean_dec(v_fst_711_);
lean_dec_ref_known(v_e_584_, 4);
lean_dec(v_offset_585_);
return v___x_713_;
}
}
else
{
lean_dec_ref_known(v_e_584_, 4);
lean_dec(v_offset_585_);
return v___x_708_;
}
}
case 10:
{
lean_object* v_data_752_; lean_object* v_expr_753_; lean_object* v___x_754_; 
v_data_752_ = lean_ctor_get(v_e_584_, 0);
v_expr_753_ = lean_ctor_get(v_e_584_, 1);
lean_inc_ref(v_expr_753_);
v___x_754_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(v_beginIdx_581_, v_n_582_, v_subst_583_, v_expr_753_, v_offset_585_, v_a_586_, v_a_587_, v_a_588_, v_a_589_);
if (lean_obj_tag(v___x_754_) == 0)
{
lean_object* v_a_755_; lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_776_; 
v_a_755_ = lean_ctor_get(v___x_754_, 0);
v_a_756_ = lean_ctor_get(v___x_754_, 1);
v_isSharedCheck_776_ = !lean_is_exclusive(v___x_754_);
if (v_isSharedCheck_776_ == 0)
{
v___x_758_ = v___x_754_;
v_isShared_759_ = v_isSharedCheck_776_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_a_756_);
lean_inc(v_a_755_);
lean_dec(v___x_754_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_776_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v_fst_760_; lean_object* v_snd_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_775_; 
v_fst_760_ = lean_ctor_get(v_a_755_, 0);
v_snd_761_ = lean_ctor_get(v_a_755_, 1);
v_isSharedCheck_775_ = !lean_is_exclusive(v_a_755_);
if (v_isSharedCheck_775_ == 0)
{
v___x_763_ = v_a_755_;
v_isShared_764_ = v_isSharedCheck_775_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_snd_761_);
lean_inc(v_fst_760_);
lean_dec(v_a_755_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_775_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
size_t v___x_765_; size_t v___x_766_; uint8_t v___x_767_; 
v___x_765_ = lean_ptr_addr(v_expr_753_);
v___x_766_ = lean_ptr_addr(v_fst_760_);
v___x_767_ = lean_usize_dec_eq(v___x_765_, v___x_766_);
if (v___x_767_ == 0)
{
lean_object* v___x_768_; 
lean_inc(v_data_752_);
lean_del_object(v___x_763_);
lean_del_object(v___x_758_);
lean_dec_ref_known(v_e_584_, 2);
v___x_768_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__6(v_data_752_, v_fst_760_, v_snd_761_, v_a_587_, v_a_588_, v_a_756_);
return v___x_768_;
}
else
{
lean_object* v___x_770_; 
lean_dec(v_fst_760_);
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 0, v_e_584_);
v___x_770_ = v___x_763_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_e_584_);
lean_ctor_set(v_reuseFailAlloc_774_, 1, v_snd_761_);
v___x_770_ = v_reuseFailAlloc_774_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
lean_object* v___x_772_; 
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
lean_ctor_set(v_reuseFailAlloc_773_, 1, v_a_756_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_584_, 2);
return v___x_754_;
}
}
case 11:
{
lean_object* v_typeName_777_; lean_object* v_idx_778_; lean_object* v_struct_779_; lean_object* v___x_780_; 
v_typeName_777_ = lean_ctor_get(v_e_584_, 0);
v_idx_778_ = lean_ctor_get(v_e_584_, 1);
v_struct_779_ = lean_ctor_get(v_e_584_, 2);
lean_inc_ref(v_struct_779_);
v___x_780_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(v_beginIdx_581_, v_n_582_, v_subst_583_, v_struct_779_, v_offset_585_, v_a_586_, v_a_587_, v_a_588_, v_a_589_);
if (lean_obj_tag(v___x_780_) == 0)
{
lean_object* v_a_781_; lean_object* v_a_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_802_; 
v_a_781_ = lean_ctor_get(v___x_780_, 0);
v_a_782_ = lean_ctor_get(v___x_780_, 1);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_780_);
if (v_isSharedCheck_802_ == 0)
{
v___x_784_ = v___x_780_;
v_isShared_785_ = v_isSharedCheck_802_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_a_782_);
lean_inc(v_a_781_);
lean_dec(v___x_780_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_802_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v_fst_786_; lean_object* v_snd_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_801_; 
v_fst_786_ = lean_ctor_get(v_a_781_, 0);
v_snd_787_ = lean_ctor_get(v_a_781_, 1);
v_isSharedCheck_801_ = !lean_is_exclusive(v_a_781_);
if (v_isSharedCheck_801_ == 0)
{
v___x_789_ = v_a_781_;
v_isShared_790_ = v_isSharedCheck_801_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_snd_787_);
lean_inc(v_fst_786_);
lean_dec(v_a_781_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_801_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
size_t v___x_791_; size_t v___x_792_; uint8_t v___x_793_; 
v___x_791_ = lean_ptr_addr(v_struct_779_);
v___x_792_ = lean_ptr_addr(v_fst_786_);
v___x_793_ = lean_usize_dec_eq(v___x_791_, v___x_792_);
if (v___x_793_ == 0)
{
lean_object* v___x_794_; 
lean_inc(v_idx_778_);
lean_inc(v_typeName_777_);
lean_del_object(v___x_789_);
lean_del_object(v___x_784_);
lean_dec_ref_known(v_e_584_, 3);
v___x_794_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__7(v_typeName_777_, v_idx_778_, v_fst_786_, v_snd_787_, v_a_587_, v_a_588_, v_a_782_);
return v___x_794_;
}
else
{
lean_object* v___x_796_; 
lean_dec(v_fst_786_);
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 0, v_e_584_);
v___x_796_ = v___x_789_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_e_584_);
lean_ctor_set(v_reuseFailAlloc_800_, 1, v_snd_787_);
v___x_796_ = v_reuseFailAlloc_800_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
lean_object* v___x_798_; 
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 0, v___x_796_);
v___x_798_ = v___x_784_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v___x_796_);
lean_ctor_set(v_reuseFailAlloc_799_, 1, v_a_782_);
v___x_798_ = v_reuseFailAlloc_799_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
return v___x_798_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_584_, 3);
return v___x_780_;
}
}
default: 
{
lean_object* v___x_803_; lean_object* v___x_804_; 
lean_dec(v_offset_585_);
lean_dec_ref(v_e_584_);
v___x_803_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__3);
v___x_804_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8(v___x_803_, v_a_586_, v_a_587_, v_a_588_, v_a_589_);
return v___x_804_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(lean_object* v_beginIdx_805_, lean_object* v_n_806_, lean_object* v_subst_807_, lean_object* v_e_808_, lean_object* v_offset_809_, lean_object* v_a_810_, uint8_t v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_){
_start:
{
lean_object* v_key_814_; lean_object* v___x_815_; 
lean_inc(v_offset_809_);
lean_inc_ref(v_e_808_);
v_key_814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_814_, 0, v_e_808_);
lean_ctor_set(v_key_814_, 1, v_offset_809_);
v___x_815_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3___redArg(v_a_810_, v_key_814_);
if (lean_obj_tag(v___x_815_) == 1)
{
lean_object* v_val_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
lean_dec_ref_known(v_key_814_, 2);
lean_dec(v_offset_809_);
lean_dec_ref(v_e_808_);
v_val_816_ = lean_ctor_get(v___x_815_, 0);
lean_inc(v_val_816_);
lean_dec_ref_known(v___x_815_, 1);
v___x_817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_817_, 0, v_val_816_);
lean_ctor_set(v___x_817_, 1, v_a_810_);
v___x_818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_818_, 0, v___x_817_);
lean_ctor_set(v___x_818_, 1, v_a_813_);
return v___x_818_;
}
else
{
lean_object* v_s_u2081_819_; 
lean_dec(v___x_815_);
v_s_u2081_819_ = lean_nat_add(v_beginIdx_805_, v_offset_809_);
switch(lean_obj_tag(v_e_808_))
{
case 0:
{
lean_object* v_deBruijnIndex_820_; uint8_t v___x_821_; 
v_deBruijnIndex_820_ = lean_ctor_get(v_e_808_, 0);
v___x_821_ = lean_nat_dec_le(v_s_u2081_819_, v_deBruijnIndex_820_);
lean_dec(v_s_u2081_819_);
if (v___x_821_ == 0)
{
lean_object* v___x_822_; 
lean_dec(v_offset_809_);
v___x_822_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_814_, v_e_808_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
return v___x_822_;
}
else
{
lean_object* v___x_823_; uint8_t v___x_824_; 
lean_inc(v_deBruijnIndex_820_);
lean_dec_ref_known(v_e_808_, 1);
v___x_823_ = lean_nat_add(v_offset_809_, v_n_806_);
v___x_824_ = lean_nat_dec_lt(v_deBruijnIndex_820_, v___x_823_);
lean_dec(v___x_823_);
if (v___x_824_ == 0)
{
lean_object* v___x_825_; lean_object* v___x_826_; 
lean_dec(v_offset_809_);
v___x_825_ = lean_nat_sub(v_deBruijnIndex_820_, v_n_806_);
lean_dec(v_deBruijnIndex_820_);
v___x_826_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___redArg(v___x_825_, v_a_813_);
if (lean_obj_tag(v___x_826_) == 0)
{
lean_object* v_a_827_; lean_object* v_a_828_; lean_object* v___x_829_; 
v_a_827_ = lean_ctor_get(v___x_826_, 0);
lean_inc(v_a_827_);
v_a_828_ = lean_ctor_get(v___x_826_, 1);
lean_inc(v_a_828_);
lean_dec_ref_known(v___x_826_, 2);
v___x_829_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_814_, v_a_827_, v_a_810_, v_a_811_, v_a_812_, v_a_828_);
return v___x_829_;
}
else
{
lean_object* v_a_830_; lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_838_; 
lean_dec_ref_known(v_key_814_, 2);
lean_dec_ref(v_a_810_);
v_a_830_ = lean_ctor_get(v___x_826_, 0);
v_a_831_ = lean_ctor_get(v___x_826_, 1);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_838_ == 0)
{
v___x_833_ = v___x_826_;
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_inc(v_a_830_);
lean_dec(v___x_826_);
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
else
{
lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v_v_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_839_ = lean_nat_sub(v_deBruijnIndex_820_, v_offset_809_);
lean_dec(v_deBruijnIndex_820_);
v___x_840_ = lean_nat_sub(v_n_806_, v___x_839_);
lean_dec(v___x_839_);
v___x_841_ = lean_unsigned_to_nat(1u);
v___x_842_ = lean_nat_sub(v___x_840_, v___x_841_);
lean_dec(v___x_840_);
v_v_843_ = lean_array_fget_borrowed(v_subst_807_, v___x_842_);
lean_dec(v___x_842_);
v___x_844_ = lean_unsigned_to_nat(0u);
lean_inc(v_v_843_);
v___x_845_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(v_v_843_, v___x_844_, v_offset_809_, v_a_811_, v_a_812_, v_a_813_);
lean_dec(v_offset_809_);
if (lean_obj_tag(v___x_845_) == 0)
{
lean_object* v_a_846_; lean_object* v_a_847_; lean_object* v___x_848_; 
v_a_846_ = lean_ctor_get(v___x_845_, 0);
lean_inc(v_a_846_);
v_a_847_ = lean_ctor_get(v___x_845_, 1);
lean_inc(v_a_847_);
lean_dec_ref_known(v___x_845_, 2);
v___x_848_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_814_, v_a_846_, v_a_810_, v_a_811_, v_a_812_, v_a_847_);
return v___x_848_;
}
else
{
lean_object* v_a_849_; lean_object* v_a_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_857_; 
lean_dec_ref_known(v_key_814_, 2);
lean_dec_ref(v_a_810_);
v_a_849_ = lean_ctor_get(v___x_845_, 0);
v_a_850_ = lean_ctor_get(v___x_845_, 1);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_857_ == 0)
{
v___x_852_ = v___x_845_;
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_inc(v_a_849_);
lean_dec(v___x_845_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_855_; 
if (v_isShared_853_ == 0)
{
v___x_855_ = v___x_852_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_a_849_);
lean_ctor_set(v_reuseFailAlloc_856_, 1, v_a_850_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
}
}
}
case 9:
{
lean_object* v___x_858_; 
lean_dec(v_s_u2081_819_);
lean_dec(v_offset_809_);
v___x_858_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_814_, v_e_808_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
return v___x_858_;
}
case 2:
{
lean_object* v___x_859_; 
lean_dec(v_s_u2081_819_);
lean_dec(v_offset_809_);
v___x_859_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_814_, v_e_808_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
return v___x_859_;
}
case 1:
{
lean_object* v___x_860_; 
lean_dec(v_s_u2081_819_);
lean_dec(v_offset_809_);
v___x_860_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_814_, v_e_808_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
return v___x_860_;
}
case 4:
{
lean_object* v___x_861_; 
lean_dec(v_s_u2081_819_);
lean_dec(v_offset_809_);
v___x_861_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_814_, v_e_808_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
return v___x_861_;
}
case 3:
{
lean_object* v___x_862_; 
lean_dec(v_s_u2081_819_);
lean_dec(v_offset_809_);
v___x_862_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_814_, v_e_808_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
return v___x_862_;
}
default: 
{
lean_object* v___x_863_; uint8_t v___x_864_; 
v___x_863_ = l_Lean_Expr_looseBVarRange(v_e_808_);
v___x_864_ = lean_nat_dec_le(v___x_863_, v_s_u2081_819_);
lean_dec(v_s_u2081_819_);
lean_dec(v___x_863_);
if (v___x_864_ == 0)
{
switch(lean_obj_tag(v_e_808_))
{
case 9:
{
lean_object* v___x_865_; 
lean_dec(v_offset_809_);
v___x_865_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_814_, v_e_808_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
return v___x_865_;
}
case 2:
{
lean_object* v___x_866_; 
lean_dec(v_offset_809_);
v___x_866_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_814_, v_e_808_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
return v___x_866_;
}
case 0:
{
lean_object* v___x_867_; 
lean_dec(v_offset_809_);
v___x_867_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_814_, v_e_808_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
return v___x_867_;
}
case 1:
{
lean_object* v___x_868_; 
lean_dec(v_offset_809_);
v___x_868_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_814_, v_e_808_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
return v___x_868_;
}
case 4:
{
lean_object* v___x_869_; 
lean_dec(v_offset_809_);
v___x_869_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_814_, v_e_808_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
return v___x_869_;
}
case 3:
{
lean_object* v___x_870_; 
lean_dec(v_offset_809_);
v___x_870_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_814_, v_e_808_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
return v___x_870_;
}
default: 
{
lean_object* v___x_871_; 
v___x_871_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1(v_beginIdx_805_, v_n_806_, v_subst_807_, v_e_808_, v_offset_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_object* v_a_872_; lean_object* v_a_873_; lean_object* v_fst_874_; lean_object* v_snd_875_; lean_object* v___x_876_; 
v_a_872_ = lean_ctor_get(v___x_871_, 0);
lean_inc(v_a_872_);
v_a_873_ = lean_ctor_get(v___x_871_, 1);
lean_inc(v_a_873_);
lean_dec_ref_known(v___x_871_, 2);
v_fst_874_ = lean_ctor_get(v_a_872_, 0);
lean_inc(v_fst_874_);
v_snd_875_ = lean_ctor_get(v_a_872_, 1);
lean_inc(v_snd_875_);
lean_dec(v_a_872_);
v___x_876_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_814_, v_fst_874_, v_snd_875_, v_a_811_, v_a_812_, v_a_873_);
return v___x_876_;
}
else
{
lean_dec_ref_known(v_key_814_, 2);
return v___x_871_;
}
}
}
}
else
{
lean_object* v___x_877_; 
lean_dec(v_offset_809_);
v___x_877_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_814_, v_e_808_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
return v___x_877_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1___boxed(lean_object* v_beginIdx_878_, lean_object* v_n_879_, lean_object* v_subst_880_, lean_object* v_e_881_, lean_object* v_offset_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_){
_start:
{
uint8_t v_a_boxed_887_; lean_object* v_res_888_; 
v_a_boxed_887_ = lean_unbox(v_a_884_);
v_res_888_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(v_beginIdx_878_, v_n_879_, v_subst_880_, v_e_881_, v_offset_882_, v_a_883_, v_a_boxed_887_, v_a_885_, v_a_886_);
lean_dec_ref(v_a_885_);
lean_dec_ref(v_subst_880_);
lean_dec(v_n_879_);
lean_dec(v_beginIdx_878_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___boxed(lean_object* v_beginIdx_889_, lean_object* v_n_890_, lean_object* v_subst_891_, lean_object* v_e_892_, lean_object* v_offset_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_){
_start:
{
uint8_t v_a_boxed_898_; lean_object* v_res_899_; 
v_a_boxed_898_ = lean_unbox(v_a_895_);
v_res_899_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1(v_beginIdx_889_, v_n_890_, v_subst_891_, v_e_892_, v_offset_893_, v_a_894_, v_a_boxed_898_, v_a_896_, v_a_897_);
lean_dec_ref(v_a_896_);
lean_dec_ref(v_subst_891_);
lean_dec(v_n_890_);
lean_dec(v_beginIdx_889_);
return v_res_899_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__0(void){
_start:
{
lean_object* v_cellCount_900_; lean_object* v___x_901_; 
v_cellCount_900_ = lean_unsigned_to_nat(16u);
v___x_901_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_900_);
return v___x_901_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__1(void){
_start:
{
lean_object* v_cellCount_902_; lean_object* v___x_903_; 
v_cellCount_902_ = lean_unsigned_to_nat(16u);
v___x_903_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_902_);
return v___x_903_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__2(void){
_start:
{
lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_904_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__1, &l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__1_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__1);
v___x_905_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__0, &l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__0_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__0);
v___x_906_ = lean_unsigned_to_nat(0u);
v___x_907_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_907_, 0, v___x_906_);
lean_ctor_set(v___x_907_, 1, v___x_905_);
lean_ctor_set(v___x_907_, 2, v___x_904_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevRangeS___lam__0(lean_object* v_e_908_, lean_object* v_beginIdx_909_, lean_object* v_n_910_, lean_object* v_subst_911_, uint8_t v_debug_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
lean_object* v___x_915_; 
v___x_915_ = lean_unsigned_to_nat(0u);
switch(lean_obj_tag(v_e_908_))
{
case 0:
{
lean_object* v_deBruijnIndex_916_; uint8_t v___x_917_; 
v_deBruijnIndex_916_ = lean_ctor_get(v_e_908_, 0);
v___x_917_ = lean_nat_dec_le(v_beginIdx_909_, v_deBruijnIndex_916_);
if (v___x_917_ == 0)
{
lean_object* v___x_918_; 
v___x_918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_918_, 0, v_e_908_);
lean_ctor_set(v___x_918_, 1, v___y_914_);
return v___x_918_;
}
else
{
uint8_t v___x_919_; 
lean_inc(v_deBruijnIndex_916_);
lean_dec_ref_known(v_e_908_, 1);
v___x_919_ = lean_nat_dec_lt(v_deBruijnIndex_916_, v_n_910_);
if (v___x_919_ == 0)
{
lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_920_ = lean_nat_sub(v_deBruijnIndex_916_, v_n_910_);
lean_dec(v_deBruijnIndex_916_);
v___x_921_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___redArg(v___x_920_, v___y_914_);
return v___x_921_;
}
else
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v_v_925_; lean_object* v___x_926_; 
v___x_922_ = lean_nat_sub(v_n_910_, v_deBruijnIndex_916_);
lean_dec(v_deBruijnIndex_916_);
v___x_923_ = lean_unsigned_to_nat(1u);
v___x_924_ = lean_nat_sub(v___x_922_, v___x_923_);
lean_dec(v___x_922_);
v_v_925_ = lean_array_fget_borrowed(v_subst_911_, v___x_924_);
lean_dec(v___x_924_);
lean_inc(v_v_925_);
v___x_926_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(v_v_925_, v___x_915_, v___x_915_, v_debug_912_, v___y_913_, v___y_914_);
return v___x_926_;
}
}
}
case 9:
{
lean_object* v___x_927_; 
v___x_927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_927_, 0, v_e_908_);
lean_ctor_set(v___x_927_, 1, v___y_914_);
return v___x_927_;
}
case 2:
{
lean_object* v___x_928_; 
v___x_928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_928_, 0, v_e_908_);
lean_ctor_set(v___x_928_, 1, v___y_914_);
return v___x_928_;
}
case 1:
{
lean_object* v___x_929_; 
v___x_929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_929_, 0, v_e_908_);
lean_ctor_set(v___x_929_, 1, v___y_914_);
return v___x_929_;
}
case 4:
{
lean_object* v___x_930_; 
v___x_930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_930_, 0, v_e_908_);
lean_ctor_set(v___x_930_, 1, v___y_914_);
return v___x_930_;
}
case 3:
{
lean_object* v___x_931_; 
v___x_931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_931_, 0, v_e_908_);
lean_ctor_set(v___x_931_, 1, v___y_914_);
return v___x_931_;
}
default: 
{
lean_object* v___x_932_; uint8_t v___x_933_; 
v___x_932_ = l_Lean_Expr_looseBVarRange(v_e_908_);
v___x_933_ = lean_nat_dec_le(v___x_932_, v_beginIdx_909_);
lean_dec(v___x_932_);
if (v___x_933_ == 0)
{
switch(lean_obj_tag(v_e_908_))
{
case 9:
{
lean_object* v___x_934_; 
v___x_934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_934_, 0, v_e_908_);
lean_ctor_set(v___x_934_, 1, v___y_914_);
return v___x_934_;
}
case 2:
{
lean_object* v___x_935_; 
v___x_935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_935_, 0, v_e_908_);
lean_ctor_set(v___x_935_, 1, v___y_914_);
return v___x_935_;
}
case 0:
{
lean_object* v___x_936_; 
v___x_936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_936_, 0, v_e_908_);
lean_ctor_set(v___x_936_, 1, v___y_914_);
return v___x_936_;
}
case 1:
{
lean_object* v___x_937_; 
v___x_937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_937_, 0, v_e_908_);
lean_ctor_set(v___x_937_, 1, v___y_914_);
return v___x_937_;
}
case 4:
{
lean_object* v___x_938_; 
v___x_938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_938_, 0, v_e_908_);
lean_ctor_set(v___x_938_, 1, v___y_914_);
return v___x_938_;
}
case 3:
{
lean_object* v___x_939_; 
v___x_939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_939_, 0, v_e_908_);
lean_ctor_set(v___x_939_, 1, v___y_914_);
return v___x_939_;
}
default: 
{
lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_940_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__2, &l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__2_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__2);
v___x_941_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1(v_beginIdx_909_, v_n_910_, v_subst_911_, v_e_908_, v___x_915_, v___x_940_, v_debug_912_, v___y_913_, v___y_914_);
if (lean_obj_tag(v___x_941_) == 0)
{
lean_object* v_a_942_; lean_object* v_a_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_951_; 
v_a_942_ = lean_ctor_get(v___x_941_, 0);
v_a_943_ = lean_ctor_get(v___x_941_, 1);
v_isSharedCheck_951_ = !lean_is_exclusive(v___x_941_);
if (v_isSharedCheck_951_ == 0)
{
v___x_945_ = v___x_941_;
v_isShared_946_ = v_isSharedCheck_951_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_a_943_);
lean_inc(v_a_942_);
lean_dec(v___x_941_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_951_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v_fst_947_; lean_object* v___x_949_; 
v_fst_947_ = lean_ctor_get(v_a_942_, 0);
lean_inc(v_fst_947_);
lean_dec(v_a_942_);
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 0, v_fst_947_);
v___x_949_ = v___x_945_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_fst_947_);
lean_ctor_set(v_reuseFailAlloc_950_, 1, v_a_943_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
}
else
{
lean_object* v_a_952_; lean_object* v_a_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_960_; 
v_a_952_ = lean_ctor_get(v___x_941_, 0);
v_a_953_ = lean_ctor_get(v___x_941_, 1);
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_941_);
if (v_isSharedCheck_960_ == 0)
{
v___x_955_ = v___x_941_;
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_a_953_);
lean_inc(v_a_952_);
lean_dec(v___x_941_);
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
}
else
{
lean_object* v___x_961_; 
v___x_961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_961_, 0, v_e_908_);
lean_ctor_set(v___x_961_, 1, v___y_914_);
return v___x_961_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___boxed(lean_object* v_e_962_, lean_object* v_beginIdx_963_, lean_object* v_n_964_, lean_object* v_subst_965_, lean_object* v_debug_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
uint8_t v_debug_boxed_969_; lean_object* v_res_970_; 
v_debug_boxed_969_ = lean_unbox(v_debug_966_);
v_res_970_ = l_Lean_Meta_Sym_instantiateRevRangeS___lam__0(v_e_962_, v_beginIdx_963_, v_n_964_, v_subst_965_, v_debug_boxed_969_, v___y_967_, v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec_ref(v_subst_965_);
lean_dec(v_n_964_);
lean_dec(v_beginIdx_963_);
return v_res_970_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__2(void){
_start:
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_973_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__2));
v___x_974_ = lean_unsigned_to_nat(16u);
v___x_975_ = lean_unsigned_to_nat(62u);
v___x_976_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__1));
v___x_977_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__0));
v___x_978_ = l_mkPanicMessageWithDecl(v___x_977_, v___x_976_, v___x_975_, v___x_974_, v___x_973_);
return v___x_978_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__5(void){
_start:
{
lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_981_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__2));
v___x_982_ = lean_unsigned_to_nat(34u);
v___x_983_ = lean_unsigned_to_nat(20u);
v___x_984_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__4));
v___x_985_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__3));
v___x_986_ = l_mkPanicMessageWithDecl(v___x_985_, v___x_984_, v___x_983_, v___x_982_, v___x_981_);
return v___x_986_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__6(void){
_start:
{
lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_987_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__2));
v___x_988_ = lean_unsigned_to_nat(32u);
v___x_989_ = lean_unsigned_to_nat(19u);
v___x_990_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__4));
v___x_991_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__3));
v___x_992_ = l_mkPanicMessageWithDecl(v___x_991_, v___x_990_, v___x_989_, v___x_988_, v___x_987_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevRangeS(lean_object* v_e_993_, lean_object* v_beginIdx_994_, lean_object* v_endIdx_995_, lean_object* v_subst_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_){
_start:
{
uint8_t v___x_1004_; 
v___x_1004_ = lean_nat_dec_lt(v_endIdx_995_, v_beginIdx_994_);
if (v___x_1004_ == 0)
{
lean_object* v___x_1005_; uint8_t v___x_1006_; 
v___x_1005_ = lean_array_get_size(v_subst_996_);
v___x_1006_ = lean_nat_dec_lt(v___x_1005_, v_endIdx_995_);
if (v___x_1006_ == 0)
{
lean_object* v___x_1007_; lean_object* v___x_1008_; uint8_t v_debug_1009_; lean_object* v_env_1010_; lean_object* v_n_1011_; lean_object* v___x_1012_; lean_object* v___f_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1007_ = lean_st_ref_get(v_a_998_);
v___x_1008_ = lean_st_ref_get(v_a_1002_);
v_debug_1009_ = lean_ctor_get_uint8(v___x_1007_, sizeof(void*)*11);
lean_dec(v___x_1007_);
v_env_1010_ = lean_ctor_get(v___x_1008_, 0);
lean_inc_ref(v_env_1010_);
lean_dec(v___x_1008_);
v_n_1011_ = lean_nat_sub(v_endIdx_995_, v_beginIdx_994_);
v___x_1012_ = lean_box(v_debug_1009_);
v___f_1013_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___boxed), 7, 5);
lean_closure_set(v___f_1013_, 0, v_e_993_);
lean_closure_set(v___f_1013_, 1, v_beginIdx_994_);
lean_closure_set(v___f_1013_, 2, v_n_1011_);
lean_closure_set(v___f_1013_, 3, v_subst_996_);
lean_closure_set(v___f_1013_, 4, v___x_1012_);
v___x_1014_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_1014_, 0, v_env_1010_);
lean_ctor_set_uint8(v___x_1014_, sizeof(void*)*1, v___x_1006_);
lean_ctor_set_uint8(v___x_1014_, sizeof(void*)*1 + 1, v___x_1006_);
v___x_1015_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_1013_, v___x_1014_, v_a_998_);
if (lean_obj_tag(v___x_1015_) == 0)
{
lean_object* v_a_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1026_; 
v_a_1016_ = lean_ctor_get(v___x_1015_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_1015_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1018_ = v___x_1015_;
v_isShared_1019_ = v_isSharedCheck_1026_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_a_1016_);
lean_dec(v___x_1015_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1026_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
if (lean_obj_tag(v_a_1016_) == 0)
{
lean_object* v___x_1020_; lean_object* v___x_1021_; 
lean_dec_ref_known(v_a_1016_, 1);
lean_del_object(v___x_1018_);
v___x_1020_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__2, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__2_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__2);
v___x_1021_ = l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(v___x_1020_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_, v_a_1002_);
return v___x_1021_;
}
else
{
lean_object* v_a_1022_; lean_object* v___x_1024_; 
v_a_1022_ = lean_ctor_get(v_a_1016_, 0);
lean_inc(v_a_1022_);
lean_dec_ref_known(v_a_1016_, 1);
if (v_isShared_1019_ == 0)
{
lean_ctor_set(v___x_1018_, 0, v_a_1022_);
v___x_1024_ = v___x_1018_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_a_1022_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
}
}
else
{
lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1034_; 
v_a_1027_ = lean_ctor_get(v___x_1015_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_1015_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1029_ = v___x_1015_;
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_dec(v___x_1015_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1032_; 
if (v_isShared_1030_ == 0)
{
v___x_1032_ = v___x_1029_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v_a_1027_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
}
else
{
lean_object* v___x_1035_; lean_object* v___x_1036_; 
lean_dec_ref(v_subst_996_);
lean_dec(v_beginIdx_994_);
lean_dec_ref(v_e_993_);
v___x_1035_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__5, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__5_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__5);
v___x_1036_ = l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(v___x_1035_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_, v_a_1002_);
return v___x_1036_;
}
}
else
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
lean_dec_ref(v_subst_996_);
lean_dec(v_beginIdx_994_);
lean_dec_ref(v_e_993_);
v___x_1037_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__6, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__6_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__6);
v___x_1038_ = l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(v___x_1037_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_, v_a_1002_);
return v___x_1038_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevRangeS___boxed(lean_object* v_e_1039_, lean_object* v_beginIdx_1040_, lean_object* v_endIdx_1041_, lean_object* v_subst_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_e_1039_, v_beginIdx_1040_, v_endIdx_1041_, v_subst_1042_, v_a_1043_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_);
lean_dec(v_a_1048_);
lean_dec_ref(v_a_1047_);
lean_dec(v_a_1046_);
lean_dec_ref(v_a_1045_);
lean_dec(v_a_1044_);
lean_dec_ref(v_a_1043_);
lean_dec(v_endIdx_1041_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_1051_, lean_object* v_m_1052_, lean_object* v_a_1053_){
_start:
{
lean_object* v___x_1054_; 
v___x_1054_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3___redArg(v_m_1052_, v_a_1053_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1055_, lean_object* v_m_1056_, lean_object* v_a_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3(v_00_u03b2_1055_, v_m_1056_, v_a_1057_);
lean_dec_ref(v_a_1057_);
lean_dec_ref(v_m_1056_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11(lean_object* v_00_u03b2_1059_, lean_object* v_m_1060_, lean_object* v_query_1061_){
_start:
{
lean_object* v___x_1062_; 
v___x_1062_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11___redArg(v_m_1060_, v_query_1061_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11___boxed(lean_object* v_00_u03b2_1063_, lean_object* v_m_1064_, lean_object* v_query_1065_){
_start:
{
lean_object* v_res_1066_; 
v_res_1066_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11(v_00_u03b2_1063_, v_m_1064_, v_query_1065_);
lean_dec_ref(v_query_1065_);
lean_dec_ref(v_m_1064_);
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11_spec__12(lean_object* v_00_u03b2_1067_, lean_object* v_m_1068_, lean_object* v_query_1069_){
_start:
{
lean_object* v___x_1070_; 
v___x_1070_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11_spec__12___redArg(v_m_1068_, v_query_1069_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11_spec__12___boxed(lean_object* v_00_u03b2_1071_, lean_object* v_m_1072_, lean_object* v_query_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11_spec__12(v_00_u03b2_1071_, v_m_1072_, v_query_1073_);
lean_dec_ref(v_query_1073_);
lean_dec_ref(v_m_1072_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11_spec__12_spec__13(lean_object* v_00_u03b2_1075_, lean_object* v_m_1076_, lean_object* v_query_1077_, lean_object* v_x_1078_, lean_object* v_x_1079_, lean_object* v_x_1080_, lean_object* v_x_1081_){
_start:
{
lean_object* v___x_1082_; 
v___x_1082_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11_spec__12_spec__13___redArg(v_m_1076_, v_query_1077_, v_x_1078_, v_x_1079_, v_x_1080_);
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11_spec__12_spec__13___boxed(lean_object* v_00_u03b2_1083_, lean_object* v_m_1084_, lean_object* v_query_1085_, lean_object* v_x_1086_, lean_object* v_x_1087_, lean_object* v_x_1088_, lean_object* v_x_1089_){
_start:
{
lean_object* v_res_1090_; 
v_res_1090_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11_spec__12_spec__13(v_00_u03b2_1083_, v_m_1084_, v_query_1085_, v_x_1086_, v_x_1087_, v_x_1088_, v_x_1089_);
lean_dec_ref(v_query_1085_);
lean_dec_ref(v_m_1084_);
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevS(lean_object* v_e_1091_, lean_object* v_subst_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_){
_start:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1100_ = lean_unsigned_to_nat(0u);
v___x_1101_ = lean_array_get_size(v_subst_1092_);
v___x_1102_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_e_1091_, v___x_1100_, v___x_1101_, v_subst_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_);
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevS___boxed(lean_object* v_e_1103_, lean_object* v_subst_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l_Lean_Meta_Sym_instantiateRevS(v_e_1103_, v_subst_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_);
lean_dec(v_a_1110_);
lean_dec_ref(v_a_1109_);
lean_dec(v_a_1108_);
lean_dec_ref(v_a_1107_);
lean_dec(v_a_1106_);
lean_dec_ref(v_a_1105_);
return v_res_1112_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1(lean_object* v_msg_1115_, uint8_t v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_){
_start:
{
lean_object* v___f_1119_; lean_object* v___f_1120_; lean_object* v___x_1121_; lean_object* v___f_1122_; lean_object* v___f_1123_; lean_object* v___f_1124_; lean_object* v___x_2918__overap_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___f_1119_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1___closed__0));
v___f_1120_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1___closed__1));
v___x_1121_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___f_1119_, v___f_1120_);
v___f_1122_ = lean_alloc_closure((void*)(l_EStateM_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1122_, 0, v___x_1121_);
v___f_1123_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1123_, 0, v___f_1122_);
v___f_1124_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1124_, 0, v___f_1123_);
v___x_2918__overap_1125_ = lean_panic_fn_borrowed(v___f_1124_, v_msg_1115_);
lean_dec_ref(v___f_1124_);
v___x_1126_ = lean_box(v___y_1116_);
lean_inc_ref(v___y_1117_);
v___x_1127_ = lean_apply_3(v___x_2918__overap_1125_, v___x_1126_, v___y_1117_, v___y_1118_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1___boxed(lean_object* v_msg_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_){
_start:
{
uint8_t v___y_3402__boxed_1132_; lean_object* v_res_1133_; 
v___y_3402__boxed_1132_ = lean_unbox(v___y_1129_);
v_res_1133_ = l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1(v_msg_1128_, v___y_3402__boxed_1132_, v___y_1130_, v___y_1131_);
lean_dec_ref(v___y_1130_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0(lean_object* v_n_1134_, lean_object* v_beginIdx_1135_, lean_object* v_subst_1136_, lean_object* v_e_1137_, lean_object* v_offset_1138_, lean_object* v_a_1139_, uint8_t v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_){
_start:
{
switch(lean_obj_tag(v_e_1137_))
{
case 5:
{
lean_object* v_fn_1143_; lean_object* v_arg_1144_; lean_object* v___x_1145_; 
v_fn_1143_ = lean_ctor_get(v_e_1137_, 0);
v_arg_1144_ = lean_ctor_get(v_e_1137_, 1);
lean_inc(v_offset_1138_);
lean_inc_ref(v_fn_1143_);
v___x_1145_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1134_, v_beginIdx_1135_, v_subst_1136_, v_fn_1143_, v_offset_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_);
if (lean_obj_tag(v___x_1145_) == 0)
{
lean_object* v_a_1146_; lean_object* v_a_1147_; lean_object* v_fst_1148_; lean_object* v_snd_1149_; lean_object* v___x_1150_; 
v_a_1146_ = lean_ctor_get(v___x_1145_, 0);
lean_inc(v_a_1146_);
v_a_1147_ = lean_ctor_get(v___x_1145_, 1);
lean_inc(v_a_1147_);
lean_dec_ref_known(v___x_1145_, 2);
v_fst_1148_ = lean_ctor_get(v_a_1146_, 0);
lean_inc(v_fst_1148_);
v_snd_1149_ = lean_ctor_get(v_a_1146_, 1);
lean_inc(v_snd_1149_);
lean_dec(v_a_1146_);
lean_inc_ref(v_arg_1144_);
v___x_1150_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1134_, v_beginIdx_1135_, v_subst_1136_, v_arg_1144_, v_offset_1138_, v_snd_1149_, v_a_1140_, v_a_1141_, v_a_1147_);
if (lean_obj_tag(v___x_1150_) == 0)
{
lean_object* v_a_1151_; lean_object* v_a_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1177_; 
v_a_1151_ = lean_ctor_get(v___x_1150_, 0);
v_a_1152_ = lean_ctor_get(v___x_1150_, 1);
v_isSharedCheck_1177_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1154_ = v___x_1150_;
v_isShared_1155_ = v_isSharedCheck_1177_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_a_1152_);
lean_inc(v_a_1151_);
lean_dec(v___x_1150_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1177_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v_fst_1156_; lean_object* v_snd_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1176_; 
v_fst_1156_ = lean_ctor_get(v_a_1151_, 0);
v_snd_1157_ = lean_ctor_get(v_a_1151_, 1);
v_isSharedCheck_1176_ = !lean_is_exclusive(v_a_1151_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1159_ = v_a_1151_;
v_isShared_1160_ = v_isSharedCheck_1176_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_snd_1157_);
lean_inc(v_fst_1156_);
lean_dec(v_a_1151_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1176_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
uint8_t v___y_1162_; size_t v___x_1170_; size_t v___x_1171_; uint8_t v___x_1172_; 
v___x_1170_ = lean_ptr_addr(v_fn_1143_);
v___x_1171_ = lean_ptr_addr(v_fst_1148_);
v___x_1172_ = lean_usize_dec_eq(v___x_1170_, v___x_1171_);
if (v___x_1172_ == 0)
{
v___y_1162_ = v___x_1172_;
goto v___jp_1161_;
}
else
{
size_t v___x_1173_; size_t v___x_1174_; uint8_t v___x_1175_; 
v___x_1173_ = lean_ptr_addr(v_arg_1144_);
v___x_1174_ = lean_ptr_addr(v_fst_1156_);
v___x_1175_ = lean_usize_dec_eq(v___x_1173_, v___x_1174_);
v___y_1162_ = v___x_1175_;
goto v___jp_1161_;
}
v___jp_1161_:
{
if (v___y_1162_ == 0)
{
lean_object* v___x_1163_; 
lean_del_object(v___x_1159_);
lean_del_object(v___x_1154_);
lean_dec_ref_known(v_e_1137_, 2);
v___x_1163_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__2(v_fst_1148_, v_fst_1156_, v_snd_1157_, v_a_1140_, v_a_1141_, v_a_1152_);
return v___x_1163_;
}
else
{
lean_object* v___x_1165_; 
lean_dec(v_fst_1156_);
lean_dec(v_fst_1148_);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 0, v_e_1137_);
v___x_1165_ = v___x_1159_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v_e_1137_);
lean_ctor_set(v_reuseFailAlloc_1169_, 1, v_snd_1157_);
v___x_1165_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
lean_object* v___x_1167_; 
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 0, v___x_1165_);
v___x_1167_ = v___x_1154_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v___x_1165_);
lean_ctor_set(v_reuseFailAlloc_1168_, 1, v_a_1152_);
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
}
}
else
{
lean_dec(v_fst_1148_);
lean_dec_ref_known(v_e_1137_, 2);
return v___x_1150_;
}
}
else
{
lean_dec_ref_known(v_e_1137_, 2);
lean_dec(v_offset_1138_);
return v___x_1145_;
}
}
case 6:
{
lean_object* v_binderName_1178_; lean_object* v_binderType_1179_; lean_object* v_body_1180_; uint8_t v_binderInfo_1181_; lean_object* v___x_1182_; 
v_binderName_1178_ = lean_ctor_get(v_e_1137_, 0);
v_binderType_1179_ = lean_ctor_get(v_e_1137_, 1);
v_body_1180_ = lean_ctor_get(v_e_1137_, 2);
v_binderInfo_1181_ = lean_ctor_get_uint8(v_e_1137_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1138_);
lean_inc_ref(v_binderType_1179_);
v___x_1182_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1134_, v_beginIdx_1135_, v_subst_1136_, v_binderType_1179_, v_offset_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_);
if (lean_obj_tag(v___x_1182_) == 0)
{
lean_object* v_a_1183_; lean_object* v_a_1184_; lean_object* v_fst_1185_; lean_object* v_snd_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; 
v_a_1183_ = lean_ctor_get(v___x_1182_, 0);
lean_inc(v_a_1183_);
v_a_1184_ = lean_ctor_get(v___x_1182_, 1);
lean_inc(v_a_1184_);
lean_dec_ref_known(v___x_1182_, 2);
v_fst_1185_ = lean_ctor_get(v_a_1183_, 0);
lean_inc(v_fst_1185_);
v_snd_1186_ = lean_ctor_get(v_a_1183_, 1);
lean_inc(v_snd_1186_);
lean_dec(v_a_1183_);
v___x_1187_ = lean_unsigned_to_nat(1u);
v___x_1188_ = lean_nat_add(v_offset_1138_, v___x_1187_);
lean_dec(v_offset_1138_);
lean_inc_ref(v_body_1180_);
v___x_1189_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1134_, v_beginIdx_1135_, v_subst_1136_, v_body_1180_, v___x_1188_, v_snd_1186_, v_a_1140_, v_a_1141_, v_a_1184_);
if (lean_obj_tag(v___x_1189_) == 0)
{
lean_object* v_a_1190_; lean_object* v_a_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1216_; 
v_a_1190_ = lean_ctor_get(v___x_1189_, 0);
v_a_1191_ = lean_ctor_get(v___x_1189_, 1);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1189_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1193_ = v___x_1189_;
v_isShared_1194_ = v_isSharedCheck_1216_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_a_1191_);
lean_inc(v_a_1190_);
lean_dec(v___x_1189_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1216_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v_fst_1195_; lean_object* v_snd_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1215_; 
v_fst_1195_ = lean_ctor_get(v_a_1190_, 0);
v_snd_1196_ = lean_ctor_get(v_a_1190_, 1);
v_isSharedCheck_1215_ = !lean_is_exclusive(v_a_1190_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1198_ = v_a_1190_;
v_isShared_1199_ = v_isSharedCheck_1215_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_snd_1196_);
lean_inc(v_fst_1195_);
lean_dec(v_a_1190_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1215_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
uint8_t v___y_1201_; size_t v___x_1209_; size_t v___x_1210_; uint8_t v___x_1211_; 
v___x_1209_ = lean_ptr_addr(v_binderType_1179_);
v___x_1210_ = lean_ptr_addr(v_fst_1185_);
v___x_1211_ = lean_usize_dec_eq(v___x_1209_, v___x_1210_);
if (v___x_1211_ == 0)
{
v___y_1201_ = v___x_1211_;
goto v___jp_1200_;
}
else
{
size_t v___x_1212_; size_t v___x_1213_; uint8_t v___x_1214_; 
v___x_1212_ = lean_ptr_addr(v_body_1180_);
v___x_1213_ = lean_ptr_addr(v_fst_1195_);
v___x_1214_ = lean_usize_dec_eq(v___x_1212_, v___x_1213_);
v___y_1201_ = v___x_1214_;
goto v___jp_1200_;
}
v___jp_1200_:
{
if (v___y_1201_ == 0)
{
lean_object* v___x_1202_; 
lean_inc(v_binderName_1178_);
lean_del_object(v___x_1198_);
lean_del_object(v___x_1193_);
lean_dec_ref_known(v_e_1137_, 3);
v___x_1202_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__3(v_binderName_1178_, v_binderInfo_1181_, v_fst_1185_, v_fst_1195_, v_snd_1196_, v_a_1140_, v_a_1141_, v_a_1191_);
return v___x_1202_;
}
else
{
lean_object* v___x_1204_; 
lean_dec(v_fst_1195_);
lean_dec(v_fst_1185_);
if (v_isShared_1199_ == 0)
{
lean_ctor_set(v___x_1198_, 0, v_e_1137_);
v___x_1204_ = v___x_1198_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_e_1137_);
lean_ctor_set(v_reuseFailAlloc_1208_, 1, v_snd_1196_);
v___x_1204_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
lean_object* v___x_1206_; 
if (v_isShared_1194_ == 0)
{
lean_ctor_set(v___x_1193_, 0, v___x_1204_);
v___x_1206_ = v___x_1193_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v___x_1204_);
lean_ctor_set(v_reuseFailAlloc_1207_, 1, v_a_1191_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1185_);
lean_dec_ref_known(v_e_1137_, 3);
return v___x_1189_;
}
}
else
{
lean_dec_ref_known(v_e_1137_, 3);
lean_dec(v_offset_1138_);
return v___x_1182_;
}
}
case 7:
{
lean_object* v_binderName_1217_; lean_object* v_binderType_1218_; lean_object* v_body_1219_; uint8_t v_binderInfo_1220_; lean_object* v___x_1221_; 
v_binderName_1217_ = lean_ctor_get(v_e_1137_, 0);
v_binderType_1218_ = lean_ctor_get(v_e_1137_, 1);
v_body_1219_ = lean_ctor_get(v_e_1137_, 2);
v_binderInfo_1220_ = lean_ctor_get_uint8(v_e_1137_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1138_);
lean_inc_ref(v_binderType_1218_);
v___x_1221_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1134_, v_beginIdx_1135_, v_subst_1136_, v_binderType_1218_, v_offset_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_);
if (lean_obj_tag(v___x_1221_) == 0)
{
lean_object* v_a_1222_; lean_object* v_a_1223_; lean_object* v_fst_1224_; lean_object* v_snd_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; 
v_a_1222_ = lean_ctor_get(v___x_1221_, 0);
lean_inc(v_a_1222_);
v_a_1223_ = lean_ctor_get(v___x_1221_, 1);
lean_inc(v_a_1223_);
lean_dec_ref_known(v___x_1221_, 2);
v_fst_1224_ = lean_ctor_get(v_a_1222_, 0);
lean_inc(v_fst_1224_);
v_snd_1225_ = lean_ctor_get(v_a_1222_, 1);
lean_inc(v_snd_1225_);
lean_dec(v_a_1222_);
v___x_1226_ = lean_unsigned_to_nat(1u);
v___x_1227_ = lean_nat_add(v_offset_1138_, v___x_1226_);
lean_dec(v_offset_1138_);
lean_inc_ref(v_body_1219_);
v___x_1228_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1134_, v_beginIdx_1135_, v_subst_1136_, v_body_1219_, v___x_1227_, v_snd_1225_, v_a_1140_, v_a_1141_, v_a_1223_);
if (lean_obj_tag(v___x_1228_) == 0)
{
lean_object* v_a_1229_; lean_object* v_a_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1255_; 
v_a_1229_ = lean_ctor_get(v___x_1228_, 0);
v_a_1230_ = lean_ctor_get(v___x_1228_, 1);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1232_ = v___x_1228_;
v_isShared_1233_ = v_isSharedCheck_1255_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_a_1230_);
lean_inc(v_a_1229_);
lean_dec(v___x_1228_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1255_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v_fst_1234_; lean_object* v_snd_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1254_; 
v_fst_1234_ = lean_ctor_get(v_a_1229_, 0);
v_snd_1235_ = lean_ctor_get(v_a_1229_, 1);
v_isSharedCheck_1254_ = !lean_is_exclusive(v_a_1229_);
if (v_isSharedCheck_1254_ == 0)
{
v___x_1237_ = v_a_1229_;
v_isShared_1238_ = v_isSharedCheck_1254_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_snd_1235_);
lean_inc(v_fst_1234_);
lean_dec(v_a_1229_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1254_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
uint8_t v___y_1240_; size_t v___x_1248_; size_t v___x_1249_; uint8_t v___x_1250_; 
v___x_1248_ = lean_ptr_addr(v_binderType_1218_);
v___x_1249_ = lean_ptr_addr(v_fst_1224_);
v___x_1250_ = lean_usize_dec_eq(v___x_1248_, v___x_1249_);
if (v___x_1250_ == 0)
{
v___y_1240_ = v___x_1250_;
goto v___jp_1239_;
}
else
{
size_t v___x_1251_; size_t v___x_1252_; uint8_t v___x_1253_; 
v___x_1251_ = lean_ptr_addr(v_body_1219_);
v___x_1252_ = lean_ptr_addr(v_fst_1234_);
v___x_1253_ = lean_usize_dec_eq(v___x_1251_, v___x_1252_);
v___y_1240_ = v___x_1253_;
goto v___jp_1239_;
}
v___jp_1239_:
{
if (v___y_1240_ == 0)
{
lean_object* v___x_1241_; 
lean_inc(v_binderName_1217_);
lean_del_object(v___x_1237_);
lean_del_object(v___x_1232_);
lean_dec_ref_known(v_e_1137_, 3);
v___x_1241_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__4(v_binderName_1217_, v_binderInfo_1220_, v_fst_1224_, v_fst_1234_, v_snd_1235_, v_a_1140_, v_a_1141_, v_a_1230_);
return v___x_1241_;
}
else
{
lean_object* v___x_1243_; 
lean_dec(v_fst_1234_);
lean_dec(v_fst_1224_);
if (v_isShared_1238_ == 0)
{
lean_ctor_set(v___x_1237_, 0, v_e_1137_);
v___x_1243_ = v___x_1237_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_e_1137_);
lean_ctor_set(v_reuseFailAlloc_1247_, 1, v_snd_1235_);
v___x_1243_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
lean_object* v___x_1245_; 
if (v_isShared_1233_ == 0)
{
lean_ctor_set(v___x_1232_, 0, v___x_1243_);
v___x_1245_ = v___x_1232_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v___x_1243_);
lean_ctor_set(v_reuseFailAlloc_1246_, 1, v_a_1230_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1224_);
lean_dec_ref_known(v_e_1137_, 3);
return v___x_1228_;
}
}
else
{
lean_dec_ref_known(v_e_1137_, 3);
lean_dec(v_offset_1138_);
return v___x_1221_;
}
}
case 8:
{
lean_object* v_declName_1256_; lean_object* v_type_1257_; lean_object* v_value_1258_; lean_object* v_body_1259_; uint8_t v_nondep_1260_; lean_object* v___x_1261_; 
v_declName_1256_ = lean_ctor_get(v_e_1137_, 0);
v_type_1257_ = lean_ctor_get(v_e_1137_, 1);
v_value_1258_ = lean_ctor_get(v_e_1137_, 2);
v_body_1259_ = lean_ctor_get(v_e_1137_, 3);
v_nondep_1260_ = lean_ctor_get_uint8(v_e_1137_, sizeof(void*)*4 + 8);
lean_inc(v_offset_1138_);
lean_inc_ref(v_type_1257_);
v___x_1261_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1134_, v_beginIdx_1135_, v_subst_1136_, v_type_1257_, v_offset_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_object* v_a_1262_; lean_object* v_a_1263_; lean_object* v_fst_1264_; lean_object* v_snd_1265_; lean_object* v___x_1266_; 
v_a_1262_ = lean_ctor_get(v___x_1261_, 0);
lean_inc(v_a_1262_);
v_a_1263_ = lean_ctor_get(v___x_1261_, 1);
lean_inc(v_a_1263_);
lean_dec_ref_known(v___x_1261_, 2);
v_fst_1264_ = lean_ctor_get(v_a_1262_, 0);
lean_inc(v_fst_1264_);
v_snd_1265_ = lean_ctor_get(v_a_1262_, 1);
lean_inc(v_snd_1265_);
lean_dec(v_a_1262_);
lean_inc(v_offset_1138_);
lean_inc_ref(v_value_1258_);
v___x_1266_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1134_, v_beginIdx_1135_, v_subst_1136_, v_value_1258_, v_offset_1138_, v_snd_1265_, v_a_1140_, v_a_1141_, v_a_1263_);
if (lean_obj_tag(v___x_1266_) == 0)
{
lean_object* v_a_1267_; lean_object* v_a_1268_; lean_object* v_fst_1269_; lean_object* v_snd_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; 
v_a_1267_ = lean_ctor_get(v___x_1266_, 0);
lean_inc(v_a_1267_);
v_a_1268_ = lean_ctor_get(v___x_1266_, 1);
lean_inc(v_a_1268_);
lean_dec_ref_known(v___x_1266_, 2);
v_fst_1269_ = lean_ctor_get(v_a_1267_, 0);
lean_inc(v_fst_1269_);
v_snd_1270_ = lean_ctor_get(v_a_1267_, 1);
lean_inc(v_snd_1270_);
lean_dec(v_a_1267_);
v___x_1271_ = lean_unsigned_to_nat(1u);
v___x_1272_ = lean_nat_add(v_offset_1138_, v___x_1271_);
lean_dec(v_offset_1138_);
lean_inc_ref(v_body_1259_);
v___x_1273_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1134_, v_beginIdx_1135_, v_subst_1136_, v_body_1259_, v___x_1272_, v_snd_1270_, v_a_1140_, v_a_1141_, v_a_1268_);
if (lean_obj_tag(v___x_1273_) == 0)
{
lean_object* v_a_1274_; lean_object* v_a_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1304_; 
v_a_1274_ = lean_ctor_get(v___x_1273_, 0);
v_a_1275_ = lean_ctor_get(v___x_1273_, 1);
v_isSharedCheck_1304_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1277_ = v___x_1273_;
v_isShared_1278_ = v_isSharedCheck_1304_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_a_1275_);
lean_inc(v_a_1274_);
lean_dec(v___x_1273_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1304_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v_fst_1279_; lean_object* v_snd_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1303_; 
v_fst_1279_ = lean_ctor_get(v_a_1274_, 0);
v_snd_1280_ = lean_ctor_get(v_a_1274_, 1);
v_isSharedCheck_1303_ = !lean_is_exclusive(v_a_1274_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1282_ = v_a_1274_;
v_isShared_1283_ = v_isSharedCheck_1303_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_snd_1280_);
lean_inc(v_fst_1279_);
lean_dec(v_a_1274_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1303_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
uint8_t v___y_1285_; size_t v___x_1297_; size_t v___x_1298_; uint8_t v___x_1299_; 
v___x_1297_ = lean_ptr_addr(v_type_1257_);
v___x_1298_ = lean_ptr_addr(v_fst_1264_);
v___x_1299_ = lean_usize_dec_eq(v___x_1297_, v___x_1298_);
if (v___x_1299_ == 0)
{
v___y_1285_ = v___x_1299_;
goto v___jp_1284_;
}
else
{
size_t v___x_1300_; size_t v___x_1301_; uint8_t v___x_1302_; 
v___x_1300_ = lean_ptr_addr(v_value_1258_);
v___x_1301_ = lean_ptr_addr(v_fst_1269_);
v___x_1302_ = lean_usize_dec_eq(v___x_1300_, v___x_1301_);
v___y_1285_ = v___x_1302_;
goto v___jp_1284_;
}
v___jp_1284_:
{
if (v___y_1285_ == 0)
{
lean_object* v___x_1286_; 
lean_inc(v_declName_1256_);
lean_del_object(v___x_1282_);
lean_del_object(v___x_1277_);
lean_dec_ref_known(v_e_1137_, 4);
v___x_1286_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__5(v_declName_1256_, v_fst_1264_, v_fst_1269_, v_fst_1279_, v_nondep_1260_, v_snd_1280_, v_a_1140_, v_a_1141_, v_a_1275_);
return v___x_1286_;
}
else
{
size_t v___x_1287_; size_t v___x_1288_; uint8_t v___x_1289_; 
v___x_1287_ = lean_ptr_addr(v_body_1259_);
v___x_1288_ = lean_ptr_addr(v_fst_1279_);
v___x_1289_ = lean_usize_dec_eq(v___x_1287_, v___x_1288_);
if (v___x_1289_ == 0)
{
lean_object* v___x_1290_; 
lean_inc(v_declName_1256_);
lean_del_object(v___x_1282_);
lean_del_object(v___x_1277_);
lean_dec_ref_known(v_e_1137_, 4);
v___x_1290_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__5(v_declName_1256_, v_fst_1264_, v_fst_1269_, v_fst_1279_, v_nondep_1260_, v_snd_1280_, v_a_1140_, v_a_1141_, v_a_1275_);
return v___x_1290_;
}
else
{
lean_object* v___x_1292_; 
lean_dec(v_fst_1279_);
lean_dec(v_fst_1269_);
lean_dec(v_fst_1264_);
if (v_isShared_1283_ == 0)
{
lean_ctor_set(v___x_1282_, 0, v_e_1137_);
v___x_1292_ = v___x_1282_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_e_1137_);
lean_ctor_set(v_reuseFailAlloc_1296_, 1, v_snd_1280_);
v___x_1292_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
lean_object* v___x_1294_; 
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 0, v___x_1292_);
v___x_1294_ = v___x_1277_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v___x_1292_);
lean_ctor_set(v_reuseFailAlloc_1295_, 1, v_a_1275_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
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
lean_dec(v_fst_1269_);
lean_dec(v_fst_1264_);
lean_dec_ref_known(v_e_1137_, 4);
return v___x_1273_;
}
}
else
{
lean_dec(v_fst_1264_);
lean_dec_ref_known(v_e_1137_, 4);
lean_dec(v_offset_1138_);
return v___x_1266_;
}
}
else
{
lean_dec_ref_known(v_e_1137_, 4);
lean_dec(v_offset_1138_);
return v___x_1261_;
}
}
case 10:
{
lean_object* v_data_1305_; lean_object* v_expr_1306_; lean_object* v___x_1307_; 
v_data_1305_ = lean_ctor_get(v_e_1137_, 0);
v_expr_1306_ = lean_ctor_get(v_e_1137_, 1);
lean_inc_ref(v_expr_1306_);
v___x_1307_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1134_, v_beginIdx_1135_, v_subst_1136_, v_expr_1306_, v_offset_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_);
if (lean_obj_tag(v___x_1307_) == 0)
{
lean_object* v_a_1308_; lean_object* v_a_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1329_; 
v_a_1308_ = lean_ctor_get(v___x_1307_, 0);
v_a_1309_ = lean_ctor_get(v___x_1307_, 1);
v_isSharedCheck_1329_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1311_ = v___x_1307_;
v_isShared_1312_ = v_isSharedCheck_1329_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_a_1309_);
lean_inc(v_a_1308_);
lean_dec(v___x_1307_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1329_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v_fst_1313_; lean_object* v_snd_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1328_; 
v_fst_1313_ = lean_ctor_get(v_a_1308_, 0);
v_snd_1314_ = lean_ctor_get(v_a_1308_, 1);
v_isSharedCheck_1328_ = !lean_is_exclusive(v_a_1308_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1316_ = v_a_1308_;
v_isShared_1317_ = v_isSharedCheck_1328_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_snd_1314_);
lean_inc(v_fst_1313_);
lean_dec(v_a_1308_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1328_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
size_t v___x_1318_; size_t v___x_1319_; uint8_t v___x_1320_; 
v___x_1318_ = lean_ptr_addr(v_expr_1306_);
v___x_1319_ = lean_ptr_addr(v_fst_1313_);
v___x_1320_ = lean_usize_dec_eq(v___x_1318_, v___x_1319_);
if (v___x_1320_ == 0)
{
lean_object* v___x_1321_; 
lean_inc(v_data_1305_);
lean_del_object(v___x_1316_);
lean_del_object(v___x_1311_);
lean_dec_ref_known(v_e_1137_, 2);
v___x_1321_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__6(v_data_1305_, v_fst_1313_, v_snd_1314_, v_a_1140_, v_a_1141_, v_a_1309_);
return v___x_1321_;
}
else
{
lean_object* v___x_1323_; 
lean_dec(v_fst_1313_);
if (v_isShared_1317_ == 0)
{
lean_ctor_set(v___x_1316_, 0, v_e_1137_);
v___x_1323_ = v___x_1316_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_e_1137_);
lean_ctor_set(v_reuseFailAlloc_1327_, 1, v_snd_1314_);
v___x_1323_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
lean_object* v___x_1325_; 
if (v_isShared_1312_ == 0)
{
lean_ctor_set(v___x_1311_, 0, v___x_1323_);
v___x_1325_ = v___x_1311_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v___x_1323_);
lean_ctor_set(v_reuseFailAlloc_1326_, 1, v_a_1309_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_1137_, 2);
return v___x_1307_;
}
}
case 11:
{
lean_object* v_typeName_1330_; lean_object* v_idx_1331_; lean_object* v_struct_1332_; lean_object* v___x_1333_; 
v_typeName_1330_ = lean_ctor_get(v_e_1137_, 0);
v_idx_1331_ = lean_ctor_get(v_e_1137_, 1);
v_struct_1332_ = lean_ctor_get(v_e_1137_, 2);
lean_inc_ref(v_struct_1332_);
v___x_1333_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1134_, v_beginIdx_1135_, v_subst_1136_, v_struct_1332_, v_offset_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_);
if (lean_obj_tag(v___x_1333_) == 0)
{
lean_object* v_a_1334_; lean_object* v_a_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1355_; 
v_a_1334_ = lean_ctor_get(v___x_1333_, 0);
v_a_1335_ = lean_ctor_get(v___x_1333_, 1);
v_isSharedCheck_1355_ = !lean_is_exclusive(v___x_1333_);
if (v_isSharedCheck_1355_ == 0)
{
v___x_1337_ = v___x_1333_;
v_isShared_1338_ = v_isSharedCheck_1355_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_a_1335_);
lean_inc(v_a_1334_);
lean_dec(v___x_1333_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1355_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v_fst_1339_; lean_object* v_snd_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1354_; 
v_fst_1339_ = lean_ctor_get(v_a_1334_, 0);
v_snd_1340_ = lean_ctor_get(v_a_1334_, 1);
v_isSharedCheck_1354_ = !lean_is_exclusive(v_a_1334_);
if (v_isSharedCheck_1354_ == 0)
{
v___x_1342_ = v_a_1334_;
v_isShared_1343_ = v_isSharedCheck_1354_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_snd_1340_);
lean_inc(v_fst_1339_);
lean_dec(v_a_1334_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1354_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
size_t v___x_1344_; size_t v___x_1345_; uint8_t v___x_1346_; 
v___x_1344_ = lean_ptr_addr(v_struct_1332_);
v___x_1345_ = lean_ptr_addr(v_fst_1339_);
v___x_1346_ = lean_usize_dec_eq(v___x_1344_, v___x_1345_);
if (v___x_1346_ == 0)
{
lean_object* v___x_1347_; 
lean_inc(v_idx_1331_);
lean_inc(v_typeName_1330_);
lean_del_object(v___x_1342_);
lean_del_object(v___x_1337_);
lean_dec_ref_known(v_e_1137_, 3);
v___x_1347_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__7(v_typeName_1330_, v_idx_1331_, v_fst_1339_, v_snd_1340_, v_a_1140_, v_a_1141_, v_a_1335_);
return v___x_1347_;
}
else
{
lean_object* v___x_1349_; 
lean_dec(v_fst_1339_);
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 0, v_e_1137_);
v___x_1349_ = v___x_1342_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v_e_1137_);
lean_ctor_set(v_reuseFailAlloc_1353_, 1, v_snd_1340_);
v___x_1349_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
lean_object* v___x_1351_; 
if (v_isShared_1338_ == 0)
{
lean_ctor_set(v___x_1337_, 0, v___x_1349_);
v___x_1351_ = v___x_1337_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v___x_1349_);
lean_ctor_set(v_reuseFailAlloc_1352_, 1, v_a_1335_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_1137_, 3);
return v___x_1333_;
}
}
default: 
{
lean_object* v___x_1356_; lean_object* v___x_1357_; 
lean_dec(v_offset_1138_);
lean_dec_ref(v_e_1137_);
v___x_1356_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__3);
v___x_1357_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8(v___x_1356_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_);
return v___x_1357_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(lean_object* v_n_1358_, lean_object* v_beginIdx_1359_, lean_object* v_subst_1360_, lean_object* v_e_1361_, lean_object* v_offset_1362_, lean_object* v_a_1363_, uint8_t v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_){
_start:
{
lean_object* v_key_1367_; lean_object* v___x_1368_; 
lean_inc(v_offset_1362_);
lean_inc_ref(v_e_1361_);
v_key_1367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1367_, 0, v_e_1361_);
lean_ctor_set(v_key_1367_, 1, v_offset_1362_);
v___x_1368_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3___redArg(v_a_1363_, v_key_1367_);
if (lean_obj_tag(v___x_1368_) == 1)
{
lean_object* v_val_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; 
lean_dec_ref_known(v_key_1367_, 2);
lean_dec(v_offset_1362_);
lean_dec_ref(v_e_1361_);
v_val_1369_ = lean_ctor_get(v___x_1368_, 0);
lean_inc(v_val_1369_);
lean_dec_ref_known(v___x_1368_, 1);
v___x_1370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1370_, 0, v_val_1369_);
lean_ctor_set(v___x_1370_, 1, v_a_1363_);
v___x_1371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1371_, 0, v___x_1370_);
lean_ctor_set(v___x_1371_, 1, v_a_1366_);
return v___x_1371_;
}
else
{
lean_dec(v___x_1368_);
switch(lean_obj_tag(v_e_1361_))
{
case 0:
{
lean_object* v_deBruijnIndex_1372_; uint8_t v___x_1373_; 
v_deBruijnIndex_1372_ = lean_ctor_get(v_e_1361_, 0);
v___x_1373_ = lean_nat_dec_le(v_offset_1362_, v_deBruijnIndex_1372_);
if (v___x_1373_ == 0)
{
lean_object* v___x_1374_; 
lean_dec(v_offset_1362_);
v___x_1374_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1367_, v_e_1361_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_);
return v___x_1374_;
}
else
{
lean_object* v___x_1375_; uint8_t v___x_1376_; 
lean_inc(v_deBruijnIndex_1372_);
lean_dec_ref_known(v_e_1361_, 1);
v___x_1375_ = lean_nat_add(v_offset_1362_, v_n_1358_);
v___x_1376_ = lean_nat_dec_lt(v_deBruijnIndex_1372_, v___x_1375_);
lean_dec(v___x_1375_);
if (v___x_1376_ == 0)
{
lean_object* v___x_1377_; lean_object* v___x_1378_; 
lean_dec(v_offset_1362_);
v___x_1377_ = lean_nat_sub(v_deBruijnIndex_1372_, v_n_1358_);
lean_dec(v_deBruijnIndex_1372_);
v___x_1378_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___redArg(v___x_1377_, v_a_1366_);
if (lean_obj_tag(v___x_1378_) == 0)
{
lean_object* v_a_1379_; lean_object* v_a_1380_; lean_object* v___x_1381_; 
v_a_1379_ = lean_ctor_get(v___x_1378_, 0);
lean_inc(v_a_1379_);
v_a_1380_ = lean_ctor_get(v___x_1378_, 1);
lean_inc(v_a_1380_);
lean_dec_ref_known(v___x_1378_, 2);
v___x_1381_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1367_, v_a_1379_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1380_);
return v___x_1381_;
}
else
{
lean_object* v_a_1382_; lean_object* v_a_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1390_; 
lean_dec_ref_known(v_key_1367_, 2);
lean_dec_ref(v_a_1363_);
v_a_1382_ = lean_ctor_get(v___x_1378_, 0);
v_a_1383_ = lean_ctor_get(v___x_1378_, 1);
v_isSharedCheck_1390_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1390_ == 0)
{
v___x_1385_ = v___x_1378_;
v_isShared_1386_ = v_isSharedCheck_1390_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_a_1383_);
lean_inc(v_a_1382_);
lean_dec(v___x_1378_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1390_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v___x_1388_; 
if (v_isShared_1386_ == 0)
{
v___x_1388_ = v___x_1385_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v_a_1382_);
lean_ctor_set(v_reuseFailAlloc_1389_, 1, v_a_1383_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
return v___x_1388_;
}
}
}
}
else
{
lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v_v_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1391_ = lean_nat_add(v_beginIdx_1359_, v_deBruijnIndex_1372_);
lean_dec(v_deBruijnIndex_1372_);
v___x_1392_ = lean_nat_sub(v___x_1391_, v_offset_1362_);
lean_dec(v___x_1391_);
v_v_1393_ = lean_array_fget_borrowed(v_subst_1360_, v___x_1392_);
lean_dec(v___x_1392_);
v___x_1394_ = lean_unsigned_to_nat(0u);
lean_inc(v_v_1393_);
v___x_1395_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(v_v_1393_, v___x_1394_, v_offset_1362_, v_a_1364_, v_a_1365_, v_a_1366_);
lean_dec(v_offset_1362_);
if (lean_obj_tag(v___x_1395_) == 0)
{
lean_object* v_a_1396_; lean_object* v_a_1397_; lean_object* v___x_1398_; 
v_a_1396_ = lean_ctor_get(v___x_1395_, 0);
lean_inc(v_a_1396_);
v_a_1397_ = lean_ctor_get(v___x_1395_, 1);
lean_inc(v_a_1397_);
lean_dec_ref_known(v___x_1395_, 2);
v___x_1398_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1367_, v_a_1396_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1397_);
return v___x_1398_;
}
else
{
lean_object* v_a_1399_; lean_object* v_a_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1407_; 
lean_dec_ref_known(v_key_1367_, 2);
lean_dec_ref(v_a_1363_);
v_a_1399_ = lean_ctor_get(v___x_1395_, 0);
v_a_1400_ = lean_ctor_get(v___x_1395_, 1);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1402_ = v___x_1395_;
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_a_1400_);
lean_inc(v_a_1399_);
lean_dec(v___x_1395_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1405_; 
if (v_isShared_1403_ == 0)
{
v___x_1405_ = v___x_1402_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v_a_1399_);
lean_ctor_set(v_reuseFailAlloc_1406_, 1, v_a_1400_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
}
}
}
}
case 9:
{
lean_object* v___x_1408_; 
lean_dec(v_offset_1362_);
v___x_1408_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1367_, v_e_1361_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_);
return v___x_1408_;
}
case 2:
{
lean_object* v___x_1409_; 
lean_dec(v_offset_1362_);
v___x_1409_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1367_, v_e_1361_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_);
return v___x_1409_;
}
case 1:
{
lean_object* v___x_1410_; 
lean_dec(v_offset_1362_);
v___x_1410_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1367_, v_e_1361_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_);
return v___x_1410_;
}
case 4:
{
lean_object* v___x_1411_; 
lean_dec(v_offset_1362_);
v___x_1411_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1367_, v_e_1361_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_);
return v___x_1411_;
}
case 3:
{
lean_object* v___x_1412_; 
lean_dec(v_offset_1362_);
v___x_1412_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1367_, v_e_1361_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_);
return v___x_1412_;
}
default: 
{
lean_object* v___x_1413_; uint8_t v___x_1414_; 
v___x_1413_ = l_Lean_Expr_looseBVarRange(v_e_1361_);
v___x_1414_ = lean_nat_dec_le(v___x_1413_, v_offset_1362_);
lean_dec(v___x_1413_);
if (v___x_1414_ == 0)
{
switch(lean_obj_tag(v_e_1361_))
{
case 9:
{
lean_object* v___x_1415_; 
lean_dec(v_offset_1362_);
v___x_1415_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1367_, v_e_1361_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_);
return v___x_1415_;
}
case 2:
{
lean_object* v___x_1416_; 
lean_dec(v_offset_1362_);
v___x_1416_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1367_, v_e_1361_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_);
return v___x_1416_;
}
case 0:
{
lean_object* v___x_1417_; 
lean_dec(v_offset_1362_);
v___x_1417_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1367_, v_e_1361_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_);
return v___x_1417_;
}
case 1:
{
lean_object* v___x_1418_; 
lean_dec(v_offset_1362_);
v___x_1418_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1367_, v_e_1361_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_);
return v___x_1418_;
}
case 4:
{
lean_object* v___x_1419_; 
lean_dec(v_offset_1362_);
v___x_1419_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1367_, v_e_1361_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_);
return v___x_1419_;
}
case 3:
{
lean_object* v___x_1420_; 
lean_dec(v_offset_1362_);
v___x_1420_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1367_, v_e_1361_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_);
return v___x_1420_;
}
default: 
{
lean_object* v___x_1421_; 
v___x_1421_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0(v_n_1358_, v_beginIdx_1359_, v_subst_1360_, v_e_1361_, v_offset_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_);
if (lean_obj_tag(v___x_1421_) == 0)
{
lean_object* v_a_1422_; lean_object* v_a_1423_; lean_object* v_fst_1424_; lean_object* v_snd_1425_; lean_object* v___x_1426_; 
v_a_1422_ = lean_ctor_get(v___x_1421_, 0);
lean_inc(v_a_1422_);
v_a_1423_ = lean_ctor_get(v___x_1421_, 1);
lean_inc(v_a_1423_);
lean_dec_ref_known(v___x_1421_, 2);
v_fst_1424_ = lean_ctor_get(v_a_1422_, 0);
lean_inc(v_fst_1424_);
v_snd_1425_ = lean_ctor_get(v_a_1422_, 1);
lean_inc(v_snd_1425_);
lean_dec(v_a_1422_);
v___x_1426_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1367_, v_fst_1424_, v_snd_1425_, v_a_1364_, v_a_1365_, v_a_1423_);
return v___x_1426_;
}
else
{
lean_dec_ref_known(v_key_1367_, 2);
return v___x_1421_;
}
}
}
}
else
{
lean_object* v___x_1427_; 
lean_dec(v_offset_1362_);
v___x_1427_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1367_, v_e_1361_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_);
return v___x_1427_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0___boxed(lean_object* v_n_1428_, lean_object* v_beginIdx_1429_, lean_object* v_subst_1430_, lean_object* v_e_1431_, lean_object* v_offset_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_){
_start:
{
uint8_t v_a_boxed_1437_; lean_object* v_res_1438_; 
v_a_boxed_1437_ = lean_unbox(v_a_1434_);
v_res_1438_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1428_, v_beginIdx_1429_, v_subst_1430_, v_e_1431_, v_offset_1432_, v_a_1433_, v_a_boxed_1437_, v_a_1435_, v_a_1436_);
lean_dec_ref(v_a_1435_);
lean_dec_ref(v_subst_1430_);
lean_dec(v_beginIdx_1429_);
lean_dec(v_n_1428_);
return v_res_1438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0___boxed(lean_object* v_n_1439_, lean_object* v_beginIdx_1440_, lean_object* v_subst_1441_, lean_object* v_e_1442_, lean_object* v_offset_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_){
_start:
{
uint8_t v_a_boxed_1448_; lean_object* v_res_1449_; 
v_a_boxed_1448_ = lean_unbox(v_a_1445_);
v_res_1449_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0(v_n_1439_, v_beginIdx_1440_, v_subst_1441_, v_e_1442_, v_offset_1443_, v_a_1444_, v_a_boxed_1448_, v_a_1446_, v_a_1447_);
lean_dec_ref(v_a_1446_);
lean_dec_ref(v_subst_1441_);
lean_dec(v_beginIdx_1440_);
lean_dec(v_n_1439_);
return v_res_1449_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__1(void){
_start:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1451_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__2));
v___x_1452_ = lean_unsigned_to_nat(34u);
v___x_1453_ = lean_unsigned_to_nat(57u);
v___x_1454_ = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__0));
v___x_1455_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__3));
v___x_1456_ = l_mkPanicMessageWithDecl(v___x_1455_, v___x_1454_, v___x_1453_, v___x_1452_, v___x_1451_);
return v___x_1456_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__2(void){
_start:
{
lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; 
v___x_1457_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__2));
v___x_1458_ = lean_unsigned_to_nat(32u);
v___x_1459_ = lean_unsigned_to_nat(56u);
v___x_1460_ = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__0));
v___x_1461_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__3));
v___x_1462_ = l_mkPanicMessageWithDecl(v___x_1461_, v___x_1460_, v___x_1459_, v___x_1458_, v___x_1457_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27(lean_object* v_e_1463_, lean_object* v_beginIdx_1464_, lean_object* v_endIdx_1465_, lean_object* v_subst_1466_, uint8_t v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_){
_start:
{
uint8_t v___x_1470_; 
v___x_1470_ = lean_nat_dec_lt(v_endIdx_1465_, v_beginIdx_1464_);
if (v___x_1470_ == 0)
{
lean_object* v___x_1471_; uint8_t v___x_1472_; 
v___x_1471_ = lean_array_get_size(v_subst_1466_);
v___x_1472_ = lean_nat_dec_lt(v___x_1471_, v_endIdx_1465_);
if (v___x_1472_ == 0)
{
lean_object* v_n_1473_; lean_object* v___x_1474_; 
v_n_1473_ = lean_nat_sub(v_endIdx_1465_, v_beginIdx_1464_);
v___x_1474_ = lean_unsigned_to_nat(0u);
switch(lean_obj_tag(v_e_1463_))
{
case 0:
{
lean_object* v_deBruijnIndex_1475_; uint8_t v___x_1476_; 
v_deBruijnIndex_1475_ = lean_ctor_get(v_e_1463_, 0);
v___x_1476_ = lean_nat_dec_le(v___x_1474_, v_deBruijnIndex_1475_);
if (v___x_1476_ == 0)
{
lean_object* v___x_1477_; 
lean_dec(v_n_1473_);
v___x_1477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1477_, 0, v_e_1463_);
lean_ctor_set(v___x_1477_, 1, v_a_1469_);
return v___x_1477_;
}
else
{
uint8_t v___x_1478_; 
lean_inc(v_deBruijnIndex_1475_);
lean_dec_ref_known(v_e_1463_, 1);
v___x_1478_ = lean_nat_dec_lt(v_deBruijnIndex_1475_, v_n_1473_);
if (v___x_1478_ == 0)
{
lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___x_1479_ = lean_nat_sub(v_deBruijnIndex_1475_, v_n_1473_);
lean_dec(v_n_1473_);
lean_dec(v_deBruijnIndex_1475_);
v___x_1480_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___redArg(v___x_1479_, v_a_1469_);
return v___x_1480_;
}
else
{
lean_object* v___x_1481_; lean_object* v_v_1482_; lean_object* v___x_1483_; 
lean_dec(v_n_1473_);
v___x_1481_ = lean_nat_add(v_beginIdx_1464_, v_deBruijnIndex_1475_);
lean_dec(v_deBruijnIndex_1475_);
v_v_1482_ = lean_array_fget_borrowed(v_subst_1466_, v___x_1481_);
lean_dec(v___x_1481_);
lean_inc(v_v_1482_);
v___x_1483_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(v_v_1482_, v___x_1474_, v___x_1474_, v_a_1467_, v_a_1468_, v_a_1469_);
return v___x_1483_;
}
}
}
case 9:
{
lean_object* v___x_1484_; 
lean_dec(v_n_1473_);
v___x_1484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1484_, 0, v_e_1463_);
lean_ctor_set(v___x_1484_, 1, v_a_1469_);
return v___x_1484_;
}
case 2:
{
lean_object* v___x_1485_; 
lean_dec(v_n_1473_);
v___x_1485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1485_, 0, v_e_1463_);
lean_ctor_set(v___x_1485_, 1, v_a_1469_);
return v___x_1485_;
}
case 1:
{
lean_object* v___x_1486_; 
lean_dec(v_n_1473_);
v___x_1486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1486_, 0, v_e_1463_);
lean_ctor_set(v___x_1486_, 1, v_a_1469_);
return v___x_1486_;
}
case 4:
{
lean_object* v___x_1487_; 
lean_dec(v_n_1473_);
v___x_1487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1487_, 0, v_e_1463_);
lean_ctor_set(v___x_1487_, 1, v_a_1469_);
return v___x_1487_;
}
case 3:
{
lean_object* v___x_1488_; 
lean_dec(v_n_1473_);
v___x_1488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1488_, 0, v_e_1463_);
lean_ctor_set(v___x_1488_, 1, v_a_1469_);
return v___x_1488_;
}
default: 
{
lean_object* v___x_1489_; uint8_t v___x_1490_; 
v___x_1489_ = l_Lean_Expr_looseBVarRange(v_e_1463_);
v___x_1490_ = lean_nat_dec_le(v___x_1489_, v___x_1474_);
lean_dec(v___x_1489_);
if (v___x_1490_ == 0)
{
switch(lean_obj_tag(v_e_1463_))
{
case 9:
{
lean_object* v___x_1491_; 
lean_dec(v_n_1473_);
v___x_1491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1491_, 0, v_e_1463_);
lean_ctor_set(v___x_1491_, 1, v_a_1469_);
return v___x_1491_;
}
case 2:
{
lean_object* v___x_1492_; 
lean_dec(v_n_1473_);
v___x_1492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1492_, 0, v_e_1463_);
lean_ctor_set(v___x_1492_, 1, v_a_1469_);
return v___x_1492_;
}
case 0:
{
lean_object* v___x_1493_; 
lean_dec(v_n_1473_);
v___x_1493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1493_, 0, v_e_1463_);
lean_ctor_set(v___x_1493_, 1, v_a_1469_);
return v___x_1493_;
}
case 1:
{
lean_object* v___x_1494_; 
lean_dec(v_n_1473_);
v___x_1494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1494_, 0, v_e_1463_);
lean_ctor_set(v___x_1494_, 1, v_a_1469_);
return v___x_1494_;
}
case 4:
{
lean_object* v___x_1495_; 
lean_dec(v_n_1473_);
v___x_1495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1495_, 0, v_e_1463_);
lean_ctor_set(v___x_1495_, 1, v_a_1469_);
return v___x_1495_;
}
case 3:
{
lean_object* v___x_1496_; 
lean_dec(v_n_1473_);
v___x_1496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1496_, 0, v_e_1463_);
lean_ctor_set(v___x_1496_, 1, v_a_1469_);
return v___x_1496_;
}
default: 
{
lean_object* v___x_1497_; lean_object* v___x_1498_; 
v___x_1497_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__2, &l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__2_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__2);
v___x_1498_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0(v_n_1473_, v_beginIdx_1464_, v_subst_1466_, v_e_1463_, v___x_1474_, v___x_1497_, v_a_1467_, v_a_1468_, v_a_1469_);
lean_dec(v_n_1473_);
if (lean_obj_tag(v___x_1498_) == 0)
{
lean_object* v_a_1499_; lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1508_; 
v_a_1499_ = lean_ctor_get(v___x_1498_, 0);
v_a_1500_ = lean_ctor_get(v___x_1498_, 1);
v_isSharedCheck_1508_ = !lean_is_exclusive(v___x_1498_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1502_ = v___x_1498_;
v_isShared_1503_ = v_isSharedCheck_1508_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_inc(v_a_1499_);
lean_dec(v___x_1498_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1508_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v_fst_1504_; lean_object* v___x_1506_; 
v_fst_1504_ = lean_ctor_get(v_a_1499_, 0);
lean_inc(v_fst_1504_);
lean_dec(v_a_1499_);
if (v_isShared_1503_ == 0)
{
lean_ctor_set(v___x_1502_, 0, v_fst_1504_);
v___x_1506_ = v___x_1502_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_fst_1504_);
lean_ctor_set(v_reuseFailAlloc_1507_, 1, v_a_1500_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
}
else
{
lean_object* v_a_1509_; lean_object* v_a_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1517_; 
v_a_1509_ = lean_ctor_get(v___x_1498_, 0);
v_a_1510_ = lean_ctor_get(v___x_1498_, 1);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1498_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1512_ = v___x_1498_;
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_a_1510_);
lean_inc(v_a_1509_);
lean_dec(v___x_1498_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___x_1515_; 
if (v_isShared_1513_ == 0)
{
v___x_1515_ = v___x_1512_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_a_1509_);
lean_ctor_set(v_reuseFailAlloc_1516_, 1, v_a_1510_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
}
}
}
else
{
lean_object* v___x_1518_; 
lean_dec(v_n_1473_);
v___x_1518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1518_, 0, v_e_1463_);
lean_ctor_set(v___x_1518_, 1, v_a_1469_);
return v___x_1518_;
}
}
}
}
else
{
lean_object* v___x_1519_; lean_object* v___x_1520_; 
lean_dec_ref(v_e_1463_);
v___x_1519_ = lean_obj_once(&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__1, &l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__1_once, _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__1);
v___x_1520_ = l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1(v___x_1519_, v_a_1467_, v_a_1468_, v_a_1469_);
return v___x_1520_;
}
}
else
{
lean_object* v___x_1521_; lean_object* v___x_1522_; 
lean_dec_ref(v_e_1463_);
v___x_1521_ = lean_obj_once(&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__2, &l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__2_once, _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__2);
v___x_1522_ = l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1(v___x_1521_, v_a_1467_, v_a_1468_, v_a_1469_);
return v___x_1522_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___boxed(lean_object* v_e_1523_, lean_object* v_beginIdx_1524_, lean_object* v_endIdx_1525_, lean_object* v_subst_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_){
_start:
{
uint8_t v_a_boxed_1530_; lean_object* v_res_1531_; 
v_a_boxed_1530_ = lean_unbox(v_a_1527_);
v_res_1531_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27(v_e_1523_, v_beginIdx_1524_, v_endIdx_1525_, v_subst_1526_, v_a_boxed_1530_, v_a_1528_, v_a_1529_);
lean_dec_ref(v_a_1528_);
lean_dec_ref(v_subst_1526_);
lean_dec(v_endIdx_1525_);
lean_dec(v_beginIdx_1524_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27(lean_object* v_e_1532_, lean_object* v_subst_1533_, uint8_t v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_){
_start:
{
lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; 
v___x_1537_ = lean_unsigned_to_nat(0u);
v___x_1538_ = lean_array_get_size(v_subst_1533_);
v___x_1539_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27(v_e_1532_, v___x_1537_, v___x_1538_, v_subst_1533_, v_a_1534_, v_a_1535_, v_a_1536_);
return v___x_1539_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27___boxed(lean_object* v_e_1540_, lean_object* v_subst_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_){
_start:
{
uint8_t v_a_boxed_1545_; lean_object* v_res_1546_; 
v_a_boxed_1545_ = lean_unbox(v_a_1542_);
v_res_1546_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27(v_e_1540_, v_subst_1541_, v_a_boxed_1545_, v_a_1543_, v_a_1544_);
lean_dec_ref(v_a_1543_);
lean_dec_ref(v_subst_1541_);
return v_res_1546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateS(lean_object* v_e_1547_, lean_object* v_subst_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_){
_start:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; uint8_t v_debug_1558_; lean_object* v_env_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; uint8_t v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1556_ = lean_st_ref_get(v_a_1550_);
v___x_1557_ = lean_st_ref_get(v_a_1554_);
v_debug_1558_ = lean_ctor_get_uint8(v___x_1556_, sizeof(void*)*11);
lean_dec(v___x_1556_);
v_env_1559_ = lean_ctor_get(v___x_1557_, 0);
lean_inc_ref(v_env_1559_);
lean_dec(v___x_1557_);
v___x_1560_ = lean_box(v_debug_1558_);
v___x_1561_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27___boxed), 5, 3);
lean_closure_set(v___x_1561_, 0, v_e_1547_);
lean_closure_set(v___x_1561_, 1, v_subst_1548_);
lean_closure_set(v___x_1561_, 2, v___x_1560_);
v___x_1562_ = 0;
v___x_1563_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_1563_, 0, v_env_1559_);
lean_ctor_set_uint8(v___x_1563_, sizeof(void*)*1, v___x_1562_);
lean_ctor_set_uint8(v___x_1563_, sizeof(void*)*1 + 1, v___x_1562_);
v___x_1564_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___x_1561_, v___x_1563_, v_a_1550_);
if (lean_obj_tag(v___x_1564_) == 0)
{
lean_object* v_a_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1575_; 
v_a_1565_ = lean_ctor_get(v___x_1564_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1567_ = v___x_1564_;
v_isShared_1568_ = v_isSharedCheck_1575_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_a_1565_);
lean_dec(v___x_1564_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1575_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
if (lean_obj_tag(v_a_1565_) == 0)
{
lean_object* v___x_1569_; lean_object* v___x_1570_; 
lean_dec_ref_known(v_a_1565_, 1);
lean_del_object(v___x_1567_);
v___x_1569_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__2, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__2_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__2);
v___x_1570_ = l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(v___x_1569_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_);
return v___x_1570_;
}
else
{
lean_object* v_a_1571_; lean_object* v___x_1573_; 
v_a_1571_ = lean_ctor_get(v_a_1565_, 0);
lean_inc(v_a_1571_);
lean_dec_ref_known(v_a_1565_, 1);
if (v_isShared_1568_ == 0)
{
lean_ctor_set(v___x_1567_, 0, v_a_1571_);
v___x_1573_ = v___x_1567_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v_a_1571_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
}
}
else
{
lean_object* v_a_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1583_; 
v_a_1576_ = lean_ctor_get(v___x_1564_, 0);
v_isSharedCheck_1583_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1578_ = v___x_1564_;
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_a_1576_);
lean_dec(v___x_1564_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1581_; 
if (v_isShared_1579_ == 0)
{
v___x_1581_ = v___x_1578_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v_a_1576_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
return v___x_1581_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateS___boxed(lean_object* v_e_1584_, lean_object* v_subst_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_){
_start:
{
lean_object* v_res_1593_; 
v_res_1593_ = l_Lean_Meta_Sym_instantiateS(v_e_1584_, v_subst_1585_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_, v_a_1590_, v_a_1591_);
lean_dec(v_a_1591_);
lean_dec_ref(v_a_1590_);
lean_dec(v_a_1589_);
lean_dec_ref(v_a_1588_);
lean_dec(v_a_1587_);
lean_dec_ref(v_a_1586_);
return v_res_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0_spec__0(lean_object* v_f_1594_, lean_object* v_a_1595_, uint8_t v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_){
_start:
{
lean_object* v___y_1600_; 
if (v___y_1596_ == 0)
{
v___y_1600_ = v___y_1598_;
goto v___jp_1599_;
}
else
{
lean_object* v___x_1603_; 
v___x_1603_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_f_1594_, v___y_1596_, v___y_1597_, v___y_1598_);
if (lean_obj_tag(v___x_1603_) == 0)
{
lean_object* v_a_1604_; lean_object* v___x_1605_; 
v_a_1604_ = lean_ctor_get(v___x_1603_, 1);
lean_inc(v_a_1604_);
lean_dec_ref_known(v___x_1603_, 2);
v___x_1605_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_a_1595_, v___y_1596_, v___y_1597_, v_a_1604_);
if (lean_obj_tag(v___x_1605_) == 0)
{
lean_object* v_a_1606_; 
v_a_1606_ = lean_ctor_get(v___x_1605_, 1);
lean_inc(v_a_1606_);
lean_dec_ref_known(v___x_1605_, 2);
v___y_1600_ = v_a_1606_;
goto v___jp_1599_;
}
else
{
lean_object* v_a_1607_; lean_object* v_a_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1615_; 
lean_dec_ref(v_a_1595_);
lean_dec_ref(v_f_1594_);
v_a_1607_ = lean_ctor_get(v___x_1605_, 0);
v_a_1608_ = lean_ctor_get(v___x_1605_, 1);
v_isSharedCheck_1615_ = !lean_is_exclusive(v___x_1605_);
if (v_isSharedCheck_1615_ == 0)
{
v___x_1610_ = v___x_1605_;
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_a_1608_);
lean_inc(v_a_1607_);
lean_dec(v___x_1605_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
lean_object* v___x_1613_; 
if (v_isShared_1611_ == 0)
{
v___x_1613_ = v___x_1610_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v_a_1607_);
lean_ctor_set(v_reuseFailAlloc_1614_, 1, v_a_1608_);
v___x_1613_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
return v___x_1613_;
}
}
}
}
else
{
lean_object* v_a_1616_; lean_object* v_a_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1624_; 
lean_dec_ref(v_a_1595_);
lean_dec_ref(v_f_1594_);
v_a_1616_ = lean_ctor_get(v___x_1603_, 0);
v_a_1617_ = lean_ctor_get(v___x_1603_, 1);
v_isSharedCheck_1624_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1619_ = v___x_1603_;
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_a_1617_);
lean_inc(v_a_1616_);
lean_dec(v___x_1603_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1622_; 
if (v_isShared_1620_ == 0)
{
v___x_1622_ = v___x_1619_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v_a_1616_);
lean_ctor_set(v_reuseFailAlloc_1623_, 1, v_a_1617_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
return v___x_1622_;
}
}
}
}
v___jp_1599_:
{
lean_object* v___x_1601_; lean_object* v___x_1602_; 
v___x_1601_ = l_Lean_Expr_app___override(v_f_1594_, v_a_1595_);
v___x_1602_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1601_, v___y_1600_);
return v___x_1602_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0_spec__0___boxed(lean_object* v_f_1625_, lean_object* v_a_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_){
_start:
{
uint8_t v___y_1405__boxed_1630_; lean_object* v_res_1631_; 
v___y_1405__boxed_1630_ = lean_unbox(v___y_1627_);
v_res_1631_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0_spec__0(v_f_1625_, v_a_1626_, v___y_1405__boxed_1630_, v___y_1628_, v___y_1629_);
lean_dec_ref(v___y_1628_);
return v_res_1631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0(lean_object* v_revArgs_1632_, lean_object* v_start_1633_, lean_object* v_b_1634_, lean_object* v_i_1635_, uint8_t v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_){
_start:
{
uint8_t v___x_1639_; 
v___x_1639_ = lean_nat_dec_le(v_i_1635_, v_start_1633_);
if (v___x_1639_ == 0)
{
lean_object* v___x_1640_; lean_object* v_i_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; 
v___x_1640_ = lean_unsigned_to_nat(1u);
v_i_1641_ = lean_nat_sub(v_i_1635_, v___x_1640_);
lean_dec(v_i_1635_);
v___x_1642_ = l_Lean_instInhabitedExpr;
v___x_1643_ = lean_array_get_borrowed(v___x_1642_, v_revArgs_1632_, v_i_1641_);
lean_inc(v___x_1643_);
v___x_1644_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0_spec__0(v_b_1634_, v___x_1643_, v___y_1636_, v___y_1637_, v___y_1638_);
if (lean_obj_tag(v___x_1644_) == 0)
{
lean_object* v_a_1645_; lean_object* v_a_1646_; 
v_a_1645_ = lean_ctor_get(v___x_1644_, 0);
lean_inc(v_a_1645_);
v_a_1646_ = lean_ctor_get(v___x_1644_, 1);
lean_inc(v_a_1646_);
lean_dec_ref_known(v___x_1644_, 2);
v_b_1634_ = v_a_1645_;
v_i_1635_ = v_i_1641_;
v___y_1638_ = v_a_1646_;
goto _start;
}
else
{
lean_dec(v_i_1641_);
return v___x_1644_;
}
}
else
{
lean_object* v___x_1648_; 
lean_dec(v_i_1635_);
v___x_1648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1648_, 0, v_b_1634_);
lean_ctor_set(v___x_1648_, 1, v___y_1638_);
return v___x_1648_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0___boxed(lean_object* v_revArgs_1649_, lean_object* v_start_1650_, lean_object* v_b_1651_, lean_object* v_i_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_){
_start:
{
uint8_t v___y_1468__boxed_1656_; lean_object* v_res_1657_; 
v___y_1468__boxed_1656_ = lean_unbox(v___y_1653_);
v_res_1657_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0(v_revArgs_1649_, v_start_1650_, v_b_1651_, v_i_1652_, v___y_1468__boxed_1656_, v___y_1654_, v___y_1655_);
lean_dec_ref(v___y_1654_);
lean_dec(v_start_1650_);
lean_dec_ref(v_revArgs_1649_);
return v_res_1657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go(lean_object* v_revArgs_1658_, lean_object* v_sz_1659_, lean_object* v_e_1660_, lean_object* v_i_1661_, uint8_t v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_){
_start:
{
switch(lean_obj_tag(v_e_1660_))
{
case 6:
{
lean_object* v_body_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; uint8_t v___x_1668_; 
v_body_1665_ = lean_ctor_get(v_e_1660_, 2);
lean_inc_ref(v_body_1665_);
lean_dec_ref_known(v_e_1660_, 3);
v___x_1666_ = lean_unsigned_to_nat(1u);
v___x_1667_ = lean_nat_add(v_i_1661_, v___x_1666_);
lean_dec(v_i_1661_);
v___x_1668_ = lean_nat_dec_lt(v___x_1667_, v_sz_1659_);
if (v___x_1668_ == 0)
{
lean_object* v___x_1669_; 
lean_dec(v___x_1667_);
v___x_1669_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27(v_body_1665_, v_revArgs_1658_, v_a_1662_, v_a_1663_, v_a_1664_);
return v___x_1669_;
}
else
{
v_e_1660_ = v_body_1665_;
v_i_1661_ = v___x_1667_;
goto _start;
}
}
case 10:
{
lean_object* v_expr_1671_; 
v_expr_1671_ = lean_ctor_get(v_e_1660_, 1);
lean_inc_ref(v_expr_1671_);
lean_dec_ref_known(v_e_1660_, 2);
v_e_1660_ = v_expr_1671_;
goto _start;
}
default: 
{
lean_object* v_n_1673_; lean_object* v___x_1674_; 
v_n_1673_ = lean_nat_sub(v_sz_1659_, v_i_1661_);
lean_dec(v_i_1661_);
v___x_1674_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27(v_e_1660_, v_n_1673_, v_sz_1659_, v_revArgs_1658_, v_a_1662_, v_a_1663_, v_a_1664_);
if (lean_obj_tag(v___x_1674_) == 0)
{
lean_object* v_a_1675_; lean_object* v_a_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; 
v_a_1675_ = lean_ctor_get(v___x_1674_, 0);
lean_inc(v_a_1675_);
v_a_1676_ = lean_ctor_get(v___x_1674_, 1);
lean_inc(v_a_1676_);
lean_dec_ref_known(v___x_1674_, 2);
v___x_1677_ = lean_unsigned_to_nat(0u);
v___x_1678_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0(v_revArgs_1658_, v___x_1677_, v_a_1675_, v_n_1673_, v_a_1662_, v_a_1663_, v_a_1676_);
return v___x_1678_;
}
else
{
lean_dec(v_n_1673_);
return v___x_1674_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go___boxed(lean_object* v_revArgs_1679_, lean_object* v_sz_1680_, lean_object* v_e_1681_, lean_object* v_i_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_){
_start:
{
uint8_t v_a_boxed_1686_; lean_object* v_res_1687_; 
v_a_boxed_1686_ = lean_unbox(v_a_1683_);
v_res_1687_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go(v_revArgs_1679_, v_sz_1680_, v_e_1681_, v_i_1682_, v_a_boxed_1686_, v_a_1684_, v_a_1685_);
lean_dec_ref(v_a_1684_);
lean_dec(v_sz_1680_);
lean_dec_ref(v_revArgs_1679_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27(lean_object* v_f_1688_, lean_object* v_revArgs_1689_, uint8_t v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_){
_start:
{
lean_object* v_sz_1693_; lean_object* v___x_1694_; uint8_t v___x_1695_; 
v_sz_1693_ = lean_array_get_size(v_revArgs_1689_);
v___x_1694_ = lean_unsigned_to_nat(0u);
v___x_1695_ = lean_nat_dec_eq(v_sz_1693_, v___x_1694_);
if (v___x_1695_ == 0)
{
lean_object* v___x_1696_; 
v___x_1696_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go(v_revArgs_1689_, v_sz_1693_, v_f_1688_, v___x_1694_, v_a_1690_, v_a_1691_, v_a_1692_);
return v___x_1696_;
}
else
{
lean_object* v___x_1697_; 
v___x_1697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1697_, 0, v_f_1688_);
lean_ctor_set(v___x_1697_, 1, v_a_1692_);
return v___x_1697_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27___boxed(lean_object* v_f_1698_, lean_object* v_revArgs_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_){
_start:
{
uint8_t v_a_boxed_1703_; lean_object* v_res_1704_; 
v_a_boxed_1703_ = lean_unbox(v_a_1700_);
v_res_1704_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27(v_f_1698_, v_revArgs_1699_, v_a_boxed_1703_, v_a_1701_, v_a_1702_);
lean_dec_ref(v_a_1701_);
lean_dec_ref(v_revArgs_1699_);
return v_res_1704_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0_spec__1___redArg(lean_object* v_b_1705_, lean_object* v_acc_1706_, lean_object* v_i_1707_){
_start:
{
lean_object* v___y_1709_; lean_object* v_keyArray_1717_; lean_object* v_valueArray_1718_; lean_object* v___x_1719_; uint8_t v___x_1720_; 
v_keyArray_1717_ = lean_ctor_get(v_b_1705_, 1);
v_valueArray_1718_ = lean_ctor_get(v_b_1705_, 2);
v___x_1719_ = lean_array_get_size(v_keyArray_1717_);
v___x_1720_ = lean_nat_dec_lt(v_i_1707_, v___x_1719_);
if (v___x_1720_ == 0)
{
lean_dec(v_i_1707_);
return v_acc_1706_;
}
else
{
lean_object* v___x_1721_; uint8_t v_isSome_1722_; 
v___x_1721_ = lean_array_fget_borrowed(v_keyArray_1717_, v_i_1707_);
v_isSome_1722_ = lean_noption_is_some(v___x_1721_);
if (v_isSome_1722_ == 0)
{
goto v___jp_1713_;
}
else
{
lean_object* v___x_1723_; uint8_t v_isSome_1724_; 
v___x_1723_ = lean_array_fget_borrowed(v_valueArray_1718_, v_i_1707_);
v_isSome_1724_ = lean_noption_is_some(v___x_1723_);
if (v_isSome_1724_ == 0)
{
goto v___jp_1713_;
}
else
{
lean_object* v_val_1725_; lean_object* v_val_1726_; lean_object* v_i_1728_; lean_object* v___x_1733_; 
lean_inc(v___x_1721_);
v_val_1725_ = lean_noption_get(v___x_1721_);
lean_inc(v___x_1723_);
v_val_1726_ = lean_noption_get(v___x_1723_);
v___x_1733_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11_spec__12___redArg(v_acc_1706_, v_val_1725_);
switch(lean_obj_tag(v___x_1733_))
{
case 0:
{
lean_object* v_index_1734_; lean_object* v_size_1735_; lean_object* v___x_1736_; 
v_index_1734_ = lean_ctor_get(v___x_1733_, 0);
lean_inc(v_index_1734_);
lean_dec_ref_known(v___x_1733_, 3);
v_size_1735_ = lean_ctor_get(v_acc_1706_, 0);
lean_inc(v_size_1735_);
v___x_1736_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_1706_, v_size_1735_, v_index_1734_, v_val_1725_, v_val_1726_);
lean_dec(v_index_1734_);
v___y_1709_ = v___x_1736_;
goto v___jp_1708_;
}
case 1:
{
lean_object* v_index_1737_; 
v_index_1737_ = lean_ctor_get(v___x_1733_, 0);
lean_inc(v_index_1737_);
lean_dec_ref_known(v___x_1733_, 1);
v_i_1728_ = v_index_1737_;
goto v___jp_1727_;
}
default: 
{
lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1738_ = lean_unsigned_to_nat(0u);
v___x_1739_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_1706_, v___x_1738_);
if (lean_obj_tag(v___x_1739_) == 0)
{
lean_object* v_index_1740_; 
v_index_1740_ = lean_ctor_get(v___x_1739_, 0);
lean_inc(v_index_1740_);
lean_dec_ref_known(v___x_1739_, 1);
v_i_1728_ = v_index_1740_;
goto v___jp_1727_;
}
else
{
lean_dec(v_val_1726_);
lean_dec(v_val_1725_);
v___y_1709_ = v_acc_1706_;
goto v___jp_1708_;
}
}
}
v___jp_1727_:
{
lean_object* v_size_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; 
v_size_1729_ = lean_ctor_get(v_acc_1706_, 0);
v___x_1730_ = lean_unsigned_to_nat(1u);
v___x_1731_ = lean_nat_add(v_size_1729_, v___x_1730_);
v___x_1732_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_1706_, v___x_1731_, v_i_1728_, v_val_1725_, v_val_1726_);
lean_dec(v_i_1728_);
v___y_1709_ = v___x_1732_;
goto v___jp_1708_;
}
}
}
}
v___jp_1708_:
{
lean_object* v___x_1710_; lean_object* v___x_1711_; 
v___x_1710_ = lean_unsigned_to_nat(1u);
v___x_1711_ = lean_nat_add(v_i_1707_, v___x_1710_);
lean_dec(v_i_1707_);
v_acc_1706_ = v___y_1709_;
v_i_1707_ = v___x_1711_;
goto _start;
}
v___jp_1713_:
{
lean_object* v___x_1714_; lean_object* v___x_1715_; 
v___x_1714_ = lean_unsigned_to_nat(1u);
v___x_1715_ = lean_nat_add(v_i_1707_, v___x_1714_);
lean_dec(v_i_1707_);
v_i_1707_ = v___x_1715_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_b_1741_, lean_object* v_acc_1742_, lean_object* v_i_1743_){
_start:
{
lean_object* v_res_1744_; 
v_res_1744_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0_spec__1___redArg(v_b_1741_, v_acc_1742_, v_i_1743_);
lean_dec_ref(v_b_1741_);
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(lean_object* v_init_1745_, lean_object* v_b_1746_){
_start:
{
lean_object* v___x_1747_; lean_object* v___x_1748_; 
v___x_1747_ = lean_unsigned_to_nat(0u);
v___x_1748_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0_spec__1___redArg(v_b_1746_, v_init_1745_, v___x_1747_);
return v___x_1748_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg___boxed(lean_object* v_init_1749_, lean_object* v_b_1750_){
_start:
{
lean_object* v_res_1751_; 
v_res_1751_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_init_1749_, v_b_1750_);
lean_dec_ref(v_b_1750_);
return v_res_1751_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0___redArg(lean_object* v_m_1752_){
_start:
{
lean_object* v_keyArray_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v_cellCount_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v_target_1760_; lean_object* v___x_1761_; 
v_keyArray_1753_ = lean_ctor_get(v_m_1752_, 1);
v___x_1754_ = lean_array_get_size(v_keyArray_1753_);
v___x_1755_ = lean_unsigned_to_nat(2u);
v_cellCount_1756_ = lean_nat_mul(v___x_1754_, v___x_1755_);
v___x_1757_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_1756_);
v___x_1758_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1756_);
v___x_1759_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1756_);
v_target_1760_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_1760_, 0, v___x_1757_);
lean_ctor_set(v_target_1760_, 1, v___x_1758_);
lean_ctor_set(v_target_1760_, 2, v___x_1759_);
v___x_1761_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_target_1760_, v_m_1752_);
return v___x_1761_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0___redArg___boxed(lean_object* v_m_1762_){
_start:
{
lean_object* v_res_1763_; 
v_res_1763_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0___redArg(v_m_1762_);
lean_dec_ref(v_m_1762_);
return v_res_1763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(lean_object* v_key_1764_, lean_object* v_r_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_){
_start:
{
lean_object* v___y_1769_; lean_object* v___y_1773_; lean_object* v_i_1774_; lean_object* v___y_1790_; lean_object* v_i_1791_; lean_object* v___y_1797_; lean_object* v___x_1806_; 
v___x_1806_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11_spec__12___redArg(v_a_1766_, v_key_1764_);
switch(lean_obj_tag(v___x_1806_))
{
case 0:
{
lean_object* v_index_1807_; lean_object* v_size_1808_; lean_object* v___x_1809_; 
v_index_1807_ = lean_ctor_get(v___x_1806_, 0);
lean_inc(v_index_1807_);
lean_dec_ref_known(v___x_1806_, 3);
v_size_1808_ = lean_ctor_get(v_a_1766_, 0);
lean_inc(v_size_1808_);
lean_inc_ref(v_r_1765_);
v___x_1809_ = l_Std_DHashMap_Raw_setEntry___redArg(v_a_1766_, v_size_1808_, v_index_1807_, v_key_1764_, v_r_1765_);
lean_dec(v_index_1807_);
v___y_1769_ = v___x_1809_;
goto v___jp_1768_;
}
case 1:
{
lean_object* v_index_1810_; lean_object* v_size_1811_; lean_object* v_keyArray_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; uint8_t v___x_1816_; 
v_index_1810_ = lean_ctor_get(v___x_1806_, 0);
lean_inc(v_index_1810_);
lean_dec_ref_known(v___x_1806_, 1);
v_size_1811_ = lean_ctor_get(v_a_1766_, 0);
v_keyArray_1812_ = lean_ctor_get(v_a_1766_, 1);
v___x_1813_ = lean_unsigned_to_nat(1u);
v___x_1814_ = lean_nat_add(v_size_1811_, v___x_1813_);
v___x_1815_ = lean_array_get_size(v_keyArray_1812_);
v___x_1816_ = lean_nat_dec_lt(v___x_1814_, v___x_1815_);
if (v___x_1816_ == 0)
{
lean_dec(v___x_1814_);
lean_dec(v_index_1810_);
goto v___jp_1779_;
}
else
{
lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; uint8_t v___x_1821_; 
v___x_1817_ = lean_unsigned_to_nat(4u);
v___x_1818_ = lean_nat_mul(v___x_1814_, v___x_1817_);
v___x_1819_ = lean_unsigned_to_nat(3u);
v___x_1820_ = lean_nat_mul(v___x_1815_, v___x_1819_);
v___x_1821_ = lean_nat_dec_le(v___x_1818_, v___x_1820_);
lean_dec(v___x_1820_);
lean_dec(v___x_1818_);
if (v___x_1821_ == 0)
{
lean_dec(v___x_1814_);
lean_dec(v_index_1810_);
goto v___jp_1779_;
}
else
{
lean_object* v___x_1822_; 
lean_inc_ref(v_r_1765_);
v___x_1822_ = l_Std_DHashMap_Raw_setEntry___redArg(v_a_1766_, v___x_1814_, v_index_1810_, v_key_1764_, v_r_1765_);
lean_dec(v_index_1810_);
v___y_1769_ = v___x_1822_;
goto v___jp_1768_;
}
}
}
default: 
{
lean_object* v_size_1823_; lean_object* v_keyArray_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; uint8_t v___x_1828_; 
v_size_1823_ = lean_ctor_get(v_a_1766_, 0);
v_keyArray_1824_ = lean_ctor_get(v_a_1766_, 1);
v___x_1825_ = lean_unsigned_to_nat(1u);
v___x_1826_ = lean_nat_add(v_size_1823_, v___x_1825_);
v___x_1827_ = lean_array_get_size(v_keyArray_1824_);
v___x_1828_ = lean_nat_dec_lt(v___x_1826_, v___x_1827_);
if (v___x_1828_ == 0)
{
lean_object* v___x_1829_; 
lean_dec(v___x_1826_);
v___x_1829_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1766_);
lean_dec_ref(v_a_1766_);
v___y_1797_ = v___x_1829_;
goto v___jp_1796_;
}
else
{
lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; uint8_t v___x_1834_; 
v___x_1830_ = lean_unsigned_to_nat(4u);
v___x_1831_ = lean_nat_mul(v___x_1826_, v___x_1830_);
lean_dec(v___x_1826_);
v___x_1832_ = lean_unsigned_to_nat(3u);
v___x_1833_ = lean_nat_mul(v___x_1827_, v___x_1832_);
v___x_1834_ = lean_nat_dec_le(v___x_1831_, v___x_1833_);
lean_dec(v___x_1833_);
lean_dec(v___x_1831_);
if (v___x_1834_ == 0)
{
lean_object* v___x_1835_; 
v___x_1835_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1766_);
lean_dec_ref(v_a_1766_);
v___y_1797_ = v___x_1835_;
goto v___jp_1796_;
}
else
{
v___y_1797_ = v_a_1766_;
goto v___jp_1796_;
}
}
}
}
v___jp_1768_:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1770_, 0, v_r_1765_);
lean_ctor_set(v___x_1770_, 1, v___y_1769_);
v___x_1771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1771_, 0, v___x_1770_);
lean_ctor_set(v___x_1771_, 1, v_a_1767_);
return v___x_1771_;
}
v___jp_1772_:
{
lean_object* v_size_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; 
v_size_1775_ = lean_ctor_get(v___y_1773_, 0);
v___x_1776_ = lean_unsigned_to_nat(1u);
v___x_1777_ = lean_nat_add(v_size_1775_, v___x_1776_);
lean_inc_ref(v_r_1765_);
v___x_1778_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1773_, v___x_1777_, v_i_1774_, v_key_1764_, v_r_1765_);
lean_dec(v_i_1774_);
v___y_1769_ = v___x_1778_;
goto v___jp_1768_;
}
v___jp_1779_:
{
lean_object* v___x_1780_; lean_object* v___x_1781_; 
v___x_1780_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1766_);
lean_dec_ref(v_a_1766_);
v___x_1781_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11_spec__12___redArg(v___x_1780_, v_key_1764_);
switch(lean_obj_tag(v___x_1781_))
{
case 0:
{
lean_object* v_index_1782_; lean_object* v_size_1783_; lean_object* v___x_1784_; 
v_index_1782_ = lean_ctor_get(v___x_1781_, 0);
lean_inc(v_index_1782_);
lean_dec_ref_known(v___x_1781_, 3);
v_size_1783_ = lean_ctor_get(v___x_1780_, 0);
lean_inc(v_size_1783_);
lean_inc_ref(v_r_1765_);
v___x_1784_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1780_, v_size_1783_, v_index_1782_, v_key_1764_, v_r_1765_);
lean_dec(v_index_1782_);
v___y_1769_ = v___x_1784_;
goto v___jp_1768_;
}
case 1:
{
lean_object* v_index_1785_; 
v_index_1785_ = lean_ctor_get(v___x_1781_, 0);
lean_inc(v_index_1785_);
lean_dec_ref_known(v___x_1781_, 1);
v___y_1773_ = v___x_1780_;
v_i_1774_ = v_index_1785_;
goto v___jp_1772_;
}
default: 
{
lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1786_ = lean_unsigned_to_nat(0u);
v___x_1787_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1780_, v___x_1786_);
if (lean_obj_tag(v___x_1787_) == 0)
{
lean_object* v_index_1788_; 
v_index_1788_ = lean_ctor_get(v___x_1787_, 0);
lean_inc(v_index_1788_);
lean_dec_ref_known(v___x_1787_, 1);
v___y_1773_ = v___x_1780_;
v_i_1774_ = v_index_1788_;
goto v___jp_1772_;
}
else
{
lean_dec_ref(v_key_1764_);
v___y_1769_ = v___x_1780_;
goto v___jp_1768_;
}
}
}
}
v___jp_1789_:
{
lean_object* v_size_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; 
v_size_1792_ = lean_ctor_get(v___y_1790_, 0);
v___x_1793_ = lean_unsigned_to_nat(1u);
v___x_1794_ = lean_nat_add(v_size_1792_, v___x_1793_);
lean_inc_ref(v_r_1765_);
v___x_1795_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1790_, v___x_1794_, v_i_1791_, v_key_1764_, v_r_1765_);
lean_dec(v_i_1791_);
v___y_1769_ = v___x_1795_;
goto v___jp_1768_;
}
v___jp_1796_:
{
lean_object* v___x_1798_; 
v___x_1798_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11_spec__12___redArg(v___y_1797_, v_key_1764_);
switch(lean_obj_tag(v___x_1798_))
{
case 0:
{
lean_object* v_index_1799_; lean_object* v_size_1800_; lean_object* v___x_1801_; 
v_index_1799_ = lean_ctor_get(v___x_1798_, 0);
lean_inc(v_index_1799_);
lean_dec_ref_known(v___x_1798_, 3);
v_size_1800_ = lean_ctor_get(v___y_1797_, 0);
lean_inc(v_size_1800_);
lean_inc_ref(v_r_1765_);
v___x_1801_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1797_, v_size_1800_, v_index_1799_, v_key_1764_, v_r_1765_);
lean_dec(v_index_1799_);
v___y_1769_ = v___x_1801_;
goto v___jp_1768_;
}
case 1:
{
lean_object* v_index_1802_; 
v_index_1802_ = lean_ctor_get(v___x_1798_, 0);
lean_inc(v_index_1802_);
lean_dec_ref_known(v___x_1798_, 1);
v___y_1790_ = v___y_1797_;
v_i_1791_ = v_index_1802_;
goto v___jp_1789_;
}
default: 
{
lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1803_ = lean_unsigned_to_nat(0u);
v___x_1804_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1797_, v___x_1803_);
if (lean_obj_tag(v___x_1804_) == 0)
{
lean_object* v_index_1805_; 
v_index_1805_ = lean_ctor_get(v___x_1804_, 0);
lean_inc(v_index_1805_);
lean_dec_ref_known(v___x_1804_, 1);
v___y_1790_ = v___y_1797_;
v_i_1791_ = v_index_1805_;
goto v___jp_1789_;
}
else
{
lean_dec_ref(v_key_1764_);
v___y_1769_ = v___y_1797_;
goto v___jp_1768_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save(lean_object* v_key_1836_, lean_object* v_r_1837_, lean_object* v_a_1838_, uint8_t v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_){
_start:
{
lean_object* v___x_1842_; 
v___x_1842_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_1836_, v_r_1837_, v_a_1838_, v_a_1841_);
return v___x_1842_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___boxed(lean_object* v_key_1843_, lean_object* v_r_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_){
_start:
{
uint8_t v_a_boxed_1849_; lean_object* v_res_1850_; 
v_a_boxed_1849_ = lean_unbox(v_a_1846_);
v_res_1850_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save(v_key_1843_, v_r_1844_, v_a_1845_, v_a_boxed_1849_, v_a_1847_, v_a_1848_);
lean_dec_ref(v_a_1847_);
return v_res_1850_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0(lean_object* v_00_u03b2_1851_, lean_object* v_m_1852_){
_start:
{
lean_object* v___x_1853_; 
v___x_1853_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0___redArg(v_m_1852_);
return v___x_1853_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0___boxed(lean_object* v_00_u03b2_1854_, lean_object* v_m_1855_){
_start:
{
lean_object* v_res_1856_; 
v_res_1856_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0(v_00_u03b2_1854_, v_m_1855_);
lean_dec_ref(v_m_1855_);
return v_res_1856_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0(lean_object* v_00_u03b2_1857_, lean_object* v_init_1858_, lean_object* v_b_1859_){
_start:
{
lean_object* v___x_1860_; 
v___x_1860_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_init_1858_, v_b_1859_);
return v___x_1860_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1861_, lean_object* v_init_1862_, lean_object* v_b_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0(v_00_u03b2_1861_, v_init_1862_, v_b_1863_);
lean_dec_ref(v_b_1863_);
return v_res_1864_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1865_, lean_object* v_b_1866_, lean_object* v_acc_1867_, lean_object* v_i_1868_){
_start:
{
lean_object* v___x_1869_; 
v___x_1869_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0_spec__1___redArg(v_b_1866_, v_acc_1867_, v_i_1868_);
return v___x_1869_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1870_, lean_object* v_b_1871_, lean_object* v_acc_1872_, lean_object* v_i_1873_){
_start:
{
lean_object* v_res_1874_; 
v_res_1874_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0_spec__1(v_00_u03b2_1870_, v_b_1871_, v_acc_1872_, v_i_1873_);
lean_dec_ref(v_b_1871_);
return v_res_1874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0___redArg(lean_object* v_idx_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_){
_start:
{
lean_object* v___x_1878_; lean_object* v___x_1879_; 
v___x_1878_ = l_Lean_Expr_bvar___override(v_idx_1875_);
v___x_1879_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1878_, v___y_1877_);
if (lean_obj_tag(v___x_1879_) == 0)
{
lean_object* v_a_1880_; lean_object* v_a_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1889_; 
v_a_1880_ = lean_ctor_get(v___x_1879_, 0);
v_a_1881_ = lean_ctor_get(v___x_1879_, 1);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1879_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1883_ = v___x_1879_;
v_isShared_1884_ = v_isSharedCheck_1889_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_a_1881_);
lean_inc(v_a_1880_);
lean_dec(v___x_1879_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1889_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1885_; lean_object* v___x_1887_; 
v___x_1885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1885_, 0, v_a_1880_);
lean_ctor_set(v___x_1885_, 1, v___y_1876_);
if (v_isShared_1884_ == 0)
{
lean_ctor_set(v___x_1883_, 0, v___x_1885_);
v___x_1887_ = v___x_1883_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v___x_1885_);
lean_ctor_set(v_reuseFailAlloc_1888_, 1, v_a_1881_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
return v___x_1887_;
}
}
}
else
{
lean_object* v_a_1890_; lean_object* v_a_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1898_; 
lean_dec_ref(v___y_1876_);
v_a_1890_ = lean_ctor_get(v___x_1879_, 0);
v_a_1891_ = lean_ctor_get(v___x_1879_, 1);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1879_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1893_ = v___x_1879_;
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_a_1891_);
lean_inc(v_a_1890_);
lean_dec(v___x_1879_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1896_; 
if (v_isShared_1894_ == 0)
{
v___x_1896_ = v___x_1893_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_a_1890_);
lean_ctor_set(v_reuseFailAlloc_1897_, 1, v_a_1891_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0(lean_object* v_idx_1899_, lean_object* v___y_1900_, uint8_t v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_){
_start:
{
lean_object* v___x_1904_; 
v___x_1904_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0___redArg(v_idx_1899_, v___y_1900_, v___y_1903_);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0___boxed(lean_object* v_idx_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_){
_start:
{
uint8_t v___y_1133__boxed_1910_; lean_object* v_res_1911_; 
v___y_1133__boxed_1910_ = lean_unbox(v___y_1907_);
v_res_1911_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0(v_idx_1905_, v___y_1906_, v___y_1133__boxed_1910_, v___y_1908_, v___y_1909_);
lean_dec_ref(v___y_1908_);
return v_res_1911_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(lean_object* v_subst_1912_, lean_object* v_e_1913_, lean_object* v_bidx_1914_, lean_object* v_offset_1915_, lean_object* v_a_1916_, uint8_t v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_){
_start:
{
uint8_t v___x_1920_; 
v___x_1920_ = lean_nat_dec_le(v_offset_1915_, v_bidx_1914_);
if (v___x_1920_ == 0)
{
lean_object* v___x_1921_; lean_object* v___x_1922_; 
v___x_1921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1921_, 0, v_e_1913_);
lean_ctor_set(v___x_1921_, 1, v_a_1916_);
v___x_1922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1921_);
lean_ctor_set(v___x_1922_, 1, v_a_1919_);
return v___x_1922_;
}
else
{
lean_object* v_n_1923_; lean_object* v___x_1924_; uint8_t v___x_1925_; 
lean_dec_ref(v_e_1913_);
v_n_1923_ = lean_array_get_size(v_subst_1912_);
v___x_1924_ = lean_nat_add(v_offset_1915_, v_n_1923_);
v___x_1925_ = lean_nat_dec_lt(v_bidx_1914_, v___x_1924_);
lean_dec(v___x_1924_);
if (v___x_1925_ == 0)
{
lean_object* v___x_1926_; lean_object* v___x_1927_; 
v___x_1926_ = lean_nat_sub(v_bidx_1914_, v_n_1923_);
v___x_1927_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0___redArg(v___x_1926_, v_a_1916_, v_a_1919_);
return v___x_1927_;
}
else
{
lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v_v_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1928_ = lean_nat_sub(v_bidx_1914_, v_offset_1915_);
v___x_1929_ = lean_nat_sub(v_n_1923_, v___x_1928_);
lean_dec(v___x_1928_);
v___x_1930_ = lean_unsigned_to_nat(1u);
v___x_1931_ = lean_nat_sub(v___x_1929_, v___x_1930_);
lean_dec(v___x_1929_);
v_v_1932_ = lean_array_fget_borrowed(v_subst_1912_, v___x_1931_);
lean_dec(v___x_1931_);
v___x_1933_ = lean_unsigned_to_nat(0u);
lean_inc(v_v_1932_);
v___x_1934_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(v_v_1932_, v___x_1933_, v_offset_1915_, v_a_1917_, v_a_1918_, v_a_1919_);
if (lean_obj_tag(v___x_1934_) == 0)
{
lean_object* v_a_1935_; lean_object* v_a_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1944_; 
v_a_1935_ = lean_ctor_get(v___x_1934_, 0);
v_a_1936_ = lean_ctor_get(v___x_1934_, 1);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1938_ = v___x_1934_;
v_isShared_1939_ = v_isSharedCheck_1944_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_a_1936_);
lean_inc(v_a_1935_);
lean_dec(v___x_1934_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1944_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1940_; lean_object* v___x_1942_; 
v___x_1940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1940_, 0, v_a_1935_);
lean_ctor_set(v___x_1940_, 1, v_a_1916_);
if (v_isShared_1939_ == 0)
{
lean_ctor_set(v___x_1938_, 0, v___x_1940_);
v___x_1942_ = v___x_1938_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v___x_1940_);
lean_ctor_set(v_reuseFailAlloc_1943_, 1, v_a_1936_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
return v___x_1942_;
}
}
}
else
{
lean_object* v_a_1945_; lean_object* v_a_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1953_; 
lean_dec_ref(v_a_1916_);
v_a_1945_ = lean_ctor_get(v___x_1934_, 0);
v_a_1946_ = lean_ctor_get(v___x_1934_, 1);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1948_ = v___x_1934_;
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_a_1946_);
lean_inc(v_a_1945_);
lean_dec(v___x_1934_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___x_1951_; 
if (v_isShared_1949_ == 0)
{
v___x_1951_ = v___x_1948_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_a_1945_);
lean_ctor_set(v_reuseFailAlloc_1952_, 1, v_a_1946_);
v___x_1951_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
return v___x_1951_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar___boxed(lean_object* v_subst_1954_, lean_object* v_e_1955_, lean_object* v_bidx_1956_, lean_object* v_offset_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_){
_start:
{
uint8_t v_a_boxed_1962_; lean_object* v_res_1963_; 
v_a_boxed_1962_ = lean_unbox(v_a_1959_);
v_res_1963_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(v_subst_1954_, v_e_1955_, v_bidx_1956_, v_offset_1957_, v_a_1958_, v_a_boxed_1962_, v_a_1960_, v_a_1961_);
lean_dec_ref(v_a_1960_);
lean_dec(v_offset_1957_);
lean_dec(v_bidx_1956_);
lean_dec_ref(v_subst_1954_);
return v_res_1963_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault(lean_object* v_subst_1964_, lean_object* v_e_1965_, lean_object* v_offset_1966_, lean_object* v_a_1967_, uint8_t v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_){
_start:
{
if (lean_obj_tag(v_e_1965_) == 5)
{
lean_object* v_fn_1971_; lean_object* v_arg_1972_; lean_object* v_key_1973_; lean_object* v___x_1974_; 
v_fn_1971_ = lean_ctor_get(v_e_1965_, 0);
v_arg_1972_ = lean_ctor_get(v_e_1965_, 1);
lean_inc(v_offset_1966_);
lean_inc_ref(v_e_1965_);
v_key_1973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1973_, 0, v_e_1965_);
lean_ctor_set(v_key_1973_, 1, v_offset_1966_);
v___x_1974_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3___redArg(v_a_1967_, v_key_1973_);
if (lean_obj_tag(v___x_1974_) == 1)
{
lean_object* v_val_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; 
lean_dec_ref_known(v_key_1973_, 2);
lean_dec_ref_known(v_e_1965_, 2);
lean_dec(v_offset_1966_);
v_val_1975_ = lean_ctor_get(v___x_1974_, 0);
lean_inc(v_val_1975_);
lean_dec_ref_known(v___x_1974_, 1);
v___x_1976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1976_, 0, v_val_1975_);
lean_ctor_set(v___x_1976_, 1, v_a_1967_);
v___x_1977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1977_, 0, v___x_1976_);
lean_ctor_set(v___x_1977_, 1, v_a_1970_);
return v___x_1977_;
}
else
{
lean_object* v___x_1978_; 
lean_dec(v___x_1974_);
lean_inc(v_offset_1966_);
lean_inc_ref(v_fn_1971_);
v___x_1978_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault(v_subst_1964_, v_fn_1971_, v_offset_1966_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_);
if (lean_obj_tag(v___x_1978_) == 0)
{
lean_object* v_a_1979_; lean_object* v_a_1980_; lean_object* v_fst_1981_; lean_object* v_snd_1982_; lean_object* v___x_1983_; 
v_a_1979_ = lean_ctor_get(v___x_1978_, 0);
lean_inc(v_a_1979_);
v_a_1980_ = lean_ctor_get(v___x_1978_, 1);
lean_inc(v_a_1980_);
lean_dec_ref_known(v___x_1978_, 2);
v_fst_1981_ = lean_ctor_get(v_a_1979_, 0);
lean_inc(v_fst_1981_);
v_snd_1982_ = lean_ctor_get(v_a_1979_, 1);
lean_inc(v_snd_1982_);
lean_dec(v_a_1979_);
lean_inc_ref(v_arg_1972_);
v___x_1983_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1964_, v_arg_1972_, v_offset_1966_, v_snd_1982_, v_a_1968_, v_a_1969_, v_a_1980_);
if (lean_obj_tag(v___x_1983_) == 0)
{
lean_object* v_a_1984_; lean_object* v_a_1985_; lean_object* v_fst_1986_; lean_object* v_snd_1987_; uint8_t v___y_1989_; size_t v___x_1997_; size_t v___x_1998_; uint8_t v___x_1999_; 
v_a_1984_ = lean_ctor_get(v___x_1983_, 0);
lean_inc(v_a_1984_);
v_a_1985_ = lean_ctor_get(v___x_1983_, 1);
lean_inc(v_a_1985_);
lean_dec_ref_known(v___x_1983_, 2);
v_fst_1986_ = lean_ctor_get(v_a_1984_, 0);
lean_inc(v_fst_1986_);
v_snd_1987_ = lean_ctor_get(v_a_1984_, 1);
lean_inc(v_snd_1987_);
lean_dec(v_a_1984_);
v___x_1997_ = lean_ptr_addr(v_fn_1971_);
v___x_1998_ = lean_ptr_addr(v_fst_1981_);
v___x_1999_ = lean_usize_dec_eq(v___x_1997_, v___x_1998_);
if (v___x_1999_ == 0)
{
v___y_1989_ = v___x_1999_;
goto v___jp_1988_;
}
else
{
size_t v___x_2000_; size_t v___x_2001_; uint8_t v___x_2002_; 
v___x_2000_ = lean_ptr_addr(v_arg_1972_);
v___x_2001_ = lean_ptr_addr(v_fst_1986_);
v___x_2002_ = lean_usize_dec_eq(v___x_2000_, v___x_2001_);
v___y_1989_ = v___x_2002_;
goto v___jp_1988_;
}
v___jp_1988_:
{
if (v___y_1989_ == 0)
{
lean_object* v___x_1990_; 
lean_dec_ref_known(v_e_1965_, 2);
v___x_1990_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__2(v_fst_1981_, v_fst_1986_, v_snd_1987_, v_a_1968_, v_a_1969_, v_a_1985_);
if (lean_obj_tag(v___x_1990_) == 0)
{
lean_object* v_a_1991_; lean_object* v_a_1992_; lean_object* v_fst_1993_; lean_object* v_snd_1994_; lean_object* v___x_1995_; 
v_a_1991_ = lean_ctor_get(v___x_1990_, 0);
lean_inc(v_a_1991_);
v_a_1992_ = lean_ctor_get(v___x_1990_, 1);
lean_inc(v_a_1992_);
lean_dec_ref_known(v___x_1990_, 2);
v_fst_1993_ = lean_ctor_get(v_a_1991_, 0);
lean_inc(v_fst_1993_);
v_snd_1994_ = lean_ctor_get(v_a_1991_, 1);
lean_inc(v_snd_1994_);
lean_dec(v_a_1991_);
v___x_1995_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_1973_, v_fst_1993_, v_snd_1994_, v_a_1992_);
return v___x_1995_;
}
else
{
lean_dec_ref_known(v_key_1973_, 2);
return v___x_1990_;
}
}
else
{
lean_object* v___x_1996_; 
lean_dec(v_fst_1986_);
lean_dec(v_fst_1981_);
v___x_1996_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_1973_, v_e_1965_, v_snd_1987_, v_a_1985_);
return v___x_1996_;
}
}
}
else
{
lean_dec(v_fst_1981_);
lean_dec_ref_known(v_key_1973_, 2);
lean_dec_ref_known(v_e_1965_, 2);
return v___x_1983_;
}
}
else
{
lean_dec_ref_known(v_key_1973_, 2);
lean_dec_ref_known(v_e_1965_, 2);
lean_dec(v_offset_1966_);
return v___x_1978_;
}
}
}
else
{
lean_object* v___x_2003_; 
v___x_2003_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1964_, v_e_1965_, v_offset_1966_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_);
return v___x_2003_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__2(void){
_start:
{
lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; 
v___x_2006_ = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__1));
v___x_2007_ = lean_unsigned_to_nat(25u);
v___x_2008_ = lean_unsigned_to_nat(148u);
v___x_2009_ = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__0));
v___x_2010_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__0));
v___x_2011_ = l_mkPanicMessageWithDecl(v___x_2010_, v___x_2009_, v___x_2008_, v___x_2007_, v___x_2006_);
return v___x_2011_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__1(void){
_start:
{
lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; 
v___x_2013_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__2));
v___x_2014_ = lean_unsigned_to_nat(11u);
v___x_2015_ = lean_unsigned_to_nat(165u);
v___x_2016_ = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__0));
v___x_2017_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__3));
v___x_2018_ = l_mkPanicMessageWithDecl(v___x_2017_, v___x_2016_, v___x_2015_, v___x_2014_, v___x_2013_);
return v___x_2018_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta(lean_object* v_subst_2019_, lean_object* v_e_2020_, lean_object* v_f_2021_, lean_object* v_argsRev_2022_, lean_object* v_offset_2023_, uint8_t v_modified_2024_, lean_object* v_a_2025_, uint8_t v_a_2026_, lean_object* v_a_2027_, lean_object* v_a_2028_){
_start:
{
switch(lean_obj_tag(v_f_2021_))
{
case 5:
{
lean_object* v_fn_2029_; lean_object* v_arg_2030_; lean_object* v___x_2031_; 
v_fn_2029_ = lean_ctor_get(v_f_2021_, 0);
lean_inc_ref(v_fn_2029_);
v_arg_2030_ = lean_ctor_get(v_f_2021_, 1);
lean_inc_ref_n(v_arg_2030_, 2);
lean_dec_ref_known(v_f_2021_, 2);
lean_inc(v_offset_2023_);
v___x_2031_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_2019_, v_arg_2030_, v_offset_2023_, v_a_2025_, v_a_2026_, v_a_2027_, v_a_2028_);
if (lean_obj_tag(v___x_2031_) == 0)
{
lean_object* v_a_2032_; lean_object* v_a_2033_; lean_object* v_fst_2034_; lean_object* v_snd_2035_; lean_object* v___x_2036_; 
v_a_2032_ = lean_ctor_get(v___x_2031_, 0);
lean_inc(v_a_2032_);
v_a_2033_ = lean_ctor_get(v___x_2031_, 1);
lean_inc(v_a_2033_);
lean_dec_ref_known(v___x_2031_, 2);
v_fst_2034_ = lean_ctor_get(v_a_2032_, 0);
lean_inc_n(v_fst_2034_, 2);
v_snd_2035_ = lean_ctor_get(v_a_2032_, 1);
lean_inc(v_snd_2035_);
lean_dec(v_a_2032_);
v___x_2036_ = lean_array_push(v_argsRev_2022_, v_fst_2034_);
if (v_modified_2024_ == 0)
{
size_t v___x_2037_; size_t v___x_2038_; uint8_t v___x_2039_; 
v___x_2037_ = lean_ptr_addr(v_arg_2030_);
lean_dec_ref(v_arg_2030_);
v___x_2038_ = lean_ptr_addr(v_fst_2034_);
lean_dec(v_fst_2034_);
v___x_2039_ = lean_usize_dec_eq(v___x_2037_, v___x_2038_);
if (v___x_2039_ == 0)
{
uint8_t v___x_2040_; 
v___x_2040_ = 1;
v_f_2021_ = v_fn_2029_;
v_argsRev_2022_ = v___x_2036_;
v_modified_2024_ = v___x_2040_;
v_a_2025_ = v_snd_2035_;
v_a_2028_ = v_a_2033_;
goto _start;
}
else
{
v_f_2021_ = v_fn_2029_;
v_argsRev_2022_ = v___x_2036_;
v_a_2025_ = v_snd_2035_;
v_a_2028_ = v_a_2033_;
goto _start;
}
}
else
{
lean_dec(v_fst_2034_);
lean_dec_ref(v_arg_2030_);
v_f_2021_ = v_fn_2029_;
v_argsRev_2022_ = v___x_2036_;
v_a_2025_ = v_snd_2035_;
v_a_2028_ = v_a_2033_;
goto _start;
}
}
else
{
lean_dec_ref(v_arg_2030_);
lean_dec_ref(v_fn_2029_);
lean_dec(v_offset_2023_);
lean_dec_ref(v_argsRev_2022_);
lean_dec_ref(v_e_2020_);
return v___x_2031_;
}
}
case 0:
{
lean_object* v_deBruijnIndex_2044_; lean_object* v___x_2045_; 
v_deBruijnIndex_2044_ = lean_ctor_get(v_f_2021_, 0);
lean_inc_ref(v_f_2021_);
v___x_2045_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(v_subst_2019_, v_f_2021_, v_deBruijnIndex_2044_, v_offset_2023_, v_a_2025_, v_a_2026_, v_a_2027_, v_a_2028_);
lean_dec(v_offset_2023_);
if (lean_obj_tag(v___x_2045_) == 0)
{
lean_object* v_a_2046_; lean_object* v_a_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2087_; 
v_a_2046_ = lean_ctor_get(v___x_2045_, 0);
v_a_2047_ = lean_ctor_get(v___x_2045_, 1);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2049_ = v___x_2045_;
v_isShared_2050_ = v_isSharedCheck_2087_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_a_2047_);
lean_inc(v_a_2046_);
lean_dec(v___x_2045_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2087_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v_fst_2051_; lean_object* v_snd_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2086_; 
v_fst_2051_ = lean_ctor_get(v_a_2046_, 0);
v_snd_2052_ = lean_ctor_get(v_a_2046_, 1);
v_isSharedCheck_2086_ = !lean_is_exclusive(v_a_2046_);
if (v_isSharedCheck_2086_ == 0)
{
v___x_2054_ = v_a_2046_;
v_isShared_2055_ = v_isSharedCheck_2086_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_snd_2052_);
lean_inc(v_fst_2051_);
lean_dec(v_a_2046_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2086_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
if (v_modified_2024_ == 0)
{
size_t v___x_2079_; size_t v___x_2080_; uint8_t v___x_2081_; 
v___x_2079_ = lean_ptr_addr(v_f_2021_);
lean_dec_ref_known(v_f_2021_, 1);
v___x_2080_ = lean_ptr_addr(v_fst_2051_);
v___x_2081_ = lean_usize_dec_eq(v___x_2079_, v___x_2080_);
if (v___x_2081_ == 0)
{
lean_del_object(v___x_2049_);
lean_dec_ref(v_e_2020_);
goto v___jp_2056_;
}
else
{
lean_object* v___x_2082_; lean_object* v___x_2084_; 
lean_del_object(v___x_2054_);
lean_dec(v_fst_2051_);
lean_dec_ref(v_argsRev_2022_);
v___x_2082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2082_, 0, v_e_2020_);
lean_ctor_set(v___x_2082_, 1, v_snd_2052_);
if (v_isShared_2050_ == 0)
{
lean_ctor_set(v___x_2049_, 0, v___x_2082_);
v___x_2084_ = v___x_2049_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v___x_2082_);
lean_ctor_set(v_reuseFailAlloc_2085_, 1, v_a_2047_);
v___x_2084_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
return v___x_2084_;
}
}
}
else
{
lean_del_object(v___x_2049_);
lean_dec_ref_known(v_f_2021_, 1);
lean_dec_ref(v_e_2020_);
goto v___jp_2056_;
}
v___jp_2056_:
{
lean_object* v___x_2057_; 
v___x_2057_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27(v_fst_2051_, v_argsRev_2022_, v_a_2026_, v_a_2027_, v_a_2047_);
lean_dec_ref(v_argsRev_2022_);
if (lean_obj_tag(v___x_2057_) == 0)
{
lean_object* v_a_2058_; lean_object* v_a_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2069_; 
v_a_2058_ = lean_ctor_get(v___x_2057_, 0);
v_a_2059_ = lean_ctor_get(v___x_2057_, 1);
v_isSharedCheck_2069_ = !lean_is_exclusive(v___x_2057_);
if (v_isSharedCheck_2069_ == 0)
{
v___x_2061_ = v___x_2057_;
v_isShared_2062_ = v_isSharedCheck_2069_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_a_2059_);
lean_inc(v_a_2058_);
lean_dec(v___x_2057_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2069_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2064_; 
if (v_isShared_2055_ == 0)
{
lean_ctor_set(v___x_2054_, 0, v_a_2058_);
v___x_2064_ = v___x_2054_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v_a_2058_);
lean_ctor_set(v_reuseFailAlloc_2068_, 1, v_snd_2052_);
v___x_2064_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
lean_object* v___x_2066_; 
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 0, v___x_2064_);
v___x_2066_ = v___x_2061_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v___x_2064_);
lean_ctor_set(v_reuseFailAlloc_2067_, 1, v_a_2059_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
}
}
else
{
lean_object* v_a_2070_; lean_object* v_a_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2078_; 
lean_del_object(v___x_2054_);
lean_dec(v_snd_2052_);
v_a_2070_ = lean_ctor_get(v___x_2057_, 0);
v_a_2071_ = lean_ctor_get(v___x_2057_, 1);
v_isSharedCheck_2078_ = !lean_is_exclusive(v___x_2057_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2073_ = v___x_2057_;
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_a_2071_);
lean_inc(v_a_2070_);
lean_dec(v___x_2057_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2076_; 
if (v_isShared_2074_ == 0)
{
v___x_2076_ = v___x_2073_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v_a_2070_);
lean_ctor_set(v_reuseFailAlloc_2077_, 1, v_a_2071_);
v___x_2076_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
return v___x_2076_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_f_2021_, 1);
lean_dec_ref(v_argsRev_2022_);
lean_dec_ref(v_e_2020_);
return v___x_2045_;
}
}
default: 
{
lean_object* v___x_2088_; lean_object* v___x_2089_; 
lean_dec(v_offset_2023_);
lean_dec_ref(v_argsRev_2022_);
lean_dec_ref(v_f_2021_);
lean_dec_ref(v_e_2020_);
v___x_2088_ = lean_obj_once(&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__1, &l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__1_once, _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__1);
v___x_2089_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8(v___x_2088_, v_a_2025_, v_a_2026_, v_a_2027_, v_a_2028_);
return v___x_2089_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg(lean_object* v_subst_2090_, lean_object* v_e_2091_, lean_object* v_f_2092_, lean_object* v_arg_2093_, lean_object* v_offset_2094_, lean_object* v_a_2095_, uint8_t v_a_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_){
_start:
{
lean_object* v___x_2099_; 
lean_inc(v_offset_2094_);
lean_inc_ref(v_arg_2093_);
v___x_2099_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_2090_, v_arg_2093_, v_offset_2094_, v_a_2095_, v_a_2096_, v_a_2097_, v_a_2098_);
if (lean_obj_tag(v___x_2099_) == 0)
{
lean_object* v_a_2100_; lean_object* v_a_2101_; lean_object* v_fst_2102_; lean_object* v_snd_2103_; lean_object* v___x_2104_; uint8_t v___x_2105_; 
v_a_2100_ = lean_ctor_get(v___x_2099_, 0);
lean_inc(v_a_2100_);
v_a_2101_ = lean_ctor_get(v___x_2099_, 1);
lean_inc(v_a_2101_);
lean_dec_ref_known(v___x_2099_, 2);
v_fst_2102_ = lean_ctor_get(v_a_2100_, 0);
lean_inc(v_fst_2102_);
v_snd_2103_ = lean_ctor_get(v_a_2100_, 1);
lean_inc(v_snd_2103_);
lean_dec(v_a_2100_);
v___x_2104_ = l_Lean_Expr_getAppFn(v_f_2092_);
v___x_2105_ = l_Lean_Expr_isBVar(v___x_2104_);
lean_dec_ref(v___x_2104_);
if (v___x_2105_ == 0)
{
lean_object* v___x_2106_; 
lean_dec_ref(v_arg_2093_);
v___x_2106_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault(v_subst_2090_, v_f_2092_, v_offset_2094_, v_snd_2103_, v_a_2096_, v_a_2097_, v_a_2101_);
if (lean_obj_tag(v___x_2106_) == 0)
{
lean_object* v_a_2107_; lean_object* v_a_2108_; lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2137_; 
v_a_2107_ = lean_ctor_get(v___x_2106_, 0);
v_a_2108_ = lean_ctor_get(v___x_2106_, 1);
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2106_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2110_ = v___x_2106_;
v_isShared_2111_ = v_isSharedCheck_2137_;
goto v_resetjp_2109_;
}
else
{
lean_inc(v_a_2108_);
lean_inc(v_a_2107_);
lean_dec(v___x_2106_);
v___x_2110_ = lean_box(0);
v_isShared_2111_ = v_isSharedCheck_2137_;
goto v_resetjp_2109_;
}
v_resetjp_2109_:
{
lean_object* v_fst_2112_; lean_object* v_snd_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2136_; 
v_fst_2112_ = lean_ctor_get(v_a_2107_, 0);
v_snd_2113_ = lean_ctor_get(v_a_2107_, 1);
v_isSharedCheck_2136_ = !lean_is_exclusive(v_a_2107_);
if (v_isSharedCheck_2136_ == 0)
{
v___x_2115_ = v_a_2107_;
v_isShared_2116_ = v_isSharedCheck_2136_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_snd_2113_);
lean_inc(v_fst_2112_);
lean_dec(v_a_2107_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2136_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
uint8_t v___y_2118_; 
if (lean_obj_tag(v_e_2091_) == 5)
{
lean_object* v_fn_2126_; lean_object* v_arg_2127_; size_t v___x_2128_; size_t v___x_2129_; uint8_t v___x_2130_; 
v_fn_2126_ = lean_ctor_get(v_e_2091_, 0);
v_arg_2127_ = lean_ctor_get(v_e_2091_, 1);
v___x_2128_ = lean_ptr_addr(v_fn_2126_);
v___x_2129_ = lean_ptr_addr(v_fst_2112_);
v___x_2130_ = lean_usize_dec_eq(v___x_2128_, v___x_2129_);
if (v___x_2130_ == 0)
{
v___y_2118_ = v___x_2130_;
goto v___jp_2117_;
}
else
{
size_t v___x_2131_; size_t v___x_2132_; uint8_t v___x_2133_; 
v___x_2131_ = lean_ptr_addr(v_arg_2127_);
v___x_2132_ = lean_ptr_addr(v_fst_2102_);
v___x_2133_ = lean_usize_dec_eq(v___x_2131_, v___x_2132_);
v___y_2118_ = v___x_2133_;
goto v___jp_2117_;
}
}
else
{
lean_object* v___x_2134_; lean_object* v___x_2135_; 
lean_del_object(v___x_2115_);
lean_dec(v_fst_2112_);
lean_del_object(v___x_2110_);
lean_dec(v_fst_2102_);
lean_dec_ref(v_e_2091_);
v___x_2134_ = lean_obj_once(&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__2, &l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__2_once, _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__2);
v___x_2135_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8(v___x_2134_, v_snd_2113_, v_a_2096_, v_a_2097_, v_a_2108_);
return v___x_2135_;
}
v___jp_2117_:
{
if (v___y_2118_ == 0)
{
lean_object* v___x_2119_; 
lean_del_object(v___x_2115_);
lean_del_object(v___x_2110_);
lean_dec_ref(v_e_2091_);
v___x_2119_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__2(v_fst_2112_, v_fst_2102_, v_snd_2113_, v_a_2096_, v_a_2097_, v_a_2108_);
return v___x_2119_;
}
else
{
lean_object* v___x_2121_; 
lean_dec(v_fst_2112_);
lean_dec(v_fst_2102_);
if (v_isShared_2116_ == 0)
{
lean_ctor_set(v___x_2115_, 0, v_e_2091_);
v___x_2121_ = v___x_2115_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v_e_2091_);
lean_ctor_set(v_reuseFailAlloc_2125_, 1, v_snd_2113_);
v___x_2121_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
lean_object* v___x_2123_; 
if (v_isShared_2111_ == 0)
{
lean_ctor_set(v___x_2110_, 0, v___x_2121_);
v___x_2123_ = v___x_2110_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v___x_2121_);
lean_ctor_set(v_reuseFailAlloc_2124_, 1, v_a_2108_);
v___x_2123_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
return v___x_2123_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_2102_);
lean_dec_ref(v_e_2091_);
return v___x_2106_;
}
}
else
{
lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; size_t v___x_2141_; size_t v___x_2142_; uint8_t v___x_2143_; 
v___x_2138_ = lean_unsigned_to_nat(1u);
v___x_2139_ = lean_mk_empty_array_with_capacity(v___x_2138_);
lean_inc(v_fst_2102_);
v___x_2140_ = lean_array_push(v___x_2139_, v_fst_2102_);
v___x_2141_ = lean_ptr_addr(v_arg_2093_);
lean_dec_ref(v_arg_2093_);
v___x_2142_ = lean_ptr_addr(v_fst_2102_);
lean_dec(v_fst_2102_);
v___x_2143_ = lean_usize_dec_eq(v___x_2141_, v___x_2142_);
if (v___x_2143_ == 0)
{
lean_object* v___x_2144_; 
v___x_2144_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta(v_subst_2090_, v_e_2091_, v_f_2092_, v___x_2140_, v_offset_2094_, v___x_2105_, v_snd_2103_, v_a_2096_, v_a_2097_, v_a_2101_);
return v___x_2144_;
}
else
{
uint8_t v___x_2145_; lean_object* v___x_2146_; 
v___x_2145_ = 0;
v___x_2146_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta(v_subst_2090_, v_e_2091_, v_f_2092_, v___x_2140_, v_offset_2094_, v___x_2145_, v_snd_2103_, v_a_2096_, v_a_2097_, v_a_2101_);
return v___x_2146_;
}
}
}
else
{
lean_dec(v_offset_2094_);
lean_dec_ref(v_arg_2093_);
lean_dec_ref(v_f_2092_);
lean_dec_ref(v_e_2091_);
return v___x_2099_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__1(void){
_start:
{
lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; 
v___x_2148_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__2));
v___x_2149_ = lean_unsigned_to_nat(59u);
v___x_2150_ = lean_unsigned_to_nat(176u);
v___x_2151_ = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__0));
v___x_2152_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__3));
v___x_2153_ = l_mkPanicMessageWithDecl(v___x_2152_, v___x_2151_, v___x_2150_, v___x_2149_, v___x_2148_);
return v___x_2153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit(lean_object* v_subst_2154_, lean_object* v_e_2155_, lean_object* v_offset_2156_, lean_object* v_a_2157_, uint8_t v_a_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_){
_start:
{
switch(lean_obj_tag(v_e_2155_))
{
case 0:
{
lean_object* v_deBruijnIndex_2161_; lean_object* v___x_2162_; 
v_deBruijnIndex_2161_ = lean_ctor_get(v_e_2155_, 0);
lean_inc(v_deBruijnIndex_2161_);
v___x_2162_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(v_subst_2154_, v_e_2155_, v_deBruijnIndex_2161_, v_offset_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_);
lean_dec(v_offset_2156_);
lean_dec(v_deBruijnIndex_2161_);
return v___x_2162_;
}
case 5:
{
lean_object* v_fn_2163_; lean_object* v_arg_2164_; lean_object* v___x_2165_; 
v_fn_2163_ = lean_ctor_get(v_e_2155_, 0);
lean_inc_ref(v_fn_2163_);
v_arg_2164_ = lean_ctor_get(v_e_2155_, 1);
lean_inc_ref(v_arg_2164_);
v___x_2165_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg(v_subst_2154_, v_e_2155_, v_fn_2163_, v_arg_2164_, v_offset_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_);
return v___x_2165_;
}
case 6:
{
lean_object* v_binderName_2166_; lean_object* v_binderType_2167_; lean_object* v_body_2168_; uint8_t v_binderInfo_2169_; lean_object* v___x_2170_; 
v_binderName_2166_ = lean_ctor_get(v_e_2155_, 0);
v_binderType_2167_ = lean_ctor_get(v_e_2155_, 1);
v_body_2168_ = lean_ctor_get(v_e_2155_, 2);
v_binderInfo_2169_ = lean_ctor_get_uint8(v_e_2155_, sizeof(void*)*3 + 8);
lean_inc(v_offset_2156_);
lean_inc_ref(v_binderType_2167_);
v___x_2170_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_2154_, v_binderType_2167_, v_offset_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_);
if (lean_obj_tag(v___x_2170_) == 0)
{
lean_object* v_a_2171_; lean_object* v_a_2172_; lean_object* v_fst_2173_; lean_object* v_snd_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; 
v_a_2171_ = lean_ctor_get(v___x_2170_, 0);
lean_inc(v_a_2171_);
v_a_2172_ = lean_ctor_get(v___x_2170_, 1);
lean_inc(v_a_2172_);
lean_dec_ref_known(v___x_2170_, 2);
v_fst_2173_ = lean_ctor_get(v_a_2171_, 0);
lean_inc(v_fst_2173_);
v_snd_2174_ = lean_ctor_get(v_a_2171_, 1);
lean_inc(v_snd_2174_);
lean_dec(v_a_2171_);
v___x_2175_ = lean_unsigned_to_nat(1u);
v___x_2176_ = lean_nat_add(v_offset_2156_, v___x_2175_);
lean_dec(v_offset_2156_);
lean_inc_ref(v_body_2168_);
v___x_2177_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_2154_, v_body_2168_, v___x_2176_, v_snd_2174_, v_a_2158_, v_a_2159_, v_a_2172_);
if (lean_obj_tag(v___x_2177_) == 0)
{
lean_object* v_a_2178_; lean_object* v_a_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2204_; 
v_a_2178_ = lean_ctor_get(v___x_2177_, 0);
v_a_2179_ = lean_ctor_get(v___x_2177_, 1);
v_isSharedCheck_2204_ = !lean_is_exclusive(v___x_2177_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2181_ = v___x_2177_;
v_isShared_2182_ = v_isSharedCheck_2204_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_a_2179_);
lean_inc(v_a_2178_);
lean_dec(v___x_2177_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2204_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v_fst_2183_; lean_object* v_snd_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2203_; 
v_fst_2183_ = lean_ctor_get(v_a_2178_, 0);
v_snd_2184_ = lean_ctor_get(v_a_2178_, 1);
v_isSharedCheck_2203_ = !lean_is_exclusive(v_a_2178_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_2186_ = v_a_2178_;
v_isShared_2187_ = v_isSharedCheck_2203_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_snd_2184_);
lean_inc(v_fst_2183_);
lean_dec(v_a_2178_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2203_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
uint8_t v___y_2189_; size_t v___x_2197_; size_t v___x_2198_; uint8_t v___x_2199_; 
v___x_2197_ = lean_ptr_addr(v_binderType_2167_);
v___x_2198_ = lean_ptr_addr(v_fst_2173_);
v___x_2199_ = lean_usize_dec_eq(v___x_2197_, v___x_2198_);
if (v___x_2199_ == 0)
{
v___y_2189_ = v___x_2199_;
goto v___jp_2188_;
}
else
{
size_t v___x_2200_; size_t v___x_2201_; uint8_t v___x_2202_; 
v___x_2200_ = lean_ptr_addr(v_body_2168_);
v___x_2201_ = lean_ptr_addr(v_fst_2183_);
v___x_2202_ = lean_usize_dec_eq(v___x_2200_, v___x_2201_);
v___y_2189_ = v___x_2202_;
goto v___jp_2188_;
}
v___jp_2188_:
{
if (v___y_2189_ == 0)
{
lean_object* v___x_2190_; 
lean_inc(v_binderName_2166_);
lean_del_object(v___x_2186_);
lean_del_object(v___x_2181_);
lean_dec_ref_known(v_e_2155_, 3);
v___x_2190_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__3(v_binderName_2166_, v_binderInfo_2169_, v_fst_2173_, v_fst_2183_, v_snd_2184_, v_a_2158_, v_a_2159_, v_a_2179_);
return v___x_2190_;
}
else
{
lean_object* v___x_2192_; 
lean_dec(v_fst_2183_);
lean_dec(v_fst_2173_);
if (v_isShared_2187_ == 0)
{
lean_ctor_set(v___x_2186_, 0, v_e_2155_);
v___x_2192_ = v___x_2186_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_e_2155_);
lean_ctor_set(v_reuseFailAlloc_2196_, 1, v_snd_2184_);
v___x_2192_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
lean_object* v___x_2194_; 
if (v_isShared_2182_ == 0)
{
lean_ctor_set(v___x_2181_, 0, v___x_2192_);
v___x_2194_ = v___x_2181_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v___x_2192_);
lean_ctor_set(v_reuseFailAlloc_2195_, 1, v_a_2179_);
v___x_2194_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
return v___x_2194_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_2173_);
lean_dec_ref_known(v_e_2155_, 3);
return v___x_2177_;
}
}
else
{
lean_dec_ref_known(v_e_2155_, 3);
lean_dec(v_offset_2156_);
return v___x_2170_;
}
}
case 7:
{
lean_object* v_binderName_2205_; lean_object* v_binderType_2206_; lean_object* v_body_2207_; uint8_t v_binderInfo_2208_; lean_object* v___x_2209_; 
v_binderName_2205_ = lean_ctor_get(v_e_2155_, 0);
v_binderType_2206_ = lean_ctor_get(v_e_2155_, 1);
v_body_2207_ = lean_ctor_get(v_e_2155_, 2);
v_binderInfo_2208_ = lean_ctor_get_uint8(v_e_2155_, sizeof(void*)*3 + 8);
lean_inc(v_offset_2156_);
lean_inc_ref(v_binderType_2206_);
v___x_2209_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_2154_, v_binderType_2206_, v_offset_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_);
if (lean_obj_tag(v___x_2209_) == 0)
{
lean_object* v_a_2210_; lean_object* v_a_2211_; lean_object* v_fst_2212_; lean_object* v_snd_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; 
v_a_2210_ = lean_ctor_get(v___x_2209_, 0);
lean_inc(v_a_2210_);
v_a_2211_ = lean_ctor_get(v___x_2209_, 1);
lean_inc(v_a_2211_);
lean_dec_ref_known(v___x_2209_, 2);
v_fst_2212_ = lean_ctor_get(v_a_2210_, 0);
lean_inc(v_fst_2212_);
v_snd_2213_ = lean_ctor_get(v_a_2210_, 1);
lean_inc(v_snd_2213_);
lean_dec(v_a_2210_);
v___x_2214_ = lean_unsigned_to_nat(1u);
v___x_2215_ = lean_nat_add(v_offset_2156_, v___x_2214_);
lean_dec(v_offset_2156_);
lean_inc_ref(v_body_2207_);
v___x_2216_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_2154_, v_body_2207_, v___x_2215_, v_snd_2213_, v_a_2158_, v_a_2159_, v_a_2211_);
if (lean_obj_tag(v___x_2216_) == 0)
{
lean_object* v_a_2217_; lean_object* v_a_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2243_; 
v_a_2217_ = lean_ctor_get(v___x_2216_, 0);
v_a_2218_ = lean_ctor_get(v___x_2216_, 1);
v_isSharedCheck_2243_ = !lean_is_exclusive(v___x_2216_);
if (v_isSharedCheck_2243_ == 0)
{
v___x_2220_ = v___x_2216_;
v_isShared_2221_ = v_isSharedCheck_2243_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_a_2218_);
lean_inc(v_a_2217_);
lean_dec(v___x_2216_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2243_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v_fst_2222_; lean_object* v_snd_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2242_; 
v_fst_2222_ = lean_ctor_get(v_a_2217_, 0);
v_snd_2223_ = lean_ctor_get(v_a_2217_, 1);
v_isSharedCheck_2242_ = !lean_is_exclusive(v_a_2217_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2225_ = v_a_2217_;
v_isShared_2226_ = v_isSharedCheck_2242_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_snd_2223_);
lean_inc(v_fst_2222_);
lean_dec(v_a_2217_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2242_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
uint8_t v___y_2228_; size_t v___x_2236_; size_t v___x_2237_; uint8_t v___x_2238_; 
v___x_2236_ = lean_ptr_addr(v_binderType_2206_);
v___x_2237_ = lean_ptr_addr(v_fst_2212_);
v___x_2238_ = lean_usize_dec_eq(v___x_2236_, v___x_2237_);
if (v___x_2238_ == 0)
{
v___y_2228_ = v___x_2238_;
goto v___jp_2227_;
}
else
{
size_t v___x_2239_; size_t v___x_2240_; uint8_t v___x_2241_; 
v___x_2239_ = lean_ptr_addr(v_body_2207_);
v___x_2240_ = lean_ptr_addr(v_fst_2222_);
v___x_2241_ = lean_usize_dec_eq(v___x_2239_, v___x_2240_);
v___y_2228_ = v___x_2241_;
goto v___jp_2227_;
}
v___jp_2227_:
{
if (v___y_2228_ == 0)
{
lean_object* v___x_2229_; 
lean_inc(v_binderName_2205_);
lean_del_object(v___x_2225_);
lean_del_object(v___x_2220_);
lean_dec_ref_known(v_e_2155_, 3);
v___x_2229_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__4(v_binderName_2205_, v_binderInfo_2208_, v_fst_2212_, v_fst_2222_, v_snd_2223_, v_a_2158_, v_a_2159_, v_a_2218_);
return v___x_2229_;
}
else
{
lean_object* v___x_2231_; 
lean_dec(v_fst_2222_);
lean_dec(v_fst_2212_);
if (v_isShared_2226_ == 0)
{
lean_ctor_set(v___x_2225_, 0, v_e_2155_);
v___x_2231_ = v___x_2225_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v_e_2155_);
lean_ctor_set(v_reuseFailAlloc_2235_, 1, v_snd_2223_);
v___x_2231_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
lean_object* v___x_2233_; 
if (v_isShared_2221_ == 0)
{
lean_ctor_set(v___x_2220_, 0, v___x_2231_);
v___x_2233_ = v___x_2220_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v___x_2231_);
lean_ctor_set(v_reuseFailAlloc_2234_, 1, v_a_2218_);
v___x_2233_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
return v___x_2233_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_2212_);
lean_dec_ref_known(v_e_2155_, 3);
return v___x_2216_;
}
}
else
{
lean_dec_ref_known(v_e_2155_, 3);
lean_dec(v_offset_2156_);
return v___x_2209_;
}
}
case 8:
{
lean_object* v_declName_2244_; lean_object* v_type_2245_; lean_object* v_value_2246_; lean_object* v_body_2247_; uint8_t v_nondep_2248_; lean_object* v___x_2249_; 
v_declName_2244_ = lean_ctor_get(v_e_2155_, 0);
v_type_2245_ = lean_ctor_get(v_e_2155_, 1);
v_value_2246_ = lean_ctor_get(v_e_2155_, 2);
v_body_2247_ = lean_ctor_get(v_e_2155_, 3);
v_nondep_2248_ = lean_ctor_get_uint8(v_e_2155_, sizeof(void*)*4 + 8);
lean_inc(v_offset_2156_);
lean_inc_ref(v_type_2245_);
v___x_2249_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_2154_, v_type_2245_, v_offset_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_);
if (lean_obj_tag(v___x_2249_) == 0)
{
lean_object* v_a_2250_; lean_object* v_a_2251_; lean_object* v_fst_2252_; lean_object* v_snd_2253_; lean_object* v___x_2254_; 
v_a_2250_ = lean_ctor_get(v___x_2249_, 0);
lean_inc(v_a_2250_);
v_a_2251_ = lean_ctor_get(v___x_2249_, 1);
lean_inc(v_a_2251_);
lean_dec_ref_known(v___x_2249_, 2);
v_fst_2252_ = lean_ctor_get(v_a_2250_, 0);
lean_inc(v_fst_2252_);
v_snd_2253_ = lean_ctor_get(v_a_2250_, 1);
lean_inc(v_snd_2253_);
lean_dec(v_a_2250_);
lean_inc(v_offset_2156_);
lean_inc_ref(v_value_2246_);
v___x_2254_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_2154_, v_value_2246_, v_offset_2156_, v_snd_2253_, v_a_2158_, v_a_2159_, v_a_2251_);
if (lean_obj_tag(v___x_2254_) == 0)
{
lean_object* v_a_2255_; lean_object* v_a_2256_; lean_object* v_fst_2257_; lean_object* v_snd_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; 
v_a_2255_ = lean_ctor_get(v___x_2254_, 0);
lean_inc(v_a_2255_);
v_a_2256_ = lean_ctor_get(v___x_2254_, 1);
lean_inc(v_a_2256_);
lean_dec_ref_known(v___x_2254_, 2);
v_fst_2257_ = lean_ctor_get(v_a_2255_, 0);
lean_inc(v_fst_2257_);
v_snd_2258_ = lean_ctor_get(v_a_2255_, 1);
lean_inc(v_snd_2258_);
lean_dec(v_a_2255_);
v___x_2259_ = lean_unsigned_to_nat(1u);
v___x_2260_ = lean_nat_add(v_offset_2156_, v___x_2259_);
lean_dec(v_offset_2156_);
lean_inc_ref(v_body_2247_);
v___x_2261_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_2154_, v_body_2247_, v___x_2260_, v_snd_2258_, v_a_2158_, v_a_2159_, v_a_2256_);
if (lean_obj_tag(v___x_2261_) == 0)
{
lean_object* v_a_2262_; lean_object* v_a_2263_; lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2292_; 
v_a_2262_ = lean_ctor_get(v___x_2261_, 0);
v_a_2263_ = lean_ctor_get(v___x_2261_, 1);
v_isSharedCheck_2292_ = !lean_is_exclusive(v___x_2261_);
if (v_isSharedCheck_2292_ == 0)
{
v___x_2265_ = v___x_2261_;
v_isShared_2266_ = v_isSharedCheck_2292_;
goto v_resetjp_2264_;
}
else
{
lean_inc(v_a_2263_);
lean_inc(v_a_2262_);
lean_dec(v___x_2261_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2292_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
lean_object* v_fst_2267_; lean_object* v_snd_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2291_; 
v_fst_2267_ = lean_ctor_get(v_a_2262_, 0);
v_snd_2268_ = lean_ctor_get(v_a_2262_, 1);
v_isSharedCheck_2291_ = !lean_is_exclusive(v_a_2262_);
if (v_isSharedCheck_2291_ == 0)
{
v___x_2270_ = v_a_2262_;
v_isShared_2271_ = v_isSharedCheck_2291_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_snd_2268_);
lean_inc(v_fst_2267_);
lean_dec(v_a_2262_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2291_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
uint8_t v___y_2273_; size_t v___x_2285_; size_t v___x_2286_; uint8_t v___x_2287_; 
v___x_2285_ = lean_ptr_addr(v_type_2245_);
v___x_2286_ = lean_ptr_addr(v_fst_2252_);
v___x_2287_ = lean_usize_dec_eq(v___x_2285_, v___x_2286_);
if (v___x_2287_ == 0)
{
v___y_2273_ = v___x_2287_;
goto v___jp_2272_;
}
else
{
size_t v___x_2288_; size_t v___x_2289_; uint8_t v___x_2290_; 
v___x_2288_ = lean_ptr_addr(v_value_2246_);
v___x_2289_ = lean_ptr_addr(v_fst_2257_);
v___x_2290_ = lean_usize_dec_eq(v___x_2288_, v___x_2289_);
v___y_2273_ = v___x_2290_;
goto v___jp_2272_;
}
v___jp_2272_:
{
if (v___y_2273_ == 0)
{
lean_object* v___x_2274_; 
lean_inc(v_declName_2244_);
lean_del_object(v___x_2270_);
lean_del_object(v___x_2265_);
lean_dec_ref_known(v_e_2155_, 4);
v___x_2274_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__5(v_declName_2244_, v_fst_2252_, v_fst_2257_, v_fst_2267_, v_nondep_2248_, v_snd_2268_, v_a_2158_, v_a_2159_, v_a_2263_);
return v___x_2274_;
}
else
{
size_t v___x_2275_; size_t v___x_2276_; uint8_t v___x_2277_; 
v___x_2275_ = lean_ptr_addr(v_body_2247_);
v___x_2276_ = lean_ptr_addr(v_fst_2267_);
v___x_2277_ = lean_usize_dec_eq(v___x_2275_, v___x_2276_);
if (v___x_2277_ == 0)
{
lean_object* v___x_2278_; 
lean_inc(v_declName_2244_);
lean_del_object(v___x_2270_);
lean_del_object(v___x_2265_);
lean_dec_ref_known(v_e_2155_, 4);
v___x_2278_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__5(v_declName_2244_, v_fst_2252_, v_fst_2257_, v_fst_2267_, v_nondep_2248_, v_snd_2268_, v_a_2158_, v_a_2159_, v_a_2263_);
return v___x_2278_;
}
else
{
lean_object* v___x_2280_; 
lean_dec(v_fst_2267_);
lean_dec(v_fst_2257_);
lean_dec(v_fst_2252_);
if (v_isShared_2271_ == 0)
{
lean_ctor_set(v___x_2270_, 0, v_e_2155_);
v___x_2280_ = v___x_2270_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_e_2155_);
lean_ctor_set(v_reuseFailAlloc_2284_, 1, v_snd_2268_);
v___x_2280_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
lean_object* v___x_2282_; 
if (v_isShared_2266_ == 0)
{
lean_ctor_set(v___x_2265_, 0, v___x_2280_);
v___x_2282_ = v___x_2265_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v___x_2280_);
lean_ctor_set(v_reuseFailAlloc_2283_, 1, v_a_2263_);
v___x_2282_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
return v___x_2282_;
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
lean_dec(v_fst_2257_);
lean_dec(v_fst_2252_);
lean_dec_ref_known(v_e_2155_, 4);
return v___x_2261_;
}
}
else
{
lean_dec(v_fst_2252_);
lean_dec_ref_known(v_e_2155_, 4);
lean_dec(v_offset_2156_);
return v___x_2254_;
}
}
else
{
lean_dec_ref_known(v_e_2155_, 4);
lean_dec(v_offset_2156_);
return v___x_2249_;
}
}
case 10:
{
lean_object* v_data_2293_; lean_object* v_expr_2294_; lean_object* v___x_2295_; 
v_data_2293_ = lean_ctor_get(v_e_2155_, 0);
v_expr_2294_ = lean_ctor_get(v_e_2155_, 1);
lean_inc_ref(v_expr_2294_);
v___x_2295_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_2154_, v_expr_2294_, v_offset_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_);
if (lean_obj_tag(v___x_2295_) == 0)
{
lean_object* v_a_2296_; lean_object* v_a_2297_; lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2317_; 
v_a_2296_ = lean_ctor_get(v___x_2295_, 0);
v_a_2297_ = lean_ctor_get(v___x_2295_, 1);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___x_2295_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2299_ = v___x_2295_;
v_isShared_2300_ = v_isSharedCheck_2317_;
goto v_resetjp_2298_;
}
else
{
lean_inc(v_a_2297_);
lean_inc(v_a_2296_);
lean_dec(v___x_2295_);
v___x_2299_ = lean_box(0);
v_isShared_2300_ = v_isSharedCheck_2317_;
goto v_resetjp_2298_;
}
v_resetjp_2298_:
{
lean_object* v_fst_2301_; lean_object* v_snd_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2316_; 
v_fst_2301_ = lean_ctor_get(v_a_2296_, 0);
v_snd_2302_ = lean_ctor_get(v_a_2296_, 1);
v_isSharedCheck_2316_ = !lean_is_exclusive(v_a_2296_);
if (v_isSharedCheck_2316_ == 0)
{
v___x_2304_ = v_a_2296_;
v_isShared_2305_ = v_isSharedCheck_2316_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_snd_2302_);
lean_inc(v_fst_2301_);
lean_dec(v_a_2296_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2316_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
size_t v___x_2306_; size_t v___x_2307_; uint8_t v___x_2308_; 
v___x_2306_ = lean_ptr_addr(v_expr_2294_);
v___x_2307_ = lean_ptr_addr(v_fst_2301_);
v___x_2308_ = lean_usize_dec_eq(v___x_2306_, v___x_2307_);
if (v___x_2308_ == 0)
{
lean_object* v___x_2309_; 
lean_inc(v_data_2293_);
lean_del_object(v___x_2304_);
lean_del_object(v___x_2299_);
lean_dec_ref_known(v_e_2155_, 2);
v___x_2309_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__6(v_data_2293_, v_fst_2301_, v_snd_2302_, v_a_2158_, v_a_2159_, v_a_2297_);
return v___x_2309_;
}
else
{
lean_object* v___x_2311_; 
lean_dec(v_fst_2301_);
if (v_isShared_2305_ == 0)
{
lean_ctor_set(v___x_2304_, 0, v_e_2155_);
v___x_2311_ = v___x_2304_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v_e_2155_);
lean_ctor_set(v_reuseFailAlloc_2315_, 1, v_snd_2302_);
v___x_2311_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
lean_object* v___x_2313_; 
if (v_isShared_2300_ == 0)
{
lean_ctor_set(v___x_2299_, 0, v___x_2311_);
v___x_2313_ = v___x_2299_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v___x_2311_);
lean_ctor_set(v_reuseFailAlloc_2314_, 1, v_a_2297_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
return v___x_2313_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2155_, 2);
return v___x_2295_;
}
}
case 11:
{
lean_object* v_typeName_2318_; lean_object* v_idx_2319_; lean_object* v_struct_2320_; lean_object* v___x_2321_; 
v_typeName_2318_ = lean_ctor_get(v_e_2155_, 0);
v_idx_2319_ = lean_ctor_get(v_e_2155_, 1);
v_struct_2320_ = lean_ctor_get(v_e_2155_, 2);
lean_inc_ref(v_struct_2320_);
v___x_2321_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_2154_, v_struct_2320_, v_offset_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_);
if (lean_obj_tag(v___x_2321_) == 0)
{
lean_object* v_a_2322_; lean_object* v_a_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2343_; 
v_a_2322_ = lean_ctor_get(v___x_2321_, 0);
v_a_2323_ = lean_ctor_get(v___x_2321_, 1);
v_isSharedCheck_2343_ = !lean_is_exclusive(v___x_2321_);
if (v_isSharedCheck_2343_ == 0)
{
v___x_2325_ = v___x_2321_;
v_isShared_2326_ = v_isSharedCheck_2343_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_a_2323_);
lean_inc(v_a_2322_);
lean_dec(v___x_2321_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2343_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v_fst_2327_; lean_object* v_snd_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2342_; 
v_fst_2327_ = lean_ctor_get(v_a_2322_, 0);
v_snd_2328_ = lean_ctor_get(v_a_2322_, 1);
v_isSharedCheck_2342_ = !lean_is_exclusive(v_a_2322_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2330_ = v_a_2322_;
v_isShared_2331_ = v_isSharedCheck_2342_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_snd_2328_);
lean_inc(v_fst_2327_);
lean_dec(v_a_2322_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2342_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
size_t v___x_2332_; size_t v___x_2333_; uint8_t v___x_2334_; 
v___x_2332_ = lean_ptr_addr(v_struct_2320_);
v___x_2333_ = lean_ptr_addr(v_fst_2327_);
v___x_2334_ = lean_usize_dec_eq(v___x_2332_, v___x_2333_);
if (v___x_2334_ == 0)
{
lean_object* v___x_2335_; 
lean_inc(v_idx_2319_);
lean_inc(v_typeName_2318_);
lean_del_object(v___x_2330_);
lean_del_object(v___x_2325_);
lean_dec_ref_known(v_e_2155_, 3);
v___x_2335_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__7(v_typeName_2318_, v_idx_2319_, v_fst_2327_, v_snd_2328_, v_a_2158_, v_a_2159_, v_a_2323_);
return v___x_2335_;
}
else
{
lean_object* v___x_2337_; 
lean_dec(v_fst_2327_);
if (v_isShared_2331_ == 0)
{
lean_ctor_set(v___x_2330_, 0, v_e_2155_);
v___x_2337_ = v___x_2330_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v_e_2155_);
lean_ctor_set(v_reuseFailAlloc_2341_, 1, v_snd_2328_);
v___x_2337_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
lean_object* v___x_2339_; 
if (v_isShared_2326_ == 0)
{
lean_ctor_set(v___x_2325_, 0, v___x_2337_);
v___x_2339_ = v___x_2325_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v___x_2337_);
lean_ctor_set(v_reuseFailAlloc_2340_, 1, v_a_2323_);
v___x_2339_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
return v___x_2339_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2155_, 3);
return v___x_2321_;
}
}
default: 
{
lean_object* v___x_2344_; lean_object* v___x_2345_; 
lean_dec(v_offset_2156_);
lean_dec_ref(v_e_2155_);
v___x_2344_ = lean_obj_once(&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__1, &l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__1_once, _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__1);
v___x_2345_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8(v___x_2344_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_);
return v___x_2345_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(lean_object* v_subst_2346_, lean_object* v_e_2347_, lean_object* v_offset_2348_, lean_object* v_a_2349_, uint8_t v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_){
_start:
{
lean_object* v___x_2353_; uint8_t v___x_2354_; 
v___x_2353_ = l_Lean_Expr_looseBVarRange(v_e_2347_);
v___x_2354_ = lean_nat_dec_le(v___x_2353_, v_offset_2348_);
lean_dec(v___x_2353_);
if (v___x_2354_ == 0)
{
lean_object* v_key_2355_; lean_object* v___x_2356_; 
lean_inc(v_offset_2348_);
lean_inc_ref(v_e_2347_);
v_key_2355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_2355_, 0, v_e_2347_);
lean_ctor_set(v_key_2355_, 1, v_offset_2348_);
v___x_2356_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3___redArg(v_a_2349_, v_key_2355_);
if (lean_obj_tag(v___x_2356_) == 1)
{
lean_object* v_val_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; 
lean_dec_ref_known(v_key_2355_, 2);
lean_dec(v_offset_2348_);
lean_dec_ref(v_e_2347_);
v_val_2357_ = lean_ctor_get(v___x_2356_, 0);
lean_inc(v_val_2357_);
lean_dec_ref_known(v___x_2356_, 1);
v___x_2358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2358_, 0, v_val_2357_);
lean_ctor_set(v___x_2358_, 1, v_a_2349_);
v___x_2359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2358_);
lean_ctor_set(v___x_2359_, 1, v_a_2352_);
return v___x_2359_;
}
else
{
lean_dec(v___x_2356_);
switch(lean_obj_tag(v_e_2347_))
{
case 0:
{
lean_object* v_deBruijnIndex_2360_; lean_object* v___x_2361_; 
v_deBruijnIndex_2360_ = lean_ctor_get(v_e_2347_, 0);
lean_inc(v_deBruijnIndex_2360_);
v___x_2361_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(v_subst_2346_, v_e_2347_, v_deBruijnIndex_2360_, v_offset_2348_, v_a_2349_, v_a_2350_, v_a_2351_, v_a_2352_);
lean_dec(v_offset_2348_);
lean_dec(v_deBruijnIndex_2360_);
if (lean_obj_tag(v___x_2361_) == 0)
{
lean_object* v_a_2362_; lean_object* v_a_2363_; lean_object* v_fst_2364_; lean_object* v_snd_2365_; lean_object* v___x_2366_; 
v_a_2362_ = lean_ctor_get(v___x_2361_, 0);
lean_inc(v_a_2362_);
v_a_2363_ = lean_ctor_get(v___x_2361_, 1);
lean_inc(v_a_2363_);
lean_dec_ref_known(v___x_2361_, 2);
v_fst_2364_ = lean_ctor_get(v_a_2362_, 0);
lean_inc(v_fst_2364_);
v_snd_2365_ = lean_ctor_get(v_a_2362_, 1);
lean_inc(v_snd_2365_);
lean_dec(v_a_2362_);
v___x_2366_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_2355_, v_fst_2364_, v_snd_2365_, v_a_2363_);
return v___x_2366_;
}
else
{
lean_dec_ref_known(v_key_2355_, 2);
return v___x_2361_;
}
}
case 9:
{
lean_object* v___x_2367_; 
lean_dec(v_offset_2348_);
v___x_2367_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_2355_, v_e_2347_, v_a_2349_, v_a_2352_);
return v___x_2367_;
}
case 2:
{
lean_object* v___x_2368_; 
lean_dec(v_offset_2348_);
v___x_2368_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_2355_, v_e_2347_, v_a_2349_, v_a_2352_);
return v___x_2368_;
}
case 1:
{
lean_object* v___x_2369_; 
lean_dec(v_offset_2348_);
v___x_2369_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_2355_, v_e_2347_, v_a_2349_, v_a_2352_);
return v___x_2369_;
}
case 4:
{
lean_object* v___x_2370_; 
lean_dec(v_offset_2348_);
v___x_2370_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_2355_, v_e_2347_, v_a_2349_, v_a_2352_);
return v___x_2370_;
}
case 3:
{
lean_object* v___x_2371_; 
lean_dec(v_offset_2348_);
v___x_2371_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_2355_, v_e_2347_, v_a_2349_, v_a_2352_);
return v___x_2371_;
}
default: 
{
lean_object* v___x_2372_; 
v___x_2372_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit(v_subst_2346_, v_e_2347_, v_offset_2348_, v_a_2349_, v_a_2350_, v_a_2351_, v_a_2352_);
if (lean_obj_tag(v___x_2372_) == 0)
{
lean_object* v_a_2373_; lean_object* v_a_2374_; lean_object* v_fst_2375_; lean_object* v_snd_2376_; lean_object* v___x_2377_; 
v_a_2373_ = lean_ctor_get(v___x_2372_, 0);
lean_inc(v_a_2373_);
v_a_2374_ = lean_ctor_get(v___x_2372_, 1);
lean_inc(v_a_2374_);
lean_dec_ref_known(v___x_2372_, 2);
v_fst_2375_ = lean_ctor_get(v_a_2373_, 0);
lean_inc(v_fst_2375_);
v_snd_2376_ = lean_ctor_get(v_a_2373_, 1);
lean_inc(v_snd_2376_);
lean_dec(v_a_2373_);
v___x_2377_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_2355_, v_fst_2375_, v_snd_2376_, v_a_2374_);
return v___x_2377_;
}
else
{
lean_dec_ref_known(v_key_2355_, 2);
return v___x_2372_;
}
}
}
}
}
else
{
lean_object* v___x_2378_; lean_object* v___x_2379_; 
lean_dec(v_offset_2348_);
v___x_2378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2378_, 0, v_e_2347_);
lean_ctor_set(v___x_2378_, 1, v_a_2349_);
v___x_2379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2379_, 0, v___x_2378_);
lean_ctor_set(v___x_2379_, 1, v_a_2352_);
return v___x_2379_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild___boxed(lean_object* v_subst_2380_, lean_object* v_e_2381_, lean_object* v_offset_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_){
_start:
{
uint8_t v_a_boxed_2387_; lean_object* v_res_2388_; 
v_a_boxed_2387_ = lean_unbox(v_a_2384_);
v_res_2388_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_2380_, v_e_2381_, v_offset_2382_, v_a_2383_, v_a_boxed_2387_, v_a_2385_, v_a_2386_);
lean_dec_ref(v_a_2385_);
lean_dec_ref(v_subst_2380_);
return v_res_2388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault___boxed(lean_object* v_subst_2389_, lean_object* v_e_2390_, lean_object* v_offset_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_){
_start:
{
uint8_t v_a_boxed_2396_; lean_object* v_res_2397_; 
v_a_boxed_2396_ = lean_unbox(v_a_2393_);
v_res_2397_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault(v_subst_2389_, v_e_2390_, v_offset_2391_, v_a_2392_, v_a_boxed_2396_, v_a_2394_, v_a_2395_);
lean_dec_ref(v_a_2394_);
lean_dec_ref(v_subst_2389_);
return v_res_2397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___boxed(lean_object* v_subst_2398_, lean_object* v_e_2399_, lean_object* v_f_2400_, lean_object* v_arg_2401_, lean_object* v_offset_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_){
_start:
{
uint8_t v_a_boxed_2407_; lean_object* v_res_2408_; 
v_a_boxed_2407_ = lean_unbox(v_a_2404_);
v_res_2408_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg(v_subst_2398_, v_e_2399_, v_f_2400_, v_arg_2401_, v_offset_2402_, v_a_2403_, v_a_boxed_2407_, v_a_2405_, v_a_2406_);
lean_dec_ref(v_a_2405_);
lean_dec_ref(v_subst_2398_);
return v_res_2408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___boxed(lean_object* v_subst_2409_, lean_object* v_e_2410_, lean_object* v_f_2411_, lean_object* v_argsRev_2412_, lean_object* v_offset_2413_, lean_object* v_modified_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_){
_start:
{
uint8_t v_modified_boxed_2419_; uint8_t v_a_boxed_2420_; lean_object* v_res_2421_; 
v_modified_boxed_2419_ = lean_unbox(v_modified_2414_);
v_a_boxed_2420_ = lean_unbox(v_a_2416_);
v_res_2421_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta(v_subst_2409_, v_e_2410_, v_f_2411_, v_argsRev_2412_, v_offset_2413_, v_modified_boxed_2419_, v_a_2415_, v_a_boxed_2420_, v_a_2417_, v_a_2418_);
lean_dec_ref(v_a_2417_);
lean_dec_ref(v_subst_2409_);
return v_res_2421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___boxed(lean_object* v_subst_2422_, lean_object* v_e_2423_, lean_object* v_offset_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_){
_start:
{
uint8_t v_a_boxed_2429_; lean_object* v_res_2430_; 
v_a_boxed_2429_ = lean_unbox(v_a_2426_);
v_res_2430_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit(v_subst_2422_, v_e_2423_, v_offset_2424_, v_a_2425_, v_a_boxed_2429_, v_a_2427_, v_a_2428_);
lean_dec_ref(v_a_2427_);
lean_dec_ref(v_subst_2422_);
return v_res_2430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp(lean_object* v_subst_2431_, lean_object* v_e_2432_, lean_object* v_f_2433_, lean_object* v_arg_2434_, lean_object* v_offset_2435_, lean_object* v_x_2436_, lean_object* v_a_2437_, uint8_t v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_){
_start:
{
lean_object* v___x_2441_; 
v___x_2441_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg(v_subst_2431_, v_e_2432_, v_f_2433_, v_arg_2434_, v_offset_2435_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_);
return v___x_2441_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___boxed(lean_object* v_subst_2442_, lean_object* v_e_2443_, lean_object* v_f_2444_, lean_object* v_arg_2445_, lean_object* v_offset_2446_, lean_object* v_x_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_){
_start:
{
uint8_t v_a_boxed_2452_; lean_object* v_res_2453_; 
v_a_boxed_2452_ = lean_unbox(v_a_2449_);
v_res_2453_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp(v_subst_2442_, v_e_2443_, v_f_2444_, v_arg_2445_, v_offset_2446_, v_x_2447_, v_a_2448_, v_a_boxed_2452_, v_a_2450_, v_a_2451_);
lean_dec_ref(v_a_2450_);
lean_dec_ref(v_subst_2442_);
return v_res_2453_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27(lean_object* v_e_2454_, lean_object* v_subst_2455_, uint8_t v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_){
_start:
{
uint8_t v___y_2460_; lean_object* v___x_2484_; lean_object* v___x_2485_; uint8_t v___x_2486_; 
v___x_2484_ = lean_array_get_size(v_subst_2455_);
v___x_2485_ = lean_unsigned_to_nat(0u);
v___x_2486_ = lean_nat_dec_eq(v___x_2484_, v___x_2485_);
if (v___x_2486_ == 0)
{
uint8_t v___x_2487_; 
v___x_2487_ = l_Lean_Expr_hasLooseBVars(v_e_2454_);
if (v___x_2487_ == 0)
{
lean_object* v___x_2488_; 
v___x_2488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2488_, 0, v_e_2454_);
lean_ctor_set(v___x_2488_, 1, v_a_2458_);
return v___x_2488_;
}
else
{
v___y_2460_ = v___x_2486_;
goto v___jp_2459_;
}
}
else
{
v___y_2460_ = v___x_2486_;
goto v___jp_2459_;
}
v___jp_2459_:
{
if (v___y_2460_ == 0)
{
lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; 
v___x_2461_ = lean_unsigned_to_nat(0u);
v___x_2462_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__2, &l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__2_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__2);
v___x_2463_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit(v_subst_2455_, v_e_2454_, v___x_2461_, v___x_2462_, v_a_2456_, v_a_2457_, v_a_2458_);
if (lean_obj_tag(v___x_2463_) == 0)
{
lean_object* v_a_2464_; lean_object* v_a_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2473_; 
v_a_2464_ = lean_ctor_get(v___x_2463_, 0);
v_a_2465_ = lean_ctor_get(v___x_2463_, 1);
v_isSharedCheck_2473_ = !lean_is_exclusive(v___x_2463_);
if (v_isSharedCheck_2473_ == 0)
{
v___x_2467_ = v___x_2463_;
v_isShared_2468_ = v_isSharedCheck_2473_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_a_2465_);
lean_inc(v_a_2464_);
lean_dec(v___x_2463_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2473_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
lean_object* v_fst_2469_; lean_object* v___x_2471_; 
v_fst_2469_ = lean_ctor_get(v_a_2464_, 0);
lean_inc(v_fst_2469_);
lean_dec(v_a_2464_);
if (v_isShared_2468_ == 0)
{
lean_ctor_set(v___x_2467_, 0, v_fst_2469_);
v___x_2471_ = v___x_2467_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v_fst_2469_);
lean_ctor_set(v_reuseFailAlloc_2472_, 1, v_a_2465_);
v___x_2471_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
return v___x_2471_;
}
}
}
else
{
lean_object* v_a_2474_; lean_object* v_a_2475_; lean_object* v___x_2477_; uint8_t v_isShared_2478_; uint8_t v_isSharedCheck_2482_; 
v_a_2474_ = lean_ctor_get(v___x_2463_, 0);
v_a_2475_ = lean_ctor_get(v___x_2463_, 1);
v_isSharedCheck_2482_ = !lean_is_exclusive(v___x_2463_);
if (v_isSharedCheck_2482_ == 0)
{
v___x_2477_ = v___x_2463_;
v_isShared_2478_ = v_isSharedCheck_2482_;
goto v_resetjp_2476_;
}
else
{
lean_inc(v_a_2475_);
lean_inc(v_a_2474_);
lean_dec(v___x_2463_);
v___x_2477_ = lean_box(0);
v_isShared_2478_ = v_isSharedCheck_2482_;
goto v_resetjp_2476_;
}
v_resetjp_2476_:
{
lean_object* v___x_2480_; 
if (v_isShared_2478_ == 0)
{
v___x_2480_ = v___x_2477_;
goto v_reusejp_2479_;
}
else
{
lean_object* v_reuseFailAlloc_2481_; 
v_reuseFailAlloc_2481_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2481_, 0, v_a_2474_);
lean_ctor_set(v_reuseFailAlloc_2481_, 1, v_a_2475_);
v___x_2480_ = v_reuseFailAlloc_2481_;
goto v_reusejp_2479_;
}
v_reusejp_2479_:
{
return v___x_2480_;
}
}
}
}
else
{
lean_object* v___x_2483_; 
v___x_2483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2483_, 0, v_e_2454_);
lean_ctor_set(v___x_2483_, 1, v_a_2458_);
return v___x_2483_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27___boxed(lean_object* v_e_2489_, lean_object* v_subst_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_){
_start:
{
uint8_t v_a_boxed_2494_; lean_object* v_res_2495_; 
v_a_boxed_2494_ = lean_unbox(v_a_2491_);
v_res_2495_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27(v_e_2489_, v_subst_2490_, v_a_boxed_2494_, v_a_2492_, v_a_2493_);
lean_dec_ref(v_a_2492_);
lean_dec_ref(v_subst_2490_);
return v_res_2495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevBetaS(lean_object* v_e_2496_, lean_object* v_subst_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_){
_start:
{
uint8_t v___x_2505_; 
v___x_2505_ = l_Lean_Expr_hasLooseBVars(v_e_2496_);
if (v___x_2505_ == 0)
{
lean_object* v___x_2506_; 
lean_dec_ref(v_subst_2497_);
v___x_2506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2506_, 0, v_e_2496_);
return v___x_2506_;
}
else
{
lean_object* v___x_2507_; lean_object* v___x_2508_; uint8_t v___x_2509_; 
v___x_2507_ = lean_array_get_size(v_subst_2497_);
v___x_2508_ = lean_unsigned_to_nat(0u);
v___x_2509_ = lean_nat_dec_eq(v___x_2507_, v___x_2508_);
if (v___x_2509_ == 0)
{
lean_object* v___x_2510_; lean_object* v___x_2511_; uint8_t v_debug_2512_; lean_object* v_env_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; 
v___x_2510_ = lean_st_ref_get(v_a_2499_);
v___x_2511_ = lean_st_ref_get(v_a_2503_);
v_debug_2512_ = lean_ctor_get_uint8(v___x_2510_, sizeof(void*)*11);
lean_dec(v___x_2510_);
v_env_2513_ = lean_ctor_get(v___x_2511_, 0);
lean_inc_ref(v_env_2513_);
lean_dec(v___x_2511_);
v___x_2514_ = lean_box(v_debug_2512_);
v___x_2515_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27___boxed), 5, 3);
lean_closure_set(v___x_2515_, 0, v_e_2496_);
lean_closure_set(v___x_2515_, 1, v_subst_2497_);
lean_closure_set(v___x_2515_, 2, v___x_2514_);
v___x_2516_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2516_, 0, v_env_2513_);
lean_ctor_set_uint8(v___x_2516_, sizeof(void*)*1, v___x_2509_);
lean_ctor_set_uint8(v___x_2516_, sizeof(void*)*1 + 1, v___x_2509_);
v___x_2517_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___x_2515_, v___x_2516_, v_a_2499_);
if (lean_obj_tag(v___x_2517_) == 0)
{
lean_object* v_a_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2528_; 
v_a_2518_ = lean_ctor_get(v___x_2517_, 0);
v_isSharedCheck_2528_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2528_ == 0)
{
v___x_2520_ = v___x_2517_;
v_isShared_2521_ = v_isSharedCheck_2528_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_a_2518_);
lean_dec(v___x_2517_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2528_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
if (lean_obj_tag(v_a_2518_) == 0)
{
lean_object* v___x_2522_; lean_object* v___x_2523_; 
lean_dec_ref_known(v_a_2518_, 1);
lean_del_object(v___x_2520_);
v___x_2522_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__2, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__2_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__2);
v___x_2523_ = l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(v___x_2522_, v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_);
return v___x_2523_;
}
else
{
lean_object* v_a_2524_; lean_object* v___x_2526_; 
v_a_2524_ = lean_ctor_get(v_a_2518_, 0);
lean_inc(v_a_2524_);
lean_dec_ref_known(v_a_2518_, 1);
if (v_isShared_2521_ == 0)
{
lean_ctor_set(v___x_2520_, 0, v_a_2524_);
v___x_2526_ = v___x_2520_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2527_; 
v_reuseFailAlloc_2527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2527_, 0, v_a_2524_);
v___x_2526_ = v_reuseFailAlloc_2527_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
return v___x_2526_;
}
}
}
}
else
{
lean_object* v_a_2529_; lean_object* v___x_2531_; uint8_t v_isShared_2532_; uint8_t v_isSharedCheck_2536_; 
v_a_2529_ = lean_ctor_get(v___x_2517_, 0);
v_isSharedCheck_2536_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2536_ == 0)
{
v___x_2531_ = v___x_2517_;
v_isShared_2532_ = v_isSharedCheck_2536_;
goto v_resetjp_2530_;
}
else
{
lean_inc(v_a_2529_);
lean_dec(v___x_2517_);
v___x_2531_ = lean_box(0);
v_isShared_2532_ = v_isSharedCheck_2536_;
goto v_resetjp_2530_;
}
v_resetjp_2530_:
{
lean_object* v___x_2534_; 
if (v_isShared_2532_ == 0)
{
v___x_2534_ = v___x_2531_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v_a_2529_);
v___x_2534_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
return v___x_2534_;
}
}
}
}
else
{
lean_object* v___x_2537_; 
lean_dec_ref(v_subst_2497_);
v___x_2537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2537_, 0, v_e_2496_);
return v___x_2537_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevBetaS___boxed(lean_object* v_e_2538_, lean_object* v_subst_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_){
_start:
{
lean_object* v_res_2547_; 
v_res_2547_ = l_Lean_Meta_Sym_instantiateRevBetaS(v_e_2538_, v_subst_2539_, v_a_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_);
lean_dec(v_a_2545_);
lean_dec_ref(v_a_2544_);
lean_dec(v_a_2543_);
lean_dec_ref(v_a_2542_);
lean_dec(v_a_2541_);
lean_dec_ref(v_a_2540_);
return v_res_2547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_betaRevS(lean_object* v_f_2548_, lean_object* v_revArgs_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_){
_start:
{
lean_object* v___x_2557_; lean_object* v___x_2558_; uint8_t v_debug_2559_; lean_object* v_env_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; uint8_t v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; 
v___x_2557_ = lean_st_ref_get(v_a_2551_);
v___x_2558_ = lean_st_ref_get(v_a_2555_);
v_debug_2559_ = lean_ctor_get_uint8(v___x_2557_, sizeof(void*)*11);
lean_dec(v___x_2557_);
v_env_2560_ = lean_ctor_get(v___x_2558_, 0);
lean_inc_ref(v_env_2560_);
lean_dec(v___x_2558_);
v___x_2561_ = lean_box(v_debug_2559_);
v___x_2562_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27___boxed), 5, 3);
lean_closure_set(v___x_2562_, 0, v_f_2548_);
lean_closure_set(v___x_2562_, 1, v_revArgs_2549_);
lean_closure_set(v___x_2562_, 2, v___x_2561_);
v___x_2563_ = 0;
v___x_2564_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2564_, 0, v_env_2560_);
lean_ctor_set_uint8(v___x_2564_, sizeof(void*)*1, v___x_2563_);
lean_ctor_set_uint8(v___x_2564_, sizeof(void*)*1 + 1, v___x_2563_);
v___x_2565_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___x_2562_, v___x_2564_, v_a_2551_);
if (lean_obj_tag(v___x_2565_) == 0)
{
lean_object* v_a_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2576_; 
v_a_2566_ = lean_ctor_get(v___x_2565_, 0);
v_isSharedCheck_2576_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2576_ == 0)
{
v___x_2568_ = v___x_2565_;
v_isShared_2569_ = v_isSharedCheck_2576_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_a_2566_);
lean_dec(v___x_2565_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2576_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
if (lean_obj_tag(v_a_2566_) == 0)
{
lean_object* v___x_2570_; lean_object* v___x_2571_; 
lean_dec_ref_known(v_a_2566_, 1);
lean_del_object(v___x_2568_);
v___x_2570_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__2, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__2_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__2);
v___x_2571_ = l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(v___x_2570_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_);
return v___x_2571_;
}
else
{
lean_object* v_a_2572_; lean_object* v___x_2574_; 
v_a_2572_ = lean_ctor_get(v_a_2566_, 0);
lean_inc(v_a_2572_);
lean_dec_ref_known(v_a_2566_, 1);
if (v_isShared_2569_ == 0)
{
lean_ctor_set(v___x_2568_, 0, v_a_2572_);
v___x_2574_ = v___x_2568_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_a_2572_);
v___x_2574_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
return v___x_2574_;
}
}
}
}
else
{
lean_object* v_a_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2584_; 
v_a_2577_ = lean_ctor_get(v___x_2565_, 0);
v_isSharedCheck_2584_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2584_ == 0)
{
v___x_2579_ = v___x_2565_;
v_isShared_2580_ = v_isSharedCheck_2584_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_a_2577_);
lean_dec(v___x_2565_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2584_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v___x_2582_; 
if (v_isShared_2580_ == 0)
{
v___x_2582_ = v___x_2579_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v_a_2577_);
v___x_2582_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
return v___x_2582_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_betaRevS___boxed(lean_object* v_f_2585_, lean_object* v_revArgs_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_){
_start:
{
lean_object* v_res_2594_; 
v_res_2594_ = l_Lean_Meta_Sym_betaRevS(v_f_2585_, v_revArgs_2586_, v_a_2587_, v_a_2588_, v_a_2589_, v_a_2590_, v_a_2591_, v_a_2592_);
lean_dec(v_a_2592_);
lean_dec_ref(v_a_2591_);
lean_dec(v_a_2590_);
lean_dec_ref(v_a_2589_);
lean_dec(v_a_2588_);
lean_dec_ref(v_a_2587_);
return v_res_2594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_betaS(lean_object* v_f_2595_, lean_object* v_args_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_){
_start:
{
lean_object* v___x_2604_; lean_object* v___x_2605_; 
v___x_2604_ = l_Array_reverse___redArg(v_args_2596_);
v___x_2605_ = l_Lean_Meta_Sym_betaRevS(v_f_2595_, v___x_2604_, v_a_2597_, v_a_2598_, v_a_2599_, v_a_2600_, v_a_2601_, v_a_2602_);
return v___x_2605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_betaS___boxed(lean_object* v_f_2606_, lean_object* v_args_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_, lean_object* v_a_2610_, lean_object* v_a_2611_, lean_object* v_a_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_){
_start:
{
lean_object* v_res_2615_; 
v_res_2615_ = l_Lean_Meta_Sym_betaS(v_f_2606_, v_args_2607_, v_a_2608_, v_a_2609_, v_a_2610_, v_a_2611_, v_a_2612_, v_a_2613_);
lean_dec(v_a_2613_);
lean_dec_ref(v_a_2612_);
lean_dec(v_a_2611_);
lean_dec_ref(v_a_2610_);
lean_dec(v_a_2609_);
lean_dec_ref(v_a_2608_);
return v_res_2615_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_LooseBVarsS(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_LooseBVarsS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_LooseBVarsS(uint8_t builtin);
lean_object* initialize_Init_Grind(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_LooseBVarsS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InstantiateS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_InstantiateS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_InstantiateS(builtin);
}
#ifdef __cplusplus
}
#endif
