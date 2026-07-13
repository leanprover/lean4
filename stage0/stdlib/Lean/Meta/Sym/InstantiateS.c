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
lean_object* l_Lean_Meta_Sym_instBEqExprPtr___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instHashableExprPtr___lam__0___boxed(lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instInhabited___redArg___lam__0(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Builder_share1___redArg(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_liftLooseBVarsS_x27(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_looseBVarRange(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
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
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
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
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
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
uint8_t v___y_25932__boxed_14_; lean_object* v_res_15_; 
v___y_25932__boxed_14_ = lean_unbox(v___y_11_);
v_res_15_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0(v_idx_10_, v___y_25932__boxed_14_, v___y_12_, v___y_13_);
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
lean_object* v___x_25_; lean_object* v___x_2974__overap_26_; lean_object* v___x_27_; 
v___x_25_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__0, &l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__0);
v___x_2974__overap_26_ = lean_panic_fn_borrowed(v___x_25_, v_msg_17_);
lean_inc(v___y_23_);
lean_inc_ref(v___y_22_);
lean_inc(v___y_21_);
lean_inc_ref(v___y_20_);
lean_inc(v___y_19_);
lean_inc_ref(v___y_18_);
v___x_27_ = lean_apply_7(v___x_2974__overap_26_, v___y_18_, v___y_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_, lean_box(0));
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
lean_inc_ref(v_f_37_);
v___x_67_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_f_37_, v___y_40_, v___y_41_, v___y_42_);
if (lean_obj_tag(v___x_67_) == 0)
{
lean_object* v_a_68_; lean_object* v___x_69_; 
v_a_68_ = lean_ctor_get(v___x_67_, 1);
lean_inc(v_a_68_);
lean_dec_ref_known(v___x_67_, 2);
lean_inc_ref(v_a_38_);
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
uint8_t v___y_25972__boxed_95_; lean_object* v_res_96_; 
v___y_25972__boxed_95_ = lean_unbox(v___y_92_);
v_res_96_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__2(v_f_89_, v_a_90_, v___y_91_, v___y_25972__boxed_95_, v___y_93_, v___y_94_);
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
lean_inc_ref(v_t_99_);
v___x_129_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_99_, v___y_102_, v___y_103_, v___y_104_);
if (lean_obj_tag(v___x_129_) == 0)
{
lean_object* v_a_130_; lean_object* v___x_131_; 
v_a_130_ = lean_ctor_get(v___x_129_, 1);
lean_inc(v_a_130_);
lean_dec_ref_known(v___x_129_, 2);
lean_inc_ref(v_b_100_);
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
uint8_t v_bi_boxed_159_; uint8_t v___y_26078__boxed_160_; lean_object* v_res_161_; 
v_bi_boxed_159_ = lean_unbox(v_bi_152_);
v___y_26078__boxed_160_ = lean_unbox(v___y_156_);
v_res_161_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__4(v_x_151_, v_bi_boxed_159_, v_t_153_, v_b_154_, v___y_155_, v___y_26078__boxed_160_, v___y_157_, v___y_158_);
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
lean_inc_ref(v_struct_164_);
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
uint8_t v___y_26184__boxed_211_; lean_object* v_res_212_; 
v___y_26184__boxed_211_ = lean_unbox(v___y_208_);
v_res_212_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__7(v_structName_204_, v_idx_205_, v_struct_206_, v___y_207_, v___y_26184__boxed_211_, v___y_209_, v___y_210_);
lean_dec_ref(v___y_209_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8(lean_object* v_msg_220_, lean_object* v___y_221_, uint8_t v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_){
_start:
{
lean_object* v___f_225_; lean_object* v___f_226_; lean_object* v___f_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___f_237_; lean_object* v___f_238_; lean_object* v___f_239_; lean_object* v___f_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_25528__overap_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v___f_225_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8___closed__0));
v___f_226_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8___closed__1));
v___f_227_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8___closed__2));
v___x_228_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8___closed__3));
v___x_229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
lean_ctor_set(v___x_229_, 1, v___f_225_);
v___x_230_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8___closed__4));
v___x_231_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8___closed__5));
v___x_232_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_232_, 0, v___x_229_);
lean_ctor_set(v___x_232_, 1, v___x_230_);
lean_ctor_set(v___x_232_, 2, v___f_226_);
lean_ctor_set(v___x_232_, 3, v___f_227_);
lean_ctor_set(v___x_232_, 4, v___x_231_);
v___x_233_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8___closed__6));
v___x_234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_234_, 0, v___x_232_);
lean_ctor_set(v___x_234_, 1, v___x_233_);
v___x_235_ = l_ReaderT_instMonad___redArg(v___x_234_);
v___x_236_ = l_ReaderT_instMonad___redArg(v___x_235_);
lean_inc_ref_n(v___x_236_, 6);
v___f_237_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_237_, 0, v___x_236_);
v___f_238_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_238_, 0, v___x_236_);
v___f_239_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_239_, 0, v___x_236_);
v___f_240_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_240_, 0, v___x_236_);
v___x_241_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_241_, 0, lean_box(0));
lean_closure_set(v___x_241_, 1, lean_box(0));
lean_closure_set(v___x_241_, 2, v___x_236_);
v___x_242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_242_, 0, v___x_241_);
lean_ctor_set(v___x_242_, 1, v___f_237_);
v___x_243_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_243_, 0, lean_box(0));
lean_closure_set(v___x_243_, 1, lean_box(0));
lean_closure_set(v___x_243_, 2, v___x_236_);
v___x_244_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_244_, 0, v___x_242_);
lean_ctor_set(v___x_244_, 1, v___x_243_);
lean_ctor_set(v___x_244_, 2, v___f_238_);
lean_ctor_set(v___x_244_, 3, v___f_239_);
lean_ctor_set(v___x_244_, 4, v___f_240_);
v___x_245_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_245_, 0, lean_box(0));
lean_closure_set(v___x_245_, 1, lean_box(0));
lean_closure_set(v___x_245_, 2, v___x_236_);
v___x_246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_246_, 0, v___x_244_);
lean_ctor_set(v___x_246_, 1, v___x_245_);
v___x_247_ = l_Lean_instInhabitedExpr;
v___x_248_ = l_instInhabitedOfMonad___redArg(v___x_246_, v___x_247_);
v___x_25528__overap_249_ = lean_panic_fn_borrowed(v___x_248_, v_msg_220_);
lean_dec(v___x_248_);
v___x_250_ = lean_box(v___y_222_);
lean_inc_ref(v___y_223_);
v___x_251_ = lean_apply_4(v___x_25528__overap_249_, v___y_221_, v___x_250_, v___y_223_, v___y_224_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8___boxed(lean_object* v_msg_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_){
_start:
{
uint8_t v___y_26281__boxed_257_; lean_object* v_res_258_; 
v___y_26281__boxed_257_ = lean_unbox(v___y_254_);
v_res_258_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8(v_msg_252_, v___y_253_, v___y_26281__boxed_257_, v___y_255_, v___y_256_);
lean_dec_ref(v___y_255_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11___redArg(lean_object* v_a_259_, lean_object* v_x_260_){
_start:
{
if (lean_obj_tag(v_x_260_) == 0)
{
lean_object* v___x_261_; 
v___x_261_ = lean_box(0);
return v___x_261_;
}
else
{
lean_object* v_key_262_; lean_object* v_value_263_; lean_object* v_tail_264_; uint8_t v___y_266_; lean_object* v_fst_269_; lean_object* v_snd_270_; lean_object* v_fst_271_; lean_object* v_snd_272_; size_t v___x_273_; size_t v___x_274_; uint8_t v___x_275_; 
v_key_262_ = lean_ctor_get(v_x_260_, 0);
v_value_263_ = lean_ctor_get(v_x_260_, 1);
v_tail_264_ = lean_ctor_get(v_x_260_, 2);
v_fst_269_ = lean_ctor_get(v_key_262_, 0);
v_snd_270_ = lean_ctor_get(v_key_262_, 1);
v_fst_271_ = lean_ctor_get(v_a_259_, 0);
v_snd_272_ = lean_ctor_get(v_a_259_, 1);
v___x_273_ = lean_ptr_addr(v_fst_269_);
v___x_274_ = lean_ptr_addr(v_fst_271_);
v___x_275_ = lean_usize_dec_eq(v___x_273_, v___x_274_);
if (v___x_275_ == 0)
{
v___y_266_ = v___x_275_;
goto v___jp_265_;
}
else
{
uint8_t v___x_276_; 
v___x_276_ = lean_nat_dec_eq(v_snd_270_, v_snd_272_);
v___y_266_ = v___x_276_;
goto v___jp_265_;
}
v___jp_265_:
{
if (v___y_266_ == 0)
{
v_x_260_ = v_tail_264_;
goto _start;
}
else
{
lean_object* v___x_268_; 
lean_inc(v_value_263_);
v___x_268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_268_, 0, v_value_263_);
return v___x_268_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11___redArg___boxed(lean_object* v_a_277_, lean_object* v_x_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11___redArg(v_a_277_, v_x_278_);
lean_dec(v_x_278_);
lean_dec_ref(v_a_277_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3___redArg(lean_object* v_m_280_, lean_object* v_a_281_){
_start:
{
lean_object* v_buckets_282_; lean_object* v_fst_283_; lean_object* v_snd_284_; lean_object* v___x_285_; size_t v___x_286_; size_t v___x_287_; size_t v___x_288_; uint64_t v___x_289_; uint64_t v___x_290_; uint64_t v___x_291_; uint64_t v___x_292_; uint64_t v___x_293_; uint64_t v_fold_294_; uint64_t v___x_295_; uint64_t v___x_296_; uint64_t v___x_297_; size_t v___x_298_; size_t v___x_299_; size_t v___x_300_; size_t v___x_301_; size_t v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v_buckets_282_ = lean_ctor_get(v_m_280_, 1);
v_fst_283_ = lean_ctor_get(v_a_281_, 0);
v_snd_284_ = lean_ctor_get(v_a_281_, 1);
v___x_285_ = lean_array_get_size(v_buckets_282_);
v___x_286_ = lean_ptr_addr(v_fst_283_);
v___x_287_ = ((size_t)3ULL);
v___x_288_ = lean_usize_shift_right(v___x_286_, v___x_287_);
v___x_289_ = lean_usize_to_uint64(v___x_288_);
v___x_290_ = lean_uint64_of_nat(v_snd_284_);
v___x_291_ = lean_uint64_mix_hash(v___x_289_, v___x_290_);
v___x_292_ = 32ULL;
v___x_293_ = lean_uint64_shift_right(v___x_291_, v___x_292_);
v_fold_294_ = lean_uint64_xor(v___x_291_, v___x_293_);
v___x_295_ = 16ULL;
v___x_296_ = lean_uint64_shift_right(v_fold_294_, v___x_295_);
v___x_297_ = lean_uint64_xor(v_fold_294_, v___x_296_);
v___x_298_ = lean_uint64_to_usize(v___x_297_);
v___x_299_ = lean_usize_of_nat(v___x_285_);
v___x_300_ = ((size_t)1ULL);
v___x_301_ = lean_usize_sub(v___x_299_, v___x_300_);
v___x_302_ = lean_usize_land(v___x_298_, v___x_301_);
v___x_303_ = lean_array_uget_borrowed(v_buckets_282_, v___x_302_);
v___x_304_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11___redArg(v_a_281_, v___x_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_m_305_, lean_object* v_a_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3___redArg(v_m_305_, v_a_306_);
lean_dec_ref(v_a_306_);
lean_dec_ref(v_m_305_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__3(lean_object* v_x_308_, uint8_t v_bi_309_, lean_object* v_t_310_, lean_object* v_b_311_, lean_object* v___y_312_, uint8_t v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_){
_start:
{
lean_object* v___y_317_; lean_object* v___y_318_; 
if (v___y_313_ == 0)
{
v___y_317_ = v___y_312_;
v___y_318_ = v___y_315_;
goto v___jp_316_;
}
else
{
lean_object* v___x_340_; 
lean_inc_ref(v_t_310_);
v___x_340_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_310_, v___y_313_, v___y_314_, v___y_315_);
if (lean_obj_tag(v___x_340_) == 0)
{
lean_object* v_a_341_; lean_object* v___x_342_; 
v_a_341_ = lean_ctor_get(v___x_340_, 1);
lean_inc(v_a_341_);
lean_dec_ref_known(v___x_340_, 2);
lean_inc_ref(v_b_311_);
v___x_342_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_311_, v___y_313_, v___y_314_, v_a_341_);
if (lean_obj_tag(v___x_342_) == 0)
{
lean_object* v_a_343_; 
v_a_343_ = lean_ctor_get(v___x_342_, 1);
lean_inc(v_a_343_);
lean_dec_ref_known(v___x_342_, 2);
v___y_317_ = v___y_312_;
v___y_318_ = v_a_343_;
goto v___jp_316_;
}
else
{
lean_object* v_a_344_; lean_object* v_a_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_352_; 
lean_dec_ref(v___y_312_);
lean_dec_ref(v_b_311_);
lean_dec_ref(v_t_310_);
lean_dec(v_x_308_);
v_a_344_ = lean_ctor_get(v___x_342_, 0);
v_a_345_ = lean_ctor_get(v___x_342_, 1);
v_isSharedCheck_352_ = !lean_is_exclusive(v___x_342_);
if (v_isSharedCheck_352_ == 0)
{
v___x_347_ = v___x_342_;
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_a_345_);
lean_inc(v_a_344_);
lean_dec(v___x_342_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_350_; 
if (v_isShared_348_ == 0)
{
v___x_350_ = v___x_347_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v_a_344_);
lean_ctor_set(v_reuseFailAlloc_351_, 1, v_a_345_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
}
}
else
{
lean_object* v_a_353_; lean_object* v_a_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_361_; 
lean_dec_ref(v___y_312_);
lean_dec_ref(v_b_311_);
lean_dec_ref(v_t_310_);
lean_dec(v_x_308_);
v_a_353_ = lean_ctor_get(v___x_340_, 0);
v_a_354_ = lean_ctor_get(v___x_340_, 1);
v_isSharedCheck_361_ = !lean_is_exclusive(v___x_340_);
if (v_isSharedCheck_361_ == 0)
{
v___x_356_ = v___x_340_;
v_isShared_357_ = v_isSharedCheck_361_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_a_354_);
lean_inc(v_a_353_);
lean_dec(v___x_340_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_361_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v___x_359_; 
if (v_isShared_357_ == 0)
{
v___x_359_ = v___x_356_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v_a_353_);
lean_ctor_set(v_reuseFailAlloc_360_, 1, v_a_354_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
return v___x_359_;
}
}
}
}
v___jp_316_:
{
lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_319_ = l_Lean_Expr_lam___override(v_x_308_, v_t_310_, v_b_311_, v_bi_309_);
v___x_320_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_319_, v___y_318_);
if (lean_obj_tag(v___x_320_) == 0)
{
lean_object* v_a_321_; lean_object* v_a_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_330_; 
v_a_321_ = lean_ctor_get(v___x_320_, 0);
v_a_322_ = lean_ctor_get(v___x_320_, 1);
v_isSharedCheck_330_ = !lean_is_exclusive(v___x_320_);
if (v_isSharedCheck_330_ == 0)
{
v___x_324_ = v___x_320_;
v_isShared_325_ = v_isSharedCheck_330_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_a_322_);
lean_inc(v_a_321_);
lean_dec(v___x_320_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_330_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_326_; lean_object* v___x_328_; 
v___x_326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_326_, 0, v_a_321_);
lean_ctor_set(v___x_326_, 1, v___y_317_);
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 0, v___x_326_);
v___x_328_ = v___x_324_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v___x_326_);
lean_ctor_set(v_reuseFailAlloc_329_, 1, v_a_322_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
return v___x_328_;
}
}
}
else
{
lean_object* v_a_331_; lean_object* v_a_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_339_; 
lean_dec_ref(v___y_317_);
v_a_331_ = lean_ctor_get(v___x_320_, 0);
v_a_332_ = lean_ctor_get(v___x_320_, 1);
v_isSharedCheck_339_ = !lean_is_exclusive(v___x_320_);
if (v_isSharedCheck_339_ == 0)
{
v___x_334_ = v___x_320_;
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_a_332_);
lean_inc(v_a_331_);
lean_dec(v___x_320_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_337_; 
if (v_isShared_335_ == 0)
{
v___x_337_ = v___x_334_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_a_331_);
lean_ctor_set(v_reuseFailAlloc_338_, 1, v_a_332_);
v___x_337_ = v_reuseFailAlloc_338_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
return v___x_337_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__3___boxed(lean_object* v_x_362_, lean_object* v_bi_363_, lean_object* v_t_364_, lean_object* v_b_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
uint8_t v_bi_boxed_370_; uint8_t v___y_26431__boxed_371_; lean_object* v_res_372_; 
v_bi_boxed_370_ = lean_unbox(v_bi_363_);
v___y_26431__boxed_371_ = lean_unbox(v___y_367_);
v_res_372_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__3(v_x_362_, v_bi_boxed_370_, v_t_364_, v_b_365_, v___y_366_, v___y_26431__boxed_371_, v___y_368_, v___y_369_);
lean_dec_ref(v___y_368_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__5(lean_object* v_x_373_, lean_object* v_t_374_, lean_object* v_v_375_, lean_object* v_b_376_, uint8_t v_nondep_377_, lean_object* v___y_378_, uint8_t v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
lean_object* v___y_383_; lean_object* v___y_384_; 
if (v___y_379_ == 0)
{
v___y_383_ = v___y_378_;
v___y_384_ = v___y_381_;
goto v___jp_382_;
}
else
{
lean_object* v___x_406_; 
lean_inc_ref(v_t_374_);
v___x_406_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_374_, v___y_379_, v___y_380_, v___y_381_);
if (lean_obj_tag(v___x_406_) == 0)
{
lean_object* v_a_407_; lean_object* v___x_408_; 
v_a_407_ = lean_ctor_get(v___x_406_, 1);
lean_inc(v_a_407_);
lean_dec_ref_known(v___x_406_, 2);
lean_inc_ref(v_v_375_);
v___x_408_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_v_375_, v___y_379_, v___y_380_, v_a_407_);
if (lean_obj_tag(v___x_408_) == 0)
{
lean_object* v_a_409_; lean_object* v___x_410_; 
v_a_409_ = lean_ctor_get(v___x_408_, 1);
lean_inc(v_a_409_);
lean_dec_ref_known(v___x_408_, 2);
lean_inc_ref(v_b_376_);
v___x_410_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_376_, v___y_379_, v___y_380_, v_a_409_);
if (lean_obj_tag(v___x_410_) == 0)
{
lean_object* v_a_411_; 
v_a_411_ = lean_ctor_get(v___x_410_, 1);
lean_inc(v_a_411_);
lean_dec_ref_known(v___x_410_, 2);
v___y_383_ = v___y_378_;
v___y_384_ = v_a_411_;
goto v___jp_382_;
}
else
{
lean_object* v_a_412_; lean_object* v_a_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_420_; 
lean_dec_ref(v___y_378_);
lean_dec_ref(v_b_376_);
lean_dec_ref(v_v_375_);
lean_dec_ref(v_t_374_);
lean_dec(v_x_373_);
v_a_412_ = lean_ctor_get(v___x_410_, 0);
v_a_413_ = lean_ctor_get(v___x_410_, 1);
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_410_);
if (v_isSharedCheck_420_ == 0)
{
v___x_415_ = v___x_410_;
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_a_413_);
lean_inc(v_a_412_);
lean_dec(v___x_410_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_418_; 
if (v_isShared_416_ == 0)
{
v___x_418_ = v___x_415_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_a_412_);
lean_ctor_set(v_reuseFailAlloc_419_, 1, v_a_413_);
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
else
{
lean_object* v_a_421_; lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_429_; 
lean_dec_ref(v___y_378_);
lean_dec_ref(v_b_376_);
lean_dec_ref(v_v_375_);
lean_dec_ref(v_t_374_);
lean_dec(v_x_373_);
v_a_421_ = lean_ctor_get(v___x_408_, 0);
v_a_422_ = lean_ctor_get(v___x_408_, 1);
v_isSharedCheck_429_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_429_ == 0)
{
v___x_424_ = v___x_408_;
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_inc(v_a_421_);
lean_dec(v___x_408_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_427_; 
if (v_isShared_425_ == 0)
{
v___x_427_ = v___x_424_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_a_421_);
lean_ctor_set(v_reuseFailAlloc_428_, 1, v_a_422_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
}
else
{
lean_object* v_a_430_; lean_object* v_a_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_438_; 
lean_dec_ref(v___y_378_);
lean_dec_ref(v_b_376_);
lean_dec_ref(v_v_375_);
lean_dec_ref(v_t_374_);
lean_dec(v_x_373_);
v_a_430_ = lean_ctor_get(v___x_406_, 0);
v_a_431_ = lean_ctor_get(v___x_406_, 1);
v_isSharedCheck_438_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_438_ == 0)
{
v___x_433_ = v___x_406_;
v_isShared_434_ = v_isSharedCheck_438_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_a_431_);
lean_inc(v_a_430_);
lean_dec(v___x_406_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_438_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_436_; 
if (v_isShared_434_ == 0)
{
v___x_436_ = v___x_433_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_a_430_);
lean_ctor_set(v_reuseFailAlloc_437_, 1, v_a_431_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
}
}
v___jp_382_:
{
lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_385_ = l_Lean_Expr_letE___override(v_x_373_, v_t_374_, v_v_375_, v_b_376_, v_nondep_377_);
v___x_386_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_385_, v___y_384_);
if (lean_obj_tag(v___x_386_) == 0)
{
lean_object* v_a_387_; lean_object* v_a_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_396_; 
v_a_387_ = lean_ctor_get(v___x_386_, 0);
v_a_388_ = lean_ctor_get(v___x_386_, 1);
v_isSharedCheck_396_ = !lean_is_exclusive(v___x_386_);
if (v_isSharedCheck_396_ == 0)
{
v___x_390_ = v___x_386_;
v_isShared_391_ = v_isSharedCheck_396_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_a_388_);
lean_inc(v_a_387_);
lean_dec(v___x_386_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_396_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_392_; lean_object* v___x_394_; 
v___x_392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_392_, 0, v_a_387_);
lean_ctor_set(v___x_392_, 1, v___y_383_);
if (v_isShared_391_ == 0)
{
lean_ctor_set(v___x_390_, 0, v___x_392_);
v___x_394_ = v___x_390_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v___x_392_);
lean_ctor_set(v_reuseFailAlloc_395_, 1, v_a_388_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
}
else
{
lean_object* v_a_397_; lean_object* v_a_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_405_; 
lean_dec_ref(v___y_383_);
v_a_397_ = lean_ctor_get(v___x_386_, 0);
v_a_398_ = lean_ctor_get(v___x_386_, 1);
v_isSharedCheck_405_ = !lean_is_exclusive(v___x_386_);
if (v_isSharedCheck_405_ == 0)
{
v___x_400_ = v___x_386_;
v_isShared_401_ = v_isSharedCheck_405_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_a_398_);
lean_inc(v_a_397_);
lean_dec(v___x_386_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_405_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_403_; 
if (v_isShared_401_ == 0)
{
v___x_403_ = v___x_400_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_a_397_);
lean_ctor_set(v_reuseFailAlloc_404_, 1, v_a_398_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__5___boxed(lean_object* v_x_439_, lean_object* v_t_440_, lean_object* v_v_441_, lean_object* v_b_442_, lean_object* v_nondep_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
uint8_t v_nondep_boxed_448_; uint8_t v___y_26537__boxed_449_; lean_object* v_res_450_; 
v_nondep_boxed_448_ = lean_unbox(v_nondep_443_);
v___y_26537__boxed_449_ = lean_unbox(v___y_445_);
v_res_450_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__5(v_x_439_, v_t_440_, v_v_441_, v_b_442_, v_nondep_boxed_448_, v___y_444_, v___y_26537__boxed_449_, v___y_446_, v___y_447_);
lean_dec_ref(v___y_446_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__6(lean_object* v_d_451_, lean_object* v_e_452_, lean_object* v___y_453_, uint8_t v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
lean_object* v___y_458_; lean_object* v___y_459_; 
if (v___y_454_ == 0)
{
v___y_458_ = v___y_453_;
v___y_459_ = v___y_456_;
goto v___jp_457_;
}
else
{
lean_object* v___x_481_; 
lean_inc_ref(v_e_452_);
v___x_481_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_e_452_, v___y_454_, v___y_455_, v___y_456_);
if (lean_obj_tag(v___x_481_) == 0)
{
lean_object* v_a_482_; 
v_a_482_ = lean_ctor_get(v___x_481_, 1);
lean_inc(v_a_482_);
lean_dec_ref_known(v___x_481_, 2);
v___y_458_ = v___y_453_;
v___y_459_ = v_a_482_;
goto v___jp_457_;
}
else
{
lean_object* v_a_483_; lean_object* v_a_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_491_; 
lean_dec_ref(v___y_453_);
lean_dec_ref(v_e_452_);
lean_dec(v_d_451_);
v_a_483_ = lean_ctor_get(v___x_481_, 0);
v_a_484_ = lean_ctor_get(v___x_481_, 1);
v_isSharedCheck_491_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_491_ == 0)
{
v___x_486_ = v___x_481_;
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_a_484_);
lean_inc(v_a_483_);
lean_dec(v___x_481_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_489_; 
if (v_isShared_487_ == 0)
{
v___x_489_ = v___x_486_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v_a_483_);
lean_ctor_set(v_reuseFailAlloc_490_, 1, v_a_484_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
return v___x_489_;
}
}
}
}
v___jp_457_:
{
lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_460_ = l_Lean_Expr_mdata___override(v_d_451_, v_e_452_);
v___x_461_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_460_, v___y_459_);
if (lean_obj_tag(v___x_461_) == 0)
{
lean_object* v_a_462_; lean_object* v_a_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_471_; 
v_a_462_ = lean_ctor_get(v___x_461_, 0);
v_a_463_ = lean_ctor_get(v___x_461_, 1);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_461_);
if (v_isSharedCheck_471_ == 0)
{
v___x_465_ = v___x_461_;
v_isShared_466_ = v_isSharedCheck_471_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_a_463_);
lean_inc(v_a_462_);
lean_dec(v___x_461_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_471_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_467_; lean_object* v___x_469_; 
v___x_467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_467_, 0, v_a_462_);
lean_ctor_set(v___x_467_, 1, v___y_458_);
if (v_isShared_466_ == 0)
{
lean_ctor_set(v___x_465_, 0, v___x_467_);
v___x_469_ = v___x_465_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v___x_467_);
lean_ctor_set(v_reuseFailAlloc_470_, 1, v_a_463_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
}
else
{
lean_object* v_a_472_; lean_object* v_a_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_480_; 
lean_dec_ref(v___y_458_);
v_a_472_ = lean_ctor_get(v___x_461_, 0);
v_a_473_ = lean_ctor_get(v___x_461_, 1);
v_isSharedCheck_480_ = !lean_is_exclusive(v___x_461_);
if (v_isSharedCheck_480_ == 0)
{
v___x_475_ = v___x_461_;
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_a_473_);
lean_inc(v_a_472_);
lean_dec(v___x_461_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_478_; 
if (v_isShared_476_ == 0)
{
v___x_478_ = v___x_475_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_a_472_);
lean_ctor_set(v_reuseFailAlloc_479_, 1, v_a_473_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__6___boxed(lean_object* v_d_492_, lean_object* v_e_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_){
_start:
{
uint8_t v___y_26666__boxed_498_; lean_object* v_res_499_; 
v___y_26666__boxed_498_ = lean_unbox(v___y_495_);
v_res_499_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__6(v_d_492_, v_e_493_, v___y_494_, v___y_26666__boxed_498_, v___y_496_, v___y_497_);
lean_dec_ref(v___y_496_);
return v_res_499_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__3(void){
_start:
{
lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_503_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__2));
v___x_504_ = lean_unsigned_to_nat(67u);
v___x_505_ = lean_unsigned_to_nat(35u);
v___x_506_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__1));
v___x_507_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__0));
v___x_508_ = l_mkPanicMessageWithDecl(v___x_507_, v___x_506_, v___x_505_, v___x_504_, v___x_503_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1(lean_object* v_beginIdx_509_, lean_object* v_n_510_, lean_object* v_subst_511_, lean_object* v_e_512_, lean_object* v_offset_513_, lean_object* v_a_514_, uint8_t v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_){
_start:
{
switch(lean_obj_tag(v_e_512_))
{
case 5:
{
lean_object* v_fn_518_; lean_object* v_arg_519_; lean_object* v___x_520_; 
v_fn_518_ = lean_ctor_get(v_e_512_, 0);
v_arg_519_ = lean_ctor_get(v_e_512_, 1);
lean_inc(v_offset_513_);
lean_inc_ref(v_fn_518_);
v___x_520_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(v_beginIdx_509_, v_n_510_, v_subst_511_, v_fn_518_, v_offset_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_);
if (lean_obj_tag(v___x_520_) == 0)
{
lean_object* v_a_521_; lean_object* v_a_522_; lean_object* v_fst_523_; lean_object* v_snd_524_; lean_object* v___x_525_; 
v_a_521_ = lean_ctor_get(v___x_520_, 0);
lean_inc(v_a_521_);
v_a_522_ = lean_ctor_get(v___x_520_, 1);
lean_inc(v_a_522_);
lean_dec_ref_known(v___x_520_, 2);
v_fst_523_ = lean_ctor_get(v_a_521_, 0);
lean_inc(v_fst_523_);
v_snd_524_ = lean_ctor_get(v_a_521_, 1);
lean_inc(v_snd_524_);
lean_dec(v_a_521_);
lean_inc_ref(v_arg_519_);
v___x_525_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(v_beginIdx_509_, v_n_510_, v_subst_511_, v_arg_519_, v_offset_513_, v_snd_524_, v_a_515_, v_a_516_, v_a_522_);
if (lean_obj_tag(v___x_525_) == 0)
{
lean_object* v_a_526_; lean_object* v_a_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_552_; 
v_a_526_ = lean_ctor_get(v___x_525_, 0);
v_a_527_ = lean_ctor_get(v___x_525_, 1);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_552_ == 0)
{
v___x_529_ = v___x_525_;
v_isShared_530_ = v_isSharedCheck_552_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_a_527_);
lean_inc(v_a_526_);
lean_dec(v___x_525_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_552_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v_fst_531_; lean_object* v_snd_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_551_; 
v_fst_531_ = lean_ctor_get(v_a_526_, 0);
v_snd_532_ = lean_ctor_get(v_a_526_, 1);
v_isSharedCheck_551_ = !lean_is_exclusive(v_a_526_);
if (v_isSharedCheck_551_ == 0)
{
v___x_534_ = v_a_526_;
v_isShared_535_ = v_isSharedCheck_551_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_snd_532_);
lean_inc(v_fst_531_);
lean_dec(v_a_526_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_551_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
uint8_t v___y_537_; size_t v___x_545_; size_t v___x_546_; uint8_t v___x_547_; 
v___x_545_ = lean_ptr_addr(v_fn_518_);
v___x_546_ = lean_ptr_addr(v_fst_523_);
v___x_547_ = lean_usize_dec_eq(v___x_545_, v___x_546_);
if (v___x_547_ == 0)
{
v___y_537_ = v___x_547_;
goto v___jp_536_;
}
else
{
size_t v___x_548_; size_t v___x_549_; uint8_t v___x_550_; 
v___x_548_ = lean_ptr_addr(v_arg_519_);
v___x_549_ = lean_ptr_addr(v_fst_531_);
v___x_550_ = lean_usize_dec_eq(v___x_548_, v___x_549_);
v___y_537_ = v___x_550_;
goto v___jp_536_;
}
v___jp_536_:
{
if (v___y_537_ == 0)
{
lean_object* v___x_538_; 
lean_del_object(v___x_534_);
lean_del_object(v___x_529_);
lean_dec_ref_known(v_e_512_, 2);
v___x_538_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__2(v_fst_523_, v_fst_531_, v_snd_532_, v_a_515_, v_a_516_, v_a_527_);
return v___x_538_;
}
else
{
lean_object* v___x_540_; 
lean_dec(v_fst_531_);
lean_dec(v_fst_523_);
if (v_isShared_535_ == 0)
{
lean_ctor_set(v___x_534_, 0, v_e_512_);
v___x_540_ = v___x_534_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_e_512_);
lean_ctor_set(v_reuseFailAlloc_544_, 1, v_snd_532_);
v___x_540_ = v_reuseFailAlloc_544_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
lean_object* v___x_542_; 
if (v_isShared_530_ == 0)
{
lean_ctor_set(v___x_529_, 0, v___x_540_);
v___x_542_ = v___x_529_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v___x_540_);
lean_ctor_set(v_reuseFailAlloc_543_, 1, v_a_527_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_523_);
lean_dec_ref_known(v_e_512_, 2);
return v___x_525_;
}
}
else
{
lean_dec_ref_known(v_e_512_, 2);
lean_dec(v_offset_513_);
return v___x_520_;
}
}
case 6:
{
lean_object* v_binderName_553_; lean_object* v_binderType_554_; lean_object* v_body_555_; uint8_t v_binderInfo_556_; lean_object* v___x_557_; 
v_binderName_553_ = lean_ctor_get(v_e_512_, 0);
v_binderType_554_ = lean_ctor_get(v_e_512_, 1);
v_body_555_ = lean_ctor_get(v_e_512_, 2);
v_binderInfo_556_ = lean_ctor_get_uint8(v_e_512_, sizeof(void*)*3 + 8);
lean_inc(v_offset_513_);
lean_inc_ref(v_binderType_554_);
v___x_557_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(v_beginIdx_509_, v_n_510_, v_subst_511_, v_binderType_554_, v_offset_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_);
if (lean_obj_tag(v___x_557_) == 0)
{
lean_object* v_a_558_; lean_object* v_a_559_; lean_object* v_fst_560_; lean_object* v_snd_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v_a_558_ = lean_ctor_get(v___x_557_, 0);
lean_inc(v_a_558_);
v_a_559_ = lean_ctor_get(v___x_557_, 1);
lean_inc(v_a_559_);
lean_dec_ref_known(v___x_557_, 2);
v_fst_560_ = lean_ctor_get(v_a_558_, 0);
lean_inc(v_fst_560_);
v_snd_561_ = lean_ctor_get(v_a_558_, 1);
lean_inc(v_snd_561_);
lean_dec(v_a_558_);
v___x_562_ = lean_unsigned_to_nat(1u);
v___x_563_ = lean_nat_add(v_offset_513_, v___x_562_);
lean_dec(v_offset_513_);
lean_inc_ref(v_body_555_);
v___x_564_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(v_beginIdx_509_, v_n_510_, v_subst_511_, v_body_555_, v___x_563_, v_snd_561_, v_a_515_, v_a_516_, v_a_559_);
if (lean_obj_tag(v___x_564_) == 0)
{
lean_object* v_a_565_; lean_object* v_a_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_591_; 
v_a_565_ = lean_ctor_get(v___x_564_, 0);
v_a_566_ = lean_ctor_get(v___x_564_, 1);
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_591_ == 0)
{
v___x_568_ = v___x_564_;
v_isShared_569_ = v_isSharedCheck_591_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_a_566_);
lean_inc(v_a_565_);
lean_dec(v___x_564_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_591_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v_fst_570_; lean_object* v_snd_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_590_; 
v_fst_570_ = lean_ctor_get(v_a_565_, 0);
v_snd_571_ = lean_ctor_get(v_a_565_, 1);
v_isSharedCheck_590_ = !lean_is_exclusive(v_a_565_);
if (v_isSharedCheck_590_ == 0)
{
v___x_573_ = v_a_565_;
v_isShared_574_ = v_isSharedCheck_590_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_snd_571_);
lean_inc(v_fst_570_);
lean_dec(v_a_565_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_590_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
uint8_t v___y_576_; size_t v___x_584_; size_t v___x_585_; uint8_t v___x_586_; 
v___x_584_ = lean_ptr_addr(v_binderType_554_);
v___x_585_ = lean_ptr_addr(v_fst_560_);
v___x_586_ = lean_usize_dec_eq(v___x_584_, v___x_585_);
if (v___x_586_ == 0)
{
v___y_576_ = v___x_586_;
goto v___jp_575_;
}
else
{
size_t v___x_587_; size_t v___x_588_; uint8_t v___x_589_; 
v___x_587_ = lean_ptr_addr(v_body_555_);
v___x_588_ = lean_ptr_addr(v_fst_570_);
v___x_589_ = lean_usize_dec_eq(v___x_587_, v___x_588_);
v___y_576_ = v___x_589_;
goto v___jp_575_;
}
v___jp_575_:
{
if (v___y_576_ == 0)
{
lean_object* v___x_577_; 
lean_inc(v_binderName_553_);
lean_del_object(v___x_573_);
lean_del_object(v___x_568_);
lean_dec_ref_known(v_e_512_, 3);
v___x_577_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__3(v_binderName_553_, v_binderInfo_556_, v_fst_560_, v_fst_570_, v_snd_571_, v_a_515_, v_a_516_, v_a_566_);
return v___x_577_;
}
else
{
lean_object* v___x_579_; 
lean_dec(v_fst_570_);
lean_dec(v_fst_560_);
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 0, v_e_512_);
v___x_579_ = v___x_573_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_e_512_);
lean_ctor_set(v_reuseFailAlloc_583_, 1, v_snd_571_);
v___x_579_ = v_reuseFailAlloc_583_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
lean_object* v___x_581_; 
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 0, v___x_579_);
v___x_581_ = v___x_568_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v___x_579_);
lean_ctor_set(v_reuseFailAlloc_582_, 1, v_a_566_);
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
}
else
{
lean_dec(v_fst_560_);
lean_dec_ref_known(v_e_512_, 3);
return v___x_564_;
}
}
else
{
lean_dec_ref_known(v_e_512_, 3);
lean_dec(v_offset_513_);
return v___x_557_;
}
}
case 7:
{
lean_object* v_binderName_592_; lean_object* v_binderType_593_; lean_object* v_body_594_; uint8_t v_binderInfo_595_; lean_object* v___x_596_; 
v_binderName_592_ = lean_ctor_get(v_e_512_, 0);
v_binderType_593_ = lean_ctor_get(v_e_512_, 1);
v_body_594_ = lean_ctor_get(v_e_512_, 2);
v_binderInfo_595_ = lean_ctor_get_uint8(v_e_512_, sizeof(void*)*3 + 8);
lean_inc(v_offset_513_);
lean_inc_ref(v_binderType_593_);
v___x_596_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(v_beginIdx_509_, v_n_510_, v_subst_511_, v_binderType_593_, v_offset_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_);
if (lean_obj_tag(v___x_596_) == 0)
{
lean_object* v_a_597_; lean_object* v_a_598_; lean_object* v_fst_599_; lean_object* v_snd_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v_a_597_ = lean_ctor_get(v___x_596_, 0);
lean_inc(v_a_597_);
v_a_598_ = lean_ctor_get(v___x_596_, 1);
lean_inc(v_a_598_);
lean_dec_ref_known(v___x_596_, 2);
v_fst_599_ = lean_ctor_get(v_a_597_, 0);
lean_inc(v_fst_599_);
v_snd_600_ = lean_ctor_get(v_a_597_, 1);
lean_inc(v_snd_600_);
lean_dec(v_a_597_);
v___x_601_ = lean_unsigned_to_nat(1u);
v___x_602_ = lean_nat_add(v_offset_513_, v___x_601_);
lean_dec(v_offset_513_);
lean_inc_ref(v_body_594_);
v___x_603_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(v_beginIdx_509_, v_n_510_, v_subst_511_, v_body_594_, v___x_602_, v_snd_600_, v_a_515_, v_a_516_, v_a_598_);
if (lean_obj_tag(v___x_603_) == 0)
{
lean_object* v_a_604_; lean_object* v_a_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_630_; 
v_a_604_ = lean_ctor_get(v___x_603_, 0);
v_a_605_ = lean_ctor_get(v___x_603_, 1);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_603_);
if (v_isSharedCheck_630_ == 0)
{
v___x_607_ = v___x_603_;
v_isShared_608_ = v_isSharedCheck_630_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_a_605_);
lean_inc(v_a_604_);
lean_dec(v___x_603_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_630_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v_fst_609_; lean_object* v_snd_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_629_; 
v_fst_609_ = lean_ctor_get(v_a_604_, 0);
v_snd_610_ = lean_ctor_get(v_a_604_, 1);
v_isSharedCheck_629_ = !lean_is_exclusive(v_a_604_);
if (v_isSharedCheck_629_ == 0)
{
v___x_612_ = v_a_604_;
v_isShared_613_ = v_isSharedCheck_629_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_snd_610_);
lean_inc(v_fst_609_);
lean_dec(v_a_604_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_629_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
uint8_t v___y_615_; size_t v___x_623_; size_t v___x_624_; uint8_t v___x_625_; 
v___x_623_ = lean_ptr_addr(v_binderType_593_);
v___x_624_ = lean_ptr_addr(v_fst_599_);
v___x_625_ = lean_usize_dec_eq(v___x_623_, v___x_624_);
if (v___x_625_ == 0)
{
v___y_615_ = v___x_625_;
goto v___jp_614_;
}
else
{
size_t v___x_626_; size_t v___x_627_; uint8_t v___x_628_; 
v___x_626_ = lean_ptr_addr(v_body_594_);
v___x_627_ = lean_ptr_addr(v_fst_609_);
v___x_628_ = lean_usize_dec_eq(v___x_626_, v___x_627_);
v___y_615_ = v___x_628_;
goto v___jp_614_;
}
v___jp_614_:
{
if (v___y_615_ == 0)
{
lean_object* v___x_616_; 
lean_inc(v_binderName_592_);
lean_del_object(v___x_612_);
lean_del_object(v___x_607_);
lean_dec_ref_known(v_e_512_, 3);
v___x_616_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__4(v_binderName_592_, v_binderInfo_595_, v_fst_599_, v_fst_609_, v_snd_610_, v_a_515_, v_a_516_, v_a_605_);
return v___x_616_;
}
else
{
lean_object* v___x_618_; 
lean_dec(v_fst_609_);
lean_dec(v_fst_599_);
if (v_isShared_613_ == 0)
{
lean_ctor_set(v___x_612_, 0, v_e_512_);
v___x_618_ = v___x_612_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_e_512_);
lean_ctor_set(v_reuseFailAlloc_622_, 1, v_snd_610_);
v___x_618_ = v_reuseFailAlloc_622_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
lean_object* v___x_620_; 
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 0, v___x_618_);
v___x_620_ = v___x_607_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v___x_618_);
lean_ctor_set(v_reuseFailAlloc_621_, 1, v_a_605_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_599_);
lean_dec_ref_known(v_e_512_, 3);
return v___x_603_;
}
}
else
{
lean_dec_ref_known(v_e_512_, 3);
lean_dec(v_offset_513_);
return v___x_596_;
}
}
case 8:
{
lean_object* v_declName_631_; lean_object* v_type_632_; lean_object* v_value_633_; lean_object* v_body_634_; uint8_t v_nondep_635_; lean_object* v___x_636_; 
v_declName_631_ = lean_ctor_get(v_e_512_, 0);
v_type_632_ = lean_ctor_get(v_e_512_, 1);
v_value_633_ = lean_ctor_get(v_e_512_, 2);
v_body_634_ = lean_ctor_get(v_e_512_, 3);
v_nondep_635_ = lean_ctor_get_uint8(v_e_512_, sizeof(void*)*4 + 8);
lean_inc(v_offset_513_);
lean_inc_ref(v_type_632_);
v___x_636_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(v_beginIdx_509_, v_n_510_, v_subst_511_, v_type_632_, v_offset_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_);
if (lean_obj_tag(v___x_636_) == 0)
{
lean_object* v_a_637_; lean_object* v_a_638_; lean_object* v_fst_639_; lean_object* v_snd_640_; lean_object* v___x_641_; 
v_a_637_ = lean_ctor_get(v___x_636_, 0);
lean_inc(v_a_637_);
v_a_638_ = lean_ctor_get(v___x_636_, 1);
lean_inc(v_a_638_);
lean_dec_ref_known(v___x_636_, 2);
v_fst_639_ = lean_ctor_get(v_a_637_, 0);
lean_inc(v_fst_639_);
v_snd_640_ = lean_ctor_get(v_a_637_, 1);
lean_inc(v_snd_640_);
lean_dec(v_a_637_);
lean_inc(v_offset_513_);
lean_inc_ref(v_value_633_);
v___x_641_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(v_beginIdx_509_, v_n_510_, v_subst_511_, v_value_633_, v_offset_513_, v_snd_640_, v_a_515_, v_a_516_, v_a_638_);
if (lean_obj_tag(v___x_641_) == 0)
{
lean_object* v_a_642_; lean_object* v_a_643_; lean_object* v_fst_644_; lean_object* v_snd_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v_a_642_ = lean_ctor_get(v___x_641_, 0);
lean_inc(v_a_642_);
v_a_643_ = lean_ctor_get(v___x_641_, 1);
lean_inc(v_a_643_);
lean_dec_ref_known(v___x_641_, 2);
v_fst_644_ = lean_ctor_get(v_a_642_, 0);
lean_inc(v_fst_644_);
v_snd_645_ = lean_ctor_get(v_a_642_, 1);
lean_inc(v_snd_645_);
lean_dec(v_a_642_);
v___x_646_ = lean_unsigned_to_nat(1u);
v___x_647_ = lean_nat_add(v_offset_513_, v___x_646_);
lean_dec(v_offset_513_);
lean_inc_ref(v_body_634_);
v___x_648_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(v_beginIdx_509_, v_n_510_, v_subst_511_, v_body_634_, v___x_647_, v_snd_645_, v_a_515_, v_a_516_, v_a_643_);
if (lean_obj_tag(v___x_648_) == 0)
{
lean_object* v_a_649_; lean_object* v_a_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_679_; 
v_a_649_ = lean_ctor_get(v___x_648_, 0);
v_a_650_ = lean_ctor_get(v___x_648_, 1);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_648_);
if (v_isSharedCheck_679_ == 0)
{
v___x_652_ = v___x_648_;
v_isShared_653_ = v_isSharedCheck_679_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_a_650_);
lean_inc(v_a_649_);
lean_dec(v___x_648_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_679_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v_fst_654_; lean_object* v_snd_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_678_; 
v_fst_654_ = lean_ctor_get(v_a_649_, 0);
v_snd_655_ = lean_ctor_get(v_a_649_, 1);
v_isSharedCheck_678_ = !lean_is_exclusive(v_a_649_);
if (v_isSharedCheck_678_ == 0)
{
v___x_657_ = v_a_649_;
v_isShared_658_ = v_isSharedCheck_678_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_snd_655_);
lean_inc(v_fst_654_);
lean_dec(v_a_649_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_678_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
uint8_t v___y_660_; size_t v___x_672_; size_t v___x_673_; uint8_t v___x_674_; 
v___x_672_ = lean_ptr_addr(v_type_632_);
v___x_673_ = lean_ptr_addr(v_fst_639_);
v___x_674_ = lean_usize_dec_eq(v___x_672_, v___x_673_);
if (v___x_674_ == 0)
{
v___y_660_ = v___x_674_;
goto v___jp_659_;
}
else
{
size_t v___x_675_; size_t v___x_676_; uint8_t v___x_677_; 
v___x_675_ = lean_ptr_addr(v_value_633_);
v___x_676_ = lean_ptr_addr(v_fst_644_);
v___x_677_ = lean_usize_dec_eq(v___x_675_, v___x_676_);
v___y_660_ = v___x_677_;
goto v___jp_659_;
}
v___jp_659_:
{
if (v___y_660_ == 0)
{
lean_object* v___x_661_; 
lean_inc(v_declName_631_);
lean_del_object(v___x_657_);
lean_del_object(v___x_652_);
lean_dec_ref_known(v_e_512_, 4);
v___x_661_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__5(v_declName_631_, v_fst_639_, v_fst_644_, v_fst_654_, v_nondep_635_, v_snd_655_, v_a_515_, v_a_516_, v_a_650_);
return v___x_661_;
}
else
{
size_t v___x_662_; size_t v___x_663_; uint8_t v___x_664_; 
v___x_662_ = lean_ptr_addr(v_body_634_);
v___x_663_ = lean_ptr_addr(v_fst_654_);
v___x_664_ = lean_usize_dec_eq(v___x_662_, v___x_663_);
if (v___x_664_ == 0)
{
lean_object* v___x_665_; 
lean_inc(v_declName_631_);
lean_del_object(v___x_657_);
lean_del_object(v___x_652_);
lean_dec_ref_known(v_e_512_, 4);
v___x_665_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__5(v_declName_631_, v_fst_639_, v_fst_644_, v_fst_654_, v_nondep_635_, v_snd_655_, v_a_515_, v_a_516_, v_a_650_);
return v___x_665_;
}
else
{
lean_object* v___x_667_; 
lean_dec(v_fst_654_);
lean_dec(v_fst_644_);
lean_dec(v_fst_639_);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 0, v_e_512_);
v___x_667_ = v___x_657_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_e_512_);
lean_ctor_set(v_reuseFailAlloc_671_, 1, v_snd_655_);
v___x_667_ = v_reuseFailAlloc_671_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
lean_object* v___x_669_; 
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 0, v___x_667_);
v___x_669_ = v___x_652_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v___x_667_);
lean_ctor_set(v_reuseFailAlloc_670_, 1, v_a_650_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
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
lean_dec(v_fst_644_);
lean_dec(v_fst_639_);
lean_dec_ref_known(v_e_512_, 4);
return v___x_648_;
}
}
else
{
lean_dec(v_fst_639_);
lean_dec_ref_known(v_e_512_, 4);
lean_dec(v_offset_513_);
return v___x_641_;
}
}
else
{
lean_dec_ref_known(v_e_512_, 4);
lean_dec(v_offset_513_);
return v___x_636_;
}
}
case 10:
{
lean_object* v_data_680_; lean_object* v_expr_681_; lean_object* v___x_682_; 
v_data_680_ = lean_ctor_get(v_e_512_, 0);
v_expr_681_ = lean_ctor_get(v_e_512_, 1);
lean_inc_ref(v_expr_681_);
v___x_682_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(v_beginIdx_509_, v_n_510_, v_subst_511_, v_expr_681_, v_offset_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_);
if (lean_obj_tag(v___x_682_) == 0)
{
lean_object* v_a_683_; lean_object* v_a_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_704_; 
v_a_683_ = lean_ctor_get(v___x_682_, 0);
v_a_684_ = lean_ctor_get(v___x_682_, 1);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_682_);
if (v_isSharedCheck_704_ == 0)
{
v___x_686_ = v___x_682_;
v_isShared_687_ = v_isSharedCheck_704_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_a_684_);
lean_inc(v_a_683_);
lean_dec(v___x_682_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_704_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v_fst_688_; lean_object* v_snd_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_703_; 
v_fst_688_ = lean_ctor_get(v_a_683_, 0);
v_snd_689_ = lean_ctor_get(v_a_683_, 1);
v_isSharedCheck_703_ = !lean_is_exclusive(v_a_683_);
if (v_isSharedCheck_703_ == 0)
{
v___x_691_ = v_a_683_;
v_isShared_692_ = v_isSharedCheck_703_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_snd_689_);
lean_inc(v_fst_688_);
lean_dec(v_a_683_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_703_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
size_t v___x_693_; size_t v___x_694_; uint8_t v___x_695_; 
v___x_693_ = lean_ptr_addr(v_expr_681_);
v___x_694_ = lean_ptr_addr(v_fst_688_);
v___x_695_ = lean_usize_dec_eq(v___x_693_, v___x_694_);
if (v___x_695_ == 0)
{
lean_object* v___x_696_; 
lean_inc(v_data_680_);
lean_del_object(v___x_691_);
lean_del_object(v___x_686_);
lean_dec_ref_known(v_e_512_, 2);
v___x_696_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__6(v_data_680_, v_fst_688_, v_snd_689_, v_a_515_, v_a_516_, v_a_684_);
return v___x_696_;
}
else
{
lean_object* v___x_698_; 
lean_dec(v_fst_688_);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 0, v_e_512_);
v___x_698_ = v___x_691_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_e_512_);
lean_ctor_set(v_reuseFailAlloc_702_, 1, v_snd_689_);
v___x_698_ = v_reuseFailAlloc_702_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
lean_object* v___x_700_; 
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 0, v___x_698_);
v___x_700_ = v___x_686_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v___x_698_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v_a_684_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_512_, 2);
return v___x_682_;
}
}
case 11:
{
lean_object* v_typeName_705_; lean_object* v_idx_706_; lean_object* v_struct_707_; lean_object* v___x_708_; 
v_typeName_705_ = lean_ctor_get(v_e_512_, 0);
v_idx_706_ = lean_ctor_get(v_e_512_, 1);
v_struct_707_ = lean_ctor_get(v_e_512_, 2);
lean_inc_ref(v_struct_707_);
v___x_708_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(v_beginIdx_509_, v_n_510_, v_subst_511_, v_struct_707_, v_offset_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_);
if (lean_obj_tag(v___x_708_) == 0)
{
lean_object* v_a_709_; lean_object* v_a_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_730_; 
v_a_709_ = lean_ctor_get(v___x_708_, 0);
v_a_710_ = lean_ctor_get(v___x_708_, 1);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_730_ == 0)
{
v___x_712_ = v___x_708_;
v_isShared_713_ = v_isSharedCheck_730_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_a_710_);
lean_inc(v_a_709_);
lean_dec(v___x_708_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_730_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v_fst_714_; lean_object* v_snd_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_729_; 
v_fst_714_ = lean_ctor_get(v_a_709_, 0);
v_snd_715_ = lean_ctor_get(v_a_709_, 1);
v_isSharedCheck_729_ = !lean_is_exclusive(v_a_709_);
if (v_isSharedCheck_729_ == 0)
{
v___x_717_ = v_a_709_;
v_isShared_718_ = v_isSharedCheck_729_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_snd_715_);
lean_inc(v_fst_714_);
lean_dec(v_a_709_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_729_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
size_t v___x_719_; size_t v___x_720_; uint8_t v___x_721_; 
v___x_719_ = lean_ptr_addr(v_struct_707_);
v___x_720_ = lean_ptr_addr(v_fst_714_);
v___x_721_ = lean_usize_dec_eq(v___x_719_, v___x_720_);
if (v___x_721_ == 0)
{
lean_object* v___x_722_; 
lean_inc(v_idx_706_);
lean_inc(v_typeName_705_);
lean_del_object(v___x_717_);
lean_del_object(v___x_712_);
lean_dec_ref_known(v_e_512_, 3);
v___x_722_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__7(v_typeName_705_, v_idx_706_, v_fst_714_, v_snd_715_, v_a_515_, v_a_516_, v_a_710_);
return v___x_722_;
}
else
{
lean_object* v___x_724_; 
lean_dec(v_fst_714_);
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 0, v_e_512_);
v___x_724_ = v___x_717_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_e_512_);
lean_ctor_set(v_reuseFailAlloc_728_, 1, v_snd_715_);
v___x_724_ = v_reuseFailAlloc_728_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
lean_object* v___x_726_; 
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 0, v___x_724_);
v___x_726_ = v___x_712_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v___x_724_);
lean_ctor_set(v_reuseFailAlloc_727_, 1, v_a_710_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_512_, 3);
return v___x_708_;
}
}
default: 
{
lean_object* v___x_731_; lean_object* v___x_732_; 
lean_dec(v_offset_513_);
lean_dec_ref(v_e_512_);
v___x_731_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__3);
v___x_732_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8(v___x_731_, v_a_514_, v_a_515_, v_a_516_, v_a_517_);
return v___x_732_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(lean_object* v_beginIdx_733_, lean_object* v_n_734_, lean_object* v_subst_735_, lean_object* v_e_736_, lean_object* v_offset_737_, lean_object* v_a_738_, uint8_t v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_){
_start:
{
lean_object* v_key_742_; lean_object* v___x_743_; 
lean_inc(v_offset_737_);
lean_inc_ref(v_e_736_);
v_key_742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_742_, 0, v_e_736_);
lean_ctor_set(v_key_742_, 1, v_offset_737_);
v___x_743_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3___redArg(v_a_738_, v_key_742_);
if (lean_obj_tag(v___x_743_) == 1)
{
lean_object* v_val_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
lean_dec_ref_known(v_key_742_, 2);
lean_dec(v_offset_737_);
lean_dec_ref(v_e_736_);
v_val_744_ = lean_ctor_get(v___x_743_, 0);
lean_inc(v_val_744_);
lean_dec_ref_known(v___x_743_, 1);
v___x_745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_745_, 0, v_val_744_);
lean_ctor_set(v___x_745_, 1, v_a_738_);
v___x_746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_746_, 0, v___x_745_);
lean_ctor_set(v___x_746_, 1, v_a_741_);
return v___x_746_;
}
else
{
lean_object* v_s_u2081_747_; 
lean_dec(v___x_743_);
v_s_u2081_747_ = lean_nat_add(v_beginIdx_733_, v_offset_737_);
switch(lean_obj_tag(v_e_736_))
{
case 0:
{
lean_object* v_deBruijnIndex_748_; uint8_t v___x_749_; 
v_deBruijnIndex_748_ = lean_ctor_get(v_e_736_, 0);
v___x_749_ = lean_nat_dec_le(v_s_u2081_747_, v_deBruijnIndex_748_);
lean_dec(v_s_u2081_747_);
if (v___x_749_ == 0)
{
lean_object* v___x_750_; 
lean_dec(v_offset_737_);
v___x_750_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_742_, v_e_736_, v_a_738_, v_a_739_, v_a_740_, v_a_741_);
return v___x_750_;
}
else
{
lean_object* v___x_751_; uint8_t v___x_752_; 
lean_inc(v_deBruijnIndex_748_);
lean_dec_ref_known(v_e_736_, 1);
v___x_751_ = lean_nat_add(v_offset_737_, v_n_734_);
v___x_752_ = lean_nat_dec_lt(v_deBruijnIndex_748_, v___x_751_);
lean_dec(v___x_751_);
if (v___x_752_ == 0)
{
lean_object* v___x_753_; lean_object* v___x_754_; 
lean_dec(v_offset_737_);
v___x_753_ = lean_nat_sub(v_deBruijnIndex_748_, v_n_734_);
lean_dec(v_deBruijnIndex_748_);
v___x_754_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___redArg(v___x_753_, v_a_741_);
if (lean_obj_tag(v___x_754_) == 0)
{
lean_object* v_a_755_; lean_object* v_a_756_; lean_object* v___x_757_; 
v_a_755_ = lean_ctor_get(v___x_754_, 0);
lean_inc(v_a_755_);
v_a_756_ = lean_ctor_get(v___x_754_, 1);
lean_inc(v_a_756_);
lean_dec_ref_known(v___x_754_, 2);
v___x_757_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_742_, v_a_755_, v_a_738_, v_a_739_, v_a_740_, v_a_756_);
return v___x_757_;
}
else
{
lean_object* v_a_758_; lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_766_; 
lean_dec_ref_known(v_key_742_, 2);
lean_dec_ref(v_a_738_);
v_a_758_ = lean_ctor_get(v___x_754_, 0);
v_a_759_ = lean_ctor_get(v___x_754_, 1);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_754_);
if (v_isSharedCheck_766_ == 0)
{
v___x_761_ = v___x_754_;
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_inc(v_a_758_);
lean_dec(v___x_754_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_764_; 
if (v_isShared_762_ == 0)
{
v___x_764_ = v___x_761_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_a_758_);
lean_ctor_set(v_reuseFailAlloc_765_, 1, v_a_759_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
}
else
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v_v_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_767_ = lean_nat_sub(v_deBruijnIndex_748_, v_offset_737_);
lean_dec(v_deBruijnIndex_748_);
v___x_768_ = lean_nat_sub(v_n_734_, v___x_767_);
lean_dec(v___x_767_);
v___x_769_ = lean_unsigned_to_nat(1u);
v___x_770_ = lean_nat_sub(v___x_768_, v___x_769_);
lean_dec(v___x_768_);
v_v_771_ = lean_array_fget_borrowed(v_subst_735_, v___x_770_);
lean_dec(v___x_770_);
v___x_772_ = lean_unsigned_to_nat(0u);
lean_inc(v_v_771_);
v___x_773_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(v_v_771_, v___x_772_, v_offset_737_, v_a_739_, v_a_740_, v_a_741_);
lean_dec(v_offset_737_);
if (lean_obj_tag(v___x_773_) == 0)
{
lean_object* v_a_774_; lean_object* v_a_775_; lean_object* v___x_776_; 
v_a_774_ = lean_ctor_get(v___x_773_, 0);
lean_inc(v_a_774_);
v_a_775_ = lean_ctor_get(v___x_773_, 1);
lean_inc(v_a_775_);
lean_dec_ref_known(v___x_773_, 2);
v___x_776_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_742_, v_a_774_, v_a_738_, v_a_739_, v_a_740_, v_a_775_);
return v___x_776_;
}
else
{
lean_object* v_a_777_; lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_785_; 
lean_dec_ref_known(v_key_742_, 2);
lean_dec_ref(v_a_738_);
v_a_777_ = lean_ctor_get(v___x_773_, 0);
v_a_778_ = lean_ctor_get(v___x_773_, 1);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_785_ == 0)
{
v___x_780_ = v___x_773_;
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_inc(v_a_777_);
lean_dec(v___x_773_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_783_; 
if (v_isShared_781_ == 0)
{
v___x_783_ = v___x_780_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_a_777_);
lean_ctor_set(v_reuseFailAlloc_784_, 1, v_a_778_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
}
}
}
case 9:
{
lean_object* v___x_786_; 
lean_dec(v_s_u2081_747_);
lean_dec(v_offset_737_);
v___x_786_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_742_, v_e_736_, v_a_738_, v_a_739_, v_a_740_, v_a_741_);
return v___x_786_;
}
case 2:
{
lean_object* v___x_787_; 
lean_dec(v_s_u2081_747_);
lean_dec(v_offset_737_);
v___x_787_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_742_, v_e_736_, v_a_738_, v_a_739_, v_a_740_, v_a_741_);
return v___x_787_;
}
case 1:
{
lean_object* v___x_788_; 
lean_dec(v_s_u2081_747_);
lean_dec(v_offset_737_);
v___x_788_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_742_, v_e_736_, v_a_738_, v_a_739_, v_a_740_, v_a_741_);
return v___x_788_;
}
case 4:
{
lean_object* v___x_789_; 
lean_dec(v_s_u2081_747_);
lean_dec(v_offset_737_);
v___x_789_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_742_, v_e_736_, v_a_738_, v_a_739_, v_a_740_, v_a_741_);
return v___x_789_;
}
case 3:
{
lean_object* v___x_790_; 
lean_dec(v_s_u2081_747_);
lean_dec(v_offset_737_);
v___x_790_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_742_, v_e_736_, v_a_738_, v_a_739_, v_a_740_, v_a_741_);
return v___x_790_;
}
default: 
{
lean_object* v___x_791_; uint8_t v___x_792_; 
v___x_791_ = l_Lean_Expr_looseBVarRange(v_e_736_);
v___x_792_ = lean_nat_dec_le(v___x_791_, v_s_u2081_747_);
lean_dec(v_s_u2081_747_);
lean_dec(v___x_791_);
if (v___x_792_ == 0)
{
switch(lean_obj_tag(v_e_736_))
{
case 9:
{
lean_object* v___x_793_; 
lean_dec(v_offset_737_);
v___x_793_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_742_, v_e_736_, v_a_738_, v_a_739_, v_a_740_, v_a_741_);
return v___x_793_;
}
case 2:
{
lean_object* v___x_794_; 
lean_dec(v_offset_737_);
v___x_794_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_742_, v_e_736_, v_a_738_, v_a_739_, v_a_740_, v_a_741_);
return v___x_794_;
}
case 0:
{
lean_object* v___x_795_; 
lean_dec(v_offset_737_);
v___x_795_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_742_, v_e_736_, v_a_738_, v_a_739_, v_a_740_, v_a_741_);
return v___x_795_;
}
case 1:
{
lean_object* v___x_796_; 
lean_dec(v_offset_737_);
v___x_796_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_742_, v_e_736_, v_a_738_, v_a_739_, v_a_740_, v_a_741_);
return v___x_796_;
}
case 4:
{
lean_object* v___x_797_; 
lean_dec(v_offset_737_);
v___x_797_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_742_, v_e_736_, v_a_738_, v_a_739_, v_a_740_, v_a_741_);
return v___x_797_;
}
case 3:
{
lean_object* v___x_798_; 
lean_dec(v_offset_737_);
v___x_798_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_742_, v_e_736_, v_a_738_, v_a_739_, v_a_740_, v_a_741_);
return v___x_798_;
}
default: 
{
lean_object* v___x_799_; 
v___x_799_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1(v_beginIdx_733_, v_n_734_, v_subst_735_, v_e_736_, v_offset_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v_a_800_; lean_object* v_a_801_; lean_object* v_fst_802_; lean_object* v_snd_803_; lean_object* v___x_804_; 
v_a_800_ = lean_ctor_get(v___x_799_, 0);
lean_inc(v_a_800_);
v_a_801_ = lean_ctor_get(v___x_799_, 1);
lean_inc(v_a_801_);
lean_dec_ref_known(v___x_799_, 2);
v_fst_802_ = lean_ctor_get(v_a_800_, 0);
lean_inc(v_fst_802_);
v_snd_803_ = lean_ctor_get(v_a_800_, 1);
lean_inc(v_snd_803_);
lean_dec(v_a_800_);
v___x_804_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_742_, v_fst_802_, v_snd_803_, v_a_739_, v_a_740_, v_a_801_);
return v___x_804_;
}
else
{
lean_dec_ref_known(v_key_742_, 2);
return v___x_799_;
}
}
}
}
else
{
lean_object* v___x_805_; 
lean_dec(v_offset_737_);
v___x_805_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_742_, v_e_736_, v_a_738_, v_a_739_, v_a_740_, v_a_741_);
return v___x_805_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1___boxed(lean_object* v_beginIdx_806_, lean_object* v_n_807_, lean_object* v_subst_808_, lean_object* v_e_809_, lean_object* v_offset_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_){
_start:
{
uint8_t v_a_boxed_815_; lean_object* v_res_816_; 
v_a_boxed_815_ = lean_unbox(v_a_812_);
v_res_816_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(v_beginIdx_806_, v_n_807_, v_subst_808_, v_e_809_, v_offset_810_, v_a_811_, v_a_boxed_815_, v_a_813_, v_a_814_);
lean_dec_ref(v_a_813_);
lean_dec_ref(v_subst_808_);
lean_dec(v_n_807_);
lean_dec(v_beginIdx_806_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___boxed(lean_object* v_beginIdx_817_, lean_object* v_n_818_, lean_object* v_subst_819_, lean_object* v_e_820_, lean_object* v_offset_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_){
_start:
{
uint8_t v_a_boxed_826_; lean_object* v_res_827_; 
v_a_boxed_826_ = lean_unbox(v_a_823_);
v_res_827_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1(v_beginIdx_817_, v_n_818_, v_subst_819_, v_e_820_, v_offset_821_, v_a_822_, v_a_boxed_826_, v_a_824_, v_a_825_);
lean_dec_ref(v_a_824_);
lean_dec_ref(v_subst_819_);
lean_dec(v_n_818_);
lean_dec(v_beginIdx_817_);
return v_res_827_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__0(void){
_start:
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_828_ = lean_box(0);
v___x_829_ = lean_unsigned_to_nat(16u);
v___x_830_ = lean_mk_array(v___x_829_, v___x_828_);
return v___x_830_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__1(void){
_start:
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_831_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__0, &l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__0_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__0);
v___x_832_ = lean_unsigned_to_nat(0u);
v___x_833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_833_, 0, v___x_832_);
lean_ctor_set(v___x_833_, 1, v___x_831_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevRangeS___lam__0(lean_object* v_e_834_, lean_object* v_beginIdx_835_, lean_object* v_n_836_, lean_object* v_subst_837_, uint8_t v_debug_838_, lean_object* v___y_839_, lean_object* v___y_840_){
_start:
{
lean_object* v___x_841_; 
v___x_841_ = lean_unsigned_to_nat(0u);
switch(lean_obj_tag(v_e_834_))
{
case 0:
{
lean_object* v_deBruijnIndex_842_; uint8_t v___x_843_; 
v_deBruijnIndex_842_ = lean_ctor_get(v_e_834_, 0);
v___x_843_ = lean_nat_dec_le(v_beginIdx_835_, v_deBruijnIndex_842_);
if (v___x_843_ == 0)
{
lean_object* v___x_844_; 
v___x_844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_844_, 0, v_e_834_);
lean_ctor_set(v___x_844_, 1, v___y_840_);
return v___x_844_;
}
else
{
uint8_t v___x_845_; 
lean_inc(v_deBruijnIndex_842_);
lean_dec_ref_known(v_e_834_, 1);
v___x_845_ = lean_nat_dec_lt(v_deBruijnIndex_842_, v_n_836_);
if (v___x_845_ == 0)
{
lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_846_ = lean_nat_sub(v_deBruijnIndex_842_, v_n_836_);
lean_dec(v_deBruijnIndex_842_);
v___x_847_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___redArg(v___x_846_, v___y_840_);
return v___x_847_;
}
else
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v_v_851_; lean_object* v___x_852_; 
v___x_848_ = lean_nat_sub(v_n_836_, v_deBruijnIndex_842_);
lean_dec(v_deBruijnIndex_842_);
v___x_849_ = lean_unsigned_to_nat(1u);
v___x_850_ = lean_nat_sub(v___x_848_, v___x_849_);
lean_dec(v___x_848_);
v_v_851_ = lean_array_fget_borrowed(v_subst_837_, v___x_850_);
lean_dec(v___x_850_);
lean_inc(v_v_851_);
v___x_852_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(v_v_851_, v___x_841_, v___x_841_, v_debug_838_, v___y_839_, v___y_840_);
return v___x_852_;
}
}
}
case 9:
{
lean_object* v___x_853_; 
v___x_853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_853_, 0, v_e_834_);
lean_ctor_set(v___x_853_, 1, v___y_840_);
return v___x_853_;
}
case 2:
{
lean_object* v___x_854_; 
v___x_854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_854_, 0, v_e_834_);
lean_ctor_set(v___x_854_, 1, v___y_840_);
return v___x_854_;
}
case 1:
{
lean_object* v___x_855_; 
v___x_855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_855_, 0, v_e_834_);
lean_ctor_set(v___x_855_, 1, v___y_840_);
return v___x_855_;
}
case 4:
{
lean_object* v___x_856_; 
v___x_856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_856_, 0, v_e_834_);
lean_ctor_set(v___x_856_, 1, v___y_840_);
return v___x_856_;
}
case 3:
{
lean_object* v___x_857_; 
v___x_857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_857_, 0, v_e_834_);
lean_ctor_set(v___x_857_, 1, v___y_840_);
return v___x_857_;
}
default: 
{
lean_object* v___x_858_; uint8_t v___x_859_; 
v___x_858_ = l_Lean_Expr_looseBVarRange(v_e_834_);
v___x_859_ = lean_nat_dec_le(v___x_858_, v_beginIdx_835_);
lean_dec(v___x_858_);
if (v___x_859_ == 0)
{
switch(lean_obj_tag(v_e_834_))
{
case 9:
{
lean_object* v___x_860_; 
v___x_860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_860_, 0, v_e_834_);
lean_ctor_set(v___x_860_, 1, v___y_840_);
return v___x_860_;
}
case 2:
{
lean_object* v___x_861_; 
v___x_861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_861_, 0, v_e_834_);
lean_ctor_set(v___x_861_, 1, v___y_840_);
return v___x_861_;
}
case 0:
{
lean_object* v___x_862_; 
v___x_862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_862_, 0, v_e_834_);
lean_ctor_set(v___x_862_, 1, v___y_840_);
return v___x_862_;
}
case 1:
{
lean_object* v___x_863_; 
v___x_863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_863_, 0, v_e_834_);
lean_ctor_set(v___x_863_, 1, v___y_840_);
return v___x_863_;
}
case 4:
{
lean_object* v___x_864_; 
v___x_864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_864_, 0, v_e_834_);
lean_ctor_set(v___x_864_, 1, v___y_840_);
return v___x_864_;
}
case 3:
{
lean_object* v___x_865_; 
v___x_865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_865_, 0, v_e_834_);
lean_ctor_set(v___x_865_, 1, v___y_840_);
return v___x_865_;
}
default: 
{
lean_object* v___x_866_; lean_object* v___x_867_; 
v___x_866_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__1, &l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__1_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__1);
v___x_867_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1(v_beginIdx_835_, v_n_836_, v_subst_837_, v_e_834_, v___x_841_, v___x_866_, v_debug_838_, v___y_839_, v___y_840_);
if (lean_obj_tag(v___x_867_) == 0)
{
lean_object* v_a_868_; lean_object* v_a_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_877_; 
v_a_868_ = lean_ctor_get(v___x_867_, 0);
v_a_869_ = lean_ctor_get(v___x_867_, 1);
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_877_ == 0)
{
v___x_871_ = v___x_867_;
v_isShared_872_ = v_isSharedCheck_877_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_a_869_);
lean_inc(v_a_868_);
lean_dec(v___x_867_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_877_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v_fst_873_; lean_object* v___x_875_; 
v_fst_873_ = lean_ctor_get(v_a_868_, 0);
lean_inc(v_fst_873_);
lean_dec(v_a_868_);
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 0, v_fst_873_);
v___x_875_ = v___x_871_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_fst_873_);
lean_ctor_set(v_reuseFailAlloc_876_, 1, v_a_869_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
else
{
lean_object* v_a_878_; lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_886_; 
v_a_878_ = lean_ctor_get(v___x_867_, 0);
v_a_879_ = lean_ctor_get(v___x_867_, 1);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_886_ == 0)
{
v___x_881_ = v___x_867_;
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_inc(v_a_878_);
lean_dec(v___x_867_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_884_; 
if (v_isShared_882_ == 0)
{
v___x_884_ = v___x_881_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_a_878_);
lean_ctor_set(v_reuseFailAlloc_885_, 1, v_a_879_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
}
}
}
else
{
lean_object* v___x_887_; 
v___x_887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_887_, 0, v_e_834_);
lean_ctor_set(v___x_887_, 1, v___y_840_);
return v___x_887_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___boxed(lean_object* v_e_888_, lean_object* v_beginIdx_889_, lean_object* v_n_890_, lean_object* v_subst_891_, lean_object* v_debug_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
uint8_t v_debug_boxed_895_; lean_object* v_res_896_; 
v_debug_boxed_895_ = lean_unbox(v_debug_892_);
v_res_896_ = l_Lean_Meta_Sym_instantiateRevRangeS___lam__0(v_e_888_, v_beginIdx_889_, v_n_890_, v_subst_891_, v_debug_boxed_895_, v___y_893_, v___y_894_);
lean_dec_ref(v___y_893_);
lean_dec_ref(v_subst_891_);
lean_dec(v_n_890_);
lean_dec(v_beginIdx_889_);
return v_res_896_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__2(void){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_899_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__2));
v___x_900_ = lean_unsigned_to_nat(16u);
v___x_901_ = lean_unsigned_to_nat(62u);
v___x_902_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__1));
v___x_903_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__0));
v___x_904_ = l_mkPanicMessageWithDecl(v___x_903_, v___x_902_, v___x_901_, v___x_900_, v___x_899_);
return v___x_904_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__5(void){
_start:
{
lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_907_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__2));
v___x_908_ = lean_unsigned_to_nat(34u);
v___x_909_ = lean_unsigned_to_nat(20u);
v___x_910_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__4));
v___x_911_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__3));
v___x_912_ = l_mkPanicMessageWithDecl(v___x_911_, v___x_910_, v___x_909_, v___x_908_, v___x_907_);
return v___x_912_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__6(void){
_start:
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_913_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__2));
v___x_914_ = lean_unsigned_to_nat(32u);
v___x_915_ = lean_unsigned_to_nat(19u);
v___x_916_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__4));
v___x_917_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__3));
v___x_918_ = l_mkPanicMessageWithDecl(v___x_917_, v___x_916_, v___x_915_, v___x_914_, v___x_913_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevRangeS(lean_object* v_e_919_, lean_object* v_beginIdx_920_, lean_object* v_endIdx_921_, lean_object* v_subst_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_){
_start:
{
uint8_t v___x_930_; 
v___x_930_ = lean_nat_dec_lt(v_endIdx_921_, v_beginIdx_920_);
if (v___x_930_ == 0)
{
lean_object* v___x_931_; uint8_t v___x_932_; 
v___x_931_ = lean_array_get_size(v_subst_922_);
v___x_932_ = lean_nat_dec_lt(v___x_931_, v_endIdx_921_);
if (v___x_932_ == 0)
{
lean_object* v___x_933_; lean_object* v___x_934_; uint8_t v_debug_935_; lean_object* v_env_936_; lean_object* v_n_937_; lean_object* v___x_938_; lean_object* v___f_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_933_ = lean_st_ref_get(v_a_924_);
v___x_934_ = lean_st_ref_get(v_a_928_);
v_debug_935_ = lean_ctor_get_uint8(v___x_933_, sizeof(void*)*11);
lean_dec(v___x_933_);
v_env_936_ = lean_ctor_get(v___x_934_, 0);
lean_inc_ref(v_env_936_);
lean_dec(v___x_934_);
v_n_937_ = lean_nat_sub(v_endIdx_921_, v_beginIdx_920_);
v___x_938_ = lean_box(v_debug_935_);
v___f_939_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___boxed), 7, 5);
lean_closure_set(v___f_939_, 0, v_e_919_);
lean_closure_set(v___f_939_, 1, v_beginIdx_920_);
lean_closure_set(v___f_939_, 2, v_n_937_);
lean_closure_set(v___f_939_, 3, v_subst_922_);
lean_closure_set(v___f_939_, 4, v___x_938_);
v___x_940_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_940_, 0, v_env_936_);
lean_ctor_set_uint8(v___x_940_, sizeof(void*)*1, v___x_932_);
lean_ctor_set_uint8(v___x_940_, sizeof(void*)*1 + 1, v___x_932_);
v___x_941_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_939_, v___x_940_, v_a_924_);
if (lean_obj_tag(v___x_941_) == 0)
{
lean_object* v_a_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_952_; 
v_a_942_ = lean_ctor_get(v___x_941_, 0);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_941_);
if (v_isSharedCheck_952_ == 0)
{
v___x_944_ = v___x_941_;
v_isShared_945_ = v_isSharedCheck_952_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_a_942_);
lean_dec(v___x_941_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_952_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
if (lean_obj_tag(v_a_942_) == 0)
{
lean_object* v___x_946_; lean_object* v___x_947_; 
lean_dec_ref_known(v_a_942_, 1);
lean_del_object(v___x_944_);
v___x_946_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__2, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__2_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__2);
v___x_947_ = l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(v___x_946_, v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_);
return v___x_947_;
}
else
{
lean_object* v_a_948_; lean_object* v___x_950_; 
v_a_948_ = lean_ctor_get(v_a_942_, 0);
lean_inc(v_a_948_);
lean_dec_ref_known(v_a_942_, 1);
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 0, v_a_948_);
v___x_950_ = v___x_944_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v_a_948_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
}
}
else
{
lean_object* v_a_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_960_; 
v_a_953_ = lean_ctor_get(v___x_941_, 0);
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
v_reuseFailAlloc_959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_a_953_);
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
else
{
lean_object* v___x_961_; lean_object* v___x_962_; 
lean_dec_ref(v_subst_922_);
lean_dec(v_beginIdx_920_);
lean_dec_ref(v_e_919_);
v___x_961_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__5, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__5_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__5);
v___x_962_ = l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(v___x_961_, v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_);
return v___x_962_;
}
}
else
{
lean_object* v___x_963_; lean_object* v___x_964_; 
lean_dec_ref(v_subst_922_);
lean_dec(v_beginIdx_920_);
lean_dec_ref(v_e_919_);
v___x_963_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__6, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__6_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__6);
v___x_964_ = l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(v___x_963_, v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_);
return v___x_964_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevRangeS___boxed(lean_object* v_e_965_, lean_object* v_beginIdx_966_, lean_object* v_endIdx_967_, lean_object* v_subst_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_e_965_, v_beginIdx_966_, v_endIdx_967_, v_subst_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
lean_dec(v_a_974_);
lean_dec_ref(v_a_973_);
lean_dec(v_a_972_);
lean_dec_ref(v_a_971_);
lean_dec(v_a_970_);
lean_dec_ref(v_a_969_);
lean_dec(v_endIdx_967_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_977_, lean_object* v_m_978_, lean_object* v_a_979_){
_start:
{
lean_object* v___x_980_; 
v___x_980_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3___redArg(v_m_978_, v_a_979_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_981_, lean_object* v_m_982_, lean_object* v_a_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3(v_00_u03b2_981_, v_m_982_, v_a_983_);
lean_dec_ref(v_a_983_);
lean_dec_ref(v_m_982_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11(lean_object* v_00_u03b2_985_, lean_object* v_a_986_, lean_object* v_x_987_){
_start:
{
lean_object* v___x_988_; 
v___x_988_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11___redArg(v_a_986_, v_x_987_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11___boxed(lean_object* v_00_u03b2_989_, lean_object* v_a_990_, lean_object* v_x_991_){
_start:
{
lean_object* v_res_992_; 
v_res_992_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11(v_00_u03b2_989_, v_a_990_, v_x_991_);
lean_dec(v_x_991_);
lean_dec_ref(v_a_990_);
return v_res_992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevS(lean_object* v_e_993_, lean_object* v_subst_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_){
_start:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1002_ = lean_unsigned_to_nat(0u);
v___x_1003_ = lean_array_get_size(v_subst_994_);
v___x_1004_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_e_993_, v___x_1002_, v___x_1003_, v_subst_994_, v_a_995_, v_a_996_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevS___boxed(lean_object* v_e_1005_, lean_object* v_subst_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l_Lean_Meta_Sym_instantiateRevS(v_e_1005_, v_subst_1006_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_);
lean_dec(v_a_1012_);
lean_dec_ref(v_a_1011_);
lean_dec(v_a_1010_);
lean_dec_ref(v_a_1009_);
lean_dec(v_a_1008_);
lean_dec_ref(v_a_1007_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1(lean_object* v_msg_1017_, uint8_t v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_){
_start:
{
lean_object* v___f_1021_; lean_object* v___f_1022_; lean_object* v___x_1023_; lean_object* v___f_1024_; lean_object* v___f_1025_; lean_object* v___f_1026_; lean_object* v___x_2919__overap_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___f_1021_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1___closed__0));
v___f_1022_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1___closed__1));
v___x_1023_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___f_1021_, v___f_1022_);
v___f_1024_ = lean_alloc_closure((void*)(l_EStateM_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1024_, 0, v___x_1023_);
v___f_1025_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1025_, 0, v___f_1024_);
v___f_1026_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1026_, 0, v___f_1025_);
v___x_2919__overap_1027_ = lean_panic_fn_borrowed(v___f_1026_, v_msg_1017_);
lean_dec_ref(v___f_1026_);
v___x_1028_ = lean_box(v___y_1018_);
lean_inc_ref(v___y_1019_);
v___x_1029_ = lean_apply_3(v___x_2919__overap_1027_, v___x_1028_, v___y_1019_, v___y_1020_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1___boxed(lean_object* v_msg_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_){
_start:
{
uint8_t v___y_3406__boxed_1034_; lean_object* v_res_1035_; 
v___y_3406__boxed_1034_ = lean_unbox(v___y_1031_);
v_res_1035_ = l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1(v_msg_1030_, v___y_3406__boxed_1034_, v___y_1032_, v___y_1033_);
lean_dec_ref(v___y_1032_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0(lean_object* v_n_1036_, lean_object* v_beginIdx_1037_, lean_object* v_subst_1038_, lean_object* v_e_1039_, lean_object* v_offset_1040_, lean_object* v_a_1041_, uint8_t v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_){
_start:
{
switch(lean_obj_tag(v_e_1039_))
{
case 5:
{
lean_object* v_fn_1045_; lean_object* v_arg_1046_; lean_object* v___x_1047_; 
v_fn_1045_ = lean_ctor_get(v_e_1039_, 0);
v_arg_1046_ = lean_ctor_get(v_e_1039_, 1);
lean_inc(v_offset_1040_);
lean_inc_ref(v_fn_1045_);
v___x_1047_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1036_, v_beginIdx_1037_, v_subst_1038_, v_fn_1045_, v_offset_1040_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_);
if (lean_obj_tag(v___x_1047_) == 0)
{
lean_object* v_a_1048_; lean_object* v_a_1049_; lean_object* v_fst_1050_; lean_object* v_snd_1051_; lean_object* v___x_1052_; 
v_a_1048_ = lean_ctor_get(v___x_1047_, 0);
lean_inc(v_a_1048_);
v_a_1049_ = lean_ctor_get(v___x_1047_, 1);
lean_inc(v_a_1049_);
lean_dec_ref_known(v___x_1047_, 2);
v_fst_1050_ = lean_ctor_get(v_a_1048_, 0);
lean_inc(v_fst_1050_);
v_snd_1051_ = lean_ctor_get(v_a_1048_, 1);
lean_inc(v_snd_1051_);
lean_dec(v_a_1048_);
lean_inc_ref(v_arg_1046_);
v___x_1052_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1036_, v_beginIdx_1037_, v_subst_1038_, v_arg_1046_, v_offset_1040_, v_snd_1051_, v_a_1042_, v_a_1043_, v_a_1049_);
if (lean_obj_tag(v___x_1052_) == 0)
{
lean_object* v_a_1053_; lean_object* v_a_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1079_; 
v_a_1053_ = lean_ctor_get(v___x_1052_, 0);
v_a_1054_ = lean_ctor_get(v___x_1052_, 1);
v_isSharedCheck_1079_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1056_ = v___x_1052_;
v_isShared_1057_ = v_isSharedCheck_1079_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_a_1054_);
lean_inc(v_a_1053_);
lean_dec(v___x_1052_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1079_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v_fst_1058_; lean_object* v_snd_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1078_; 
v_fst_1058_ = lean_ctor_get(v_a_1053_, 0);
v_snd_1059_ = lean_ctor_get(v_a_1053_, 1);
v_isSharedCheck_1078_ = !lean_is_exclusive(v_a_1053_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1061_ = v_a_1053_;
v_isShared_1062_ = v_isSharedCheck_1078_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_snd_1059_);
lean_inc(v_fst_1058_);
lean_dec(v_a_1053_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1078_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
uint8_t v___y_1064_; size_t v___x_1072_; size_t v___x_1073_; uint8_t v___x_1074_; 
v___x_1072_ = lean_ptr_addr(v_fn_1045_);
v___x_1073_ = lean_ptr_addr(v_fst_1050_);
v___x_1074_ = lean_usize_dec_eq(v___x_1072_, v___x_1073_);
if (v___x_1074_ == 0)
{
v___y_1064_ = v___x_1074_;
goto v___jp_1063_;
}
else
{
size_t v___x_1075_; size_t v___x_1076_; uint8_t v___x_1077_; 
v___x_1075_ = lean_ptr_addr(v_arg_1046_);
v___x_1076_ = lean_ptr_addr(v_fst_1058_);
v___x_1077_ = lean_usize_dec_eq(v___x_1075_, v___x_1076_);
v___y_1064_ = v___x_1077_;
goto v___jp_1063_;
}
v___jp_1063_:
{
if (v___y_1064_ == 0)
{
lean_object* v___x_1065_; 
lean_del_object(v___x_1061_);
lean_del_object(v___x_1056_);
lean_dec_ref_known(v_e_1039_, 2);
v___x_1065_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__2(v_fst_1050_, v_fst_1058_, v_snd_1059_, v_a_1042_, v_a_1043_, v_a_1054_);
return v___x_1065_;
}
else
{
lean_object* v___x_1067_; 
lean_dec(v_fst_1058_);
lean_dec(v_fst_1050_);
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 0, v_e_1039_);
v___x_1067_ = v___x_1061_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v_e_1039_);
lean_ctor_set(v_reuseFailAlloc_1071_, 1, v_snd_1059_);
v___x_1067_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
lean_object* v___x_1069_; 
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 0, v___x_1067_);
v___x_1069_ = v___x_1056_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1067_);
lean_ctor_set(v_reuseFailAlloc_1070_, 1, v_a_1054_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1050_);
lean_dec_ref_known(v_e_1039_, 2);
return v___x_1052_;
}
}
else
{
lean_dec_ref_known(v_e_1039_, 2);
lean_dec(v_offset_1040_);
return v___x_1047_;
}
}
case 6:
{
lean_object* v_binderName_1080_; lean_object* v_binderType_1081_; lean_object* v_body_1082_; uint8_t v_binderInfo_1083_; lean_object* v___x_1084_; 
v_binderName_1080_ = lean_ctor_get(v_e_1039_, 0);
v_binderType_1081_ = lean_ctor_get(v_e_1039_, 1);
v_body_1082_ = lean_ctor_get(v_e_1039_, 2);
v_binderInfo_1083_ = lean_ctor_get_uint8(v_e_1039_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1040_);
lean_inc_ref(v_binderType_1081_);
v___x_1084_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1036_, v_beginIdx_1037_, v_subst_1038_, v_binderType_1081_, v_offset_1040_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v_a_1085_; lean_object* v_a_1086_; lean_object* v_fst_1087_; lean_object* v_snd_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
lean_inc(v_a_1085_);
v_a_1086_ = lean_ctor_get(v___x_1084_, 1);
lean_inc(v_a_1086_);
lean_dec_ref_known(v___x_1084_, 2);
v_fst_1087_ = lean_ctor_get(v_a_1085_, 0);
lean_inc(v_fst_1087_);
v_snd_1088_ = lean_ctor_get(v_a_1085_, 1);
lean_inc(v_snd_1088_);
lean_dec(v_a_1085_);
v___x_1089_ = lean_unsigned_to_nat(1u);
v___x_1090_ = lean_nat_add(v_offset_1040_, v___x_1089_);
lean_dec(v_offset_1040_);
lean_inc_ref(v_body_1082_);
v___x_1091_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1036_, v_beginIdx_1037_, v_subst_1038_, v_body_1082_, v___x_1090_, v_snd_1088_, v_a_1042_, v_a_1043_, v_a_1086_);
if (lean_obj_tag(v___x_1091_) == 0)
{
lean_object* v_a_1092_; lean_object* v_a_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1118_; 
v_a_1092_ = lean_ctor_get(v___x_1091_, 0);
v_a_1093_ = lean_ctor_get(v___x_1091_, 1);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1095_ = v___x_1091_;
v_isShared_1096_ = v_isSharedCheck_1118_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_a_1093_);
lean_inc(v_a_1092_);
lean_dec(v___x_1091_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1118_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v_fst_1097_; lean_object* v_snd_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1117_; 
v_fst_1097_ = lean_ctor_get(v_a_1092_, 0);
v_snd_1098_ = lean_ctor_get(v_a_1092_, 1);
v_isSharedCheck_1117_ = !lean_is_exclusive(v_a_1092_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1100_ = v_a_1092_;
v_isShared_1101_ = v_isSharedCheck_1117_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_snd_1098_);
lean_inc(v_fst_1097_);
lean_dec(v_a_1092_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1117_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
uint8_t v___y_1103_; size_t v___x_1111_; size_t v___x_1112_; uint8_t v___x_1113_; 
v___x_1111_ = lean_ptr_addr(v_binderType_1081_);
v___x_1112_ = lean_ptr_addr(v_fst_1087_);
v___x_1113_ = lean_usize_dec_eq(v___x_1111_, v___x_1112_);
if (v___x_1113_ == 0)
{
v___y_1103_ = v___x_1113_;
goto v___jp_1102_;
}
else
{
size_t v___x_1114_; size_t v___x_1115_; uint8_t v___x_1116_; 
v___x_1114_ = lean_ptr_addr(v_body_1082_);
v___x_1115_ = lean_ptr_addr(v_fst_1097_);
v___x_1116_ = lean_usize_dec_eq(v___x_1114_, v___x_1115_);
v___y_1103_ = v___x_1116_;
goto v___jp_1102_;
}
v___jp_1102_:
{
if (v___y_1103_ == 0)
{
lean_object* v___x_1104_; 
lean_inc(v_binderName_1080_);
lean_del_object(v___x_1100_);
lean_del_object(v___x_1095_);
lean_dec_ref_known(v_e_1039_, 3);
v___x_1104_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__3(v_binderName_1080_, v_binderInfo_1083_, v_fst_1087_, v_fst_1097_, v_snd_1098_, v_a_1042_, v_a_1043_, v_a_1093_);
return v___x_1104_;
}
else
{
lean_object* v___x_1106_; 
lean_dec(v_fst_1097_);
lean_dec(v_fst_1087_);
if (v_isShared_1101_ == 0)
{
lean_ctor_set(v___x_1100_, 0, v_e_1039_);
v___x_1106_ = v___x_1100_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_e_1039_);
lean_ctor_set(v_reuseFailAlloc_1110_, 1, v_snd_1098_);
v___x_1106_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
lean_object* v___x_1108_; 
if (v_isShared_1096_ == 0)
{
lean_ctor_set(v___x_1095_, 0, v___x_1106_);
v___x_1108_ = v___x_1095_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v___x_1106_);
lean_ctor_set(v_reuseFailAlloc_1109_, 1, v_a_1093_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1087_);
lean_dec_ref_known(v_e_1039_, 3);
return v___x_1091_;
}
}
else
{
lean_dec_ref_known(v_e_1039_, 3);
lean_dec(v_offset_1040_);
return v___x_1084_;
}
}
case 7:
{
lean_object* v_binderName_1119_; lean_object* v_binderType_1120_; lean_object* v_body_1121_; uint8_t v_binderInfo_1122_; lean_object* v___x_1123_; 
v_binderName_1119_ = lean_ctor_get(v_e_1039_, 0);
v_binderType_1120_ = lean_ctor_get(v_e_1039_, 1);
v_body_1121_ = lean_ctor_get(v_e_1039_, 2);
v_binderInfo_1122_ = lean_ctor_get_uint8(v_e_1039_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1040_);
lean_inc_ref(v_binderType_1120_);
v___x_1123_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1036_, v_beginIdx_1037_, v_subst_1038_, v_binderType_1120_, v_offset_1040_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_);
if (lean_obj_tag(v___x_1123_) == 0)
{
lean_object* v_a_1124_; lean_object* v_a_1125_; lean_object* v_fst_1126_; lean_object* v_snd_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
v_a_1124_ = lean_ctor_get(v___x_1123_, 0);
lean_inc(v_a_1124_);
v_a_1125_ = lean_ctor_get(v___x_1123_, 1);
lean_inc(v_a_1125_);
lean_dec_ref_known(v___x_1123_, 2);
v_fst_1126_ = lean_ctor_get(v_a_1124_, 0);
lean_inc(v_fst_1126_);
v_snd_1127_ = lean_ctor_get(v_a_1124_, 1);
lean_inc(v_snd_1127_);
lean_dec(v_a_1124_);
v___x_1128_ = lean_unsigned_to_nat(1u);
v___x_1129_ = lean_nat_add(v_offset_1040_, v___x_1128_);
lean_dec(v_offset_1040_);
lean_inc_ref(v_body_1121_);
v___x_1130_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1036_, v_beginIdx_1037_, v_subst_1038_, v_body_1121_, v___x_1129_, v_snd_1127_, v_a_1042_, v_a_1043_, v_a_1125_);
if (lean_obj_tag(v___x_1130_) == 0)
{
lean_object* v_a_1131_; lean_object* v_a_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1157_; 
v_a_1131_ = lean_ctor_get(v___x_1130_, 0);
v_a_1132_ = lean_ctor_get(v___x_1130_, 1);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1134_ = v___x_1130_;
v_isShared_1135_ = v_isSharedCheck_1157_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_a_1132_);
lean_inc(v_a_1131_);
lean_dec(v___x_1130_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1157_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v_fst_1136_; lean_object* v_snd_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1156_; 
v_fst_1136_ = lean_ctor_get(v_a_1131_, 0);
v_snd_1137_ = lean_ctor_get(v_a_1131_, 1);
v_isSharedCheck_1156_ = !lean_is_exclusive(v_a_1131_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1139_ = v_a_1131_;
v_isShared_1140_ = v_isSharedCheck_1156_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_snd_1137_);
lean_inc(v_fst_1136_);
lean_dec(v_a_1131_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1156_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
uint8_t v___y_1142_; size_t v___x_1150_; size_t v___x_1151_; uint8_t v___x_1152_; 
v___x_1150_ = lean_ptr_addr(v_binderType_1120_);
v___x_1151_ = lean_ptr_addr(v_fst_1126_);
v___x_1152_ = lean_usize_dec_eq(v___x_1150_, v___x_1151_);
if (v___x_1152_ == 0)
{
v___y_1142_ = v___x_1152_;
goto v___jp_1141_;
}
else
{
size_t v___x_1153_; size_t v___x_1154_; uint8_t v___x_1155_; 
v___x_1153_ = lean_ptr_addr(v_body_1121_);
v___x_1154_ = lean_ptr_addr(v_fst_1136_);
v___x_1155_ = lean_usize_dec_eq(v___x_1153_, v___x_1154_);
v___y_1142_ = v___x_1155_;
goto v___jp_1141_;
}
v___jp_1141_:
{
if (v___y_1142_ == 0)
{
lean_object* v___x_1143_; 
lean_inc(v_binderName_1119_);
lean_del_object(v___x_1139_);
lean_del_object(v___x_1134_);
lean_dec_ref_known(v_e_1039_, 3);
v___x_1143_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__4(v_binderName_1119_, v_binderInfo_1122_, v_fst_1126_, v_fst_1136_, v_snd_1137_, v_a_1042_, v_a_1043_, v_a_1132_);
return v___x_1143_;
}
else
{
lean_object* v___x_1145_; 
lean_dec(v_fst_1136_);
lean_dec(v_fst_1126_);
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 0, v_e_1039_);
v___x_1145_ = v___x_1139_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_e_1039_);
lean_ctor_set(v_reuseFailAlloc_1149_, 1, v_snd_1137_);
v___x_1145_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
lean_object* v___x_1147_; 
if (v_isShared_1135_ == 0)
{
lean_ctor_set(v___x_1134_, 0, v___x_1145_);
v___x_1147_ = v___x_1134_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v___x_1145_);
lean_ctor_set(v_reuseFailAlloc_1148_, 1, v_a_1132_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1126_);
lean_dec_ref_known(v_e_1039_, 3);
return v___x_1130_;
}
}
else
{
lean_dec_ref_known(v_e_1039_, 3);
lean_dec(v_offset_1040_);
return v___x_1123_;
}
}
case 8:
{
lean_object* v_declName_1158_; lean_object* v_type_1159_; lean_object* v_value_1160_; lean_object* v_body_1161_; uint8_t v_nondep_1162_; lean_object* v___x_1163_; 
v_declName_1158_ = lean_ctor_get(v_e_1039_, 0);
v_type_1159_ = lean_ctor_get(v_e_1039_, 1);
v_value_1160_ = lean_ctor_get(v_e_1039_, 2);
v_body_1161_ = lean_ctor_get(v_e_1039_, 3);
v_nondep_1162_ = lean_ctor_get_uint8(v_e_1039_, sizeof(void*)*4 + 8);
lean_inc(v_offset_1040_);
lean_inc_ref(v_type_1159_);
v___x_1163_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1036_, v_beginIdx_1037_, v_subst_1038_, v_type_1159_, v_offset_1040_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_);
if (lean_obj_tag(v___x_1163_) == 0)
{
lean_object* v_a_1164_; lean_object* v_a_1165_; lean_object* v_fst_1166_; lean_object* v_snd_1167_; lean_object* v___x_1168_; 
v_a_1164_ = lean_ctor_get(v___x_1163_, 0);
lean_inc(v_a_1164_);
v_a_1165_ = lean_ctor_get(v___x_1163_, 1);
lean_inc(v_a_1165_);
lean_dec_ref_known(v___x_1163_, 2);
v_fst_1166_ = lean_ctor_get(v_a_1164_, 0);
lean_inc(v_fst_1166_);
v_snd_1167_ = lean_ctor_get(v_a_1164_, 1);
lean_inc(v_snd_1167_);
lean_dec(v_a_1164_);
lean_inc(v_offset_1040_);
lean_inc_ref(v_value_1160_);
v___x_1168_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1036_, v_beginIdx_1037_, v_subst_1038_, v_value_1160_, v_offset_1040_, v_snd_1167_, v_a_1042_, v_a_1043_, v_a_1165_);
if (lean_obj_tag(v___x_1168_) == 0)
{
lean_object* v_a_1169_; lean_object* v_a_1170_; lean_object* v_fst_1171_; lean_object* v_snd_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; 
v_a_1169_ = lean_ctor_get(v___x_1168_, 0);
lean_inc(v_a_1169_);
v_a_1170_ = lean_ctor_get(v___x_1168_, 1);
lean_inc(v_a_1170_);
lean_dec_ref_known(v___x_1168_, 2);
v_fst_1171_ = lean_ctor_get(v_a_1169_, 0);
lean_inc(v_fst_1171_);
v_snd_1172_ = lean_ctor_get(v_a_1169_, 1);
lean_inc(v_snd_1172_);
lean_dec(v_a_1169_);
v___x_1173_ = lean_unsigned_to_nat(1u);
v___x_1174_ = lean_nat_add(v_offset_1040_, v___x_1173_);
lean_dec(v_offset_1040_);
lean_inc_ref(v_body_1161_);
v___x_1175_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1036_, v_beginIdx_1037_, v_subst_1038_, v_body_1161_, v___x_1174_, v_snd_1172_, v_a_1042_, v_a_1043_, v_a_1170_);
if (lean_obj_tag(v___x_1175_) == 0)
{
lean_object* v_a_1176_; lean_object* v_a_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1206_; 
v_a_1176_ = lean_ctor_get(v___x_1175_, 0);
v_a_1177_ = lean_ctor_get(v___x_1175_, 1);
v_isSharedCheck_1206_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1179_ = v___x_1175_;
v_isShared_1180_ = v_isSharedCheck_1206_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_a_1177_);
lean_inc(v_a_1176_);
lean_dec(v___x_1175_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1206_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v_fst_1181_; lean_object* v_snd_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1205_; 
v_fst_1181_ = lean_ctor_get(v_a_1176_, 0);
v_snd_1182_ = lean_ctor_get(v_a_1176_, 1);
v_isSharedCheck_1205_ = !lean_is_exclusive(v_a_1176_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1184_ = v_a_1176_;
v_isShared_1185_ = v_isSharedCheck_1205_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_snd_1182_);
lean_inc(v_fst_1181_);
lean_dec(v_a_1176_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1205_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
uint8_t v___y_1187_; size_t v___x_1199_; size_t v___x_1200_; uint8_t v___x_1201_; 
v___x_1199_ = lean_ptr_addr(v_type_1159_);
v___x_1200_ = lean_ptr_addr(v_fst_1166_);
v___x_1201_ = lean_usize_dec_eq(v___x_1199_, v___x_1200_);
if (v___x_1201_ == 0)
{
v___y_1187_ = v___x_1201_;
goto v___jp_1186_;
}
else
{
size_t v___x_1202_; size_t v___x_1203_; uint8_t v___x_1204_; 
v___x_1202_ = lean_ptr_addr(v_value_1160_);
v___x_1203_ = lean_ptr_addr(v_fst_1171_);
v___x_1204_ = lean_usize_dec_eq(v___x_1202_, v___x_1203_);
v___y_1187_ = v___x_1204_;
goto v___jp_1186_;
}
v___jp_1186_:
{
if (v___y_1187_ == 0)
{
lean_object* v___x_1188_; 
lean_inc(v_declName_1158_);
lean_del_object(v___x_1184_);
lean_del_object(v___x_1179_);
lean_dec_ref_known(v_e_1039_, 4);
v___x_1188_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__5(v_declName_1158_, v_fst_1166_, v_fst_1171_, v_fst_1181_, v_nondep_1162_, v_snd_1182_, v_a_1042_, v_a_1043_, v_a_1177_);
return v___x_1188_;
}
else
{
size_t v___x_1189_; size_t v___x_1190_; uint8_t v___x_1191_; 
v___x_1189_ = lean_ptr_addr(v_body_1161_);
v___x_1190_ = lean_ptr_addr(v_fst_1181_);
v___x_1191_ = lean_usize_dec_eq(v___x_1189_, v___x_1190_);
if (v___x_1191_ == 0)
{
lean_object* v___x_1192_; 
lean_inc(v_declName_1158_);
lean_del_object(v___x_1184_);
lean_del_object(v___x_1179_);
lean_dec_ref_known(v_e_1039_, 4);
v___x_1192_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__5(v_declName_1158_, v_fst_1166_, v_fst_1171_, v_fst_1181_, v_nondep_1162_, v_snd_1182_, v_a_1042_, v_a_1043_, v_a_1177_);
return v___x_1192_;
}
else
{
lean_object* v___x_1194_; 
lean_dec(v_fst_1181_);
lean_dec(v_fst_1171_);
lean_dec(v_fst_1166_);
if (v_isShared_1185_ == 0)
{
lean_ctor_set(v___x_1184_, 0, v_e_1039_);
v___x_1194_ = v___x_1184_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_e_1039_);
lean_ctor_set(v_reuseFailAlloc_1198_, 1, v_snd_1182_);
v___x_1194_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
lean_object* v___x_1196_; 
if (v_isShared_1180_ == 0)
{
lean_ctor_set(v___x_1179_, 0, v___x_1194_);
v___x_1196_ = v___x_1179_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v___x_1194_);
lean_ctor_set(v_reuseFailAlloc_1197_, 1, v_a_1177_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
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
lean_dec(v_fst_1171_);
lean_dec(v_fst_1166_);
lean_dec_ref_known(v_e_1039_, 4);
return v___x_1175_;
}
}
else
{
lean_dec(v_fst_1166_);
lean_dec_ref_known(v_e_1039_, 4);
lean_dec(v_offset_1040_);
return v___x_1168_;
}
}
else
{
lean_dec_ref_known(v_e_1039_, 4);
lean_dec(v_offset_1040_);
return v___x_1163_;
}
}
case 10:
{
lean_object* v_data_1207_; lean_object* v_expr_1208_; lean_object* v___x_1209_; 
v_data_1207_ = lean_ctor_get(v_e_1039_, 0);
v_expr_1208_ = lean_ctor_get(v_e_1039_, 1);
lean_inc_ref(v_expr_1208_);
v___x_1209_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1036_, v_beginIdx_1037_, v_subst_1038_, v_expr_1208_, v_offset_1040_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_);
if (lean_obj_tag(v___x_1209_) == 0)
{
lean_object* v_a_1210_; lean_object* v_a_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1231_; 
v_a_1210_ = lean_ctor_get(v___x_1209_, 0);
v_a_1211_ = lean_ctor_get(v___x_1209_, 1);
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1213_ = v___x_1209_;
v_isShared_1214_ = v_isSharedCheck_1231_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_a_1211_);
lean_inc(v_a_1210_);
lean_dec(v___x_1209_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1231_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v_fst_1215_; lean_object* v_snd_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1230_; 
v_fst_1215_ = lean_ctor_get(v_a_1210_, 0);
v_snd_1216_ = lean_ctor_get(v_a_1210_, 1);
v_isSharedCheck_1230_ = !lean_is_exclusive(v_a_1210_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1218_ = v_a_1210_;
v_isShared_1219_ = v_isSharedCheck_1230_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_snd_1216_);
lean_inc(v_fst_1215_);
lean_dec(v_a_1210_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1230_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
size_t v___x_1220_; size_t v___x_1221_; uint8_t v___x_1222_; 
v___x_1220_ = lean_ptr_addr(v_expr_1208_);
v___x_1221_ = lean_ptr_addr(v_fst_1215_);
v___x_1222_ = lean_usize_dec_eq(v___x_1220_, v___x_1221_);
if (v___x_1222_ == 0)
{
lean_object* v___x_1223_; 
lean_inc(v_data_1207_);
lean_del_object(v___x_1218_);
lean_del_object(v___x_1213_);
lean_dec_ref_known(v_e_1039_, 2);
v___x_1223_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__6(v_data_1207_, v_fst_1215_, v_snd_1216_, v_a_1042_, v_a_1043_, v_a_1211_);
return v___x_1223_;
}
else
{
lean_object* v___x_1225_; 
lean_dec(v_fst_1215_);
if (v_isShared_1219_ == 0)
{
lean_ctor_set(v___x_1218_, 0, v_e_1039_);
v___x_1225_ = v___x_1218_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_e_1039_);
lean_ctor_set(v_reuseFailAlloc_1229_, 1, v_snd_1216_);
v___x_1225_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
lean_object* v___x_1227_; 
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 0, v___x_1225_);
v___x_1227_ = v___x_1213_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v___x_1225_);
lean_ctor_set(v_reuseFailAlloc_1228_, 1, v_a_1211_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_1039_, 2);
return v___x_1209_;
}
}
case 11:
{
lean_object* v_typeName_1232_; lean_object* v_idx_1233_; lean_object* v_struct_1234_; lean_object* v___x_1235_; 
v_typeName_1232_ = lean_ctor_get(v_e_1039_, 0);
v_idx_1233_ = lean_ctor_get(v_e_1039_, 1);
v_struct_1234_ = lean_ctor_get(v_e_1039_, 2);
lean_inc_ref(v_struct_1234_);
v___x_1235_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1036_, v_beginIdx_1037_, v_subst_1038_, v_struct_1234_, v_offset_1040_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_);
if (lean_obj_tag(v___x_1235_) == 0)
{
lean_object* v_a_1236_; lean_object* v_a_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1257_; 
v_a_1236_ = lean_ctor_get(v___x_1235_, 0);
v_a_1237_ = lean_ctor_get(v___x_1235_, 1);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1235_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1239_ = v___x_1235_;
v_isShared_1240_ = v_isSharedCheck_1257_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_a_1237_);
lean_inc(v_a_1236_);
lean_dec(v___x_1235_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1257_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v_fst_1241_; lean_object* v_snd_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1256_; 
v_fst_1241_ = lean_ctor_get(v_a_1236_, 0);
v_snd_1242_ = lean_ctor_get(v_a_1236_, 1);
v_isSharedCheck_1256_ = !lean_is_exclusive(v_a_1236_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1244_ = v_a_1236_;
v_isShared_1245_ = v_isSharedCheck_1256_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_snd_1242_);
lean_inc(v_fst_1241_);
lean_dec(v_a_1236_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1256_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
size_t v___x_1246_; size_t v___x_1247_; uint8_t v___x_1248_; 
v___x_1246_ = lean_ptr_addr(v_struct_1234_);
v___x_1247_ = lean_ptr_addr(v_fst_1241_);
v___x_1248_ = lean_usize_dec_eq(v___x_1246_, v___x_1247_);
if (v___x_1248_ == 0)
{
lean_object* v___x_1249_; 
lean_inc(v_idx_1233_);
lean_inc(v_typeName_1232_);
lean_del_object(v___x_1244_);
lean_del_object(v___x_1239_);
lean_dec_ref_known(v_e_1039_, 3);
v___x_1249_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__7(v_typeName_1232_, v_idx_1233_, v_fst_1241_, v_snd_1242_, v_a_1042_, v_a_1043_, v_a_1237_);
return v___x_1249_;
}
else
{
lean_object* v___x_1251_; 
lean_dec(v_fst_1241_);
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 0, v_e_1039_);
v___x_1251_ = v___x_1244_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_e_1039_);
lean_ctor_set(v_reuseFailAlloc_1255_, 1, v_snd_1242_);
v___x_1251_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
lean_object* v___x_1253_; 
if (v_isShared_1240_ == 0)
{
lean_ctor_set(v___x_1239_, 0, v___x_1251_);
v___x_1253_ = v___x_1239_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v___x_1251_);
lean_ctor_set(v_reuseFailAlloc_1254_, 1, v_a_1237_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_1039_, 3);
return v___x_1235_;
}
}
default: 
{
lean_object* v___x_1258_; lean_object* v___x_1259_; 
lean_dec(v_offset_1040_);
lean_dec_ref(v_e_1039_);
v___x_1258_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__3);
v___x_1259_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8(v___x_1258_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_);
return v___x_1259_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(lean_object* v_n_1260_, lean_object* v_beginIdx_1261_, lean_object* v_subst_1262_, lean_object* v_e_1263_, lean_object* v_offset_1264_, lean_object* v_a_1265_, uint8_t v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_){
_start:
{
lean_object* v_key_1269_; lean_object* v___x_1270_; 
lean_inc(v_offset_1264_);
lean_inc_ref(v_e_1263_);
v_key_1269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1269_, 0, v_e_1263_);
lean_ctor_set(v_key_1269_, 1, v_offset_1264_);
v___x_1270_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3___redArg(v_a_1265_, v_key_1269_);
if (lean_obj_tag(v___x_1270_) == 1)
{
lean_object* v_val_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; 
lean_dec_ref_known(v_key_1269_, 2);
lean_dec(v_offset_1264_);
lean_dec_ref(v_e_1263_);
v_val_1271_ = lean_ctor_get(v___x_1270_, 0);
lean_inc(v_val_1271_);
lean_dec_ref_known(v___x_1270_, 1);
v___x_1272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1272_, 0, v_val_1271_);
lean_ctor_set(v___x_1272_, 1, v_a_1265_);
v___x_1273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1273_, 0, v___x_1272_);
lean_ctor_set(v___x_1273_, 1, v_a_1268_);
return v___x_1273_;
}
else
{
lean_dec(v___x_1270_);
switch(lean_obj_tag(v_e_1263_))
{
case 0:
{
lean_object* v_deBruijnIndex_1274_; uint8_t v___x_1275_; 
v_deBruijnIndex_1274_ = lean_ctor_get(v_e_1263_, 0);
v___x_1275_ = lean_nat_dec_le(v_offset_1264_, v_deBruijnIndex_1274_);
if (v___x_1275_ == 0)
{
lean_object* v___x_1276_; 
lean_dec(v_offset_1264_);
v___x_1276_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1269_, v_e_1263_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_);
return v___x_1276_;
}
else
{
lean_object* v___x_1277_; uint8_t v___x_1278_; 
lean_inc(v_deBruijnIndex_1274_);
lean_dec_ref_known(v_e_1263_, 1);
v___x_1277_ = lean_nat_add(v_offset_1264_, v_n_1260_);
v___x_1278_ = lean_nat_dec_lt(v_deBruijnIndex_1274_, v___x_1277_);
lean_dec(v___x_1277_);
if (v___x_1278_ == 0)
{
lean_object* v___x_1279_; lean_object* v___x_1280_; 
lean_dec(v_offset_1264_);
v___x_1279_ = lean_nat_sub(v_deBruijnIndex_1274_, v_n_1260_);
lean_dec(v_deBruijnIndex_1274_);
v___x_1280_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___redArg(v___x_1279_, v_a_1268_);
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_object* v_a_1281_; lean_object* v_a_1282_; lean_object* v___x_1283_; 
v_a_1281_ = lean_ctor_get(v___x_1280_, 0);
lean_inc(v_a_1281_);
v_a_1282_ = lean_ctor_get(v___x_1280_, 1);
lean_inc(v_a_1282_);
lean_dec_ref_known(v___x_1280_, 2);
v___x_1283_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1269_, v_a_1281_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1282_);
return v___x_1283_;
}
else
{
lean_object* v_a_1284_; lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1292_; 
lean_dec_ref_known(v_key_1269_, 2);
lean_dec_ref(v_a_1265_);
v_a_1284_ = lean_ctor_get(v___x_1280_, 0);
v_a_1285_ = lean_ctor_get(v___x_1280_, 1);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1287_ = v___x_1280_;
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_inc(v_a_1284_);
lean_dec(v___x_1280_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1290_; 
if (v_isShared_1288_ == 0)
{
v___x_1290_ = v___x_1287_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_a_1284_);
lean_ctor_set(v_reuseFailAlloc_1291_, 1, v_a_1285_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
}
else
{
lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v_v_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; 
v___x_1293_ = lean_nat_add(v_beginIdx_1261_, v_deBruijnIndex_1274_);
lean_dec(v_deBruijnIndex_1274_);
v___x_1294_ = lean_nat_sub(v___x_1293_, v_offset_1264_);
lean_dec(v___x_1293_);
v_v_1295_ = lean_array_fget_borrowed(v_subst_1262_, v___x_1294_);
lean_dec(v___x_1294_);
v___x_1296_ = lean_unsigned_to_nat(0u);
lean_inc(v_v_1295_);
v___x_1297_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(v_v_1295_, v___x_1296_, v_offset_1264_, v_a_1266_, v_a_1267_, v_a_1268_);
lean_dec(v_offset_1264_);
if (lean_obj_tag(v___x_1297_) == 0)
{
lean_object* v_a_1298_; lean_object* v_a_1299_; lean_object* v___x_1300_; 
v_a_1298_ = lean_ctor_get(v___x_1297_, 0);
lean_inc(v_a_1298_);
v_a_1299_ = lean_ctor_get(v___x_1297_, 1);
lean_inc(v_a_1299_);
lean_dec_ref_known(v___x_1297_, 2);
v___x_1300_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1269_, v_a_1298_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1299_);
return v___x_1300_;
}
else
{
lean_object* v_a_1301_; lean_object* v_a_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1309_; 
lean_dec_ref_known(v_key_1269_, 2);
lean_dec_ref(v_a_1265_);
v_a_1301_ = lean_ctor_get(v___x_1297_, 0);
v_a_1302_ = lean_ctor_get(v___x_1297_, 1);
v_isSharedCheck_1309_ = !lean_is_exclusive(v___x_1297_);
if (v_isSharedCheck_1309_ == 0)
{
v___x_1304_ = v___x_1297_;
v_isShared_1305_ = v_isSharedCheck_1309_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_a_1302_);
lean_inc(v_a_1301_);
lean_dec(v___x_1297_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1309_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
lean_object* v___x_1307_; 
if (v_isShared_1305_ == 0)
{
v___x_1307_ = v___x_1304_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v_a_1301_);
lean_ctor_set(v_reuseFailAlloc_1308_, 1, v_a_1302_);
v___x_1307_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
return v___x_1307_;
}
}
}
}
}
}
case 9:
{
lean_object* v___x_1310_; 
lean_dec(v_offset_1264_);
v___x_1310_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1269_, v_e_1263_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_);
return v___x_1310_;
}
case 2:
{
lean_object* v___x_1311_; 
lean_dec(v_offset_1264_);
v___x_1311_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1269_, v_e_1263_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_);
return v___x_1311_;
}
case 1:
{
lean_object* v___x_1312_; 
lean_dec(v_offset_1264_);
v___x_1312_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1269_, v_e_1263_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_);
return v___x_1312_;
}
case 4:
{
lean_object* v___x_1313_; 
lean_dec(v_offset_1264_);
v___x_1313_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1269_, v_e_1263_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_);
return v___x_1313_;
}
case 3:
{
lean_object* v___x_1314_; 
lean_dec(v_offset_1264_);
v___x_1314_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1269_, v_e_1263_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_);
return v___x_1314_;
}
default: 
{
lean_object* v___x_1315_; uint8_t v___x_1316_; 
v___x_1315_ = l_Lean_Expr_looseBVarRange(v_e_1263_);
v___x_1316_ = lean_nat_dec_le(v___x_1315_, v_offset_1264_);
lean_dec(v___x_1315_);
if (v___x_1316_ == 0)
{
switch(lean_obj_tag(v_e_1263_))
{
case 9:
{
lean_object* v___x_1317_; 
lean_dec(v_offset_1264_);
v___x_1317_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1269_, v_e_1263_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_);
return v___x_1317_;
}
case 2:
{
lean_object* v___x_1318_; 
lean_dec(v_offset_1264_);
v___x_1318_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1269_, v_e_1263_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_);
return v___x_1318_;
}
case 0:
{
lean_object* v___x_1319_; 
lean_dec(v_offset_1264_);
v___x_1319_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1269_, v_e_1263_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_);
return v___x_1319_;
}
case 1:
{
lean_object* v___x_1320_; 
lean_dec(v_offset_1264_);
v___x_1320_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1269_, v_e_1263_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_);
return v___x_1320_;
}
case 4:
{
lean_object* v___x_1321_; 
lean_dec(v_offset_1264_);
v___x_1321_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1269_, v_e_1263_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_);
return v___x_1321_;
}
case 3:
{
lean_object* v___x_1322_; 
lean_dec(v_offset_1264_);
v___x_1322_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1269_, v_e_1263_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_);
return v___x_1322_;
}
default: 
{
lean_object* v___x_1323_; 
v___x_1323_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0(v_n_1260_, v_beginIdx_1261_, v_subst_1262_, v_e_1263_, v_offset_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_);
if (lean_obj_tag(v___x_1323_) == 0)
{
lean_object* v_a_1324_; lean_object* v_a_1325_; lean_object* v_fst_1326_; lean_object* v_snd_1327_; lean_object* v___x_1328_; 
v_a_1324_ = lean_ctor_get(v___x_1323_, 0);
lean_inc(v_a_1324_);
v_a_1325_ = lean_ctor_get(v___x_1323_, 1);
lean_inc(v_a_1325_);
lean_dec_ref_known(v___x_1323_, 2);
v_fst_1326_ = lean_ctor_get(v_a_1324_, 0);
lean_inc(v_fst_1326_);
v_snd_1327_ = lean_ctor_get(v_a_1324_, 1);
lean_inc(v_snd_1327_);
lean_dec(v_a_1324_);
v___x_1328_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1269_, v_fst_1326_, v_snd_1327_, v_a_1266_, v_a_1267_, v_a_1325_);
return v___x_1328_;
}
else
{
lean_dec_ref_known(v_key_1269_, 2);
return v___x_1323_;
}
}
}
}
else
{
lean_object* v___x_1329_; 
lean_dec(v_offset_1264_);
v___x_1329_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1269_, v_e_1263_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_);
return v___x_1329_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0___boxed(lean_object* v_n_1330_, lean_object* v_beginIdx_1331_, lean_object* v_subst_1332_, lean_object* v_e_1333_, lean_object* v_offset_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_){
_start:
{
uint8_t v_a_boxed_1339_; lean_object* v_res_1340_; 
v_a_boxed_1339_ = lean_unbox(v_a_1336_);
v_res_1340_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1330_, v_beginIdx_1331_, v_subst_1332_, v_e_1333_, v_offset_1334_, v_a_1335_, v_a_boxed_1339_, v_a_1337_, v_a_1338_);
lean_dec_ref(v_a_1337_);
lean_dec_ref(v_subst_1332_);
lean_dec(v_beginIdx_1331_);
lean_dec(v_n_1330_);
return v_res_1340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0___boxed(lean_object* v_n_1341_, lean_object* v_beginIdx_1342_, lean_object* v_subst_1343_, lean_object* v_e_1344_, lean_object* v_offset_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_){
_start:
{
uint8_t v_a_boxed_1350_; lean_object* v_res_1351_; 
v_a_boxed_1350_ = lean_unbox(v_a_1347_);
v_res_1351_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0(v_n_1341_, v_beginIdx_1342_, v_subst_1343_, v_e_1344_, v_offset_1345_, v_a_1346_, v_a_boxed_1350_, v_a_1348_, v_a_1349_);
lean_dec_ref(v_a_1348_);
lean_dec_ref(v_subst_1343_);
lean_dec(v_beginIdx_1342_);
lean_dec(v_n_1341_);
return v_res_1351_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__1(void){
_start:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___x_1353_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__2));
v___x_1354_ = lean_unsigned_to_nat(34u);
v___x_1355_ = lean_unsigned_to_nat(57u);
v___x_1356_ = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__0));
v___x_1357_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__3));
v___x_1358_ = l_mkPanicMessageWithDecl(v___x_1357_, v___x_1356_, v___x_1355_, v___x_1354_, v___x_1353_);
return v___x_1358_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__2(void){
_start:
{
lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1359_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__2));
v___x_1360_ = lean_unsigned_to_nat(32u);
v___x_1361_ = lean_unsigned_to_nat(56u);
v___x_1362_ = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__0));
v___x_1363_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__3));
v___x_1364_ = l_mkPanicMessageWithDecl(v___x_1363_, v___x_1362_, v___x_1361_, v___x_1360_, v___x_1359_);
return v___x_1364_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27(lean_object* v_e_1365_, lean_object* v_beginIdx_1366_, lean_object* v_endIdx_1367_, lean_object* v_subst_1368_, uint8_t v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_){
_start:
{
uint8_t v___x_1372_; 
v___x_1372_ = lean_nat_dec_lt(v_endIdx_1367_, v_beginIdx_1366_);
if (v___x_1372_ == 0)
{
lean_object* v___x_1373_; uint8_t v___x_1374_; 
v___x_1373_ = lean_array_get_size(v_subst_1368_);
v___x_1374_ = lean_nat_dec_lt(v___x_1373_, v_endIdx_1367_);
if (v___x_1374_ == 0)
{
lean_object* v_n_1375_; lean_object* v___x_1376_; 
v_n_1375_ = lean_nat_sub(v_endIdx_1367_, v_beginIdx_1366_);
v___x_1376_ = lean_unsigned_to_nat(0u);
switch(lean_obj_tag(v_e_1365_))
{
case 0:
{
lean_object* v_deBruijnIndex_1377_; uint8_t v___x_1378_; 
v_deBruijnIndex_1377_ = lean_ctor_get(v_e_1365_, 0);
v___x_1378_ = lean_nat_dec_le(v___x_1376_, v_deBruijnIndex_1377_);
if (v___x_1378_ == 0)
{
lean_object* v___x_1379_; 
lean_dec(v_n_1375_);
v___x_1379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1379_, 0, v_e_1365_);
lean_ctor_set(v___x_1379_, 1, v_a_1371_);
return v___x_1379_;
}
else
{
uint8_t v___x_1380_; 
lean_inc(v_deBruijnIndex_1377_);
lean_dec_ref_known(v_e_1365_, 1);
v___x_1380_ = lean_nat_dec_lt(v_deBruijnIndex_1377_, v_n_1375_);
if (v___x_1380_ == 0)
{
lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1381_ = lean_nat_sub(v_deBruijnIndex_1377_, v_n_1375_);
lean_dec(v_n_1375_);
lean_dec(v_deBruijnIndex_1377_);
v___x_1382_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___redArg(v___x_1381_, v_a_1371_);
return v___x_1382_;
}
else
{
lean_object* v___x_1383_; lean_object* v_v_1384_; lean_object* v___x_1385_; 
lean_dec(v_n_1375_);
v___x_1383_ = lean_nat_add(v_beginIdx_1366_, v_deBruijnIndex_1377_);
lean_dec(v_deBruijnIndex_1377_);
v_v_1384_ = lean_array_fget_borrowed(v_subst_1368_, v___x_1383_);
lean_dec(v___x_1383_);
lean_inc(v_v_1384_);
v___x_1385_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(v_v_1384_, v___x_1376_, v___x_1376_, v_a_1369_, v_a_1370_, v_a_1371_);
return v___x_1385_;
}
}
}
case 9:
{
lean_object* v___x_1386_; 
lean_dec(v_n_1375_);
v___x_1386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1386_, 0, v_e_1365_);
lean_ctor_set(v___x_1386_, 1, v_a_1371_);
return v___x_1386_;
}
case 2:
{
lean_object* v___x_1387_; 
lean_dec(v_n_1375_);
v___x_1387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1387_, 0, v_e_1365_);
lean_ctor_set(v___x_1387_, 1, v_a_1371_);
return v___x_1387_;
}
case 1:
{
lean_object* v___x_1388_; 
lean_dec(v_n_1375_);
v___x_1388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1388_, 0, v_e_1365_);
lean_ctor_set(v___x_1388_, 1, v_a_1371_);
return v___x_1388_;
}
case 4:
{
lean_object* v___x_1389_; 
lean_dec(v_n_1375_);
v___x_1389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1389_, 0, v_e_1365_);
lean_ctor_set(v___x_1389_, 1, v_a_1371_);
return v___x_1389_;
}
case 3:
{
lean_object* v___x_1390_; 
lean_dec(v_n_1375_);
v___x_1390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1390_, 0, v_e_1365_);
lean_ctor_set(v___x_1390_, 1, v_a_1371_);
return v___x_1390_;
}
default: 
{
lean_object* v___x_1391_; uint8_t v___x_1392_; 
v___x_1391_ = l_Lean_Expr_looseBVarRange(v_e_1365_);
v___x_1392_ = lean_nat_dec_le(v___x_1391_, v___x_1376_);
lean_dec(v___x_1391_);
if (v___x_1392_ == 0)
{
switch(lean_obj_tag(v_e_1365_))
{
case 9:
{
lean_object* v___x_1393_; 
lean_dec(v_n_1375_);
v___x_1393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1393_, 0, v_e_1365_);
lean_ctor_set(v___x_1393_, 1, v_a_1371_);
return v___x_1393_;
}
case 2:
{
lean_object* v___x_1394_; 
lean_dec(v_n_1375_);
v___x_1394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1394_, 0, v_e_1365_);
lean_ctor_set(v___x_1394_, 1, v_a_1371_);
return v___x_1394_;
}
case 0:
{
lean_object* v___x_1395_; 
lean_dec(v_n_1375_);
v___x_1395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1395_, 0, v_e_1365_);
lean_ctor_set(v___x_1395_, 1, v_a_1371_);
return v___x_1395_;
}
case 1:
{
lean_object* v___x_1396_; 
lean_dec(v_n_1375_);
v___x_1396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1396_, 0, v_e_1365_);
lean_ctor_set(v___x_1396_, 1, v_a_1371_);
return v___x_1396_;
}
case 4:
{
lean_object* v___x_1397_; 
lean_dec(v_n_1375_);
v___x_1397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1397_, 0, v_e_1365_);
lean_ctor_set(v___x_1397_, 1, v_a_1371_);
return v___x_1397_;
}
case 3:
{
lean_object* v___x_1398_; 
lean_dec(v_n_1375_);
v___x_1398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1398_, 0, v_e_1365_);
lean_ctor_set(v___x_1398_, 1, v_a_1371_);
return v___x_1398_;
}
default: 
{
lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1399_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__1, &l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__1_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__1);
v___x_1400_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0(v_n_1375_, v_beginIdx_1366_, v_subst_1368_, v_e_1365_, v___x_1376_, v___x_1399_, v_a_1369_, v_a_1370_, v_a_1371_);
lean_dec(v_n_1375_);
if (lean_obj_tag(v___x_1400_) == 0)
{
lean_object* v_a_1401_; lean_object* v_a_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1410_; 
v_a_1401_ = lean_ctor_get(v___x_1400_, 0);
v_a_1402_ = lean_ctor_get(v___x_1400_, 1);
v_isSharedCheck_1410_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1404_ = v___x_1400_;
v_isShared_1405_ = v_isSharedCheck_1410_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_a_1402_);
lean_inc(v_a_1401_);
lean_dec(v___x_1400_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1410_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v_fst_1406_; lean_object* v___x_1408_; 
v_fst_1406_ = lean_ctor_get(v_a_1401_, 0);
lean_inc(v_fst_1406_);
lean_dec(v_a_1401_);
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 0, v_fst_1406_);
v___x_1408_ = v___x_1404_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v_fst_1406_);
lean_ctor_set(v_reuseFailAlloc_1409_, 1, v_a_1402_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
}
else
{
lean_object* v_a_1411_; lean_object* v_a_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1419_; 
v_a_1411_ = lean_ctor_get(v___x_1400_, 0);
v_a_1412_ = lean_ctor_get(v___x_1400_, 1);
v_isSharedCheck_1419_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1414_ = v___x_1400_;
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_a_1412_);
lean_inc(v_a_1411_);
lean_dec(v___x_1400_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1417_; 
if (v_isShared_1415_ == 0)
{
v___x_1417_ = v___x_1414_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_a_1411_);
lean_ctor_set(v_reuseFailAlloc_1418_, 1, v_a_1412_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
return v___x_1417_;
}
}
}
}
}
}
else
{
lean_object* v___x_1420_; 
lean_dec(v_n_1375_);
v___x_1420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1420_, 0, v_e_1365_);
lean_ctor_set(v___x_1420_, 1, v_a_1371_);
return v___x_1420_;
}
}
}
}
else
{
lean_object* v___x_1421_; lean_object* v___x_1422_; 
lean_dec_ref(v_e_1365_);
v___x_1421_ = lean_obj_once(&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__1, &l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__1_once, _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__1);
v___x_1422_ = l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1(v___x_1421_, v_a_1369_, v_a_1370_, v_a_1371_);
return v___x_1422_;
}
}
else
{
lean_object* v___x_1423_; lean_object* v___x_1424_; 
lean_dec_ref(v_e_1365_);
v___x_1423_ = lean_obj_once(&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__2, &l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__2_once, _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__2);
v___x_1424_ = l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1(v___x_1423_, v_a_1369_, v_a_1370_, v_a_1371_);
return v___x_1424_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___boxed(lean_object* v_e_1425_, lean_object* v_beginIdx_1426_, lean_object* v_endIdx_1427_, lean_object* v_subst_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_){
_start:
{
uint8_t v_a_boxed_1432_; lean_object* v_res_1433_; 
v_a_boxed_1432_ = lean_unbox(v_a_1429_);
v_res_1433_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27(v_e_1425_, v_beginIdx_1426_, v_endIdx_1427_, v_subst_1428_, v_a_boxed_1432_, v_a_1430_, v_a_1431_);
lean_dec_ref(v_a_1430_);
lean_dec_ref(v_subst_1428_);
lean_dec(v_endIdx_1427_);
lean_dec(v_beginIdx_1426_);
return v_res_1433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27(lean_object* v_e_1434_, lean_object* v_subst_1435_, uint8_t v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_){
_start:
{
lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; 
v___x_1439_ = lean_unsigned_to_nat(0u);
v___x_1440_ = lean_array_get_size(v_subst_1435_);
v___x_1441_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27(v_e_1434_, v___x_1439_, v___x_1440_, v_subst_1435_, v_a_1436_, v_a_1437_, v_a_1438_);
return v___x_1441_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27___boxed(lean_object* v_e_1442_, lean_object* v_subst_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_){
_start:
{
uint8_t v_a_boxed_1447_; lean_object* v_res_1448_; 
v_a_boxed_1447_ = lean_unbox(v_a_1444_);
v_res_1448_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27(v_e_1442_, v_subst_1443_, v_a_boxed_1447_, v_a_1445_, v_a_1446_);
lean_dec_ref(v_a_1445_);
lean_dec_ref(v_subst_1443_);
return v_res_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateS(lean_object* v_e_1449_, lean_object* v_subst_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_){
_start:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; uint8_t v_debug_1460_; lean_object* v_env_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; uint8_t v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___x_1458_ = lean_st_ref_get(v_a_1452_);
v___x_1459_ = lean_st_ref_get(v_a_1456_);
v_debug_1460_ = lean_ctor_get_uint8(v___x_1458_, sizeof(void*)*11);
lean_dec(v___x_1458_);
v_env_1461_ = lean_ctor_get(v___x_1459_, 0);
lean_inc_ref(v_env_1461_);
lean_dec(v___x_1459_);
v___x_1462_ = lean_box(v_debug_1460_);
v___x_1463_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27___boxed), 5, 3);
lean_closure_set(v___x_1463_, 0, v_e_1449_);
lean_closure_set(v___x_1463_, 1, v_subst_1450_);
lean_closure_set(v___x_1463_, 2, v___x_1462_);
v___x_1464_ = 0;
v___x_1465_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_1465_, 0, v_env_1461_);
lean_ctor_set_uint8(v___x_1465_, sizeof(void*)*1, v___x_1464_);
lean_ctor_set_uint8(v___x_1465_, sizeof(void*)*1 + 1, v___x_1464_);
v___x_1466_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___x_1463_, v___x_1465_, v_a_1452_);
if (lean_obj_tag(v___x_1466_) == 0)
{
lean_object* v_a_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1477_; 
v_a_1467_ = lean_ctor_get(v___x_1466_, 0);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1466_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1469_ = v___x_1466_;
v_isShared_1470_ = v_isSharedCheck_1477_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_a_1467_);
lean_dec(v___x_1466_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1477_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
if (lean_obj_tag(v_a_1467_) == 0)
{
lean_object* v___x_1471_; lean_object* v___x_1472_; 
lean_dec_ref_known(v_a_1467_, 1);
lean_del_object(v___x_1469_);
v___x_1471_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__2, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__2_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__2);
v___x_1472_ = l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(v___x_1471_, v_a_1451_, v_a_1452_, v_a_1453_, v_a_1454_, v_a_1455_, v_a_1456_);
return v___x_1472_;
}
else
{
lean_object* v_a_1473_; lean_object* v___x_1475_; 
v_a_1473_ = lean_ctor_get(v_a_1467_, 0);
lean_inc(v_a_1473_);
lean_dec_ref_known(v_a_1467_, 1);
if (v_isShared_1470_ == 0)
{
lean_ctor_set(v___x_1469_, 0, v_a_1473_);
v___x_1475_ = v___x_1469_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_a_1473_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
return v___x_1475_;
}
}
}
}
else
{
lean_object* v_a_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1485_; 
v_a_1478_ = lean_ctor_get(v___x_1466_, 0);
v_isSharedCheck_1485_ = !lean_is_exclusive(v___x_1466_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1480_ = v___x_1466_;
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_a_1478_);
lean_dec(v___x_1466_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1483_; 
if (v_isShared_1481_ == 0)
{
v___x_1483_ = v___x_1480_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v_a_1478_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
return v___x_1483_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateS___boxed(lean_object* v_e_1486_, lean_object* v_subst_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_){
_start:
{
lean_object* v_res_1495_; 
v_res_1495_ = l_Lean_Meta_Sym_instantiateS(v_e_1486_, v_subst_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_);
lean_dec(v_a_1493_);
lean_dec_ref(v_a_1492_);
lean_dec(v_a_1491_);
lean_dec_ref(v_a_1490_);
lean_dec(v_a_1489_);
lean_dec_ref(v_a_1488_);
return v_res_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0_spec__0(lean_object* v_f_1496_, lean_object* v_a_1497_, uint8_t v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_){
_start:
{
lean_object* v___y_1502_; 
if (v___y_1498_ == 0)
{
v___y_1502_ = v___y_1500_;
goto v___jp_1501_;
}
else
{
lean_object* v___x_1505_; 
lean_inc_ref(v_f_1496_);
v___x_1505_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_f_1496_, v___y_1498_, v___y_1499_, v___y_1500_);
if (lean_obj_tag(v___x_1505_) == 0)
{
lean_object* v_a_1506_; lean_object* v___x_1507_; 
v_a_1506_ = lean_ctor_get(v___x_1505_, 1);
lean_inc(v_a_1506_);
lean_dec_ref_known(v___x_1505_, 2);
lean_inc_ref(v_a_1497_);
v___x_1507_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_a_1497_, v___y_1498_, v___y_1499_, v_a_1506_);
if (lean_obj_tag(v___x_1507_) == 0)
{
lean_object* v_a_1508_; 
v_a_1508_ = lean_ctor_get(v___x_1507_, 1);
lean_inc(v_a_1508_);
lean_dec_ref_known(v___x_1507_, 2);
v___y_1502_ = v_a_1508_;
goto v___jp_1501_;
}
else
{
lean_object* v_a_1509_; lean_object* v_a_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1517_; 
lean_dec_ref(v_a_1497_);
lean_dec_ref(v_f_1496_);
v_a_1509_ = lean_ctor_get(v___x_1507_, 0);
v_a_1510_ = lean_ctor_get(v___x_1507_, 1);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1507_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1512_ = v___x_1507_;
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_a_1510_);
lean_inc(v_a_1509_);
lean_dec(v___x_1507_);
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
else
{
lean_object* v_a_1518_; lean_object* v_a_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1526_; 
lean_dec_ref(v_a_1497_);
lean_dec_ref(v_f_1496_);
v_a_1518_ = lean_ctor_get(v___x_1505_, 0);
v_a_1519_ = lean_ctor_get(v___x_1505_, 1);
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1505_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1521_ = v___x_1505_;
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_a_1519_);
lean_inc(v_a_1518_);
lean_dec(v___x_1505_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1524_; 
if (v_isShared_1522_ == 0)
{
v___x_1524_ = v___x_1521_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_a_1518_);
lean_ctor_set(v_reuseFailAlloc_1525_, 1, v_a_1519_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
return v___x_1524_;
}
}
}
}
v___jp_1501_:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; 
v___x_1503_ = l_Lean_Expr_app___override(v_f_1496_, v_a_1497_);
v___x_1504_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1503_, v___y_1502_);
return v___x_1504_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0_spec__0___boxed(lean_object* v_f_1527_, lean_object* v_a_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_){
_start:
{
uint8_t v___y_1405__boxed_1532_; lean_object* v_res_1533_; 
v___y_1405__boxed_1532_ = lean_unbox(v___y_1529_);
v_res_1533_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0_spec__0(v_f_1527_, v_a_1528_, v___y_1405__boxed_1532_, v___y_1530_, v___y_1531_);
lean_dec_ref(v___y_1530_);
return v_res_1533_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0(lean_object* v_revArgs_1534_, lean_object* v_start_1535_, lean_object* v_b_1536_, lean_object* v_i_1537_, uint8_t v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_){
_start:
{
uint8_t v___x_1541_; 
v___x_1541_ = lean_nat_dec_le(v_i_1537_, v_start_1535_);
if (v___x_1541_ == 0)
{
lean_object* v___x_1542_; lean_object* v_i_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1542_ = lean_unsigned_to_nat(1u);
v_i_1543_ = lean_nat_sub(v_i_1537_, v___x_1542_);
lean_dec(v_i_1537_);
v___x_1544_ = l_Lean_instInhabitedExpr;
v___x_1545_ = lean_array_get_borrowed(v___x_1544_, v_revArgs_1534_, v_i_1543_);
lean_inc(v___x_1545_);
v___x_1546_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0_spec__0(v_b_1536_, v___x_1545_, v___y_1538_, v___y_1539_, v___y_1540_);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_object* v_a_1547_; lean_object* v_a_1548_; 
v_a_1547_ = lean_ctor_get(v___x_1546_, 0);
lean_inc(v_a_1547_);
v_a_1548_ = lean_ctor_get(v___x_1546_, 1);
lean_inc(v_a_1548_);
lean_dec_ref_known(v___x_1546_, 2);
v_b_1536_ = v_a_1547_;
v_i_1537_ = v_i_1543_;
v___y_1540_ = v_a_1548_;
goto _start;
}
else
{
lean_dec(v_i_1543_);
return v___x_1546_;
}
}
else
{
lean_object* v___x_1550_; 
lean_dec(v_i_1537_);
v___x_1550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1550_, 0, v_b_1536_);
lean_ctor_set(v___x_1550_, 1, v___y_1540_);
return v___x_1550_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0___boxed(lean_object* v_revArgs_1551_, lean_object* v_start_1552_, lean_object* v_b_1553_, lean_object* v_i_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_){
_start:
{
uint8_t v___y_1468__boxed_1558_; lean_object* v_res_1559_; 
v___y_1468__boxed_1558_ = lean_unbox(v___y_1555_);
v_res_1559_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0(v_revArgs_1551_, v_start_1552_, v_b_1553_, v_i_1554_, v___y_1468__boxed_1558_, v___y_1556_, v___y_1557_);
lean_dec_ref(v___y_1556_);
lean_dec(v_start_1552_);
lean_dec_ref(v_revArgs_1551_);
return v_res_1559_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go(lean_object* v_revArgs_1560_, lean_object* v_sz_1561_, lean_object* v_e_1562_, lean_object* v_i_1563_, uint8_t v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_){
_start:
{
switch(lean_obj_tag(v_e_1562_))
{
case 6:
{
lean_object* v_body_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; uint8_t v___x_1570_; 
v_body_1567_ = lean_ctor_get(v_e_1562_, 2);
lean_inc_ref(v_body_1567_);
lean_dec_ref_known(v_e_1562_, 3);
v___x_1568_ = lean_unsigned_to_nat(1u);
v___x_1569_ = lean_nat_add(v_i_1563_, v___x_1568_);
lean_dec(v_i_1563_);
v___x_1570_ = lean_nat_dec_lt(v___x_1569_, v_sz_1561_);
if (v___x_1570_ == 0)
{
lean_object* v___x_1571_; 
lean_dec(v___x_1569_);
v___x_1571_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27(v_body_1567_, v_revArgs_1560_, v_a_1564_, v_a_1565_, v_a_1566_);
return v___x_1571_;
}
else
{
v_e_1562_ = v_body_1567_;
v_i_1563_ = v___x_1569_;
goto _start;
}
}
case 10:
{
lean_object* v_expr_1573_; 
v_expr_1573_ = lean_ctor_get(v_e_1562_, 1);
lean_inc_ref(v_expr_1573_);
lean_dec_ref_known(v_e_1562_, 2);
v_e_1562_ = v_expr_1573_;
goto _start;
}
default: 
{
lean_object* v_n_1575_; lean_object* v___x_1576_; 
v_n_1575_ = lean_nat_sub(v_sz_1561_, v_i_1563_);
lean_dec(v_i_1563_);
v___x_1576_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27(v_e_1562_, v_n_1575_, v_sz_1561_, v_revArgs_1560_, v_a_1564_, v_a_1565_, v_a_1566_);
if (lean_obj_tag(v___x_1576_) == 0)
{
lean_object* v_a_1577_; lean_object* v_a_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; 
v_a_1577_ = lean_ctor_get(v___x_1576_, 0);
lean_inc(v_a_1577_);
v_a_1578_ = lean_ctor_get(v___x_1576_, 1);
lean_inc(v_a_1578_);
lean_dec_ref_known(v___x_1576_, 2);
v___x_1579_ = lean_unsigned_to_nat(0u);
v___x_1580_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0(v_revArgs_1560_, v___x_1579_, v_a_1577_, v_n_1575_, v_a_1564_, v_a_1565_, v_a_1578_);
return v___x_1580_;
}
else
{
lean_dec(v_n_1575_);
return v___x_1576_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go___boxed(lean_object* v_revArgs_1581_, lean_object* v_sz_1582_, lean_object* v_e_1583_, lean_object* v_i_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_){
_start:
{
uint8_t v_a_boxed_1588_; lean_object* v_res_1589_; 
v_a_boxed_1588_ = lean_unbox(v_a_1585_);
v_res_1589_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go(v_revArgs_1581_, v_sz_1582_, v_e_1583_, v_i_1584_, v_a_boxed_1588_, v_a_1586_, v_a_1587_);
lean_dec_ref(v_a_1586_);
lean_dec(v_sz_1582_);
lean_dec_ref(v_revArgs_1581_);
return v_res_1589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27(lean_object* v_f_1590_, lean_object* v_revArgs_1591_, uint8_t v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_){
_start:
{
lean_object* v_sz_1595_; lean_object* v___x_1596_; uint8_t v___x_1597_; 
v_sz_1595_ = lean_array_get_size(v_revArgs_1591_);
v___x_1596_ = lean_unsigned_to_nat(0u);
v___x_1597_ = lean_nat_dec_eq(v_sz_1595_, v___x_1596_);
if (v___x_1597_ == 0)
{
lean_object* v___x_1598_; 
v___x_1598_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go(v_revArgs_1591_, v_sz_1595_, v_f_1590_, v___x_1596_, v_a_1592_, v_a_1593_, v_a_1594_);
return v___x_1598_;
}
else
{
lean_object* v___x_1599_; 
v___x_1599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1599_, 0, v_f_1590_);
lean_ctor_set(v___x_1599_, 1, v_a_1594_);
return v___x_1599_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27___boxed(lean_object* v_f_1600_, lean_object* v_revArgs_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_){
_start:
{
uint8_t v_a_boxed_1605_; lean_object* v_res_1606_; 
v_a_boxed_1605_ = lean_unbox(v_a_1602_);
v_res_1606_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27(v_f_1600_, v_revArgs_1601_, v_a_boxed_1605_, v_a_1603_, v_a_1604_);
lean_dec_ref(v_a_1603_);
lean_dec_ref(v_revArgs_1601_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_1607_, lean_object* v_x_1608_){
_start:
{
if (lean_obj_tag(v_x_1608_) == 0)
{
return v_x_1607_;
}
else
{
lean_object* v_key_1609_; lean_object* v_value_1610_; lean_object* v_tail_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1641_; 
v_key_1609_ = lean_ctor_get(v_x_1608_, 0);
v_value_1610_ = lean_ctor_get(v_x_1608_, 1);
v_tail_1611_ = lean_ctor_get(v_x_1608_, 2);
v_isSharedCheck_1641_ = !lean_is_exclusive(v_x_1608_);
if (v_isSharedCheck_1641_ == 0)
{
v___x_1613_ = v_x_1608_;
v_isShared_1614_ = v_isSharedCheck_1641_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_tail_1611_);
lean_inc(v_value_1610_);
lean_inc(v_key_1609_);
lean_dec(v_x_1608_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1641_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v_fst_1615_; lean_object* v_snd_1616_; lean_object* v___x_1617_; size_t v___x_1618_; size_t v___x_1619_; size_t v___x_1620_; uint64_t v___x_1621_; uint64_t v___x_1622_; uint64_t v___x_1623_; uint64_t v___x_1624_; uint64_t v___x_1625_; uint64_t v_fold_1626_; uint64_t v___x_1627_; uint64_t v___x_1628_; uint64_t v___x_1629_; size_t v___x_1630_; size_t v___x_1631_; size_t v___x_1632_; size_t v___x_1633_; size_t v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1637_; 
v_fst_1615_ = lean_ctor_get(v_key_1609_, 0);
v_snd_1616_ = lean_ctor_get(v_key_1609_, 1);
v___x_1617_ = lean_array_get_size(v_x_1607_);
v___x_1618_ = lean_ptr_addr(v_fst_1615_);
v___x_1619_ = ((size_t)3ULL);
v___x_1620_ = lean_usize_shift_right(v___x_1618_, v___x_1619_);
v___x_1621_ = lean_usize_to_uint64(v___x_1620_);
v___x_1622_ = lean_uint64_of_nat(v_snd_1616_);
v___x_1623_ = lean_uint64_mix_hash(v___x_1621_, v___x_1622_);
v___x_1624_ = 32ULL;
v___x_1625_ = lean_uint64_shift_right(v___x_1623_, v___x_1624_);
v_fold_1626_ = lean_uint64_xor(v___x_1623_, v___x_1625_);
v___x_1627_ = 16ULL;
v___x_1628_ = lean_uint64_shift_right(v_fold_1626_, v___x_1627_);
v___x_1629_ = lean_uint64_xor(v_fold_1626_, v___x_1628_);
v___x_1630_ = lean_uint64_to_usize(v___x_1629_);
v___x_1631_ = lean_usize_of_nat(v___x_1617_);
v___x_1632_ = ((size_t)1ULL);
v___x_1633_ = lean_usize_sub(v___x_1631_, v___x_1632_);
v___x_1634_ = lean_usize_land(v___x_1630_, v___x_1633_);
v___x_1635_ = lean_array_uget_borrowed(v_x_1607_, v___x_1634_);
lean_inc(v___x_1635_);
if (v_isShared_1614_ == 0)
{
lean_ctor_set(v___x_1613_, 2, v___x_1635_);
v___x_1637_ = v___x_1613_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v_key_1609_);
lean_ctor_set(v_reuseFailAlloc_1640_, 1, v_value_1610_);
lean_ctor_set(v_reuseFailAlloc_1640_, 2, v___x_1635_);
v___x_1637_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
lean_object* v___x_1638_; 
v___x_1638_ = lean_array_uset(v_x_1607_, v___x_1634_, v___x_1637_);
v_x_1607_ = v___x_1638_;
v_x_1608_ = v_tail_1611_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2___redArg(lean_object* v_i_1642_, lean_object* v_source_1643_, lean_object* v_target_1644_){
_start:
{
lean_object* v___x_1645_; uint8_t v___x_1646_; 
v___x_1645_ = lean_array_get_size(v_source_1643_);
v___x_1646_ = lean_nat_dec_lt(v_i_1642_, v___x_1645_);
if (v___x_1646_ == 0)
{
lean_dec_ref(v_source_1643_);
lean_dec(v_i_1642_);
return v_target_1644_;
}
else
{
lean_object* v_es_1647_; lean_object* v___x_1648_; lean_object* v_source_1649_; lean_object* v_target_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; 
v_es_1647_ = lean_array_fget(v_source_1643_, v_i_1642_);
v___x_1648_ = lean_box(0);
v_source_1649_ = lean_array_fset(v_source_1643_, v_i_1642_, v___x_1648_);
v_target_1650_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3___redArg(v_target_1644_, v_es_1647_);
v___x_1651_ = lean_unsigned_to_nat(1u);
v___x_1652_ = lean_nat_add(v_i_1642_, v___x_1651_);
lean_dec(v_i_1642_);
v_i_1642_ = v___x_1652_;
v_source_1643_ = v_source_1649_;
v_target_1644_ = v_target_1650_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1___redArg(lean_object* v_data_1654_){
_start:
{
lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v_nbuckets_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; 
v___x_1655_ = lean_array_get_size(v_data_1654_);
v___x_1656_ = lean_unsigned_to_nat(2u);
v_nbuckets_1657_ = lean_nat_mul(v___x_1655_, v___x_1656_);
v___x_1658_ = lean_unsigned_to_nat(0u);
v___x_1659_ = lean_box(0);
v___x_1660_ = lean_mk_array(v_nbuckets_1657_, v___x_1659_);
v___x_1661_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2___redArg(v___x_1658_, v_data_1654_, v___x_1660_);
return v___x_1661_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(lean_object* v_a_1662_, lean_object* v_b_1663_, lean_object* v_x_1664_){
_start:
{
if (lean_obj_tag(v_x_1664_) == 0)
{
lean_dec(v_b_1663_);
lean_dec_ref(v_a_1662_);
return v_x_1664_;
}
else
{
lean_object* v_key_1665_; lean_object* v_value_1666_; lean_object* v_tail_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1688_; 
v_key_1665_ = lean_ctor_get(v_x_1664_, 0);
v_value_1666_ = lean_ctor_get(v_x_1664_, 1);
v_tail_1667_ = lean_ctor_get(v_x_1664_, 2);
v_isSharedCheck_1688_ = !lean_is_exclusive(v_x_1664_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1669_ = v_x_1664_;
v_isShared_1670_ = v_isSharedCheck_1688_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_tail_1667_);
lean_inc(v_value_1666_);
lean_inc(v_key_1665_);
lean_dec(v_x_1664_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1688_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
uint8_t v___y_1672_; lean_object* v_fst_1680_; lean_object* v_snd_1681_; lean_object* v_fst_1682_; lean_object* v_snd_1683_; size_t v___x_1684_; size_t v___x_1685_; uint8_t v___x_1686_; 
v_fst_1680_ = lean_ctor_get(v_key_1665_, 0);
v_snd_1681_ = lean_ctor_get(v_key_1665_, 1);
v_fst_1682_ = lean_ctor_get(v_a_1662_, 0);
v_snd_1683_ = lean_ctor_get(v_a_1662_, 1);
v___x_1684_ = lean_ptr_addr(v_fst_1680_);
v___x_1685_ = lean_ptr_addr(v_fst_1682_);
v___x_1686_ = lean_usize_dec_eq(v___x_1684_, v___x_1685_);
if (v___x_1686_ == 0)
{
v___y_1672_ = v___x_1686_;
goto v___jp_1671_;
}
else
{
uint8_t v___x_1687_; 
v___x_1687_ = lean_nat_dec_eq(v_snd_1681_, v_snd_1683_);
v___y_1672_ = v___x_1687_;
goto v___jp_1671_;
}
v___jp_1671_:
{
if (v___y_1672_ == 0)
{
lean_object* v___x_1673_; lean_object* v___x_1675_; 
v___x_1673_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(v_a_1662_, v_b_1663_, v_tail_1667_);
if (v_isShared_1670_ == 0)
{
lean_ctor_set(v___x_1669_, 2, v___x_1673_);
v___x_1675_ = v___x_1669_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_key_1665_);
lean_ctor_set(v_reuseFailAlloc_1676_, 1, v_value_1666_);
lean_ctor_set(v_reuseFailAlloc_1676_, 2, v___x_1673_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
else
{
lean_object* v___x_1678_; 
lean_dec(v_value_1666_);
lean_dec(v_key_1665_);
if (v_isShared_1670_ == 0)
{
lean_ctor_set(v___x_1669_, 1, v_b_1663_);
lean_ctor_set(v___x_1669_, 0, v_a_1662_);
v___x_1678_ = v___x_1669_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_a_1662_);
lean_ctor_set(v_reuseFailAlloc_1679_, 1, v_b_1663_);
lean_ctor_set(v_reuseFailAlloc_1679_, 2, v_tail_1667_);
v___x_1678_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
return v___x_1678_;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(lean_object* v_a_1689_, lean_object* v_x_1690_){
_start:
{
if (lean_obj_tag(v_x_1690_) == 0)
{
uint8_t v___x_1691_; 
v___x_1691_ = 0;
return v___x_1691_;
}
else
{
lean_object* v_key_1692_; lean_object* v_tail_1693_; uint8_t v___y_1695_; lean_object* v_fst_1697_; lean_object* v_snd_1698_; lean_object* v_fst_1699_; lean_object* v_snd_1700_; size_t v___x_1701_; size_t v___x_1702_; uint8_t v___x_1703_; 
v_key_1692_ = lean_ctor_get(v_x_1690_, 0);
v_tail_1693_ = lean_ctor_get(v_x_1690_, 2);
v_fst_1697_ = lean_ctor_get(v_key_1692_, 0);
v_snd_1698_ = lean_ctor_get(v_key_1692_, 1);
v_fst_1699_ = lean_ctor_get(v_a_1689_, 0);
v_snd_1700_ = lean_ctor_get(v_a_1689_, 1);
v___x_1701_ = lean_ptr_addr(v_fst_1697_);
v___x_1702_ = lean_ptr_addr(v_fst_1699_);
v___x_1703_ = lean_usize_dec_eq(v___x_1701_, v___x_1702_);
if (v___x_1703_ == 0)
{
v___y_1695_ = v___x_1703_;
goto v___jp_1694_;
}
else
{
uint8_t v___x_1704_; 
v___x_1704_ = lean_nat_dec_eq(v_snd_1698_, v_snd_1700_);
v___y_1695_ = v___x_1704_;
goto v___jp_1694_;
}
v___jp_1694_:
{
if (v___y_1695_ == 0)
{
v_x_1690_ = v_tail_1693_;
goto _start;
}
else
{
return v___y_1695_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg___boxed(lean_object* v_a_1705_, lean_object* v_x_1706_){
_start:
{
uint8_t v_res_1707_; lean_object* v_r_1708_; 
v_res_1707_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_a_1705_, v_x_1706_);
lean_dec(v_x_1706_);
lean_dec_ref(v_a_1705_);
v_r_1708_ = lean_box(v_res_1707_);
return v_r_1708_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0___redArg(lean_object* v_m_1709_, lean_object* v_a_1710_, lean_object* v_b_1711_){
_start:
{
lean_object* v_size_1712_; lean_object* v_buckets_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1763_; 
v_size_1712_ = lean_ctor_get(v_m_1709_, 0);
v_buckets_1713_ = lean_ctor_get(v_m_1709_, 1);
v_isSharedCheck_1763_ = !lean_is_exclusive(v_m_1709_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1715_ = v_m_1709_;
v_isShared_1716_ = v_isSharedCheck_1763_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_buckets_1713_);
lean_inc(v_size_1712_);
lean_dec(v_m_1709_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1763_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v_fst_1717_; lean_object* v_snd_1718_; lean_object* v___x_1719_; size_t v___x_1720_; size_t v___x_1721_; size_t v___x_1722_; uint64_t v___x_1723_; uint64_t v___x_1724_; uint64_t v___x_1725_; uint64_t v___x_1726_; uint64_t v___x_1727_; uint64_t v_fold_1728_; uint64_t v___x_1729_; uint64_t v___x_1730_; uint64_t v___x_1731_; size_t v___x_1732_; size_t v___x_1733_; size_t v___x_1734_; size_t v___x_1735_; size_t v___x_1736_; lean_object* v_bkt_1737_; uint8_t v___x_1738_; 
v_fst_1717_ = lean_ctor_get(v_a_1710_, 0);
v_snd_1718_ = lean_ctor_get(v_a_1710_, 1);
v___x_1719_ = lean_array_get_size(v_buckets_1713_);
v___x_1720_ = lean_ptr_addr(v_fst_1717_);
v___x_1721_ = ((size_t)3ULL);
v___x_1722_ = lean_usize_shift_right(v___x_1720_, v___x_1721_);
v___x_1723_ = lean_usize_to_uint64(v___x_1722_);
v___x_1724_ = lean_uint64_of_nat(v_snd_1718_);
v___x_1725_ = lean_uint64_mix_hash(v___x_1723_, v___x_1724_);
v___x_1726_ = 32ULL;
v___x_1727_ = lean_uint64_shift_right(v___x_1725_, v___x_1726_);
v_fold_1728_ = lean_uint64_xor(v___x_1725_, v___x_1727_);
v___x_1729_ = 16ULL;
v___x_1730_ = lean_uint64_shift_right(v_fold_1728_, v___x_1729_);
v___x_1731_ = lean_uint64_xor(v_fold_1728_, v___x_1730_);
v___x_1732_ = lean_uint64_to_usize(v___x_1731_);
v___x_1733_ = lean_usize_of_nat(v___x_1719_);
v___x_1734_ = ((size_t)1ULL);
v___x_1735_ = lean_usize_sub(v___x_1733_, v___x_1734_);
v___x_1736_ = lean_usize_land(v___x_1732_, v___x_1735_);
v_bkt_1737_ = lean_array_uget_borrowed(v_buckets_1713_, v___x_1736_);
v___x_1738_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_a_1710_, v_bkt_1737_);
if (v___x_1738_ == 0)
{
lean_object* v___x_1739_; lean_object* v_size_x27_1740_; lean_object* v___x_1741_; lean_object* v_buckets_x27_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; uint8_t v___x_1748_; 
v___x_1739_ = lean_unsigned_to_nat(1u);
v_size_x27_1740_ = lean_nat_add(v_size_1712_, v___x_1739_);
lean_dec(v_size_1712_);
lean_inc(v_bkt_1737_);
v___x_1741_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1741_, 0, v_a_1710_);
lean_ctor_set(v___x_1741_, 1, v_b_1711_);
lean_ctor_set(v___x_1741_, 2, v_bkt_1737_);
v_buckets_x27_1742_ = lean_array_uset(v_buckets_1713_, v___x_1736_, v___x_1741_);
v___x_1743_ = lean_unsigned_to_nat(4u);
v___x_1744_ = lean_nat_mul(v_size_x27_1740_, v___x_1743_);
v___x_1745_ = lean_unsigned_to_nat(3u);
v___x_1746_ = lean_nat_div(v___x_1744_, v___x_1745_);
lean_dec(v___x_1744_);
v___x_1747_ = lean_array_get_size(v_buckets_x27_1742_);
v___x_1748_ = lean_nat_dec_le(v___x_1746_, v___x_1747_);
lean_dec(v___x_1746_);
if (v___x_1748_ == 0)
{
lean_object* v_val_1749_; lean_object* v___x_1751_; 
v_val_1749_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1___redArg(v_buckets_x27_1742_);
if (v_isShared_1716_ == 0)
{
lean_ctor_set(v___x_1715_, 1, v_val_1749_);
lean_ctor_set(v___x_1715_, 0, v_size_x27_1740_);
v___x_1751_ = v___x_1715_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v_size_x27_1740_);
lean_ctor_set(v_reuseFailAlloc_1752_, 1, v_val_1749_);
v___x_1751_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
return v___x_1751_;
}
}
else
{
lean_object* v___x_1754_; 
if (v_isShared_1716_ == 0)
{
lean_ctor_set(v___x_1715_, 1, v_buckets_x27_1742_);
lean_ctor_set(v___x_1715_, 0, v_size_x27_1740_);
v___x_1754_ = v___x_1715_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v_size_x27_1740_);
lean_ctor_set(v_reuseFailAlloc_1755_, 1, v_buckets_x27_1742_);
v___x_1754_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
return v___x_1754_;
}
}
}
else
{
lean_object* v___x_1756_; lean_object* v_buckets_x27_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1761_; 
lean_inc(v_bkt_1737_);
v___x_1756_ = lean_box(0);
v_buckets_x27_1757_ = lean_array_uset(v_buckets_1713_, v___x_1736_, v___x_1756_);
v___x_1758_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(v_a_1710_, v_b_1711_, v_bkt_1737_);
v___x_1759_ = lean_array_uset(v_buckets_x27_1757_, v___x_1736_, v___x_1758_);
if (v_isShared_1716_ == 0)
{
lean_ctor_set(v___x_1715_, 1, v___x_1759_);
v___x_1761_ = v___x_1715_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v_size_1712_);
lean_ctor_set(v_reuseFailAlloc_1762_, 1, v___x_1759_);
v___x_1761_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
return v___x_1761_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(lean_object* v_key_1764_, lean_object* v_r_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_){
_start:
{
lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; 
lean_inc_ref(v_r_1765_);
v___x_1768_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1766_, v_key_1764_, v_r_1765_);
v___x_1769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1769_, 0, v_r_1765_);
lean_ctor_set(v___x_1769_, 1, v___x_1768_);
v___x_1770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1770_, 0, v___x_1769_);
lean_ctor_set(v___x_1770_, 1, v_a_1767_);
return v___x_1770_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save(lean_object* v_key_1771_, lean_object* v_r_1772_, lean_object* v_a_1773_, uint8_t v_a_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_){
_start:
{
lean_object* v___x_1777_; 
v___x_1777_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_1771_, v_r_1772_, v_a_1773_, v_a_1776_);
return v___x_1777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___boxed(lean_object* v_key_1778_, lean_object* v_r_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_){
_start:
{
uint8_t v_a_boxed_1784_; lean_object* v_res_1785_; 
v_a_boxed_1784_ = lean_unbox(v_a_1781_);
v_res_1785_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save(v_key_1778_, v_r_1779_, v_a_1780_, v_a_boxed_1784_, v_a_1782_, v_a_1783_);
lean_dec_ref(v_a_1782_);
return v_res_1785_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0(lean_object* v_00_u03b2_1786_, lean_object* v_m_1787_, lean_object* v_a_1788_, lean_object* v_b_1789_){
_start:
{
lean_object* v___x_1790_; 
v___x_1790_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0___redArg(v_m_1787_, v_a_1788_, v_b_1789_);
return v___x_1790_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0(lean_object* v_00_u03b2_1791_, lean_object* v_a_1792_, lean_object* v_x_1793_){
_start:
{
uint8_t v___x_1794_; 
v___x_1794_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_a_1792_, v_x_1793_);
return v___x_1794_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1795_, lean_object* v_a_1796_, lean_object* v_x_1797_){
_start:
{
uint8_t v_res_1798_; lean_object* v_r_1799_; 
v_res_1798_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0(v_00_u03b2_1795_, v_a_1796_, v_x_1797_);
lean_dec(v_x_1797_);
lean_dec_ref(v_a_1796_);
v_r_1799_ = lean_box(v_res_1798_);
return v_r_1799_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1(lean_object* v_00_u03b2_1800_, lean_object* v_data_1801_){
_start:
{
lean_object* v___x_1802_; 
v___x_1802_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1___redArg(v_data_1801_);
return v___x_1802_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2(lean_object* v_00_u03b2_1803_, lean_object* v_a_1804_, lean_object* v_b_1805_, lean_object* v_x_1806_){
_start:
{
lean_object* v___x_1807_; 
v___x_1807_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(v_a_1804_, v_b_1805_, v_x_1806_);
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1808_, lean_object* v_i_1809_, lean_object* v_source_1810_, lean_object* v_target_1811_){
_start:
{
lean_object* v___x_1812_; 
v___x_1812_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2___redArg(v_i_1809_, v_source_1810_, v_target_1811_);
return v___x_1812_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1813_, lean_object* v_x_1814_, lean_object* v_x_1815_){
_start:
{
lean_object* v___x_1816_; 
v___x_1816_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1814_, v_x_1815_);
return v___x_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0___redArg(lean_object* v_idx_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_){
_start:
{
lean_object* v___x_1820_; lean_object* v___x_1821_; 
v___x_1820_ = l_Lean_Expr_bvar___override(v_idx_1817_);
v___x_1821_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1820_, v___y_1819_);
if (lean_obj_tag(v___x_1821_) == 0)
{
lean_object* v_a_1822_; lean_object* v_a_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1831_; 
v_a_1822_ = lean_ctor_get(v___x_1821_, 0);
v_a_1823_ = lean_ctor_get(v___x_1821_, 1);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1825_ = v___x_1821_;
v_isShared_1826_ = v_isSharedCheck_1831_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_a_1823_);
lean_inc(v_a_1822_);
lean_dec(v___x_1821_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1831_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v___x_1827_; lean_object* v___x_1829_; 
v___x_1827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1827_, 0, v_a_1822_);
lean_ctor_set(v___x_1827_, 1, v___y_1818_);
if (v_isShared_1826_ == 0)
{
lean_ctor_set(v___x_1825_, 0, v___x_1827_);
v___x_1829_ = v___x_1825_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v___x_1827_);
lean_ctor_set(v_reuseFailAlloc_1830_, 1, v_a_1823_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
}
else
{
lean_object* v_a_1832_; lean_object* v_a_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1840_; 
lean_dec_ref(v___y_1818_);
v_a_1832_ = lean_ctor_get(v___x_1821_, 0);
v_a_1833_ = lean_ctor_get(v___x_1821_, 1);
v_isSharedCheck_1840_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1835_ = v___x_1821_;
v_isShared_1836_ = v_isSharedCheck_1840_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_a_1833_);
lean_inc(v_a_1832_);
lean_dec(v___x_1821_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1840_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v___x_1838_; 
if (v_isShared_1836_ == 0)
{
v___x_1838_ = v___x_1835_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v_a_1832_);
lean_ctor_set(v_reuseFailAlloc_1839_, 1, v_a_1833_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0(lean_object* v_idx_1841_, lean_object* v___y_1842_, uint8_t v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_){
_start:
{
lean_object* v___x_1846_; 
v___x_1846_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0___redArg(v_idx_1841_, v___y_1842_, v___y_1845_);
return v___x_1846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0___boxed(lean_object* v_idx_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_){
_start:
{
uint8_t v___y_1133__boxed_1852_; lean_object* v_res_1853_; 
v___y_1133__boxed_1852_ = lean_unbox(v___y_1849_);
v_res_1853_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0(v_idx_1847_, v___y_1848_, v___y_1133__boxed_1852_, v___y_1850_, v___y_1851_);
lean_dec_ref(v___y_1850_);
return v_res_1853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(lean_object* v_subst_1854_, lean_object* v_e_1855_, lean_object* v_bidx_1856_, lean_object* v_offset_1857_, lean_object* v_a_1858_, uint8_t v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_){
_start:
{
uint8_t v___x_1862_; 
v___x_1862_ = lean_nat_dec_le(v_offset_1857_, v_bidx_1856_);
if (v___x_1862_ == 0)
{
lean_object* v___x_1863_; lean_object* v___x_1864_; 
v___x_1863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1863_, 0, v_e_1855_);
lean_ctor_set(v___x_1863_, 1, v_a_1858_);
v___x_1864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1863_);
lean_ctor_set(v___x_1864_, 1, v_a_1861_);
return v___x_1864_;
}
else
{
lean_object* v_n_1865_; lean_object* v___x_1866_; uint8_t v___x_1867_; 
lean_dec_ref(v_e_1855_);
v_n_1865_ = lean_array_get_size(v_subst_1854_);
v___x_1866_ = lean_nat_add(v_offset_1857_, v_n_1865_);
v___x_1867_ = lean_nat_dec_lt(v_bidx_1856_, v___x_1866_);
lean_dec(v___x_1866_);
if (v___x_1867_ == 0)
{
lean_object* v___x_1868_; lean_object* v___x_1869_; 
v___x_1868_ = lean_nat_sub(v_bidx_1856_, v_n_1865_);
v___x_1869_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0___redArg(v___x_1868_, v_a_1858_, v_a_1861_);
return v___x_1869_;
}
else
{
lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v_v_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; 
v___x_1870_ = lean_nat_sub(v_bidx_1856_, v_offset_1857_);
v___x_1871_ = lean_nat_sub(v_n_1865_, v___x_1870_);
lean_dec(v___x_1870_);
v___x_1872_ = lean_unsigned_to_nat(1u);
v___x_1873_ = lean_nat_sub(v___x_1871_, v___x_1872_);
lean_dec(v___x_1871_);
v_v_1874_ = lean_array_fget_borrowed(v_subst_1854_, v___x_1873_);
lean_dec(v___x_1873_);
v___x_1875_ = lean_unsigned_to_nat(0u);
lean_inc(v_v_1874_);
v___x_1876_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(v_v_1874_, v___x_1875_, v_offset_1857_, v_a_1859_, v_a_1860_, v_a_1861_);
if (lean_obj_tag(v___x_1876_) == 0)
{
lean_object* v_a_1877_; lean_object* v_a_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1886_; 
v_a_1877_ = lean_ctor_get(v___x_1876_, 0);
v_a_1878_ = lean_ctor_get(v___x_1876_, 1);
v_isSharedCheck_1886_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1880_ = v___x_1876_;
v_isShared_1881_ = v_isSharedCheck_1886_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_a_1878_);
lean_inc(v_a_1877_);
lean_dec(v___x_1876_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1886_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1882_; lean_object* v___x_1884_; 
v___x_1882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1882_, 0, v_a_1877_);
lean_ctor_set(v___x_1882_, 1, v_a_1858_);
if (v_isShared_1881_ == 0)
{
lean_ctor_set(v___x_1880_, 0, v___x_1882_);
v___x_1884_ = v___x_1880_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v___x_1882_);
lean_ctor_set(v_reuseFailAlloc_1885_, 1, v_a_1878_);
v___x_1884_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
return v___x_1884_;
}
}
}
else
{
lean_object* v_a_1887_; lean_object* v_a_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1895_; 
lean_dec_ref(v_a_1858_);
v_a_1887_ = lean_ctor_get(v___x_1876_, 0);
v_a_1888_ = lean_ctor_get(v___x_1876_, 1);
v_isSharedCheck_1895_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1890_ = v___x_1876_;
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_a_1888_);
lean_inc(v_a_1887_);
lean_dec(v___x_1876_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___x_1893_; 
if (v_isShared_1891_ == 0)
{
v___x_1893_ = v___x_1890_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_a_1887_);
lean_ctor_set(v_reuseFailAlloc_1894_, 1, v_a_1888_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar___boxed(lean_object* v_subst_1896_, lean_object* v_e_1897_, lean_object* v_bidx_1898_, lean_object* v_offset_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_){
_start:
{
uint8_t v_a_boxed_1904_; lean_object* v_res_1905_; 
v_a_boxed_1904_ = lean_unbox(v_a_1901_);
v_res_1905_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(v_subst_1896_, v_e_1897_, v_bidx_1898_, v_offset_1899_, v_a_1900_, v_a_boxed_1904_, v_a_1902_, v_a_1903_);
lean_dec_ref(v_a_1902_);
lean_dec(v_offset_1899_);
lean_dec(v_bidx_1898_);
lean_dec_ref(v_subst_1896_);
return v_res_1905_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault(lean_object* v_subst_1906_, lean_object* v_e_1907_, lean_object* v_offset_1908_, lean_object* v_a_1909_, uint8_t v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_){
_start:
{
if (lean_obj_tag(v_e_1907_) == 5)
{
lean_object* v_fn_1913_; lean_object* v_arg_1914_; lean_object* v_key_1915_; lean_object* v___x_1916_; 
v_fn_1913_ = lean_ctor_get(v_e_1907_, 0);
v_arg_1914_ = lean_ctor_get(v_e_1907_, 1);
lean_inc(v_offset_1908_);
lean_inc_ref(v_e_1907_);
v_key_1915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1915_, 0, v_e_1907_);
lean_ctor_set(v_key_1915_, 1, v_offset_1908_);
v___x_1916_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3___redArg(v_a_1909_, v_key_1915_);
if (lean_obj_tag(v___x_1916_) == 1)
{
lean_object* v_val_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
lean_dec_ref_known(v_key_1915_, 2);
lean_dec_ref_known(v_e_1907_, 2);
lean_dec(v_offset_1908_);
v_val_1917_ = lean_ctor_get(v___x_1916_, 0);
lean_inc(v_val_1917_);
lean_dec_ref_known(v___x_1916_, 1);
v___x_1918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1918_, 0, v_val_1917_);
lean_ctor_set(v___x_1918_, 1, v_a_1909_);
v___x_1919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1918_);
lean_ctor_set(v___x_1919_, 1, v_a_1912_);
return v___x_1919_;
}
else
{
lean_object* v___x_1920_; 
lean_dec(v___x_1916_);
lean_inc(v_offset_1908_);
lean_inc_ref(v_fn_1913_);
v___x_1920_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault(v_subst_1906_, v_fn_1913_, v_offset_1908_, v_a_1909_, v_a_1910_, v_a_1911_, v_a_1912_);
if (lean_obj_tag(v___x_1920_) == 0)
{
lean_object* v_a_1921_; lean_object* v_a_1922_; lean_object* v_fst_1923_; lean_object* v_snd_1924_; lean_object* v___x_1925_; 
v_a_1921_ = lean_ctor_get(v___x_1920_, 0);
lean_inc(v_a_1921_);
v_a_1922_ = lean_ctor_get(v___x_1920_, 1);
lean_inc(v_a_1922_);
lean_dec_ref_known(v___x_1920_, 2);
v_fst_1923_ = lean_ctor_get(v_a_1921_, 0);
lean_inc(v_fst_1923_);
v_snd_1924_ = lean_ctor_get(v_a_1921_, 1);
lean_inc(v_snd_1924_);
lean_dec(v_a_1921_);
lean_inc_ref(v_arg_1914_);
v___x_1925_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1906_, v_arg_1914_, v_offset_1908_, v_snd_1924_, v_a_1910_, v_a_1911_, v_a_1922_);
if (lean_obj_tag(v___x_1925_) == 0)
{
lean_object* v_a_1926_; lean_object* v_a_1927_; lean_object* v_fst_1928_; lean_object* v_snd_1929_; uint8_t v___y_1931_; size_t v___x_1939_; size_t v___x_1940_; uint8_t v___x_1941_; 
v_a_1926_ = lean_ctor_get(v___x_1925_, 0);
lean_inc(v_a_1926_);
v_a_1927_ = lean_ctor_get(v___x_1925_, 1);
lean_inc(v_a_1927_);
lean_dec_ref_known(v___x_1925_, 2);
v_fst_1928_ = lean_ctor_get(v_a_1926_, 0);
lean_inc(v_fst_1928_);
v_snd_1929_ = lean_ctor_get(v_a_1926_, 1);
lean_inc(v_snd_1929_);
lean_dec(v_a_1926_);
v___x_1939_ = lean_ptr_addr(v_fn_1913_);
v___x_1940_ = lean_ptr_addr(v_fst_1923_);
v___x_1941_ = lean_usize_dec_eq(v___x_1939_, v___x_1940_);
if (v___x_1941_ == 0)
{
v___y_1931_ = v___x_1941_;
goto v___jp_1930_;
}
else
{
size_t v___x_1942_; size_t v___x_1943_; uint8_t v___x_1944_; 
v___x_1942_ = lean_ptr_addr(v_arg_1914_);
v___x_1943_ = lean_ptr_addr(v_fst_1928_);
v___x_1944_ = lean_usize_dec_eq(v___x_1942_, v___x_1943_);
v___y_1931_ = v___x_1944_;
goto v___jp_1930_;
}
v___jp_1930_:
{
if (v___y_1931_ == 0)
{
lean_object* v___x_1932_; 
lean_dec_ref_known(v_e_1907_, 2);
v___x_1932_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__2(v_fst_1923_, v_fst_1928_, v_snd_1929_, v_a_1910_, v_a_1911_, v_a_1927_);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v_a_1933_; lean_object* v_a_1934_; lean_object* v_fst_1935_; lean_object* v_snd_1936_; lean_object* v___x_1937_; 
v_a_1933_ = lean_ctor_get(v___x_1932_, 0);
lean_inc(v_a_1933_);
v_a_1934_ = lean_ctor_get(v___x_1932_, 1);
lean_inc(v_a_1934_);
lean_dec_ref_known(v___x_1932_, 2);
v_fst_1935_ = lean_ctor_get(v_a_1933_, 0);
lean_inc(v_fst_1935_);
v_snd_1936_ = lean_ctor_get(v_a_1933_, 1);
lean_inc(v_snd_1936_);
lean_dec(v_a_1933_);
v___x_1937_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_1915_, v_fst_1935_, v_snd_1936_, v_a_1934_);
return v___x_1937_;
}
else
{
lean_dec_ref_known(v_key_1915_, 2);
return v___x_1932_;
}
}
else
{
lean_object* v___x_1938_; 
lean_dec(v_fst_1928_);
lean_dec(v_fst_1923_);
v___x_1938_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_1915_, v_e_1907_, v_snd_1929_, v_a_1927_);
return v___x_1938_;
}
}
}
else
{
lean_dec(v_fst_1923_);
lean_dec_ref_known(v_key_1915_, 2);
lean_dec_ref_known(v_e_1907_, 2);
return v___x_1925_;
}
}
else
{
lean_dec_ref_known(v_key_1915_, 2);
lean_dec_ref_known(v_e_1907_, 2);
lean_dec(v_offset_1908_);
return v___x_1920_;
}
}
}
else
{
lean_object* v___x_1945_; 
v___x_1945_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1906_, v_e_1907_, v_offset_1908_, v_a_1909_, v_a_1910_, v_a_1911_, v_a_1912_);
return v___x_1945_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__2(void){
_start:
{
lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; 
v___x_1948_ = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__1));
v___x_1949_ = lean_unsigned_to_nat(25u);
v___x_1950_ = lean_unsigned_to_nat(148u);
v___x_1951_ = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__0));
v___x_1952_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__0));
v___x_1953_ = l_mkPanicMessageWithDecl(v___x_1952_, v___x_1951_, v___x_1950_, v___x_1949_, v___x_1948_);
return v___x_1953_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__1(void){
_start:
{
lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___x_1955_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__2));
v___x_1956_ = lean_unsigned_to_nat(11u);
v___x_1957_ = lean_unsigned_to_nat(165u);
v___x_1958_ = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__0));
v___x_1959_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__3));
v___x_1960_ = l_mkPanicMessageWithDecl(v___x_1959_, v___x_1958_, v___x_1957_, v___x_1956_, v___x_1955_);
return v___x_1960_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta(lean_object* v_subst_1961_, lean_object* v_e_1962_, lean_object* v_f_1963_, lean_object* v_argsRev_1964_, lean_object* v_offset_1965_, uint8_t v_modified_1966_, lean_object* v_a_1967_, uint8_t v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_){
_start:
{
switch(lean_obj_tag(v_f_1963_))
{
case 5:
{
lean_object* v_fn_1971_; lean_object* v_arg_1972_; lean_object* v___x_1973_; 
v_fn_1971_ = lean_ctor_get(v_f_1963_, 0);
lean_inc_ref(v_fn_1971_);
v_arg_1972_ = lean_ctor_get(v_f_1963_, 1);
lean_inc_ref_n(v_arg_1972_, 2);
lean_dec_ref_known(v_f_1963_, 2);
lean_inc(v_offset_1965_);
v___x_1973_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1961_, v_arg_1972_, v_offset_1965_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_);
if (lean_obj_tag(v___x_1973_) == 0)
{
lean_object* v_a_1974_; lean_object* v_a_1975_; lean_object* v_fst_1976_; lean_object* v_snd_1977_; lean_object* v___x_1978_; 
v_a_1974_ = lean_ctor_get(v___x_1973_, 0);
lean_inc(v_a_1974_);
v_a_1975_ = lean_ctor_get(v___x_1973_, 1);
lean_inc(v_a_1975_);
lean_dec_ref_known(v___x_1973_, 2);
v_fst_1976_ = lean_ctor_get(v_a_1974_, 0);
lean_inc_n(v_fst_1976_, 2);
v_snd_1977_ = lean_ctor_get(v_a_1974_, 1);
lean_inc(v_snd_1977_);
lean_dec(v_a_1974_);
v___x_1978_ = lean_array_push(v_argsRev_1964_, v_fst_1976_);
if (v_modified_1966_ == 0)
{
size_t v___x_1979_; size_t v___x_1980_; uint8_t v___x_1981_; 
v___x_1979_ = lean_ptr_addr(v_arg_1972_);
lean_dec_ref(v_arg_1972_);
v___x_1980_ = lean_ptr_addr(v_fst_1976_);
lean_dec(v_fst_1976_);
v___x_1981_ = lean_usize_dec_eq(v___x_1979_, v___x_1980_);
if (v___x_1981_ == 0)
{
uint8_t v___x_1982_; 
v___x_1982_ = 1;
v_f_1963_ = v_fn_1971_;
v_argsRev_1964_ = v___x_1978_;
v_modified_1966_ = v___x_1982_;
v_a_1967_ = v_snd_1977_;
v_a_1970_ = v_a_1975_;
goto _start;
}
else
{
v_f_1963_ = v_fn_1971_;
v_argsRev_1964_ = v___x_1978_;
v_a_1967_ = v_snd_1977_;
v_a_1970_ = v_a_1975_;
goto _start;
}
}
else
{
lean_dec(v_fst_1976_);
lean_dec_ref(v_arg_1972_);
v_f_1963_ = v_fn_1971_;
v_argsRev_1964_ = v___x_1978_;
v_a_1967_ = v_snd_1977_;
v_a_1970_ = v_a_1975_;
goto _start;
}
}
else
{
lean_dec_ref(v_arg_1972_);
lean_dec_ref(v_fn_1971_);
lean_dec(v_offset_1965_);
lean_dec_ref(v_argsRev_1964_);
lean_dec_ref(v_e_1962_);
return v___x_1973_;
}
}
case 0:
{
lean_object* v_deBruijnIndex_1986_; lean_object* v___x_1987_; 
v_deBruijnIndex_1986_ = lean_ctor_get(v_f_1963_, 0);
lean_inc_ref(v_f_1963_);
v___x_1987_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(v_subst_1961_, v_f_1963_, v_deBruijnIndex_1986_, v_offset_1965_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_);
lean_dec(v_offset_1965_);
if (lean_obj_tag(v___x_1987_) == 0)
{
lean_object* v_a_1988_; lean_object* v_a_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_2029_; 
v_a_1988_ = lean_ctor_get(v___x_1987_, 0);
v_a_1989_ = lean_ctor_get(v___x_1987_, 1);
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_1987_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_1991_ = v___x_1987_;
v_isShared_1992_ = v_isSharedCheck_2029_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_a_1989_);
lean_inc(v_a_1988_);
lean_dec(v___x_1987_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_2029_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v_fst_1993_; lean_object* v_snd_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2028_; 
v_fst_1993_ = lean_ctor_get(v_a_1988_, 0);
v_snd_1994_ = lean_ctor_get(v_a_1988_, 1);
v_isSharedCheck_2028_ = !lean_is_exclusive(v_a_1988_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_1996_ = v_a_1988_;
v_isShared_1997_ = v_isSharedCheck_2028_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_snd_1994_);
lean_inc(v_fst_1993_);
lean_dec(v_a_1988_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2028_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
if (v_modified_1966_ == 0)
{
size_t v___x_2021_; size_t v___x_2022_; uint8_t v___x_2023_; 
v___x_2021_ = lean_ptr_addr(v_f_1963_);
lean_dec_ref_known(v_f_1963_, 1);
v___x_2022_ = lean_ptr_addr(v_fst_1993_);
v___x_2023_ = lean_usize_dec_eq(v___x_2021_, v___x_2022_);
if (v___x_2023_ == 0)
{
lean_del_object(v___x_1991_);
lean_dec_ref(v_e_1962_);
goto v___jp_1998_;
}
else
{
lean_object* v___x_2024_; lean_object* v___x_2026_; 
lean_del_object(v___x_1996_);
lean_dec(v_fst_1993_);
lean_dec_ref(v_argsRev_1964_);
v___x_2024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2024_, 0, v_e_1962_);
lean_ctor_set(v___x_2024_, 1, v_snd_1994_);
if (v_isShared_1992_ == 0)
{
lean_ctor_set(v___x_1991_, 0, v___x_2024_);
v___x_2026_ = v___x_1991_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v___x_2024_);
lean_ctor_set(v_reuseFailAlloc_2027_, 1, v_a_1989_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
return v___x_2026_;
}
}
}
else
{
lean_del_object(v___x_1991_);
lean_dec_ref_known(v_f_1963_, 1);
lean_dec_ref(v_e_1962_);
goto v___jp_1998_;
}
v___jp_1998_:
{
lean_object* v___x_1999_; 
v___x_1999_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27(v_fst_1993_, v_argsRev_1964_, v_a_1968_, v_a_1969_, v_a_1989_);
lean_dec_ref(v_argsRev_1964_);
if (lean_obj_tag(v___x_1999_) == 0)
{
lean_object* v_a_2000_; lean_object* v_a_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2011_; 
v_a_2000_ = lean_ctor_get(v___x_1999_, 0);
v_a_2001_ = lean_ctor_get(v___x_1999_, 1);
v_isSharedCheck_2011_ = !lean_is_exclusive(v___x_1999_);
if (v_isSharedCheck_2011_ == 0)
{
v___x_2003_ = v___x_1999_;
v_isShared_2004_ = v_isSharedCheck_2011_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_a_2001_);
lean_inc(v_a_2000_);
lean_dec(v___x_1999_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2011_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2006_; 
if (v_isShared_1997_ == 0)
{
lean_ctor_set(v___x_1996_, 0, v_a_2000_);
v___x_2006_ = v___x_1996_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v_a_2000_);
lean_ctor_set(v_reuseFailAlloc_2010_, 1, v_snd_1994_);
v___x_2006_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
lean_object* v___x_2008_; 
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 0, v___x_2006_);
v___x_2008_ = v___x_2003_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v___x_2006_);
lean_ctor_set(v_reuseFailAlloc_2009_, 1, v_a_2001_);
v___x_2008_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
return v___x_2008_;
}
}
}
}
else
{
lean_object* v_a_2012_; lean_object* v_a_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2020_; 
lean_del_object(v___x_1996_);
lean_dec(v_snd_1994_);
v_a_2012_ = lean_ctor_get(v___x_1999_, 0);
v_a_2013_ = lean_ctor_get(v___x_1999_, 1);
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_1999_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2015_ = v___x_1999_;
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_a_2013_);
lean_inc(v_a_2012_);
lean_dec(v___x_1999_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v___x_2018_; 
if (v_isShared_2016_ == 0)
{
v___x_2018_ = v___x_2015_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_a_2012_);
lean_ctor_set(v_reuseFailAlloc_2019_, 1, v_a_2013_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_f_1963_, 1);
lean_dec_ref(v_argsRev_1964_);
lean_dec_ref(v_e_1962_);
return v___x_1987_;
}
}
default: 
{
lean_object* v___x_2030_; lean_object* v___x_2031_; 
lean_dec(v_offset_1965_);
lean_dec_ref(v_argsRev_1964_);
lean_dec_ref(v_f_1963_);
lean_dec_ref(v_e_1962_);
v___x_2030_ = lean_obj_once(&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__1, &l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__1_once, _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__1);
v___x_2031_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8(v___x_2030_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_);
return v___x_2031_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg(lean_object* v_subst_2032_, lean_object* v_e_2033_, lean_object* v_f_2034_, lean_object* v_arg_2035_, lean_object* v_offset_2036_, lean_object* v_a_2037_, uint8_t v_a_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_){
_start:
{
lean_object* v___x_2041_; 
lean_inc(v_offset_2036_);
lean_inc_ref(v_arg_2035_);
v___x_2041_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_2032_, v_arg_2035_, v_offset_2036_, v_a_2037_, v_a_2038_, v_a_2039_, v_a_2040_);
if (lean_obj_tag(v___x_2041_) == 0)
{
lean_object* v_a_2042_; lean_object* v_a_2043_; lean_object* v_fst_2044_; lean_object* v_snd_2045_; lean_object* v___x_2046_; uint8_t v___x_2047_; 
v_a_2042_ = lean_ctor_get(v___x_2041_, 0);
lean_inc(v_a_2042_);
v_a_2043_ = lean_ctor_get(v___x_2041_, 1);
lean_inc(v_a_2043_);
lean_dec_ref_known(v___x_2041_, 2);
v_fst_2044_ = lean_ctor_get(v_a_2042_, 0);
lean_inc(v_fst_2044_);
v_snd_2045_ = lean_ctor_get(v_a_2042_, 1);
lean_inc(v_snd_2045_);
lean_dec(v_a_2042_);
v___x_2046_ = l_Lean_Expr_getAppFn(v_f_2034_);
v___x_2047_ = l_Lean_Expr_isBVar(v___x_2046_);
lean_dec_ref(v___x_2046_);
if (v___x_2047_ == 0)
{
lean_object* v___x_2048_; 
lean_dec_ref(v_arg_2035_);
v___x_2048_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault(v_subst_2032_, v_f_2034_, v_offset_2036_, v_snd_2045_, v_a_2038_, v_a_2039_, v_a_2043_);
if (lean_obj_tag(v___x_2048_) == 0)
{
lean_object* v_a_2049_; lean_object* v_a_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2079_; 
v_a_2049_ = lean_ctor_get(v___x_2048_, 0);
v_a_2050_ = lean_ctor_get(v___x_2048_, 1);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2048_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2052_ = v___x_2048_;
v_isShared_2053_ = v_isSharedCheck_2079_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_a_2050_);
lean_inc(v_a_2049_);
lean_dec(v___x_2048_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2079_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v_fst_2054_; lean_object* v_snd_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2078_; 
v_fst_2054_ = lean_ctor_get(v_a_2049_, 0);
v_snd_2055_ = lean_ctor_get(v_a_2049_, 1);
v_isSharedCheck_2078_ = !lean_is_exclusive(v_a_2049_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2057_ = v_a_2049_;
v_isShared_2058_ = v_isSharedCheck_2078_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_snd_2055_);
lean_inc(v_fst_2054_);
lean_dec(v_a_2049_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2078_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
uint8_t v___y_2060_; 
if (lean_obj_tag(v_e_2033_) == 5)
{
lean_object* v_fn_2068_; lean_object* v_arg_2069_; size_t v___x_2070_; size_t v___x_2071_; uint8_t v___x_2072_; 
v_fn_2068_ = lean_ctor_get(v_e_2033_, 0);
v_arg_2069_ = lean_ctor_get(v_e_2033_, 1);
v___x_2070_ = lean_ptr_addr(v_fn_2068_);
v___x_2071_ = lean_ptr_addr(v_fst_2054_);
v___x_2072_ = lean_usize_dec_eq(v___x_2070_, v___x_2071_);
if (v___x_2072_ == 0)
{
v___y_2060_ = v___x_2072_;
goto v___jp_2059_;
}
else
{
size_t v___x_2073_; size_t v___x_2074_; uint8_t v___x_2075_; 
v___x_2073_ = lean_ptr_addr(v_arg_2069_);
v___x_2074_ = lean_ptr_addr(v_fst_2044_);
v___x_2075_ = lean_usize_dec_eq(v___x_2073_, v___x_2074_);
v___y_2060_ = v___x_2075_;
goto v___jp_2059_;
}
}
else
{
lean_object* v___x_2076_; lean_object* v___x_2077_; 
lean_del_object(v___x_2057_);
lean_dec(v_fst_2054_);
lean_del_object(v___x_2052_);
lean_dec(v_fst_2044_);
lean_dec_ref(v_e_2033_);
v___x_2076_ = lean_obj_once(&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__2, &l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__2_once, _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__2);
v___x_2077_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8(v___x_2076_, v_snd_2055_, v_a_2038_, v_a_2039_, v_a_2050_);
return v___x_2077_;
}
v___jp_2059_:
{
if (v___y_2060_ == 0)
{
lean_object* v___x_2061_; 
lean_del_object(v___x_2057_);
lean_del_object(v___x_2052_);
lean_dec_ref(v_e_2033_);
v___x_2061_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__2(v_fst_2054_, v_fst_2044_, v_snd_2055_, v_a_2038_, v_a_2039_, v_a_2050_);
return v___x_2061_;
}
else
{
lean_object* v___x_2063_; 
lean_dec(v_fst_2054_);
lean_dec(v_fst_2044_);
if (v_isShared_2058_ == 0)
{
lean_ctor_set(v___x_2057_, 0, v_e_2033_);
v___x_2063_ = v___x_2057_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v_e_2033_);
lean_ctor_set(v_reuseFailAlloc_2067_, 1, v_snd_2055_);
v___x_2063_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
lean_object* v___x_2065_; 
if (v_isShared_2053_ == 0)
{
lean_ctor_set(v___x_2052_, 0, v___x_2063_);
v___x_2065_ = v___x_2052_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v___x_2063_);
lean_ctor_set(v_reuseFailAlloc_2066_, 1, v_a_2050_);
v___x_2065_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
return v___x_2065_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_2044_);
lean_dec_ref(v_e_2033_);
return v___x_2048_;
}
}
else
{
lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; size_t v___x_2083_; size_t v___x_2084_; uint8_t v___x_2085_; 
v___x_2080_ = lean_unsigned_to_nat(1u);
v___x_2081_ = lean_mk_empty_array_with_capacity(v___x_2080_);
lean_inc(v_fst_2044_);
v___x_2082_ = lean_array_push(v___x_2081_, v_fst_2044_);
v___x_2083_ = lean_ptr_addr(v_arg_2035_);
lean_dec_ref(v_arg_2035_);
v___x_2084_ = lean_ptr_addr(v_fst_2044_);
lean_dec(v_fst_2044_);
v___x_2085_ = lean_usize_dec_eq(v___x_2083_, v___x_2084_);
if (v___x_2085_ == 0)
{
lean_object* v___x_2086_; 
v___x_2086_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta(v_subst_2032_, v_e_2033_, v_f_2034_, v___x_2082_, v_offset_2036_, v___x_2047_, v_snd_2045_, v_a_2038_, v_a_2039_, v_a_2043_);
return v___x_2086_;
}
else
{
uint8_t v___x_2087_; lean_object* v___x_2088_; 
v___x_2087_ = 0;
v___x_2088_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta(v_subst_2032_, v_e_2033_, v_f_2034_, v___x_2082_, v_offset_2036_, v___x_2087_, v_snd_2045_, v_a_2038_, v_a_2039_, v_a_2043_);
return v___x_2088_;
}
}
}
else
{
lean_dec(v_offset_2036_);
lean_dec_ref(v_arg_2035_);
lean_dec_ref(v_f_2034_);
lean_dec_ref(v_e_2033_);
return v___x_2041_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__1(void){
_start:
{
lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; 
v___x_2090_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__2));
v___x_2091_ = lean_unsigned_to_nat(59u);
v___x_2092_ = lean_unsigned_to_nat(176u);
v___x_2093_ = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__0));
v___x_2094_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__3));
v___x_2095_ = l_mkPanicMessageWithDecl(v___x_2094_, v___x_2093_, v___x_2092_, v___x_2091_, v___x_2090_);
return v___x_2095_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit(lean_object* v_subst_2096_, lean_object* v_e_2097_, lean_object* v_offset_2098_, lean_object* v_a_2099_, uint8_t v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_){
_start:
{
switch(lean_obj_tag(v_e_2097_))
{
case 0:
{
lean_object* v_deBruijnIndex_2103_; lean_object* v___x_2104_; 
v_deBruijnIndex_2103_ = lean_ctor_get(v_e_2097_, 0);
lean_inc(v_deBruijnIndex_2103_);
v___x_2104_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(v_subst_2096_, v_e_2097_, v_deBruijnIndex_2103_, v_offset_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_);
lean_dec(v_offset_2098_);
lean_dec(v_deBruijnIndex_2103_);
return v___x_2104_;
}
case 5:
{
lean_object* v_fn_2105_; lean_object* v_arg_2106_; lean_object* v___x_2107_; 
v_fn_2105_ = lean_ctor_get(v_e_2097_, 0);
lean_inc_ref(v_fn_2105_);
v_arg_2106_ = lean_ctor_get(v_e_2097_, 1);
lean_inc_ref(v_arg_2106_);
v___x_2107_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg(v_subst_2096_, v_e_2097_, v_fn_2105_, v_arg_2106_, v_offset_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_);
return v___x_2107_;
}
case 6:
{
lean_object* v_binderName_2108_; lean_object* v_binderType_2109_; lean_object* v_body_2110_; uint8_t v_binderInfo_2111_; lean_object* v___x_2112_; 
v_binderName_2108_ = lean_ctor_get(v_e_2097_, 0);
v_binderType_2109_ = lean_ctor_get(v_e_2097_, 1);
v_body_2110_ = lean_ctor_get(v_e_2097_, 2);
v_binderInfo_2111_ = lean_ctor_get_uint8(v_e_2097_, sizeof(void*)*3 + 8);
lean_inc(v_offset_2098_);
lean_inc_ref(v_binderType_2109_);
v___x_2112_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_2096_, v_binderType_2109_, v_offset_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_);
if (lean_obj_tag(v___x_2112_) == 0)
{
lean_object* v_a_2113_; lean_object* v_a_2114_; lean_object* v_fst_2115_; lean_object* v_snd_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; 
v_a_2113_ = lean_ctor_get(v___x_2112_, 0);
lean_inc(v_a_2113_);
v_a_2114_ = lean_ctor_get(v___x_2112_, 1);
lean_inc(v_a_2114_);
lean_dec_ref_known(v___x_2112_, 2);
v_fst_2115_ = lean_ctor_get(v_a_2113_, 0);
lean_inc(v_fst_2115_);
v_snd_2116_ = lean_ctor_get(v_a_2113_, 1);
lean_inc(v_snd_2116_);
lean_dec(v_a_2113_);
v___x_2117_ = lean_unsigned_to_nat(1u);
v___x_2118_ = lean_nat_add(v_offset_2098_, v___x_2117_);
lean_dec(v_offset_2098_);
lean_inc_ref(v_body_2110_);
v___x_2119_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_2096_, v_body_2110_, v___x_2118_, v_snd_2116_, v_a_2100_, v_a_2101_, v_a_2114_);
if (lean_obj_tag(v___x_2119_) == 0)
{
lean_object* v_a_2120_; lean_object* v_a_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2146_; 
v_a_2120_ = lean_ctor_get(v___x_2119_, 0);
v_a_2121_ = lean_ctor_get(v___x_2119_, 1);
v_isSharedCheck_2146_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2123_ = v___x_2119_;
v_isShared_2124_ = v_isSharedCheck_2146_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_a_2121_);
lean_inc(v_a_2120_);
lean_dec(v___x_2119_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2146_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v_fst_2125_; lean_object* v_snd_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2145_; 
v_fst_2125_ = lean_ctor_get(v_a_2120_, 0);
v_snd_2126_ = lean_ctor_get(v_a_2120_, 1);
v_isSharedCheck_2145_ = !lean_is_exclusive(v_a_2120_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2128_ = v_a_2120_;
v_isShared_2129_ = v_isSharedCheck_2145_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_snd_2126_);
lean_inc(v_fst_2125_);
lean_dec(v_a_2120_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2145_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
uint8_t v___y_2131_; size_t v___x_2139_; size_t v___x_2140_; uint8_t v___x_2141_; 
v___x_2139_ = lean_ptr_addr(v_binderType_2109_);
v___x_2140_ = lean_ptr_addr(v_fst_2115_);
v___x_2141_ = lean_usize_dec_eq(v___x_2139_, v___x_2140_);
if (v___x_2141_ == 0)
{
v___y_2131_ = v___x_2141_;
goto v___jp_2130_;
}
else
{
size_t v___x_2142_; size_t v___x_2143_; uint8_t v___x_2144_; 
v___x_2142_ = lean_ptr_addr(v_body_2110_);
v___x_2143_ = lean_ptr_addr(v_fst_2125_);
v___x_2144_ = lean_usize_dec_eq(v___x_2142_, v___x_2143_);
v___y_2131_ = v___x_2144_;
goto v___jp_2130_;
}
v___jp_2130_:
{
if (v___y_2131_ == 0)
{
lean_object* v___x_2132_; 
lean_inc(v_binderName_2108_);
lean_del_object(v___x_2128_);
lean_del_object(v___x_2123_);
lean_dec_ref_known(v_e_2097_, 3);
v___x_2132_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__3(v_binderName_2108_, v_binderInfo_2111_, v_fst_2115_, v_fst_2125_, v_snd_2126_, v_a_2100_, v_a_2101_, v_a_2121_);
return v___x_2132_;
}
else
{
lean_object* v___x_2134_; 
lean_dec(v_fst_2125_);
lean_dec(v_fst_2115_);
if (v_isShared_2129_ == 0)
{
lean_ctor_set(v___x_2128_, 0, v_e_2097_);
v___x_2134_ = v___x_2128_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v_e_2097_);
lean_ctor_set(v_reuseFailAlloc_2138_, 1, v_snd_2126_);
v___x_2134_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
lean_object* v___x_2136_; 
if (v_isShared_2124_ == 0)
{
lean_ctor_set(v___x_2123_, 0, v___x_2134_);
v___x_2136_ = v___x_2123_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v___x_2134_);
lean_ctor_set(v_reuseFailAlloc_2137_, 1, v_a_2121_);
v___x_2136_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
return v___x_2136_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_2115_);
lean_dec_ref_known(v_e_2097_, 3);
return v___x_2119_;
}
}
else
{
lean_dec_ref_known(v_e_2097_, 3);
lean_dec(v_offset_2098_);
return v___x_2112_;
}
}
case 7:
{
lean_object* v_binderName_2147_; lean_object* v_binderType_2148_; lean_object* v_body_2149_; uint8_t v_binderInfo_2150_; lean_object* v___x_2151_; 
v_binderName_2147_ = lean_ctor_get(v_e_2097_, 0);
v_binderType_2148_ = lean_ctor_get(v_e_2097_, 1);
v_body_2149_ = lean_ctor_get(v_e_2097_, 2);
v_binderInfo_2150_ = lean_ctor_get_uint8(v_e_2097_, sizeof(void*)*3 + 8);
lean_inc(v_offset_2098_);
lean_inc_ref(v_binderType_2148_);
v___x_2151_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_2096_, v_binderType_2148_, v_offset_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_);
if (lean_obj_tag(v___x_2151_) == 0)
{
lean_object* v_a_2152_; lean_object* v_a_2153_; lean_object* v_fst_2154_; lean_object* v_snd_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; 
v_a_2152_ = lean_ctor_get(v___x_2151_, 0);
lean_inc(v_a_2152_);
v_a_2153_ = lean_ctor_get(v___x_2151_, 1);
lean_inc(v_a_2153_);
lean_dec_ref_known(v___x_2151_, 2);
v_fst_2154_ = lean_ctor_get(v_a_2152_, 0);
lean_inc(v_fst_2154_);
v_snd_2155_ = lean_ctor_get(v_a_2152_, 1);
lean_inc(v_snd_2155_);
lean_dec(v_a_2152_);
v___x_2156_ = lean_unsigned_to_nat(1u);
v___x_2157_ = lean_nat_add(v_offset_2098_, v___x_2156_);
lean_dec(v_offset_2098_);
lean_inc_ref(v_body_2149_);
v___x_2158_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_2096_, v_body_2149_, v___x_2157_, v_snd_2155_, v_a_2100_, v_a_2101_, v_a_2153_);
if (lean_obj_tag(v___x_2158_) == 0)
{
lean_object* v_a_2159_; lean_object* v_a_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2185_; 
v_a_2159_ = lean_ctor_get(v___x_2158_, 0);
v_a_2160_ = lean_ctor_get(v___x_2158_, 1);
v_isSharedCheck_2185_ = !lean_is_exclusive(v___x_2158_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2162_ = v___x_2158_;
v_isShared_2163_ = v_isSharedCheck_2185_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_a_2160_);
lean_inc(v_a_2159_);
lean_dec(v___x_2158_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2185_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v_fst_2164_; lean_object* v_snd_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2184_; 
v_fst_2164_ = lean_ctor_get(v_a_2159_, 0);
v_snd_2165_ = lean_ctor_get(v_a_2159_, 1);
v_isSharedCheck_2184_ = !lean_is_exclusive(v_a_2159_);
if (v_isSharedCheck_2184_ == 0)
{
v___x_2167_ = v_a_2159_;
v_isShared_2168_ = v_isSharedCheck_2184_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_snd_2165_);
lean_inc(v_fst_2164_);
lean_dec(v_a_2159_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2184_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
uint8_t v___y_2170_; size_t v___x_2178_; size_t v___x_2179_; uint8_t v___x_2180_; 
v___x_2178_ = lean_ptr_addr(v_binderType_2148_);
v___x_2179_ = lean_ptr_addr(v_fst_2154_);
v___x_2180_ = lean_usize_dec_eq(v___x_2178_, v___x_2179_);
if (v___x_2180_ == 0)
{
v___y_2170_ = v___x_2180_;
goto v___jp_2169_;
}
else
{
size_t v___x_2181_; size_t v___x_2182_; uint8_t v___x_2183_; 
v___x_2181_ = lean_ptr_addr(v_body_2149_);
v___x_2182_ = lean_ptr_addr(v_fst_2164_);
v___x_2183_ = lean_usize_dec_eq(v___x_2181_, v___x_2182_);
v___y_2170_ = v___x_2183_;
goto v___jp_2169_;
}
v___jp_2169_:
{
if (v___y_2170_ == 0)
{
lean_object* v___x_2171_; 
lean_inc(v_binderName_2147_);
lean_del_object(v___x_2167_);
lean_del_object(v___x_2162_);
lean_dec_ref_known(v_e_2097_, 3);
v___x_2171_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__4(v_binderName_2147_, v_binderInfo_2150_, v_fst_2154_, v_fst_2164_, v_snd_2165_, v_a_2100_, v_a_2101_, v_a_2160_);
return v___x_2171_;
}
else
{
lean_object* v___x_2173_; 
lean_dec(v_fst_2164_);
lean_dec(v_fst_2154_);
if (v_isShared_2168_ == 0)
{
lean_ctor_set(v___x_2167_, 0, v_e_2097_);
v___x_2173_ = v___x_2167_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_e_2097_);
lean_ctor_set(v_reuseFailAlloc_2177_, 1, v_snd_2165_);
v___x_2173_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
lean_object* v___x_2175_; 
if (v_isShared_2163_ == 0)
{
lean_ctor_set(v___x_2162_, 0, v___x_2173_);
v___x_2175_ = v___x_2162_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v___x_2173_);
lean_ctor_set(v_reuseFailAlloc_2176_, 1, v_a_2160_);
v___x_2175_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
return v___x_2175_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_2154_);
lean_dec_ref_known(v_e_2097_, 3);
return v___x_2158_;
}
}
else
{
lean_dec_ref_known(v_e_2097_, 3);
lean_dec(v_offset_2098_);
return v___x_2151_;
}
}
case 8:
{
lean_object* v_declName_2186_; lean_object* v_type_2187_; lean_object* v_value_2188_; lean_object* v_body_2189_; uint8_t v_nondep_2190_; lean_object* v___x_2191_; 
v_declName_2186_ = lean_ctor_get(v_e_2097_, 0);
v_type_2187_ = lean_ctor_get(v_e_2097_, 1);
v_value_2188_ = lean_ctor_get(v_e_2097_, 2);
v_body_2189_ = lean_ctor_get(v_e_2097_, 3);
v_nondep_2190_ = lean_ctor_get_uint8(v_e_2097_, sizeof(void*)*4 + 8);
lean_inc(v_offset_2098_);
lean_inc_ref(v_type_2187_);
v___x_2191_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_2096_, v_type_2187_, v_offset_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_);
if (lean_obj_tag(v___x_2191_) == 0)
{
lean_object* v_a_2192_; lean_object* v_a_2193_; lean_object* v_fst_2194_; lean_object* v_snd_2195_; lean_object* v___x_2196_; 
v_a_2192_ = lean_ctor_get(v___x_2191_, 0);
lean_inc(v_a_2192_);
v_a_2193_ = lean_ctor_get(v___x_2191_, 1);
lean_inc(v_a_2193_);
lean_dec_ref_known(v___x_2191_, 2);
v_fst_2194_ = lean_ctor_get(v_a_2192_, 0);
lean_inc(v_fst_2194_);
v_snd_2195_ = lean_ctor_get(v_a_2192_, 1);
lean_inc(v_snd_2195_);
lean_dec(v_a_2192_);
lean_inc(v_offset_2098_);
lean_inc_ref(v_value_2188_);
v___x_2196_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_2096_, v_value_2188_, v_offset_2098_, v_snd_2195_, v_a_2100_, v_a_2101_, v_a_2193_);
if (lean_obj_tag(v___x_2196_) == 0)
{
lean_object* v_a_2197_; lean_object* v_a_2198_; lean_object* v_fst_2199_; lean_object* v_snd_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; 
v_a_2197_ = lean_ctor_get(v___x_2196_, 0);
lean_inc(v_a_2197_);
v_a_2198_ = lean_ctor_get(v___x_2196_, 1);
lean_inc(v_a_2198_);
lean_dec_ref_known(v___x_2196_, 2);
v_fst_2199_ = lean_ctor_get(v_a_2197_, 0);
lean_inc(v_fst_2199_);
v_snd_2200_ = lean_ctor_get(v_a_2197_, 1);
lean_inc(v_snd_2200_);
lean_dec(v_a_2197_);
v___x_2201_ = lean_unsigned_to_nat(1u);
v___x_2202_ = lean_nat_add(v_offset_2098_, v___x_2201_);
lean_dec(v_offset_2098_);
lean_inc_ref(v_body_2189_);
v___x_2203_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_2096_, v_body_2189_, v___x_2202_, v_snd_2200_, v_a_2100_, v_a_2101_, v_a_2198_);
if (lean_obj_tag(v___x_2203_) == 0)
{
lean_object* v_a_2204_; lean_object* v_a_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2234_; 
v_a_2204_ = lean_ctor_get(v___x_2203_, 0);
v_a_2205_ = lean_ctor_get(v___x_2203_, 1);
v_isSharedCheck_2234_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2234_ == 0)
{
v___x_2207_ = v___x_2203_;
v_isShared_2208_ = v_isSharedCheck_2234_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_a_2205_);
lean_inc(v_a_2204_);
lean_dec(v___x_2203_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2234_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v_fst_2209_; lean_object* v_snd_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2233_; 
v_fst_2209_ = lean_ctor_get(v_a_2204_, 0);
v_snd_2210_ = lean_ctor_get(v_a_2204_, 1);
v_isSharedCheck_2233_ = !lean_is_exclusive(v_a_2204_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2212_ = v_a_2204_;
v_isShared_2213_ = v_isSharedCheck_2233_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_snd_2210_);
lean_inc(v_fst_2209_);
lean_dec(v_a_2204_);
v___x_2212_ = lean_box(0);
v_isShared_2213_ = v_isSharedCheck_2233_;
goto v_resetjp_2211_;
}
v_resetjp_2211_:
{
uint8_t v___y_2215_; size_t v___x_2227_; size_t v___x_2228_; uint8_t v___x_2229_; 
v___x_2227_ = lean_ptr_addr(v_type_2187_);
v___x_2228_ = lean_ptr_addr(v_fst_2194_);
v___x_2229_ = lean_usize_dec_eq(v___x_2227_, v___x_2228_);
if (v___x_2229_ == 0)
{
v___y_2215_ = v___x_2229_;
goto v___jp_2214_;
}
else
{
size_t v___x_2230_; size_t v___x_2231_; uint8_t v___x_2232_; 
v___x_2230_ = lean_ptr_addr(v_value_2188_);
v___x_2231_ = lean_ptr_addr(v_fst_2199_);
v___x_2232_ = lean_usize_dec_eq(v___x_2230_, v___x_2231_);
v___y_2215_ = v___x_2232_;
goto v___jp_2214_;
}
v___jp_2214_:
{
if (v___y_2215_ == 0)
{
lean_object* v___x_2216_; 
lean_inc(v_declName_2186_);
lean_del_object(v___x_2212_);
lean_del_object(v___x_2207_);
lean_dec_ref_known(v_e_2097_, 4);
v___x_2216_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__5(v_declName_2186_, v_fst_2194_, v_fst_2199_, v_fst_2209_, v_nondep_2190_, v_snd_2210_, v_a_2100_, v_a_2101_, v_a_2205_);
return v___x_2216_;
}
else
{
size_t v___x_2217_; size_t v___x_2218_; uint8_t v___x_2219_; 
v___x_2217_ = lean_ptr_addr(v_body_2189_);
v___x_2218_ = lean_ptr_addr(v_fst_2209_);
v___x_2219_ = lean_usize_dec_eq(v___x_2217_, v___x_2218_);
if (v___x_2219_ == 0)
{
lean_object* v___x_2220_; 
lean_inc(v_declName_2186_);
lean_del_object(v___x_2212_);
lean_del_object(v___x_2207_);
lean_dec_ref_known(v_e_2097_, 4);
v___x_2220_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__5(v_declName_2186_, v_fst_2194_, v_fst_2199_, v_fst_2209_, v_nondep_2190_, v_snd_2210_, v_a_2100_, v_a_2101_, v_a_2205_);
return v___x_2220_;
}
else
{
lean_object* v___x_2222_; 
lean_dec(v_fst_2209_);
lean_dec(v_fst_2199_);
lean_dec(v_fst_2194_);
if (v_isShared_2213_ == 0)
{
lean_ctor_set(v___x_2212_, 0, v_e_2097_);
v___x_2222_ = v___x_2212_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_e_2097_);
lean_ctor_set(v_reuseFailAlloc_2226_, 1, v_snd_2210_);
v___x_2222_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
lean_object* v___x_2224_; 
if (v_isShared_2208_ == 0)
{
lean_ctor_set(v___x_2207_, 0, v___x_2222_);
v___x_2224_ = v___x_2207_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v___x_2222_);
lean_ctor_set(v_reuseFailAlloc_2225_, 1, v_a_2205_);
v___x_2224_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
return v___x_2224_;
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
lean_dec(v_fst_2199_);
lean_dec(v_fst_2194_);
lean_dec_ref_known(v_e_2097_, 4);
return v___x_2203_;
}
}
else
{
lean_dec(v_fst_2194_);
lean_dec_ref_known(v_e_2097_, 4);
lean_dec(v_offset_2098_);
return v___x_2196_;
}
}
else
{
lean_dec_ref_known(v_e_2097_, 4);
lean_dec(v_offset_2098_);
return v___x_2191_;
}
}
case 10:
{
lean_object* v_data_2235_; lean_object* v_expr_2236_; lean_object* v___x_2237_; 
v_data_2235_ = lean_ctor_get(v_e_2097_, 0);
v_expr_2236_ = lean_ctor_get(v_e_2097_, 1);
lean_inc_ref(v_expr_2236_);
v___x_2237_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_2096_, v_expr_2236_, v_offset_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_);
if (lean_obj_tag(v___x_2237_) == 0)
{
lean_object* v_a_2238_; lean_object* v_a_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2259_; 
v_a_2238_ = lean_ctor_get(v___x_2237_, 0);
v_a_2239_ = lean_ctor_get(v___x_2237_, 1);
v_isSharedCheck_2259_ = !lean_is_exclusive(v___x_2237_);
if (v_isSharedCheck_2259_ == 0)
{
v___x_2241_ = v___x_2237_;
v_isShared_2242_ = v_isSharedCheck_2259_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_a_2239_);
lean_inc(v_a_2238_);
lean_dec(v___x_2237_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2259_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v_fst_2243_; lean_object* v_snd_2244_; lean_object* v___x_2246_; uint8_t v_isShared_2247_; uint8_t v_isSharedCheck_2258_; 
v_fst_2243_ = lean_ctor_get(v_a_2238_, 0);
v_snd_2244_ = lean_ctor_get(v_a_2238_, 1);
v_isSharedCheck_2258_ = !lean_is_exclusive(v_a_2238_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2246_ = v_a_2238_;
v_isShared_2247_ = v_isSharedCheck_2258_;
goto v_resetjp_2245_;
}
else
{
lean_inc(v_snd_2244_);
lean_inc(v_fst_2243_);
lean_dec(v_a_2238_);
v___x_2246_ = lean_box(0);
v_isShared_2247_ = v_isSharedCheck_2258_;
goto v_resetjp_2245_;
}
v_resetjp_2245_:
{
size_t v___x_2248_; size_t v___x_2249_; uint8_t v___x_2250_; 
v___x_2248_ = lean_ptr_addr(v_expr_2236_);
v___x_2249_ = lean_ptr_addr(v_fst_2243_);
v___x_2250_ = lean_usize_dec_eq(v___x_2248_, v___x_2249_);
if (v___x_2250_ == 0)
{
lean_object* v___x_2251_; 
lean_inc(v_data_2235_);
lean_del_object(v___x_2246_);
lean_del_object(v___x_2241_);
lean_dec_ref_known(v_e_2097_, 2);
v___x_2251_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__6(v_data_2235_, v_fst_2243_, v_snd_2244_, v_a_2100_, v_a_2101_, v_a_2239_);
return v___x_2251_;
}
else
{
lean_object* v___x_2253_; 
lean_dec(v_fst_2243_);
if (v_isShared_2247_ == 0)
{
lean_ctor_set(v___x_2246_, 0, v_e_2097_);
v___x_2253_ = v___x_2246_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v_e_2097_);
lean_ctor_set(v_reuseFailAlloc_2257_, 1, v_snd_2244_);
v___x_2253_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
lean_object* v___x_2255_; 
if (v_isShared_2242_ == 0)
{
lean_ctor_set(v___x_2241_, 0, v___x_2253_);
v___x_2255_ = v___x_2241_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v___x_2253_);
lean_ctor_set(v_reuseFailAlloc_2256_, 1, v_a_2239_);
v___x_2255_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
return v___x_2255_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2097_, 2);
return v___x_2237_;
}
}
case 11:
{
lean_object* v_typeName_2260_; lean_object* v_idx_2261_; lean_object* v_struct_2262_; lean_object* v___x_2263_; 
v_typeName_2260_ = lean_ctor_get(v_e_2097_, 0);
v_idx_2261_ = lean_ctor_get(v_e_2097_, 1);
v_struct_2262_ = lean_ctor_get(v_e_2097_, 2);
lean_inc_ref(v_struct_2262_);
v___x_2263_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_2096_, v_struct_2262_, v_offset_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_);
if (lean_obj_tag(v___x_2263_) == 0)
{
lean_object* v_a_2264_; lean_object* v_a_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2285_; 
v_a_2264_ = lean_ctor_get(v___x_2263_, 0);
v_a_2265_ = lean_ctor_get(v___x_2263_, 1);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2263_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2267_ = v___x_2263_;
v_isShared_2268_ = v_isSharedCheck_2285_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_a_2265_);
lean_inc(v_a_2264_);
lean_dec(v___x_2263_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2285_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
lean_object* v_fst_2269_; lean_object* v_snd_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2284_; 
v_fst_2269_ = lean_ctor_get(v_a_2264_, 0);
v_snd_2270_ = lean_ctor_get(v_a_2264_, 1);
v_isSharedCheck_2284_ = !lean_is_exclusive(v_a_2264_);
if (v_isSharedCheck_2284_ == 0)
{
v___x_2272_ = v_a_2264_;
v_isShared_2273_ = v_isSharedCheck_2284_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_snd_2270_);
lean_inc(v_fst_2269_);
lean_dec(v_a_2264_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2284_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
size_t v___x_2274_; size_t v___x_2275_; uint8_t v___x_2276_; 
v___x_2274_ = lean_ptr_addr(v_struct_2262_);
v___x_2275_ = lean_ptr_addr(v_fst_2269_);
v___x_2276_ = lean_usize_dec_eq(v___x_2274_, v___x_2275_);
if (v___x_2276_ == 0)
{
lean_object* v___x_2277_; 
lean_inc(v_idx_2261_);
lean_inc(v_typeName_2260_);
lean_del_object(v___x_2272_);
lean_del_object(v___x_2267_);
lean_dec_ref_known(v_e_2097_, 3);
v___x_2277_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__7(v_typeName_2260_, v_idx_2261_, v_fst_2269_, v_snd_2270_, v_a_2100_, v_a_2101_, v_a_2265_);
return v___x_2277_;
}
else
{
lean_object* v___x_2279_; 
lean_dec(v_fst_2269_);
if (v_isShared_2273_ == 0)
{
lean_ctor_set(v___x_2272_, 0, v_e_2097_);
v___x_2279_ = v___x_2272_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v_e_2097_);
lean_ctor_set(v_reuseFailAlloc_2283_, 1, v_snd_2270_);
v___x_2279_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
lean_object* v___x_2281_; 
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 0, v___x_2279_);
v___x_2281_ = v___x_2267_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v___x_2279_);
lean_ctor_set(v_reuseFailAlloc_2282_, 1, v_a_2265_);
v___x_2281_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
return v___x_2281_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2097_, 3);
return v___x_2263_;
}
}
default: 
{
lean_object* v___x_2286_; lean_object* v___x_2287_; 
lean_dec(v_offset_2098_);
lean_dec_ref(v_e_2097_);
v___x_2286_ = lean_obj_once(&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__1, &l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__1_once, _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__1);
v___x_2287_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8(v___x_2286_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_);
return v___x_2287_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(lean_object* v_subst_2288_, lean_object* v_e_2289_, lean_object* v_offset_2290_, lean_object* v_a_2291_, uint8_t v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_){
_start:
{
lean_object* v___x_2295_; uint8_t v___x_2296_; 
v___x_2295_ = l_Lean_Expr_looseBVarRange(v_e_2289_);
v___x_2296_ = lean_nat_dec_le(v___x_2295_, v_offset_2290_);
lean_dec(v___x_2295_);
if (v___x_2296_ == 0)
{
lean_object* v_key_2297_; lean_object* v___x_2298_; 
lean_inc(v_offset_2290_);
lean_inc_ref(v_e_2289_);
v_key_2297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_2297_, 0, v_e_2289_);
lean_ctor_set(v_key_2297_, 1, v_offset_2290_);
v___x_2298_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3___redArg(v_a_2291_, v_key_2297_);
if (lean_obj_tag(v___x_2298_) == 1)
{
lean_object* v_val_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; 
lean_dec_ref_known(v_key_2297_, 2);
lean_dec(v_offset_2290_);
lean_dec_ref(v_e_2289_);
v_val_2299_ = lean_ctor_get(v___x_2298_, 0);
lean_inc(v_val_2299_);
lean_dec_ref_known(v___x_2298_, 1);
v___x_2300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2300_, 0, v_val_2299_);
lean_ctor_set(v___x_2300_, 1, v_a_2291_);
v___x_2301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2301_, 0, v___x_2300_);
lean_ctor_set(v___x_2301_, 1, v_a_2294_);
return v___x_2301_;
}
else
{
lean_dec(v___x_2298_);
switch(lean_obj_tag(v_e_2289_))
{
case 0:
{
lean_object* v_deBruijnIndex_2302_; lean_object* v___x_2303_; 
v_deBruijnIndex_2302_ = lean_ctor_get(v_e_2289_, 0);
lean_inc(v_deBruijnIndex_2302_);
v___x_2303_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(v_subst_2288_, v_e_2289_, v_deBruijnIndex_2302_, v_offset_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_);
lean_dec(v_offset_2290_);
lean_dec(v_deBruijnIndex_2302_);
if (lean_obj_tag(v___x_2303_) == 0)
{
lean_object* v_a_2304_; lean_object* v_a_2305_; lean_object* v_fst_2306_; lean_object* v_snd_2307_; lean_object* v___x_2308_; 
v_a_2304_ = lean_ctor_get(v___x_2303_, 0);
lean_inc(v_a_2304_);
v_a_2305_ = lean_ctor_get(v___x_2303_, 1);
lean_inc(v_a_2305_);
lean_dec_ref_known(v___x_2303_, 2);
v_fst_2306_ = lean_ctor_get(v_a_2304_, 0);
lean_inc(v_fst_2306_);
v_snd_2307_ = lean_ctor_get(v_a_2304_, 1);
lean_inc(v_snd_2307_);
lean_dec(v_a_2304_);
v___x_2308_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_2297_, v_fst_2306_, v_snd_2307_, v_a_2305_);
return v___x_2308_;
}
else
{
lean_dec_ref_known(v_key_2297_, 2);
return v___x_2303_;
}
}
case 9:
{
lean_object* v___x_2309_; 
lean_dec(v_offset_2290_);
v___x_2309_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_2297_, v_e_2289_, v_a_2291_, v_a_2294_);
return v___x_2309_;
}
case 2:
{
lean_object* v___x_2310_; 
lean_dec(v_offset_2290_);
v___x_2310_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_2297_, v_e_2289_, v_a_2291_, v_a_2294_);
return v___x_2310_;
}
case 1:
{
lean_object* v___x_2311_; 
lean_dec(v_offset_2290_);
v___x_2311_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_2297_, v_e_2289_, v_a_2291_, v_a_2294_);
return v___x_2311_;
}
case 4:
{
lean_object* v___x_2312_; 
lean_dec(v_offset_2290_);
v___x_2312_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_2297_, v_e_2289_, v_a_2291_, v_a_2294_);
return v___x_2312_;
}
case 3:
{
lean_object* v___x_2313_; 
lean_dec(v_offset_2290_);
v___x_2313_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_2297_, v_e_2289_, v_a_2291_, v_a_2294_);
return v___x_2313_;
}
default: 
{
lean_object* v___x_2314_; 
v___x_2314_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit(v_subst_2288_, v_e_2289_, v_offset_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_);
if (lean_obj_tag(v___x_2314_) == 0)
{
lean_object* v_a_2315_; lean_object* v_a_2316_; lean_object* v_fst_2317_; lean_object* v_snd_2318_; lean_object* v___x_2319_; 
v_a_2315_ = lean_ctor_get(v___x_2314_, 0);
lean_inc(v_a_2315_);
v_a_2316_ = lean_ctor_get(v___x_2314_, 1);
lean_inc(v_a_2316_);
lean_dec_ref_known(v___x_2314_, 2);
v_fst_2317_ = lean_ctor_get(v_a_2315_, 0);
lean_inc(v_fst_2317_);
v_snd_2318_ = lean_ctor_get(v_a_2315_, 1);
lean_inc(v_snd_2318_);
lean_dec(v_a_2315_);
v___x_2319_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_2297_, v_fst_2317_, v_snd_2318_, v_a_2316_);
return v___x_2319_;
}
else
{
lean_dec_ref_known(v_key_2297_, 2);
return v___x_2314_;
}
}
}
}
}
else
{
lean_object* v___x_2320_; lean_object* v___x_2321_; 
lean_dec(v_offset_2290_);
v___x_2320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2320_, 0, v_e_2289_);
lean_ctor_set(v___x_2320_, 1, v_a_2291_);
v___x_2321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2321_, 0, v___x_2320_);
lean_ctor_set(v___x_2321_, 1, v_a_2294_);
return v___x_2321_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild___boxed(lean_object* v_subst_2322_, lean_object* v_e_2323_, lean_object* v_offset_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_){
_start:
{
uint8_t v_a_boxed_2329_; lean_object* v_res_2330_; 
v_a_boxed_2329_ = lean_unbox(v_a_2326_);
v_res_2330_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_2322_, v_e_2323_, v_offset_2324_, v_a_2325_, v_a_boxed_2329_, v_a_2327_, v_a_2328_);
lean_dec_ref(v_a_2327_);
lean_dec_ref(v_subst_2322_);
return v_res_2330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault___boxed(lean_object* v_subst_2331_, lean_object* v_e_2332_, lean_object* v_offset_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_){
_start:
{
uint8_t v_a_boxed_2338_; lean_object* v_res_2339_; 
v_a_boxed_2338_ = lean_unbox(v_a_2335_);
v_res_2339_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault(v_subst_2331_, v_e_2332_, v_offset_2333_, v_a_2334_, v_a_boxed_2338_, v_a_2336_, v_a_2337_);
lean_dec_ref(v_a_2336_);
lean_dec_ref(v_subst_2331_);
return v_res_2339_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___boxed(lean_object* v_subst_2340_, lean_object* v_e_2341_, lean_object* v_f_2342_, lean_object* v_arg_2343_, lean_object* v_offset_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_){
_start:
{
uint8_t v_a_boxed_2349_; lean_object* v_res_2350_; 
v_a_boxed_2349_ = lean_unbox(v_a_2346_);
v_res_2350_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg(v_subst_2340_, v_e_2341_, v_f_2342_, v_arg_2343_, v_offset_2344_, v_a_2345_, v_a_boxed_2349_, v_a_2347_, v_a_2348_);
lean_dec_ref(v_a_2347_);
lean_dec_ref(v_subst_2340_);
return v_res_2350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___boxed(lean_object* v_subst_2351_, lean_object* v_e_2352_, lean_object* v_f_2353_, lean_object* v_argsRev_2354_, lean_object* v_offset_2355_, lean_object* v_modified_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_){
_start:
{
uint8_t v_modified_boxed_2361_; uint8_t v_a_boxed_2362_; lean_object* v_res_2363_; 
v_modified_boxed_2361_ = lean_unbox(v_modified_2356_);
v_a_boxed_2362_ = lean_unbox(v_a_2358_);
v_res_2363_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta(v_subst_2351_, v_e_2352_, v_f_2353_, v_argsRev_2354_, v_offset_2355_, v_modified_boxed_2361_, v_a_2357_, v_a_boxed_2362_, v_a_2359_, v_a_2360_);
lean_dec_ref(v_a_2359_);
lean_dec_ref(v_subst_2351_);
return v_res_2363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___boxed(lean_object* v_subst_2364_, lean_object* v_e_2365_, lean_object* v_offset_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_){
_start:
{
uint8_t v_a_boxed_2371_; lean_object* v_res_2372_; 
v_a_boxed_2371_ = lean_unbox(v_a_2368_);
v_res_2372_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit(v_subst_2364_, v_e_2365_, v_offset_2366_, v_a_2367_, v_a_boxed_2371_, v_a_2369_, v_a_2370_);
lean_dec_ref(v_a_2369_);
lean_dec_ref(v_subst_2364_);
return v_res_2372_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp(lean_object* v_subst_2373_, lean_object* v_e_2374_, lean_object* v_f_2375_, lean_object* v_arg_2376_, lean_object* v_offset_2377_, lean_object* v_x_2378_, lean_object* v_a_2379_, uint8_t v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_){
_start:
{
lean_object* v___x_2383_; 
v___x_2383_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg(v_subst_2373_, v_e_2374_, v_f_2375_, v_arg_2376_, v_offset_2377_, v_a_2379_, v_a_2380_, v_a_2381_, v_a_2382_);
return v___x_2383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___boxed(lean_object* v_subst_2384_, lean_object* v_e_2385_, lean_object* v_f_2386_, lean_object* v_arg_2387_, lean_object* v_offset_2388_, lean_object* v_x_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_){
_start:
{
uint8_t v_a_boxed_2394_; lean_object* v_res_2395_; 
v_a_boxed_2394_ = lean_unbox(v_a_2391_);
v_res_2395_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp(v_subst_2384_, v_e_2385_, v_f_2386_, v_arg_2387_, v_offset_2388_, v_x_2389_, v_a_2390_, v_a_boxed_2394_, v_a_2392_, v_a_2393_);
lean_dec_ref(v_a_2392_);
lean_dec_ref(v_subst_2384_);
return v_res_2395_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27(lean_object* v_e_2396_, lean_object* v_subst_2397_, uint8_t v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_){
_start:
{
uint8_t v___y_2402_; lean_object* v___x_2426_; lean_object* v___x_2427_; uint8_t v___x_2428_; 
v___x_2426_ = lean_array_get_size(v_subst_2397_);
v___x_2427_ = lean_unsigned_to_nat(0u);
v___x_2428_ = lean_nat_dec_eq(v___x_2426_, v___x_2427_);
if (v___x_2428_ == 0)
{
uint8_t v___x_2429_; 
v___x_2429_ = l_Lean_Expr_hasLooseBVars(v_e_2396_);
if (v___x_2429_ == 0)
{
lean_object* v___x_2430_; 
v___x_2430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2430_, 0, v_e_2396_);
lean_ctor_set(v___x_2430_, 1, v_a_2400_);
return v___x_2430_;
}
else
{
v___y_2402_ = v___x_2428_;
goto v___jp_2401_;
}
}
else
{
v___y_2402_ = v___x_2428_;
goto v___jp_2401_;
}
v___jp_2401_:
{
if (v___y_2402_ == 0)
{
lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; 
v___x_2403_ = lean_unsigned_to_nat(0u);
v___x_2404_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__1, &l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__1_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__1);
v___x_2405_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit(v_subst_2397_, v_e_2396_, v___x_2403_, v___x_2404_, v_a_2398_, v_a_2399_, v_a_2400_);
if (lean_obj_tag(v___x_2405_) == 0)
{
lean_object* v_a_2406_; lean_object* v_a_2407_; lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2415_; 
v_a_2406_ = lean_ctor_get(v___x_2405_, 0);
v_a_2407_ = lean_ctor_get(v___x_2405_, 1);
v_isSharedCheck_2415_ = !lean_is_exclusive(v___x_2405_);
if (v_isSharedCheck_2415_ == 0)
{
v___x_2409_ = v___x_2405_;
v_isShared_2410_ = v_isSharedCheck_2415_;
goto v_resetjp_2408_;
}
else
{
lean_inc(v_a_2407_);
lean_inc(v_a_2406_);
lean_dec(v___x_2405_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2415_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
lean_object* v_fst_2411_; lean_object* v___x_2413_; 
v_fst_2411_ = lean_ctor_get(v_a_2406_, 0);
lean_inc(v_fst_2411_);
lean_dec(v_a_2406_);
if (v_isShared_2410_ == 0)
{
lean_ctor_set(v___x_2409_, 0, v_fst_2411_);
v___x_2413_ = v___x_2409_;
goto v_reusejp_2412_;
}
else
{
lean_object* v_reuseFailAlloc_2414_; 
v_reuseFailAlloc_2414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2414_, 0, v_fst_2411_);
lean_ctor_set(v_reuseFailAlloc_2414_, 1, v_a_2407_);
v___x_2413_ = v_reuseFailAlloc_2414_;
goto v_reusejp_2412_;
}
v_reusejp_2412_:
{
return v___x_2413_;
}
}
}
else
{
lean_object* v_a_2416_; lean_object* v_a_2417_; lean_object* v___x_2419_; uint8_t v_isShared_2420_; uint8_t v_isSharedCheck_2424_; 
v_a_2416_ = lean_ctor_get(v___x_2405_, 0);
v_a_2417_ = lean_ctor_get(v___x_2405_, 1);
v_isSharedCheck_2424_ = !lean_is_exclusive(v___x_2405_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2419_ = v___x_2405_;
v_isShared_2420_ = v_isSharedCheck_2424_;
goto v_resetjp_2418_;
}
else
{
lean_inc(v_a_2417_);
lean_inc(v_a_2416_);
lean_dec(v___x_2405_);
v___x_2419_ = lean_box(0);
v_isShared_2420_ = v_isSharedCheck_2424_;
goto v_resetjp_2418_;
}
v_resetjp_2418_:
{
lean_object* v___x_2422_; 
if (v_isShared_2420_ == 0)
{
v___x_2422_ = v___x_2419_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v_a_2416_);
lean_ctor_set(v_reuseFailAlloc_2423_, 1, v_a_2417_);
v___x_2422_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
return v___x_2422_;
}
}
}
}
else
{
lean_object* v___x_2425_; 
v___x_2425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2425_, 0, v_e_2396_);
lean_ctor_set(v___x_2425_, 1, v_a_2400_);
return v___x_2425_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27___boxed(lean_object* v_e_2431_, lean_object* v_subst_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_){
_start:
{
uint8_t v_a_boxed_2436_; lean_object* v_res_2437_; 
v_a_boxed_2436_ = lean_unbox(v_a_2433_);
v_res_2437_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27(v_e_2431_, v_subst_2432_, v_a_boxed_2436_, v_a_2434_, v_a_2435_);
lean_dec_ref(v_a_2434_);
lean_dec_ref(v_subst_2432_);
return v_res_2437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevBetaS(lean_object* v_e_2438_, lean_object* v_subst_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_){
_start:
{
uint8_t v___x_2447_; 
v___x_2447_ = l_Lean_Expr_hasLooseBVars(v_e_2438_);
if (v___x_2447_ == 0)
{
lean_object* v___x_2448_; 
lean_dec_ref(v_subst_2439_);
v___x_2448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2448_, 0, v_e_2438_);
return v___x_2448_;
}
else
{
lean_object* v___x_2449_; lean_object* v___x_2450_; uint8_t v___x_2451_; 
v___x_2449_ = lean_array_get_size(v_subst_2439_);
v___x_2450_ = lean_unsigned_to_nat(0u);
v___x_2451_ = lean_nat_dec_eq(v___x_2449_, v___x_2450_);
if (v___x_2451_ == 0)
{
lean_object* v___x_2452_; lean_object* v___x_2453_; uint8_t v_debug_2454_; lean_object* v_env_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; 
v___x_2452_ = lean_st_ref_get(v_a_2441_);
v___x_2453_ = lean_st_ref_get(v_a_2445_);
v_debug_2454_ = lean_ctor_get_uint8(v___x_2452_, sizeof(void*)*11);
lean_dec(v___x_2452_);
v_env_2455_ = lean_ctor_get(v___x_2453_, 0);
lean_inc_ref(v_env_2455_);
lean_dec(v___x_2453_);
v___x_2456_ = lean_box(v_debug_2454_);
v___x_2457_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27___boxed), 5, 3);
lean_closure_set(v___x_2457_, 0, v_e_2438_);
lean_closure_set(v___x_2457_, 1, v_subst_2439_);
lean_closure_set(v___x_2457_, 2, v___x_2456_);
v___x_2458_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2458_, 0, v_env_2455_);
lean_ctor_set_uint8(v___x_2458_, sizeof(void*)*1, v___x_2451_);
lean_ctor_set_uint8(v___x_2458_, sizeof(void*)*1 + 1, v___x_2451_);
v___x_2459_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___x_2457_, v___x_2458_, v_a_2441_);
if (lean_obj_tag(v___x_2459_) == 0)
{
lean_object* v_a_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2470_; 
v_a_2460_ = lean_ctor_get(v___x_2459_, 0);
v_isSharedCheck_2470_ = !lean_is_exclusive(v___x_2459_);
if (v_isSharedCheck_2470_ == 0)
{
v___x_2462_ = v___x_2459_;
v_isShared_2463_ = v_isSharedCheck_2470_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_a_2460_);
lean_dec(v___x_2459_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2470_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
if (lean_obj_tag(v_a_2460_) == 0)
{
lean_object* v___x_2464_; lean_object* v___x_2465_; 
lean_dec_ref_known(v_a_2460_, 1);
lean_del_object(v___x_2462_);
v___x_2464_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__2, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__2_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__2);
v___x_2465_ = l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(v___x_2464_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_, v_a_2444_, v_a_2445_);
return v___x_2465_;
}
else
{
lean_object* v_a_2466_; lean_object* v___x_2468_; 
v_a_2466_ = lean_ctor_get(v_a_2460_, 0);
lean_inc(v_a_2466_);
lean_dec_ref_known(v_a_2460_, 1);
if (v_isShared_2463_ == 0)
{
lean_ctor_set(v___x_2462_, 0, v_a_2466_);
v___x_2468_ = v___x_2462_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v_a_2466_);
v___x_2468_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
return v___x_2468_;
}
}
}
}
else
{
lean_object* v_a_2471_; lean_object* v___x_2473_; uint8_t v_isShared_2474_; uint8_t v_isSharedCheck_2478_; 
v_a_2471_ = lean_ctor_get(v___x_2459_, 0);
v_isSharedCheck_2478_ = !lean_is_exclusive(v___x_2459_);
if (v_isSharedCheck_2478_ == 0)
{
v___x_2473_ = v___x_2459_;
v_isShared_2474_ = v_isSharedCheck_2478_;
goto v_resetjp_2472_;
}
else
{
lean_inc(v_a_2471_);
lean_dec(v___x_2459_);
v___x_2473_ = lean_box(0);
v_isShared_2474_ = v_isSharedCheck_2478_;
goto v_resetjp_2472_;
}
v_resetjp_2472_:
{
lean_object* v___x_2476_; 
if (v_isShared_2474_ == 0)
{
v___x_2476_ = v___x_2473_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v_a_2471_);
v___x_2476_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
return v___x_2476_;
}
}
}
}
else
{
lean_object* v___x_2479_; 
lean_dec_ref(v_subst_2439_);
v___x_2479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2479_, 0, v_e_2438_);
return v___x_2479_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevBetaS___boxed(lean_object* v_e_2480_, lean_object* v_subst_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_){
_start:
{
lean_object* v_res_2489_; 
v_res_2489_ = l_Lean_Meta_Sym_instantiateRevBetaS(v_e_2480_, v_subst_2481_, v_a_2482_, v_a_2483_, v_a_2484_, v_a_2485_, v_a_2486_, v_a_2487_);
lean_dec(v_a_2487_);
lean_dec_ref(v_a_2486_);
lean_dec(v_a_2485_);
lean_dec_ref(v_a_2484_);
lean_dec(v_a_2483_);
lean_dec_ref(v_a_2482_);
return v_res_2489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_betaRevS(lean_object* v_f_2490_, lean_object* v_revArgs_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_){
_start:
{
lean_object* v___x_2499_; lean_object* v___x_2500_; uint8_t v_debug_2501_; lean_object* v_env_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; uint8_t v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; 
v___x_2499_ = lean_st_ref_get(v_a_2493_);
v___x_2500_ = lean_st_ref_get(v_a_2497_);
v_debug_2501_ = lean_ctor_get_uint8(v___x_2499_, sizeof(void*)*11);
lean_dec(v___x_2499_);
v_env_2502_ = lean_ctor_get(v___x_2500_, 0);
lean_inc_ref(v_env_2502_);
lean_dec(v___x_2500_);
v___x_2503_ = lean_box(v_debug_2501_);
v___x_2504_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27___boxed), 5, 3);
lean_closure_set(v___x_2504_, 0, v_f_2490_);
lean_closure_set(v___x_2504_, 1, v_revArgs_2491_);
lean_closure_set(v___x_2504_, 2, v___x_2503_);
v___x_2505_ = 0;
v___x_2506_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2506_, 0, v_env_2502_);
lean_ctor_set_uint8(v___x_2506_, sizeof(void*)*1, v___x_2505_);
lean_ctor_set_uint8(v___x_2506_, sizeof(void*)*1 + 1, v___x_2505_);
v___x_2507_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___x_2504_, v___x_2506_, v_a_2493_);
if (lean_obj_tag(v___x_2507_) == 0)
{
lean_object* v_a_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2518_; 
v_a_2508_ = lean_ctor_get(v___x_2507_, 0);
v_isSharedCheck_2518_ = !lean_is_exclusive(v___x_2507_);
if (v_isSharedCheck_2518_ == 0)
{
v___x_2510_ = v___x_2507_;
v_isShared_2511_ = v_isSharedCheck_2518_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_a_2508_);
lean_dec(v___x_2507_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2518_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
if (lean_obj_tag(v_a_2508_) == 0)
{
lean_object* v___x_2512_; lean_object* v___x_2513_; 
lean_dec_ref_known(v_a_2508_, 1);
lean_del_object(v___x_2510_);
v___x_2512_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__2, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__2_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__2);
v___x_2513_ = l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(v___x_2512_, v_a_2492_, v_a_2493_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_);
return v___x_2513_;
}
else
{
lean_object* v_a_2514_; lean_object* v___x_2516_; 
v_a_2514_ = lean_ctor_get(v_a_2508_, 0);
lean_inc(v_a_2514_);
lean_dec_ref_known(v_a_2508_, 1);
if (v_isShared_2511_ == 0)
{
lean_ctor_set(v___x_2510_, 0, v_a_2514_);
v___x_2516_ = v___x_2510_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2517_; 
v_reuseFailAlloc_2517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2517_, 0, v_a_2514_);
v___x_2516_ = v_reuseFailAlloc_2517_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
return v___x_2516_;
}
}
}
}
else
{
lean_object* v_a_2519_; lean_object* v___x_2521_; uint8_t v_isShared_2522_; uint8_t v_isSharedCheck_2526_; 
v_a_2519_ = lean_ctor_get(v___x_2507_, 0);
v_isSharedCheck_2526_ = !lean_is_exclusive(v___x_2507_);
if (v_isSharedCheck_2526_ == 0)
{
v___x_2521_ = v___x_2507_;
v_isShared_2522_ = v_isSharedCheck_2526_;
goto v_resetjp_2520_;
}
else
{
lean_inc(v_a_2519_);
lean_dec(v___x_2507_);
v___x_2521_ = lean_box(0);
v_isShared_2522_ = v_isSharedCheck_2526_;
goto v_resetjp_2520_;
}
v_resetjp_2520_:
{
lean_object* v___x_2524_; 
if (v_isShared_2522_ == 0)
{
v___x_2524_ = v___x_2521_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v_a_2519_);
v___x_2524_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
return v___x_2524_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_betaRevS___boxed(lean_object* v_f_2527_, lean_object* v_revArgs_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_){
_start:
{
lean_object* v_res_2536_; 
v_res_2536_ = l_Lean_Meta_Sym_betaRevS(v_f_2527_, v_revArgs_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_);
lean_dec(v_a_2534_);
lean_dec_ref(v_a_2533_);
lean_dec(v_a_2532_);
lean_dec_ref(v_a_2531_);
lean_dec(v_a_2530_);
lean_dec_ref(v_a_2529_);
return v_res_2536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_betaS(lean_object* v_f_2537_, lean_object* v_args_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_){
_start:
{
lean_object* v___x_2546_; lean_object* v___x_2547_; 
v___x_2546_ = l_Array_reverse___redArg(v_args_2538_);
v___x_2547_ = l_Lean_Meta_Sym_betaRevS(v_f_2537_, v___x_2546_, v_a_2539_, v_a_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_);
return v___x_2547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_betaS___boxed(lean_object* v_f_2548_, lean_object* v_args_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_){
_start:
{
lean_object* v_res_2557_; 
v_res_2557_ = l_Lean_Meta_Sym_betaS(v_f_2548_, v_args_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_);
lean_dec(v_a_2555_);
lean_dec_ref(v_a_2554_);
lean_dec(v_a_2553_);
lean_dec_ref(v_a_2552_);
lean_dec(v_a_2551_);
lean_dec_ref(v_a_2550_);
return v_res_2557_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_LooseBVarsS(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
