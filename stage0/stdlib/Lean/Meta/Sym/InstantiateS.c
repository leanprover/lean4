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
uint8_t v___y_25934__boxed_14_; lean_object* v_res_15_; 
v___y_25934__boxed_14_ = lean_unbox(v___y_11_);
v_res_15_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0(v_idx_10_, v___y_25934__boxed_14_, v___y_12_, v___y_13_);
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
lean_object* v___x_25_; lean_object* v___x_2922__overap_26_; lean_object* v___x_27_; 
v___x_25_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__0, &l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__0);
v___x_2922__overap_26_ = lean_panic_fn_borrowed(v___x_25_, v_msg_17_);
lean_inc(v___y_23_);
lean_inc_ref(v___y_22_);
lean_inc(v___y_21_);
lean_inc_ref(v___y_20_);
lean_inc(v___y_19_);
lean_inc_ref(v___y_18_);
v___x_27_ = lean_apply_7(v___x_2922__overap_26_, v___y_18_, v___y_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_, lean_box(0));
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
uint8_t v___y_25974__boxed_95_; lean_object* v_res_96_; 
v___y_25974__boxed_95_ = lean_unbox(v___y_92_);
v_res_96_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__2(v_f_89_, v_a_90_, v___y_91_, v___y_25974__boxed_95_, v___y_93_, v___y_94_);
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
uint8_t v_bi_boxed_159_; uint8_t v___y_26080__boxed_160_; lean_object* v_res_161_; 
v_bi_boxed_159_ = lean_unbox(v_bi_152_);
v___y_26080__boxed_160_ = lean_unbox(v___y_156_);
v_res_161_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__4(v_x_151_, v_bi_boxed_159_, v_t_153_, v_b_154_, v___y_155_, v___y_26080__boxed_160_, v___y_157_, v___y_158_);
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
uint8_t v___y_26186__boxed_211_; lean_object* v_res_212_; 
v___y_26186__boxed_211_ = lean_unbox(v___y_208_);
v_res_212_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__7(v_structName_204_, v_idx_205_, v_struct_206_, v___y_207_, v___y_26186__boxed_211_, v___y_209_, v___y_210_);
lean_dec_ref(v___y_209_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8(lean_object* v_msg_220_, lean_object* v___y_221_, uint8_t v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_){
_start:
{
lean_object* v___f_225_; lean_object* v___f_226_; lean_object* v___f_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___f_237_; lean_object* v___f_238_; lean_object* v___f_239_; lean_object* v___f_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_25477__overap_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
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
v___x_25477__overap_249_ = lean_panic_fn_borrowed(v___x_248_, v_msg_220_);
lean_dec(v___x_248_);
v___x_250_ = lean_box(v___y_222_);
lean_inc_ref(v___y_223_);
v___x_251_ = lean_apply_4(v___x_25477__overap_249_, v___y_221_, v___x_250_, v___y_223_, v___y_224_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8___boxed(lean_object* v_msg_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_){
_start:
{
uint8_t v___y_26283__boxed_257_; lean_object* v_res_258_; 
v___y_26283__boxed_257_ = lean_unbox(v___y_254_);
v_res_258_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8(v_msg_252_, v___y_253_, v___y_26283__boxed_257_, v___y_255_, v___y_256_);
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
lean_object* v_key_262_; lean_object* v_value_263_; lean_object* v_tail_264_; lean_object* v_fst_265_; lean_object* v_snd_266_; lean_object* v_fst_267_; lean_object* v_snd_268_; size_t v___x_269_; size_t v___x_270_; uint8_t v___x_271_; 
v_key_262_ = lean_ctor_get(v_x_260_, 0);
v_value_263_ = lean_ctor_get(v_x_260_, 1);
v_tail_264_ = lean_ctor_get(v_x_260_, 2);
v_fst_265_ = lean_ctor_get(v_key_262_, 0);
v_snd_266_ = lean_ctor_get(v_key_262_, 1);
v_fst_267_ = lean_ctor_get(v_a_259_, 0);
v_snd_268_ = lean_ctor_get(v_a_259_, 1);
v___x_269_ = lean_ptr_addr(v_fst_265_);
v___x_270_ = lean_ptr_addr(v_fst_267_);
v___x_271_ = lean_usize_dec_eq(v___x_269_, v___x_270_);
if (v___x_271_ == 0)
{
v_x_260_ = v_tail_264_;
goto _start;
}
else
{
uint8_t v___x_273_; 
v___x_273_ = lean_nat_dec_eq(v_snd_266_, v_snd_268_);
if (v___x_273_ == 0)
{
v_x_260_ = v_tail_264_;
goto _start;
}
else
{
lean_object* v___x_275_; 
lean_inc(v_value_263_);
v___x_275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_275_, 0, v_value_263_);
return v___x_275_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11___redArg___boxed(lean_object* v_a_276_, lean_object* v_x_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11___redArg(v_a_276_, v_x_277_);
lean_dec(v_x_277_);
lean_dec_ref(v_a_276_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3___redArg(lean_object* v_m_279_, lean_object* v_a_280_){
_start:
{
lean_object* v_buckets_281_; lean_object* v_fst_282_; lean_object* v_snd_283_; lean_object* v___x_284_; size_t v___x_285_; size_t v___x_286_; size_t v___x_287_; uint64_t v___x_288_; uint64_t v___x_289_; uint64_t v___x_290_; uint64_t v___x_291_; uint64_t v___x_292_; uint64_t v_fold_293_; uint64_t v___x_294_; uint64_t v___x_295_; uint64_t v___x_296_; size_t v___x_297_; size_t v___x_298_; size_t v___x_299_; size_t v___x_300_; size_t v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v_buckets_281_ = lean_ctor_get(v_m_279_, 1);
v_fst_282_ = lean_ctor_get(v_a_280_, 0);
v_snd_283_ = lean_ctor_get(v_a_280_, 1);
v___x_284_ = lean_array_get_size(v_buckets_281_);
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
v___x_302_ = lean_array_uget_borrowed(v_buckets_281_, v___x_301_);
v___x_303_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11___redArg(v_a_280_, v___x_302_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_m_304_, lean_object* v_a_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3___redArg(v_m_304_, v_a_305_);
lean_dec_ref(v_a_305_);
lean_dec_ref(v_m_304_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__3(lean_object* v_x_307_, uint8_t v_bi_308_, lean_object* v_t_309_, lean_object* v_b_310_, lean_object* v___y_311_, uint8_t v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_){
_start:
{
lean_object* v___y_316_; lean_object* v___y_317_; 
if (v___y_312_ == 0)
{
v___y_316_ = v___y_311_;
v___y_317_ = v___y_314_;
goto v___jp_315_;
}
else
{
lean_object* v___x_339_; 
v___x_339_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_309_, v___y_312_, v___y_313_, v___y_314_);
if (lean_obj_tag(v___x_339_) == 0)
{
lean_object* v_a_340_; lean_object* v___x_341_; 
v_a_340_ = lean_ctor_get(v___x_339_, 1);
lean_inc(v_a_340_);
lean_dec_ref_known(v___x_339_, 2);
v___x_341_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_310_, v___y_312_, v___y_313_, v_a_340_);
if (lean_obj_tag(v___x_341_) == 0)
{
lean_object* v_a_342_; 
v_a_342_ = lean_ctor_get(v___x_341_, 1);
lean_inc(v_a_342_);
lean_dec_ref_known(v___x_341_, 2);
v___y_316_ = v___y_311_;
v___y_317_ = v_a_342_;
goto v___jp_315_;
}
else
{
lean_object* v_a_343_; lean_object* v_a_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_351_; 
lean_dec_ref(v___y_311_);
lean_dec_ref(v_b_310_);
lean_dec_ref(v_t_309_);
lean_dec(v_x_307_);
v_a_343_ = lean_ctor_get(v___x_341_, 0);
v_a_344_ = lean_ctor_get(v___x_341_, 1);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_341_);
if (v_isSharedCheck_351_ == 0)
{
v___x_346_ = v___x_341_;
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_a_344_);
lean_inc(v_a_343_);
lean_dec(v___x_341_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_349_; 
if (v_isShared_347_ == 0)
{
v___x_349_ = v___x_346_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_a_343_);
lean_ctor_set(v_reuseFailAlloc_350_, 1, v_a_344_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
}
}
else
{
lean_object* v_a_352_; lean_object* v_a_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_360_; 
lean_dec_ref(v___y_311_);
lean_dec_ref(v_b_310_);
lean_dec_ref(v_t_309_);
lean_dec(v_x_307_);
v_a_352_ = lean_ctor_get(v___x_339_, 0);
v_a_353_ = lean_ctor_get(v___x_339_, 1);
v_isSharedCheck_360_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_360_ == 0)
{
v___x_355_ = v___x_339_;
v_isShared_356_ = v_isSharedCheck_360_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_a_353_);
lean_inc(v_a_352_);
lean_dec(v___x_339_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_360_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___x_358_; 
if (v_isShared_356_ == 0)
{
v___x_358_ = v___x_355_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v_a_352_);
lean_ctor_set(v_reuseFailAlloc_359_, 1, v_a_353_);
v___x_358_ = v_reuseFailAlloc_359_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
return v___x_358_;
}
}
}
}
v___jp_315_:
{
lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_318_ = l_Lean_Expr_lam___override(v_x_307_, v_t_309_, v_b_310_, v_bi_308_);
v___x_319_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_318_, v___y_317_);
if (lean_obj_tag(v___x_319_) == 0)
{
lean_object* v_a_320_; lean_object* v_a_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_329_; 
v_a_320_ = lean_ctor_get(v___x_319_, 0);
v_a_321_ = lean_ctor_get(v___x_319_, 1);
v_isSharedCheck_329_ = !lean_is_exclusive(v___x_319_);
if (v_isSharedCheck_329_ == 0)
{
v___x_323_ = v___x_319_;
v_isShared_324_ = v_isSharedCheck_329_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_a_321_);
lean_inc(v_a_320_);
lean_dec(v___x_319_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_329_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_325_; lean_object* v___x_327_; 
v___x_325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_325_, 0, v_a_320_);
lean_ctor_set(v___x_325_, 1, v___y_316_);
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 0, v___x_325_);
v___x_327_ = v___x_323_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v___x_325_);
lean_ctor_set(v_reuseFailAlloc_328_, 1, v_a_321_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
}
else
{
lean_object* v_a_330_; lean_object* v_a_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_338_; 
lean_dec_ref(v___y_316_);
v_a_330_ = lean_ctor_get(v___x_319_, 0);
v_a_331_ = lean_ctor_get(v___x_319_, 1);
v_isSharedCheck_338_ = !lean_is_exclusive(v___x_319_);
if (v_isSharedCheck_338_ == 0)
{
v___x_333_ = v___x_319_;
v_isShared_334_ = v_isSharedCheck_338_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_a_331_);
lean_inc(v_a_330_);
lean_dec(v___x_319_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_338_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_336_; 
if (v_isShared_334_ == 0)
{
v___x_336_ = v___x_333_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v_a_330_);
lean_ctor_set(v_reuseFailAlloc_337_, 1, v_a_331_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__3___boxed(lean_object* v_x_361_, lean_object* v_bi_362_, lean_object* v_t_363_, lean_object* v_b_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_){
_start:
{
uint8_t v_bi_boxed_369_; uint8_t v___y_26431__boxed_370_; lean_object* v_res_371_; 
v_bi_boxed_369_ = lean_unbox(v_bi_362_);
v___y_26431__boxed_370_ = lean_unbox(v___y_366_);
v_res_371_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__3(v_x_361_, v_bi_boxed_369_, v_t_363_, v_b_364_, v___y_365_, v___y_26431__boxed_370_, v___y_367_, v___y_368_);
lean_dec_ref(v___y_367_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__5(lean_object* v_x_372_, lean_object* v_t_373_, lean_object* v_v_374_, lean_object* v_b_375_, uint8_t v_nondep_376_, lean_object* v___y_377_, uint8_t v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_){
_start:
{
lean_object* v___y_382_; lean_object* v___y_383_; 
if (v___y_378_ == 0)
{
v___y_382_ = v___y_377_;
v___y_383_ = v___y_380_;
goto v___jp_381_;
}
else
{
lean_object* v___x_405_; 
v___x_405_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_373_, v___y_378_, v___y_379_, v___y_380_);
if (lean_obj_tag(v___x_405_) == 0)
{
lean_object* v_a_406_; lean_object* v___x_407_; 
v_a_406_ = lean_ctor_get(v___x_405_, 1);
lean_inc(v_a_406_);
lean_dec_ref_known(v___x_405_, 2);
v___x_407_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_v_374_, v___y_378_, v___y_379_, v_a_406_);
if (lean_obj_tag(v___x_407_) == 0)
{
lean_object* v_a_408_; lean_object* v___x_409_; 
v_a_408_ = lean_ctor_get(v___x_407_, 1);
lean_inc(v_a_408_);
lean_dec_ref_known(v___x_407_, 2);
v___x_409_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_375_, v___y_378_, v___y_379_, v_a_408_);
if (lean_obj_tag(v___x_409_) == 0)
{
lean_object* v_a_410_; 
v_a_410_ = lean_ctor_get(v___x_409_, 1);
lean_inc(v_a_410_);
lean_dec_ref_known(v___x_409_, 2);
v___y_382_ = v___y_377_;
v___y_383_ = v_a_410_;
goto v___jp_381_;
}
else
{
lean_object* v_a_411_; lean_object* v_a_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_419_; 
lean_dec_ref(v___y_377_);
lean_dec_ref(v_b_375_);
lean_dec_ref(v_v_374_);
lean_dec_ref(v_t_373_);
lean_dec(v_x_372_);
v_a_411_ = lean_ctor_get(v___x_409_, 0);
v_a_412_ = lean_ctor_get(v___x_409_, 1);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_419_ == 0)
{
v___x_414_ = v___x_409_;
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_a_412_);
lean_inc(v_a_411_);
lean_dec(v___x_409_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_417_; 
if (v_isShared_415_ == 0)
{
v___x_417_ = v___x_414_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_a_411_);
lean_ctor_set(v_reuseFailAlloc_418_, 1, v_a_412_);
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
else
{
lean_object* v_a_420_; lean_object* v_a_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_428_; 
lean_dec_ref(v___y_377_);
lean_dec_ref(v_b_375_);
lean_dec_ref(v_v_374_);
lean_dec_ref(v_t_373_);
lean_dec(v_x_372_);
v_a_420_ = lean_ctor_get(v___x_407_, 0);
v_a_421_ = lean_ctor_get(v___x_407_, 1);
v_isSharedCheck_428_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_428_ == 0)
{
v___x_423_ = v___x_407_;
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_a_421_);
lean_inc(v_a_420_);
lean_dec(v___x_407_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_426_; 
if (v_isShared_424_ == 0)
{
v___x_426_ = v___x_423_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v_a_420_);
lean_ctor_set(v_reuseFailAlloc_427_, 1, v_a_421_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
return v___x_426_;
}
}
}
}
else
{
lean_object* v_a_429_; lean_object* v_a_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_437_; 
lean_dec_ref(v___y_377_);
lean_dec_ref(v_b_375_);
lean_dec_ref(v_v_374_);
lean_dec_ref(v_t_373_);
lean_dec(v_x_372_);
v_a_429_ = lean_ctor_get(v___x_405_, 0);
v_a_430_ = lean_ctor_get(v___x_405_, 1);
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_405_);
if (v_isSharedCheck_437_ == 0)
{
v___x_432_ = v___x_405_;
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_a_430_);
lean_inc(v_a_429_);
lean_dec(v___x_405_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_435_; 
if (v_isShared_433_ == 0)
{
v___x_435_ = v___x_432_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_a_429_);
lean_ctor_set(v_reuseFailAlloc_436_, 1, v_a_430_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
}
v___jp_381_:
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = l_Lean_Expr_letE___override(v_x_372_, v_t_373_, v_v_374_, v_b_375_, v_nondep_376_);
v___x_385_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_384_, v___y_383_);
if (lean_obj_tag(v___x_385_) == 0)
{
lean_object* v_a_386_; lean_object* v_a_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_395_; 
v_a_386_ = lean_ctor_get(v___x_385_, 0);
v_a_387_ = lean_ctor_get(v___x_385_, 1);
v_isSharedCheck_395_ = !lean_is_exclusive(v___x_385_);
if (v_isSharedCheck_395_ == 0)
{
v___x_389_ = v___x_385_;
v_isShared_390_ = v_isSharedCheck_395_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_a_387_);
lean_inc(v_a_386_);
lean_dec(v___x_385_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_395_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_391_; lean_object* v___x_393_; 
v___x_391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_391_, 0, v_a_386_);
lean_ctor_set(v___x_391_, 1, v___y_382_);
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 0, v___x_391_);
v___x_393_ = v___x_389_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v___x_391_);
lean_ctor_set(v_reuseFailAlloc_394_, 1, v_a_387_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
return v___x_393_;
}
}
}
else
{
lean_object* v_a_396_; lean_object* v_a_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_404_; 
lean_dec_ref(v___y_382_);
v_a_396_ = lean_ctor_get(v___x_385_, 0);
v_a_397_ = lean_ctor_get(v___x_385_, 1);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_385_);
if (v_isSharedCheck_404_ == 0)
{
v___x_399_ = v___x_385_;
v_isShared_400_ = v_isSharedCheck_404_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_a_397_);
lean_inc(v_a_396_);
lean_dec(v___x_385_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_404_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_402_; 
if (v_isShared_400_ == 0)
{
v___x_402_ = v___x_399_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_a_396_);
lean_ctor_set(v_reuseFailAlloc_403_, 1, v_a_397_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__5___boxed(lean_object* v_x_438_, lean_object* v_t_439_, lean_object* v_v_440_, lean_object* v_b_441_, lean_object* v_nondep_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_){
_start:
{
uint8_t v_nondep_boxed_447_; uint8_t v___y_26537__boxed_448_; lean_object* v_res_449_; 
v_nondep_boxed_447_ = lean_unbox(v_nondep_442_);
v___y_26537__boxed_448_ = lean_unbox(v___y_444_);
v_res_449_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__5(v_x_438_, v_t_439_, v_v_440_, v_b_441_, v_nondep_boxed_447_, v___y_443_, v___y_26537__boxed_448_, v___y_445_, v___y_446_);
lean_dec_ref(v___y_445_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__6(lean_object* v_d_450_, lean_object* v_e_451_, lean_object* v___y_452_, uint8_t v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_){
_start:
{
lean_object* v___y_457_; lean_object* v___y_458_; 
if (v___y_453_ == 0)
{
v___y_457_ = v___y_452_;
v___y_458_ = v___y_455_;
goto v___jp_456_;
}
else
{
lean_object* v___x_480_; 
v___x_480_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_e_451_, v___y_453_, v___y_454_, v___y_455_);
if (lean_obj_tag(v___x_480_) == 0)
{
lean_object* v_a_481_; 
v_a_481_ = lean_ctor_get(v___x_480_, 1);
lean_inc(v_a_481_);
lean_dec_ref_known(v___x_480_, 2);
v___y_457_ = v___y_452_;
v___y_458_ = v_a_481_;
goto v___jp_456_;
}
else
{
lean_object* v_a_482_; lean_object* v_a_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_490_; 
lean_dec_ref(v___y_452_);
lean_dec_ref(v_e_451_);
lean_dec(v_d_450_);
v_a_482_ = lean_ctor_get(v___x_480_, 0);
v_a_483_ = lean_ctor_get(v___x_480_, 1);
v_isSharedCheck_490_ = !lean_is_exclusive(v___x_480_);
if (v_isSharedCheck_490_ == 0)
{
v___x_485_ = v___x_480_;
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_a_483_);
lean_inc(v_a_482_);
lean_dec(v___x_480_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_488_; 
if (v_isShared_486_ == 0)
{
v___x_488_ = v___x_485_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v_a_482_);
lean_ctor_set(v_reuseFailAlloc_489_, 1, v_a_483_);
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
v___jp_456_:
{
lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_459_ = l_Lean_Expr_mdata___override(v_d_450_, v_e_451_);
v___x_460_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_459_, v___y_458_);
if (lean_obj_tag(v___x_460_) == 0)
{
lean_object* v_a_461_; lean_object* v_a_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_470_; 
v_a_461_ = lean_ctor_get(v___x_460_, 0);
v_a_462_ = lean_ctor_get(v___x_460_, 1);
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_470_ == 0)
{
v___x_464_ = v___x_460_;
v_isShared_465_ = v_isSharedCheck_470_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_a_462_);
lean_inc(v_a_461_);
lean_dec(v___x_460_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_470_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_466_; lean_object* v___x_468_; 
v___x_466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_466_, 0, v_a_461_);
lean_ctor_set(v___x_466_, 1, v___y_457_);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 0, v___x_466_);
v___x_468_ = v___x_464_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v___x_466_);
lean_ctor_set(v_reuseFailAlloc_469_, 1, v_a_462_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
else
{
lean_object* v_a_471_; lean_object* v_a_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_479_; 
lean_dec_ref(v___y_457_);
v_a_471_ = lean_ctor_get(v___x_460_, 0);
v_a_472_ = lean_ctor_get(v___x_460_, 1);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_479_ == 0)
{
v___x_474_ = v___x_460_;
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_a_472_);
lean_inc(v_a_471_);
lean_dec(v___x_460_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_477_; 
if (v_isShared_475_ == 0)
{
v___x_477_ = v___x_474_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_a_471_);
lean_ctor_set(v_reuseFailAlloc_478_, 1, v_a_472_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__6___boxed(lean_object* v_d_491_, lean_object* v_e_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_){
_start:
{
uint8_t v___y_26666__boxed_497_; lean_object* v_res_498_; 
v___y_26666__boxed_497_ = lean_unbox(v___y_494_);
v_res_498_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__6(v_d_491_, v_e_492_, v___y_493_, v___y_26666__boxed_497_, v___y_495_, v___y_496_);
lean_dec_ref(v___y_495_);
return v_res_498_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__3(void){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_502_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__2));
v___x_503_ = lean_unsigned_to_nat(67u);
v___x_504_ = lean_unsigned_to_nat(35u);
v___x_505_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__1));
v___x_506_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__0));
v___x_507_ = l_mkPanicMessageWithDecl(v___x_506_, v___x_505_, v___x_504_, v___x_503_, v___x_502_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1(lean_object* v_beginIdx_508_, lean_object* v_n_509_, lean_object* v_subst_510_, lean_object* v_e_511_, lean_object* v_offset_512_, lean_object* v_a_513_, uint8_t v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_){
_start:
{
switch(lean_obj_tag(v_e_511_))
{
case 5:
{
lean_object* v_fn_517_; lean_object* v_arg_518_; lean_object* v___x_519_; 
v_fn_517_ = lean_ctor_get(v_e_511_, 0);
v_arg_518_ = lean_ctor_get(v_e_511_, 1);
lean_inc(v_offset_512_);
lean_inc_ref(v_fn_517_);
v___x_519_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(v_beginIdx_508_, v_n_509_, v_subst_510_, v_fn_517_, v_offset_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v_a_520_; lean_object* v_a_521_; lean_object* v_fst_522_; lean_object* v_snd_523_; lean_object* v___x_524_; 
v_a_520_ = lean_ctor_get(v___x_519_, 0);
lean_inc(v_a_520_);
v_a_521_ = lean_ctor_get(v___x_519_, 1);
lean_inc(v_a_521_);
lean_dec_ref_known(v___x_519_, 2);
v_fst_522_ = lean_ctor_get(v_a_520_, 0);
lean_inc(v_fst_522_);
v_snd_523_ = lean_ctor_get(v_a_520_, 1);
lean_inc(v_snd_523_);
lean_dec(v_a_520_);
lean_inc_ref(v_arg_518_);
v___x_524_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(v_beginIdx_508_, v_n_509_, v_subst_510_, v_arg_518_, v_offset_512_, v_snd_523_, v_a_514_, v_a_515_, v_a_521_);
if (lean_obj_tag(v___x_524_) == 0)
{
lean_object* v_a_525_; lean_object* v_a_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_550_; 
v_a_525_ = lean_ctor_get(v___x_524_, 0);
v_a_526_ = lean_ctor_get(v___x_524_, 1);
v_isSharedCheck_550_ = !lean_is_exclusive(v___x_524_);
if (v_isSharedCheck_550_ == 0)
{
v___x_528_ = v___x_524_;
v_isShared_529_ = v_isSharedCheck_550_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_a_526_);
lean_inc(v_a_525_);
lean_dec(v___x_524_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_550_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v_fst_530_; lean_object* v_snd_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_549_; 
v_fst_530_ = lean_ctor_get(v_a_525_, 0);
v_snd_531_ = lean_ctor_get(v_a_525_, 1);
v_isSharedCheck_549_ = !lean_is_exclusive(v_a_525_);
if (v_isSharedCheck_549_ == 0)
{
v___x_533_ = v_a_525_;
v_isShared_534_ = v_isSharedCheck_549_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_snd_531_);
lean_inc(v_fst_530_);
lean_dec(v_a_525_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_549_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
size_t v___x_535_; size_t v___x_536_; uint8_t v___x_537_; 
v___x_535_ = lean_ptr_addr(v_fn_517_);
v___x_536_ = lean_ptr_addr(v_fst_522_);
v___x_537_ = lean_usize_dec_eq(v___x_535_, v___x_536_);
if (v___x_537_ == 0)
{
lean_object* v___x_538_; 
lean_del_object(v___x_533_);
lean_del_object(v___x_528_);
lean_dec_ref_known(v_e_511_, 2);
v___x_538_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__2(v_fst_522_, v_fst_530_, v_snd_531_, v_a_514_, v_a_515_, v_a_526_);
return v___x_538_;
}
else
{
size_t v___x_539_; size_t v___x_540_; uint8_t v___x_541_; 
v___x_539_ = lean_ptr_addr(v_arg_518_);
v___x_540_ = lean_ptr_addr(v_fst_530_);
v___x_541_ = lean_usize_dec_eq(v___x_539_, v___x_540_);
if (v___x_541_ == 0)
{
lean_object* v___x_542_; 
lean_del_object(v___x_533_);
lean_del_object(v___x_528_);
lean_dec_ref_known(v_e_511_, 2);
v___x_542_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__2(v_fst_522_, v_fst_530_, v_snd_531_, v_a_514_, v_a_515_, v_a_526_);
return v___x_542_;
}
else
{
lean_object* v___x_544_; 
lean_dec(v_fst_530_);
lean_dec(v_fst_522_);
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 0, v_e_511_);
v___x_544_ = v___x_533_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_e_511_);
lean_ctor_set(v_reuseFailAlloc_548_, 1, v_snd_531_);
v___x_544_ = v_reuseFailAlloc_548_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
lean_object* v___x_546_; 
if (v_isShared_529_ == 0)
{
lean_ctor_set(v___x_528_, 0, v___x_544_);
v___x_546_ = v___x_528_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v___x_544_);
lean_ctor_set(v_reuseFailAlloc_547_, 1, v_a_526_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_522_);
lean_dec_ref_known(v_e_511_, 2);
return v___x_524_;
}
}
else
{
lean_dec_ref_known(v_e_511_, 2);
lean_dec(v_offset_512_);
return v___x_519_;
}
}
case 6:
{
lean_object* v_binderName_551_; lean_object* v_binderType_552_; lean_object* v_body_553_; uint8_t v_binderInfo_554_; lean_object* v___x_555_; 
v_binderName_551_ = lean_ctor_get(v_e_511_, 0);
v_binderType_552_ = lean_ctor_get(v_e_511_, 1);
v_body_553_ = lean_ctor_get(v_e_511_, 2);
v_binderInfo_554_ = lean_ctor_get_uint8(v_e_511_, sizeof(void*)*3 + 8);
lean_inc(v_offset_512_);
lean_inc_ref(v_binderType_552_);
v___x_555_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(v_beginIdx_508_, v_n_509_, v_subst_510_, v_binderType_552_, v_offset_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_);
if (lean_obj_tag(v___x_555_) == 0)
{
lean_object* v_a_556_; lean_object* v_a_557_; lean_object* v_fst_558_; lean_object* v_snd_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v_a_556_ = lean_ctor_get(v___x_555_, 0);
lean_inc(v_a_556_);
v_a_557_ = lean_ctor_get(v___x_555_, 1);
lean_inc(v_a_557_);
lean_dec_ref_known(v___x_555_, 2);
v_fst_558_ = lean_ctor_get(v_a_556_, 0);
lean_inc(v_fst_558_);
v_snd_559_ = lean_ctor_get(v_a_556_, 1);
lean_inc(v_snd_559_);
lean_dec(v_a_556_);
v___x_560_ = lean_unsigned_to_nat(1u);
v___x_561_ = lean_nat_add(v_offset_512_, v___x_560_);
lean_dec(v_offset_512_);
lean_inc_ref(v_body_553_);
v___x_562_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(v_beginIdx_508_, v_n_509_, v_subst_510_, v_body_553_, v___x_561_, v_snd_559_, v_a_514_, v_a_515_, v_a_557_);
if (lean_obj_tag(v___x_562_) == 0)
{
lean_object* v_a_563_; lean_object* v_a_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_588_; 
v_a_563_ = lean_ctor_get(v___x_562_, 0);
v_a_564_ = lean_ctor_get(v___x_562_, 1);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_588_ == 0)
{
v___x_566_ = v___x_562_;
v_isShared_567_ = v_isSharedCheck_588_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_a_564_);
lean_inc(v_a_563_);
lean_dec(v___x_562_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_588_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v_fst_568_; lean_object* v_snd_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_587_; 
v_fst_568_ = lean_ctor_get(v_a_563_, 0);
v_snd_569_ = lean_ctor_get(v_a_563_, 1);
v_isSharedCheck_587_ = !lean_is_exclusive(v_a_563_);
if (v_isSharedCheck_587_ == 0)
{
v___x_571_ = v_a_563_;
v_isShared_572_ = v_isSharedCheck_587_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_snd_569_);
lean_inc(v_fst_568_);
lean_dec(v_a_563_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_587_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
size_t v___x_573_; size_t v___x_574_; uint8_t v___x_575_; 
v___x_573_ = lean_ptr_addr(v_binderType_552_);
v___x_574_ = lean_ptr_addr(v_fst_558_);
v___x_575_ = lean_usize_dec_eq(v___x_573_, v___x_574_);
if (v___x_575_ == 0)
{
lean_object* v___x_576_; 
lean_inc(v_binderName_551_);
lean_del_object(v___x_571_);
lean_del_object(v___x_566_);
lean_dec_ref_known(v_e_511_, 3);
v___x_576_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__3(v_binderName_551_, v_binderInfo_554_, v_fst_558_, v_fst_568_, v_snd_569_, v_a_514_, v_a_515_, v_a_564_);
return v___x_576_;
}
else
{
size_t v___x_577_; size_t v___x_578_; uint8_t v___x_579_; 
v___x_577_ = lean_ptr_addr(v_body_553_);
v___x_578_ = lean_ptr_addr(v_fst_568_);
v___x_579_ = lean_usize_dec_eq(v___x_577_, v___x_578_);
if (v___x_579_ == 0)
{
lean_object* v___x_580_; 
lean_inc(v_binderName_551_);
lean_del_object(v___x_571_);
lean_del_object(v___x_566_);
lean_dec_ref_known(v_e_511_, 3);
v___x_580_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__3(v_binderName_551_, v_binderInfo_554_, v_fst_558_, v_fst_568_, v_snd_569_, v_a_514_, v_a_515_, v_a_564_);
return v___x_580_;
}
else
{
lean_object* v___x_582_; 
lean_dec(v_fst_568_);
lean_dec(v_fst_558_);
if (v_isShared_572_ == 0)
{
lean_ctor_set(v___x_571_, 0, v_e_511_);
v___x_582_ = v___x_571_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_e_511_);
lean_ctor_set(v_reuseFailAlloc_586_, 1, v_snd_569_);
v___x_582_ = v_reuseFailAlloc_586_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
lean_object* v___x_584_; 
if (v_isShared_567_ == 0)
{
lean_ctor_set(v___x_566_, 0, v___x_582_);
v___x_584_ = v___x_566_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v___x_582_);
lean_ctor_set(v_reuseFailAlloc_585_, 1, v_a_564_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
return v___x_584_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_558_);
lean_dec_ref_known(v_e_511_, 3);
return v___x_562_;
}
}
else
{
lean_dec_ref_known(v_e_511_, 3);
lean_dec(v_offset_512_);
return v___x_555_;
}
}
case 7:
{
lean_object* v_binderName_589_; lean_object* v_binderType_590_; lean_object* v_body_591_; uint8_t v_binderInfo_592_; lean_object* v___x_593_; 
v_binderName_589_ = lean_ctor_get(v_e_511_, 0);
v_binderType_590_ = lean_ctor_get(v_e_511_, 1);
v_body_591_ = lean_ctor_get(v_e_511_, 2);
v_binderInfo_592_ = lean_ctor_get_uint8(v_e_511_, sizeof(void*)*3 + 8);
lean_inc(v_offset_512_);
lean_inc_ref(v_binderType_590_);
v___x_593_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(v_beginIdx_508_, v_n_509_, v_subst_510_, v_binderType_590_, v_offset_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_);
if (lean_obj_tag(v___x_593_) == 0)
{
lean_object* v_a_594_; lean_object* v_a_595_; lean_object* v_fst_596_; lean_object* v_snd_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
v_a_594_ = lean_ctor_get(v___x_593_, 0);
lean_inc(v_a_594_);
v_a_595_ = lean_ctor_get(v___x_593_, 1);
lean_inc(v_a_595_);
lean_dec_ref_known(v___x_593_, 2);
v_fst_596_ = lean_ctor_get(v_a_594_, 0);
lean_inc(v_fst_596_);
v_snd_597_ = lean_ctor_get(v_a_594_, 1);
lean_inc(v_snd_597_);
lean_dec(v_a_594_);
v___x_598_ = lean_unsigned_to_nat(1u);
v___x_599_ = lean_nat_add(v_offset_512_, v___x_598_);
lean_dec(v_offset_512_);
lean_inc_ref(v_body_591_);
v___x_600_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(v_beginIdx_508_, v_n_509_, v_subst_510_, v_body_591_, v___x_599_, v_snd_597_, v_a_514_, v_a_515_, v_a_595_);
if (lean_obj_tag(v___x_600_) == 0)
{
lean_object* v_a_601_; lean_object* v_a_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_626_; 
v_a_601_ = lean_ctor_get(v___x_600_, 0);
v_a_602_ = lean_ctor_get(v___x_600_, 1);
v_isSharedCheck_626_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_626_ == 0)
{
v___x_604_ = v___x_600_;
v_isShared_605_ = v_isSharedCheck_626_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_a_602_);
lean_inc(v_a_601_);
lean_dec(v___x_600_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_626_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v_fst_606_; lean_object* v_snd_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_625_; 
v_fst_606_ = lean_ctor_get(v_a_601_, 0);
v_snd_607_ = lean_ctor_get(v_a_601_, 1);
v_isSharedCheck_625_ = !lean_is_exclusive(v_a_601_);
if (v_isSharedCheck_625_ == 0)
{
v___x_609_ = v_a_601_;
v_isShared_610_ = v_isSharedCheck_625_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_snd_607_);
lean_inc(v_fst_606_);
lean_dec(v_a_601_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_625_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
size_t v___x_611_; size_t v___x_612_; uint8_t v___x_613_; 
v___x_611_ = lean_ptr_addr(v_binderType_590_);
v___x_612_ = lean_ptr_addr(v_fst_596_);
v___x_613_ = lean_usize_dec_eq(v___x_611_, v___x_612_);
if (v___x_613_ == 0)
{
lean_object* v___x_614_; 
lean_inc(v_binderName_589_);
lean_del_object(v___x_609_);
lean_del_object(v___x_604_);
lean_dec_ref_known(v_e_511_, 3);
v___x_614_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__4(v_binderName_589_, v_binderInfo_592_, v_fst_596_, v_fst_606_, v_snd_607_, v_a_514_, v_a_515_, v_a_602_);
return v___x_614_;
}
else
{
size_t v___x_615_; size_t v___x_616_; uint8_t v___x_617_; 
v___x_615_ = lean_ptr_addr(v_body_591_);
v___x_616_ = lean_ptr_addr(v_fst_606_);
v___x_617_ = lean_usize_dec_eq(v___x_615_, v___x_616_);
if (v___x_617_ == 0)
{
lean_object* v___x_618_; 
lean_inc(v_binderName_589_);
lean_del_object(v___x_609_);
lean_del_object(v___x_604_);
lean_dec_ref_known(v_e_511_, 3);
v___x_618_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__4(v_binderName_589_, v_binderInfo_592_, v_fst_596_, v_fst_606_, v_snd_607_, v_a_514_, v_a_515_, v_a_602_);
return v___x_618_;
}
else
{
lean_object* v___x_620_; 
lean_dec(v_fst_606_);
lean_dec(v_fst_596_);
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 0, v_e_511_);
v___x_620_ = v___x_609_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_e_511_);
lean_ctor_set(v_reuseFailAlloc_624_, 1, v_snd_607_);
v___x_620_ = v_reuseFailAlloc_624_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
lean_object* v___x_622_; 
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 0, v___x_620_);
v___x_622_ = v___x_604_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v___x_620_);
lean_ctor_set(v_reuseFailAlloc_623_, 1, v_a_602_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_596_);
lean_dec_ref_known(v_e_511_, 3);
return v___x_600_;
}
}
else
{
lean_dec_ref_known(v_e_511_, 3);
lean_dec(v_offset_512_);
return v___x_593_;
}
}
case 8:
{
lean_object* v_declName_627_; lean_object* v_type_628_; lean_object* v_value_629_; lean_object* v_body_630_; uint8_t v_nondep_631_; lean_object* v___x_632_; 
v_declName_627_ = lean_ctor_get(v_e_511_, 0);
v_type_628_ = lean_ctor_get(v_e_511_, 1);
v_value_629_ = lean_ctor_get(v_e_511_, 2);
v_body_630_ = lean_ctor_get(v_e_511_, 3);
v_nondep_631_ = lean_ctor_get_uint8(v_e_511_, sizeof(void*)*4 + 8);
lean_inc(v_offset_512_);
lean_inc_ref(v_type_628_);
v___x_632_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(v_beginIdx_508_, v_n_509_, v_subst_510_, v_type_628_, v_offset_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_);
if (lean_obj_tag(v___x_632_) == 0)
{
lean_object* v_a_633_; lean_object* v_a_634_; lean_object* v_fst_635_; lean_object* v_snd_636_; lean_object* v___x_637_; 
v_a_633_ = lean_ctor_get(v___x_632_, 0);
lean_inc(v_a_633_);
v_a_634_ = lean_ctor_get(v___x_632_, 1);
lean_inc(v_a_634_);
lean_dec_ref_known(v___x_632_, 2);
v_fst_635_ = lean_ctor_get(v_a_633_, 0);
lean_inc(v_fst_635_);
v_snd_636_ = lean_ctor_get(v_a_633_, 1);
lean_inc(v_snd_636_);
lean_dec(v_a_633_);
lean_inc(v_offset_512_);
lean_inc_ref(v_value_629_);
v___x_637_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(v_beginIdx_508_, v_n_509_, v_subst_510_, v_value_629_, v_offset_512_, v_snd_636_, v_a_514_, v_a_515_, v_a_634_);
if (lean_obj_tag(v___x_637_) == 0)
{
lean_object* v_a_638_; lean_object* v_a_639_; lean_object* v_fst_640_; lean_object* v_snd_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v_a_638_ = lean_ctor_get(v___x_637_, 0);
lean_inc(v_a_638_);
v_a_639_ = lean_ctor_get(v___x_637_, 1);
lean_inc(v_a_639_);
lean_dec_ref_known(v___x_637_, 2);
v_fst_640_ = lean_ctor_get(v_a_638_, 0);
lean_inc(v_fst_640_);
v_snd_641_ = lean_ctor_get(v_a_638_, 1);
lean_inc(v_snd_641_);
lean_dec(v_a_638_);
v___x_642_ = lean_unsigned_to_nat(1u);
v___x_643_ = lean_nat_add(v_offset_512_, v___x_642_);
lean_dec(v_offset_512_);
lean_inc_ref(v_body_630_);
v___x_644_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(v_beginIdx_508_, v_n_509_, v_subst_510_, v_body_630_, v___x_643_, v_snd_641_, v_a_514_, v_a_515_, v_a_639_);
if (lean_obj_tag(v___x_644_) == 0)
{
lean_object* v_a_645_; lean_object* v_a_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_674_; 
v_a_645_ = lean_ctor_get(v___x_644_, 0);
v_a_646_ = lean_ctor_get(v___x_644_, 1);
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_674_ == 0)
{
v___x_648_ = v___x_644_;
v_isShared_649_ = v_isSharedCheck_674_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_a_646_);
lean_inc(v_a_645_);
lean_dec(v___x_644_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_674_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v_fst_650_; lean_object* v_snd_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_673_; 
v_fst_650_ = lean_ctor_get(v_a_645_, 0);
v_snd_651_ = lean_ctor_get(v_a_645_, 1);
v_isSharedCheck_673_ = !lean_is_exclusive(v_a_645_);
if (v_isSharedCheck_673_ == 0)
{
v___x_653_ = v_a_645_;
v_isShared_654_ = v_isSharedCheck_673_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_snd_651_);
lean_inc(v_fst_650_);
lean_dec(v_a_645_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_673_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
size_t v___x_655_; size_t v___x_656_; uint8_t v___x_657_; 
v___x_655_ = lean_ptr_addr(v_type_628_);
v___x_656_ = lean_ptr_addr(v_fst_635_);
v___x_657_ = lean_usize_dec_eq(v___x_655_, v___x_656_);
if (v___x_657_ == 0)
{
lean_object* v___x_658_; 
lean_inc(v_declName_627_);
lean_del_object(v___x_653_);
lean_del_object(v___x_648_);
lean_dec_ref_known(v_e_511_, 4);
v___x_658_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__5(v_declName_627_, v_fst_635_, v_fst_640_, v_fst_650_, v_nondep_631_, v_snd_651_, v_a_514_, v_a_515_, v_a_646_);
return v___x_658_;
}
else
{
size_t v___x_659_; size_t v___x_660_; uint8_t v___x_661_; 
v___x_659_ = lean_ptr_addr(v_value_629_);
v___x_660_ = lean_ptr_addr(v_fst_640_);
v___x_661_ = lean_usize_dec_eq(v___x_659_, v___x_660_);
if (v___x_661_ == 0)
{
lean_object* v___x_662_; 
lean_inc(v_declName_627_);
lean_del_object(v___x_653_);
lean_del_object(v___x_648_);
lean_dec_ref_known(v_e_511_, 4);
v___x_662_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__5(v_declName_627_, v_fst_635_, v_fst_640_, v_fst_650_, v_nondep_631_, v_snd_651_, v_a_514_, v_a_515_, v_a_646_);
return v___x_662_;
}
else
{
size_t v___x_663_; size_t v___x_664_; uint8_t v___x_665_; 
v___x_663_ = lean_ptr_addr(v_body_630_);
v___x_664_ = lean_ptr_addr(v_fst_650_);
v___x_665_ = lean_usize_dec_eq(v___x_663_, v___x_664_);
if (v___x_665_ == 0)
{
lean_object* v___x_666_; 
lean_inc(v_declName_627_);
lean_del_object(v___x_653_);
lean_del_object(v___x_648_);
lean_dec_ref_known(v_e_511_, 4);
v___x_666_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__5(v_declName_627_, v_fst_635_, v_fst_640_, v_fst_650_, v_nondep_631_, v_snd_651_, v_a_514_, v_a_515_, v_a_646_);
return v___x_666_;
}
else
{
lean_object* v___x_668_; 
lean_dec(v_fst_650_);
lean_dec(v_fst_640_);
lean_dec(v_fst_635_);
if (v_isShared_654_ == 0)
{
lean_ctor_set(v___x_653_, 0, v_e_511_);
v___x_668_ = v___x_653_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_e_511_);
lean_ctor_set(v_reuseFailAlloc_672_, 1, v_snd_651_);
v___x_668_ = v_reuseFailAlloc_672_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
lean_object* v___x_670_; 
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 0, v___x_668_);
v___x_670_ = v___x_648_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v___x_668_);
lean_ctor_set(v_reuseFailAlloc_671_, 1, v_a_646_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
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
lean_dec(v_fst_640_);
lean_dec(v_fst_635_);
lean_dec_ref_known(v_e_511_, 4);
return v___x_644_;
}
}
else
{
lean_dec(v_fst_635_);
lean_dec_ref_known(v_e_511_, 4);
lean_dec(v_offset_512_);
return v___x_637_;
}
}
else
{
lean_dec_ref_known(v_e_511_, 4);
lean_dec(v_offset_512_);
return v___x_632_;
}
}
case 10:
{
lean_object* v_data_675_; lean_object* v_expr_676_; lean_object* v___x_677_; 
v_data_675_ = lean_ctor_get(v_e_511_, 0);
v_expr_676_ = lean_ctor_get(v_e_511_, 1);
lean_inc_ref(v_expr_676_);
v___x_677_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(v_beginIdx_508_, v_n_509_, v_subst_510_, v_expr_676_, v_offset_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_);
if (lean_obj_tag(v___x_677_) == 0)
{
lean_object* v_a_678_; lean_object* v_a_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_699_; 
v_a_678_ = lean_ctor_get(v___x_677_, 0);
v_a_679_ = lean_ctor_get(v___x_677_, 1);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_677_);
if (v_isSharedCheck_699_ == 0)
{
v___x_681_ = v___x_677_;
v_isShared_682_ = v_isSharedCheck_699_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_a_679_);
lean_inc(v_a_678_);
lean_dec(v___x_677_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_699_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v_fst_683_; lean_object* v_snd_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_698_; 
v_fst_683_ = lean_ctor_get(v_a_678_, 0);
v_snd_684_ = lean_ctor_get(v_a_678_, 1);
v_isSharedCheck_698_ = !lean_is_exclusive(v_a_678_);
if (v_isSharedCheck_698_ == 0)
{
v___x_686_ = v_a_678_;
v_isShared_687_ = v_isSharedCheck_698_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_snd_684_);
lean_inc(v_fst_683_);
lean_dec(v_a_678_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_698_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
size_t v___x_688_; size_t v___x_689_; uint8_t v___x_690_; 
v___x_688_ = lean_ptr_addr(v_expr_676_);
v___x_689_ = lean_ptr_addr(v_fst_683_);
v___x_690_ = lean_usize_dec_eq(v___x_688_, v___x_689_);
if (v___x_690_ == 0)
{
lean_object* v___x_691_; 
lean_inc(v_data_675_);
lean_del_object(v___x_686_);
lean_del_object(v___x_681_);
lean_dec_ref_known(v_e_511_, 2);
v___x_691_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__6(v_data_675_, v_fst_683_, v_snd_684_, v_a_514_, v_a_515_, v_a_679_);
return v___x_691_;
}
else
{
lean_object* v___x_693_; 
lean_dec(v_fst_683_);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 0, v_e_511_);
v___x_693_ = v___x_686_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_e_511_);
lean_ctor_set(v_reuseFailAlloc_697_, 1, v_snd_684_);
v___x_693_ = v_reuseFailAlloc_697_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
lean_object* v___x_695_; 
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 0, v___x_693_);
v___x_695_ = v___x_681_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v___x_693_);
lean_ctor_set(v_reuseFailAlloc_696_, 1, v_a_679_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_511_, 2);
return v___x_677_;
}
}
case 11:
{
lean_object* v_typeName_700_; lean_object* v_idx_701_; lean_object* v_struct_702_; lean_object* v___x_703_; 
v_typeName_700_ = lean_ctor_get(v_e_511_, 0);
v_idx_701_ = lean_ctor_get(v_e_511_, 1);
v_struct_702_ = lean_ctor_get(v_e_511_, 2);
lean_inc_ref(v_struct_702_);
v___x_703_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(v_beginIdx_508_, v_n_509_, v_subst_510_, v_struct_702_, v_offset_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_);
if (lean_obj_tag(v___x_703_) == 0)
{
lean_object* v_a_704_; lean_object* v_a_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_725_; 
v_a_704_ = lean_ctor_get(v___x_703_, 0);
v_a_705_ = lean_ctor_get(v___x_703_, 1);
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_703_);
if (v_isSharedCheck_725_ == 0)
{
v___x_707_ = v___x_703_;
v_isShared_708_ = v_isSharedCheck_725_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_a_705_);
lean_inc(v_a_704_);
lean_dec(v___x_703_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_725_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v_fst_709_; lean_object* v_snd_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_724_; 
v_fst_709_ = lean_ctor_get(v_a_704_, 0);
v_snd_710_ = lean_ctor_get(v_a_704_, 1);
v_isSharedCheck_724_ = !lean_is_exclusive(v_a_704_);
if (v_isSharedCheck_724_ == 0)
{
v___x_712_ = v_a_704_;
v_isShared_713_ = v_isSharedCheck_724_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_snd_710_);
lean_inc(v_fst_709_);
lean_dec(v_a_704_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_724_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
size_t v___x_714_; size_t v___x_715_; uint8_t v___x_716_; 
v___x_714_ = lean_ptr_addr(v_struct_702_);
v___x_715_ = lean_ptr_addr(v_fst_709_);
v___x_716_ = lean_usize_dec_eq(v___x_714_, v___x_715_);
if (v___x_716_ == 0)
{
lean_object* v___x_717_; 
lean_inc(v_idx_701_);
lean_inc(v_typeName_700_);
lean_del_object(v___x_712_);
lean_del_object(v___x_707_);
lean_dec_ref_known(v_e_511_, 3);
v___x_717_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__7(v_typeName_700_, v_idx_701_, v_fst_709_, v_snd_710_, v_a_514_, v_a_515_, v_a_705_);
return v___x_717_;
}
else
{
lean_object* v___x_719_; 
lean_dec(v_fst_709_);
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 0, v_e_511_);
v___x_719_ = v___x_712_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_e_511_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v_snd_710_);
v___x_719_ = v_reuseFailAlloc_723_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
lean_object* v___x_721_; 
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 0, v___x_719_);
v___x_721_ = v___x_707_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_719_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v_a_705_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_511_, 3);
return v___x_703_;
}
}
default: 
{
lean_object* v___x_726_; lean_object* v___x_727_; 
lean_dec(v_offset_512_);
lean_dec_ref(v_e_511_);
v___x_726_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__3);
v___x_727_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8(v___x_726_, v_a_513_, v_a_514_, v_a_515_, v_a_516_);
return v___x_727_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(lean_object* v_beginIdx_728_, lean_object* v_n_729_, lean_object* v_subst_730_, lean_object* v_e_731_, lean_object* v_offset_732_, lean_object* v_a_733_, uint8_t v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_){
_start:
{
lean_object* v_key_737_; lean_object* v___x_738_; 
lean_inc(v_offset_732_);
lean_inc_ref(v_e_731_);
v_key_737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_737_, 0, v_e_731_);
lean_ctor_set(v_key_737_, 1, v_offset_732_);
v___x_738_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3___redArg(v_a_733_, v_key_737_);
if (lean_obj_tag(v___x_738_) == 1)
{
lean_object* v_val_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
lean_dec_ref_known(v_key_737_, 2);
lean_dec(v_offset_732_);
lean_dec_ref(v_e_731_);
v_val_739_ = lean_ctor_get(v___x_738_, 0);
lean_inc(v_val_739_);
lean_dec_ref_known(v___x_738_, 1);
v___x_740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_740_, 0, v_val_739_);
lean_ctor_set(v___x_740_, 1, v_a_733_);
v___x_741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_741_, 0, v___x_740_);
lean_ctor_set(v___x_741_, 1, v_a_736_);
return v___x_741_;
}
else
{
lean_object* v_s_u2081_742_; 
lean_dec(v___x_738_);
v_s_u2081_742_ = lean_nat_add(v_beginIdx_728_, v_offset_732_);
switch(lean_obj_tag(v_e_731_))
{
case 0:
{
lean_object* v_deBruijnIndex_743_; uint8_t v___x_744_; 
v_deBruijnIndex_743_ = lean_ctor_get(v_e_731_, 0);
v___x_744_ = lean_nat_dec_le(v_s_u2081_742_, v_deBruijnIndex_743_);
lean_dec(v_s_u2081_742_);
if (v___x_744_ == 0)
{
lean_object* v___x_745_; 
lean_dec(v_offset_732_);
v___x_745_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_737_, v_e_731_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
return v___x_745_;
}
else
{
lean_object* v___x_746_; uint8_t v___x_747_; 
lean_inc(v_deBruijnIndex_743_);
lean_dec_ref_known(v_e_731_, 1);
v___x_746_ = lean_nat_add(v_offset_732_, v_n_729_);
v___x_747_ = lean_nat_dec_lt(v_deBruijnIndex_743_, v___x_746_);
lean_dec(v___x_746_);
if (v___x_747_ == 0)
{
lean_object* v___x_748_; lean_object* v___x_749_; 
lean_dec(v_offset_732_);
v___x_748_ = lean_nat_sub(v_deBruijnIndex_743_, v_n_729_);
lean_dec(v_deBruijnIndex_743_);
v___x_749_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___redArg(v___x_748_, v_a_736_);
if (lean_obj_tag(v___x_749_) == 0)
{
lean_object* v_a_750_; lean_object* v_a_751_; lean_object* v___x_752_; 
v_a_750_ = lean_ctor_get(v___x_749_, 0);
lean_inc(v_a_750_);
v_a_751_ = lean_ctor_get(v___x_749_, 1);
lean_inc(v_a_751_);
lean_dec_ref_known(v___x_749_, 2);
v___x_752_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_737_, v_a_750_, v_a_733_, v_a_734_, v_a_735_, v_a_751_);
return v___x_752_;
}
else
{
lean_object* v_a_753_; lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_761_; 
lean_dec_ref_known(v_key_737_, 2);
lean_dec_ref(v_a_733_);
v_a_753_ = lean_ctor_get(v___x_749_, 0);
v_a_754_ = lean_ctor_get(v___x_749_, 1);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_761_ == 0)
{
v___x_756_ = v___x_749_;
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_inc(v_a_753_);
lean_dec(v___x_749_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_759_; 
if (v_isShared_757_ == 0)
{
v___x_759_ = v___x_756_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_a_753_);
lean_ctor_set(v_reuseFailAlloc_760_, 1, v_a_754_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
}
else
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v_v_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_762_ = lean_nat_sub(v_deBruijnIndex_743_, v_offset_732_);
lean_dec(v_deBruijnIndex_743_);
v___x_763_ = lean_nat_sub(v_n_729_, v___x_762_);
lean_dec(v___x_762_);
v___x_764_ = lean_unsigned_to_nat(1u);
v___x_765_ = lean_nat_sub(v___x_763_, v___x_764_);
lean_dec(v___x_763_);
v_v_766_ = lean_array_fget_borrowed(v_subst_730_, v___x_765_);
lean_dec(v___x_765_);
v___x_767_ = lean_unsigned_to_nat(0u);
lean_inc(v_v_766_);
v___x_768_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(v_v_766_, v___x_767_, v_offset_732_, v_a_734_, v_a_735_, v_a_736_);
lean_dec(v_offset_732_);
if (lean_obj_tag(v___x_768_) == 0)
{
lean_object* v_a_769_; lean_object* v_a_770_; lean_object* v___x_771_; 
v_a_769_ = lean_ctor_get(v___x_768_, 0);
lean_inc(v_a_769_);
v_a_770_ = lean_ctor_get(v___x_768_, 1);
lean_inc(v_a_770_);
lean_dec_ref_known(v___x_768_, 2);
v___x_771_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_737_, v_a_769_, v_a_733_, v_a_734_, v_a_735_, v_a_770_);
return v___x_771_;
}
else
{
lean_object* v_a_772_; lean_object* v_a_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_780_; 
lean_dec_ref_known(v_key_737_, 2);
lean_dec_ref(v_a_733_);
v_a_772_ = lean_ctor_get(v___x_768_, 0);
v_a_773_ = lean_ctor_get(v___x_768_, 1);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_768_);
if (v_isSharedCheck_780_ == 0)
{
v___x_775_ = v___x_768_;
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_a_773_);
lean_inc(v_a_772_);
lean_dec(v___x_768_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_778_; 
if (v_isShared_776_ == 0)
{
v___x_778_ = v___x_775_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_a_772_);
lean_ctor_set(v_reuseFailAlloc_779_, 1, v_a_773_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
}
}
}
case 9:
{
lean_object* v___x_781_; 
lean_dec(v_s_u2081_742_);
lean_dec(v_offset_732_);
v___x_781_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_737_, v_e_731_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
return v___x_781_;
}
case 2:
{
lean_object* v___x_782_; 
lean_dec(v_s_u2081_742_);
lean_dec(v_offset_732_);
v___x_782_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_737_, v_e_731_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
return v___x_782_;
}
case 1:
{
lean_object* v___x_783_; 
lean_dec(v_s_u2081_742_);
lean_dec(v_offset_732_);
v___x_783_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_737_, v_e_731_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
return v___x_783_;
}
case 4:
{
lean_object* v___x_784_; 
lean_dec(v_s_u2081_742_);
lean_dec(v_offset_732_);
v___x_784_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_737_, v_e_731_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
return v___x_784_;
}
case 3:
{
lean_object* v___x_785_; 
lean_dec(v_s_u2081_742_);
lean_dec(v_offset_732_);
v___x_785_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_737_, v_e_731_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
return v___x_785_;
}
default: 
{
lean_object* v___x_786_; uint8_t v___x_787_; 
v___x_786_ = l_Lean_Expr_looseBVarRange(v_e_731_);
v___x_787_ = lean_nat_dec_le(v___x_786_, v_s_u2081_742_);
lean_dec(v_s_u2081_742_);
lean_dec(v___x_786_);
if (v___x_787_ == 0)
{
switch(lean_obj_tag(v_e_731_))
{
case 9:
{
lean_object* v___x_788_; 
lean_dec(v_offset_732_);
v___x_788_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_737_, v_e_731_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
return v___x_788_;
}
case 2:
{
lean_object* v___x_789_; 
lean_dec(v_offset_732_);
v___x_789_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_737_, v_e_731_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
return v___x_789_;
}
case 0:
{
lean_object* v___x_790_; 
lean_dec(v_offset_732_);
v___x_790_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_737_, v_e_731_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
return v___x_790_;
}
case 1:
{
lean_object* v___x_791_; 
lean_dec(v_offset_732_);
v___x_791_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_737_, v_e_731_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
return v___x_791_;
}
case 4:
{
lean_object* v___x_792_; 
lean_dec(v_offset_732_);
v___x_792_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_737_, v_e_731_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
return v___x_792_;
}
case 3:
{
lean_object* v___x_793_; 
lean_dec(v_offset_732_);
v___x_793_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_737_, v_e_731_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
return v___x_793_;
}
default: 
{
lean_object* v___x_794_; 
v___x_794_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1(v_beginIdx_728_, v_n_729_, v_subst_730_, v_e_731_, v_offset_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
if (lean_obj_tag(v___x_794_) == 0)
{
lean_object* v_a_795_; lean_object* v_a_796_; lean_object* v_fst_797_; lean_object* v_snd_798_; lean_object* v___x_799_; 
v_a_795_ = lean_ctor_get(v___x_794_, 0);
lean_inc(v_a_795_);
v_a_796_ = lean_ctor_get(v___x_794_, 1);
lean_inc(v_a_796_);
lean_dec_ref_known(v___x_794_, 2);
v_fst_797_ = lean_ctor_get(v_a_795_, 0);
lean_inc(v_fst_797_);
v_snd_798_ = lean_ctor_get(v_a_795_, 1);
lean_inc(v_snd_798_);
lean_dec(v_a_795_);
v___x_799_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_737_, v_fst_797_, v_snd_798_, v_a_734_, v_a_735_, v_a_796_);
return v___x_799_;
}
else
{
lean_dec_ref_known(v_key_737_, 2);
return v___x_794_;
}
}
}
}
else
{
lean_object* v___x_800_; 
lean_dec(v_offset_732_);
v___x_800_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_737_, v_e_731_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
return v___x_800_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1___boxed(lean_object* v_beginIdx_801_, lean_object* v_n_802_, lean_object* v_subst_803_, lean_object* v_e_804_, lean_object* v_offset_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_){
_start:
{
uint8_t v_a_boxed_810_; lean_object* v_res_811_; 
v_a_boxed_810_ = lean_unbox(v_a_807_);
v_res_811_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(v_beginIdx_801_, v_n_802_, v_subst_803_, v_e_804_, v_offset_805_, v_a_806_, v_a_boxed_810_, v_a_808_, v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec_ref(v_subst_803_);
lean_dec(v_n_802_);
lean_dec(v_beginIdx_801_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___boxed(lean_object* v_beginIdx_812_, lean_object* v_n_813_, lean_object* v_subst_814_, lean_object* v_e_815_, lean_object* v_offset_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_){
_start:
{
uint8_t v_a_boxed_821_; lean_object* v_res_822_; 
v_a_boxed_821_ = lean_unbox(v_a_818_);
v_res_822_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1(v_beginIdx_812_, v_n_813_, v_subst_814_, v_e_815_, v_offset_816_, v_a_817_, v_a_boxed_821_, v_a_819_, v_a_820_);
lean_dec_ref(v_a_819_);
lean_dec_ref(v_subst_814_);
lean_dec(v_n_813_);
lean_dec(v_beginIdx_812_);
return v_res_822_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__0(void){
_start:
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_823_ = lean_box(0);
v___x_824_ = lean_unsigned_to_nat(16u);
v___x_825_ = lean_mk_array(v___x_824_, v___x_823_);
return v___x_825_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__1(void){
_start:
{
lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_826_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__0, &l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__0_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__0);
v___x_827_ = lean_unsigned_to_nat(0u);
v___x_828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_828_, 0, v___x_827_);
lean_ctor_set(v___x_828_, 1, v___x_826_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevRangeS___lam__0(lean_object* v_e_829_, lean_object* v_beginIdx_830_, lean_object* v_n_831_, lean_object* v_subst_832_, uint8_t v_debug_833_, lean_object* v___y_834_, lean_object* v___y_835_){
_start:
{
lean_object* v___x_836_; 
v___x_836_ = lean_unsigned_to_nat(0u);
switch(lean_obj_tag(v_e_829_))
{
case 0:
{
lean_object* v_deBruijnIndex_837_; uint8_t v___x_838_; 
v_deBruijnIndex_837_ = lean_ctor_get(v_e_829_, 0);
v___x_838_ = lean_nat_dec_le(v_beginIdx_830_, v_deBruijnIndex_837_);
if (v___x_838_ == 0)
{
lean_object* v___x_839_; 
v___x_839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_839_, 0, v_e_829_);
lean_ctor_set(v___x_839_, 1, v___y_835_);
return v___x_839_;
}
else
{
uint8_t v___x_840_; 
lean_inc(v_deBruijnIndex_837_);
lean_dec_ref_known(v_e_829_, 1);
v___x_840_ = lean_nat_dec_lt(v_deBruijnIndex_837_, v_n_831_);
if (v___x_840_ == 0)
{
lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_841_ = lean_nat_sub(v_deBruijnIndex_837_, v_n_831_);
lean_dec(v_deBruijnIndex_837_);
v___x_842_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___redArg(v___x_841_, v___y_835_);
return v___x_842_;
}
else
{
lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v_v_846_; lean_object* v___x_847_; 
v___x_843_ = lean_nat_sub(v_n_831_, v_deBruijnIndex_837_);
lean_dec(v_deBruijnIndex_837_);
v___x_844_ = lean_unsigned_to_nat(1u);
v___x_845_ = lean_nat_sub(v___x_843_, v___x_844_);
lean_dec(v___x_843_);
v_v_846_ = lean_array_fget_borrowed(v_subst_832_, v___x_845_);
lean_dec(v___x_845_);
lean_inc(v_v_846_);
v___x_847_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(v_v_846_, v___x_836_, v___x_836_, v_debug_833_, v___y_834_, v___y_835_);
return v___x_847_;
}
}
}
case 9:
{
lean_object* v___x_848_; 
v___x_848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_848_, 0, v_e_829_);
lean_ctor_set(v___x_848_, 1, v___y_835_);
return v___x_848_;
}
case 2:
{
lean_object* v___x_849_; 
v___x_849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_849_, 0, v_e_829_);
lean_ctor_set(v___x_849_, 1, v___y_835_);
return v___x_849_;
}
case 1:
{
lean_object* v___x_850_; 
v___x_850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_850_, 0, v_e_829_);
lean_ctor_set(v___x_850_, 1, v___y_835_);
return v___x_850_;
}
case 4:
{
lean_object* v___x_851_; 
v___x_851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_851_, 0, v_e_829_);
lean_ctor_set(v___x_851_, 1, v___y_835_);
return v___x_851_;
}
case 3:
{
lean_object* v___x_852_; 
v___x_852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_852_, 0, v_e_829_);
lean_ctor_set(v___x_852_, 1, v___y_835_);
return v___x_852_;
}
default: 
{
lean_object* v___x_853_; uint8_t v___x_854_; 
v___x_853_ = l_Lean_Expr_looseBVarRange(v_e_829_);
v___x_854_ = lean_nat_dec_le(v___x_853_, v_beginIdx_830_);
lean_dec(v___x_853_);
if (v___x_854_ == 0)
{
switch(lean_obj_tag(v_e_829_))
{
case 9:
{
lean_object* v___x_855_; 
v___x_855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_855_, 0, v_e_829_);
lean_ctor_set(v___x_855_, 1, v___y_835_);
return v___x_855_;
}
case 2:
{
lean_object* v___x_856_; 
v___x_856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_856_, 0, v_e_829_);
lean_ctor_set(v___x_856_, 1, v___y_835_);
return v___x_856_;
}
case 0:
{
lean_object* v___x_857_; 
v___x_857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_857_, 0, v_e_829_);
lean_ctor_set(v___x_857_, 1, v___y_835_);
return v___x_857_;
}
case 1:
{
lean_object* v___x_858_; 
v___x_858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_858_, 0, v_e_829_);
lean_ctor_set(v___x_858_, 1, v___y_835_);
return v___x_858_;
}
case 4:
{
lean_object* v___x_859_; 
v___x_859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_859_, 0, v_e_829_);
lean_ctor_set(v___x_859_, 1, v___y_835_);
return v___x_859_;
}
case 3:
{
lean_object* v___x_860_; 
v___x_860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_860_, 0, v_e_829_);
lean_ctor_set(v___x_860_, 1, v___y_835_);
return v___x_860_;
}
default: 
{
lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_861_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__1, &l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__1_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__1);
v___x_862_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1(v_beginIdx_830_, v_n_831_, v_subst_832_, v_e_829_, v___x_836_, v___x_861_, v_debug_833_, v___y_834_, v___y_835_);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_object* v_a_863_; lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_872_; 
v_a_863_ = lean_ctor_get(v___x_862_, 0);
v_a_864_ = lean_ctor_get(v___x_862_, 1);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_872_ == 0)
{
v___x_866_ = v___x_862_;
v_isShared_867_ = v_isSharedCheck_872_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_inc(v_a_863_);
lean_dec(v___x_862_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_872_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v_fst_868_; lean_object* v___x_870_; 
v_fst_868_ = lean_ctor_get(v_a_863_, 0);
lean_inc(v_fst_868_);
lean_dec(v_a_863_);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 0, v_fst_868_);
v___x_870_ = v___x_866_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v_fst_868_);
lean_ctor_set(v_reuseFailAlloc_871_, 1, v_a_864_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
else
{
lean_object* v_a_873_; lean_object* v_a_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_881_; 
v_a_873_ = lean_ctor_get(v___x_862_, 0);
v_a_874_ = lean_ctor_get(v___x_862_, 1);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_881_ == 0)
{
v___x_876_ = v___x_862_;
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_a_874_);
lean_inc(v_a_873_);
lean_dec(v___x_862_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___x_879_; 
if (v_isShared_877_ == 0)
{
v___x_879_ = v___x_876_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_a_873_);
lean_ctor_set(v_reuseFailAlloc_880_, 1, v_a_874_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
}
}
}
else
{
lean_object* v___x_882_; 
v___x_882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_882_, 0, v_e_829_);
lean_ctor_set(v___x_882_, 1, v___y_835_);
return v___x_882_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___boxed(lean_object* v_e_883_, lean_object* v_beginIdx_884_, lean_object* v_n_885_, lean_object* v_subst_886_, lean_object* v_debug_887_, lean_object* v___y_888_, lean_object* v___y_889_){
_start:
{
uint8_t v_debug_boxed_890_; lean_object* v_res_891_; 
v_debug_boxed_890_ = lean_unbox(v_debug_887_);
v_res_891_ = l_Lean_Meta_Sym_instantiateRevRangeS___lam__0(v_e_883_, v_beginIdx_884_, v_n_885_, v_subst_886_, v_debug_boxed_890_, v___y_888_, v___y_889_);
lean_dec_ref(v___y_888_);
lean_dec_ref(v_subst_886_);
lean_dec(v_n_885_);
lean_dec(v_beginIdx_884_);
return v_res_891_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__2(void){
_start:
{
lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_894_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__2));
v___x_895_ = lean_unsigned_to_nat(16u);
v___x_896_ = lean_unsigned_to_nat(62u);
v___x_897_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__1));
v___x_898_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__0));
v___x_899_ = l_mkPanicMessageWithDecl(v___x_898_, v___x_897_, v___x_896_, v___x_895_, v___x_894_);
return v___x_899_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__5(void){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_902_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__2));
v___x_903_ = lean_unsigned_to_nat(34u);
v___x_904_ = lean_unsigned_to_nat(20u);
v___x_905_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__4));
v___x_906_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__3));
v___x_907_ = l_mkPanicMessageWithDecl(v___x_906_, v___x_905_, v___x_904_, v___x_903_, v___x_902_);
return v___x_907_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__6(void){
_start:
{
lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_908_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__2));
v___x_909_ = lean_unsigned_to_nat(32u);
v___x_910_ = lean_unsigned_to_nat(19u);
v___x_911_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__4));
v___x_912_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__3));
v___x_913_ = l_mkPanicMessageWithDecl(v___x_912_, v___x_911_, v___x_910_, v___x_909_, v___x_908_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevRangeS(lean_object* v_e_914_, lean_object* v_beginIdx_915_, lean_object* v_endIdx_916_, lean_object* v_subst_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_){
_start:
{
uint8_t v___x_925_; 
v___x_925_ = lean_nat_dec_lt(v_endIdx_916_, v_beginIdx_915_);
if (v___x_925_ == 0)
{
lean_object* v___x_926_; uint8_t v___x_927_; 
v___x_926_ = lean_array_get_size(v_subst_917_);
v___x_927_ = lean_nat_dec_lt(v___x_926_, v_endIdx_916_);
if (v___x_927_ == 0)
{
lean_object* v___x_928_; lean_object* v___x_929_; uint8_t v_debug_930_; lean_object* v_env_931_; lean_object* v_n_932_; lean_object* v___x_933_; lean_object* v___f_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_928_ = lean_st_ref_get(v_a_919_);
v___x_929_ = lean_st_ref_get(v_a_923_);
v_debug_930_ = lean_ctor_get_uint8(v___x_928_, sizeof(void*)*11);
lean_dec(v___x_928_);
v_env_931_ = lean_ctor_get(v___x_929_, 0);
lean_inc_ref(v_env_931_);
lean_dec(v___x_929_);
v_n_932_ = lean_nat_sub(v_endIdx_916_, v_beginIdx_915_);
v___x_933_ = lean_box(v_debug_930_);
v___f_934_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___boxed), 7, 5);
lean_closure_set(v___f_934_, 0, v_e_914_);
lean_closure_set(v___f_934_, 1, v_beginIdx_915_);
lean_closure_set(v___f_934_, 2, v_n_932_);
lean_closure_set(v___f_934_, 3, v_subst_917_);
lean_closure_set(v___f_934_, 4, v___x_933_);
v___x_935_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_935_, 0, v_env_931_);
lean_ctor_set_uint8(v___x_935_, sizeof(void*)*1, v___x_927_);
lean_ctor_set_uint8(v___x_935_, sizeof(void*)*1 + 1, v___x_927_);
v___x_936_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_934_, v___x_935_, v_a_919_);
if (lean_obj_tag(v___x_936_) == 0)
{
lean_object* v_a_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_947_; 
v_a_937_ = lean_ctor_get(v___x_936_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_947_ == 0)
{
v___x_939_ = v___x_936_;
v_isShared_940_ = v_isSharedCheck_947_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_a_937_);
lean_dec(v___x_936_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_947_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
if (lean_obj_tag(v_a_937_) == 0)
{
lean_object* v___x_941_; lean_object* v___x_942_; 
lean_dec_ref_known(v_a_937_, 1);
lean_del_object(v___x_939_);
v___x_941_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__2, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__2_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__2);
v___x_942_ = l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(v___x_941_, v_a_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_);
return v___x_942_;
}
else
{
lean_object* v_a_943_; lean_object* v___x_945_; 
v_a_943_ = lean_ctor_get(v_a_937_, 0);
lean_inc(v_a_943_);
lean_dec_ref_known(v_a_937_, 1);
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 0, v_a_943_);
v___x_945_ = v___x_939_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_a_943_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
else
{
lean_object* v_a_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_955_; 
v_a_948_ = lean_ctor_get(v___x_936_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_955_ == 0)
{
v___x_950_ = v___x_936_;
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_a_948_);
lean_dec(v___x_936_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_953_; 
if (v_isShared_951_ == 0)
{
v___x_953_ = v___x_950_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_a_948_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
}
else
{
lean_object* v___x_956_; lean_object* v___x_957_; 
lean_dec_ref(v_subst_917_);
lean_dec(v_beginIdx_915_);
lean_dec_ref(v_e_914_);
v___x_956_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__5, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__5_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__5);
v___x_957_ = l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(v___x_956_, v_a_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_);
return v___x_957_;
}
}
else
{
lean_object* v___x_958_; lean_object* v___x_959_; 
lean_dec_ref(v_subst_917_);
lean_dec(v_beginIdx_915_);
lean_dec_ref(v_e_914_);
v___x_958_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__6, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__6_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__6);
v___x_959_ = l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(v___x_958_, v_a_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_);
return v___x_959_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevRangeS___boxed(lean_object* v_e_960_, lean_object* v_beginIdx_961_, lean_object* v_endIdx_962_, lean_object* v_subst_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_e_960_, v_beginIdx_961_, v_endIdx_962_, v_subst_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_);
lean_dec(v_a_969_);
lean_dec_ref(v_a_968_);
lean_dec(v_a_967_);
lean_dec_ref(v_a_966_);
lean_dec(v_a_965_);
lean_dec_ref(v_a_964_);
lean_dec(v_endIdx_962_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_972_, lean_object* v_m_973_, lean_object* v_a_974_){
_start:
{
lean_object* v___x_975_; 
v___x_975_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3___redArg(v_m_973_, v_a_974_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_976_, lean_object* v_m_977_, lean_object* v_a_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3(v_00_u03b2_976_, v_m_977_, v_a_978_);
lean_dec_ref(v_a_978_);
lean_dec_ref(v_m_977_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11(lean_object* v_00_u03b2_980_, lean_object* v_a_981_, lean_object* v_x_982_){
_start:
{
lean_object* v___x_983_; 
v___x_983_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11___redArg(v_a_981_, v_x_982_);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11___boxed(lean_object* v_00_u03b2_984_, lean_object* v_a_985_, lean_object* v_x_986_){
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11(v_00_u03b2_984_, v_a_985_, v_x_986_);
lean_dec(v_x_986_);
lean_dec_ref(v_a_985_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevS(lean_object* v_e_988_, lean_object* v_subst_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_){
_start:
{
lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_997_ = lean_unsigned_to_nat(0u);
v___x_998_ = lean_array_get_size(v_subst_989_);
v___x_999_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_e_988_, v___x_997_, v___x_998_, v_subst_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_);
return v___x_999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevS___boxed(lean_object* v_e_1000_, lean_object* v_subst_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l_Lean_Meta_Sym_instantiateRevS(v_e_1000_, v_subst_1001_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_);
lean_dec(v_a_1007_);
lean_dec_ref(v_a_1006_);
lean_dec(v_a_1005_);
lean_dec_ref(v_a_1004_);
lean_dec(v_a_1003_);
lean_dec_ref(v_a_1002_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1(lean_object* v_msg_1012_, uint8_t v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_){
_start:
{
lean_object* v___f_1016_; lean_object* v___f_1017_; lean_object* v___x_1018_; lean_object* v___f_1019_; lean_object* v___f_1020_; lean_object* v___f_1021_; lean_object* v___x_2857__overap_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___f_1016_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1___closed__0));
v___f_1017_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1___closed__1));
v___x_1018_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___f_1016_, v___f_1017_);
v___f_1019_ = lean_alloc_closure((void*)(l_EStateM_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1019_, 0, v___x_1018_);
v___f_1020_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1020_, 0, v___f_1019_);
v___f_1021_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1021_, 0, v___f_1020_);
v___x_2857__overap_1022_ = lean_panic_fn_borrowed(v___f_1021_, v_msg_1012_);
lean_dec_ref(v___f_1021_);
v___x_1023_ = lean_box(v___y_1013_);
lean_inc_ref(v___y_1014_);
v___x_1024_ = lean_apply_3(v___x_2857__overap_1022_, v___x_1023_, v___y_1014_, v___y_1015_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1___boxed(lean_object* v_msg_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
uint8_t v___y_3379__boxed_1029_; lean_object* v_res_1030_; 
v___y_3379__boxed_1029_ = lean_unbox(v___y_1026_);
v_res_1030_ = l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1(v_msg_1025_, v___y_3379__boxed_1029_, v___y_1027_, v___y_1028_);
lean_dec_ref(v___y_1027_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0(lean_object* v_n_1031_, lean_object* v_beginIdx_1032_, lean_object* v_subst_1033_, lean_object* v_e_1034_, lean_object* v_offset_1035_, lean_object* v_a_1036_, uint8_t v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_){
_start:
{
switch(lean_obj_tag(v_e_1034_))
{
case 5:
{
lean_object* v_fn_1040_; lean_object* v_arg_1041_; lean_object* v___x_1042_; 
v_fn_1040_ = lean_ctor_get(v_e_1034_, 0);
v_arg_1041_ = lean_ctor_get(v_e_1034_, 1);
lean_inc(v_offset_1035_);
lean_inc_ref(v_fn_1040_);
v___x_1042_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1031_, v_beginIdx_1032_, v_subst_1033_, v_fn_1040_, v_offset_1035_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_);
if (lean_obj_tag(v___x_1042_) == 0)
{
lean_object* v_a_1043_; lean_object* v_a_1044_; lean_object* v_fst_1045_; lean_object* v_snd_1046_; lean_object* v___x_1047_; 
v_a_1043_ = lean_ctor_get(v___x_1042_, 0);
lean_inc(v_a_1043_);
v_a_1044_ = lean_ctor_get(v___x_1042_, 1);
lean_inc(v_a_1044_);
lean_dec_ref_known(v___x_1042_, 2);
v_fst_1045_ = lean_ctor_get(v_a_1043_, 0);
lean_inc(v_fst_1045_);
v_snd_1046_ = lean_ctor_get(v_a_1043_, 1);
lean_inc(v_snd_1046_);
lean_dec(v_a_1043_);
lean_inc_ref(v_arg_1041_);
v___x_1047_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1031_, v_beginIdx_1032_, v_subst_1033_, v_arg_1041_, v_offset_1035_, v_snd_1046_, v_a_1037_, v_a_1038_, v_a_1044_);
if (lean_obj_tag(v___x_1047_) == 0)
{
lean_object* v_a_1048_; lean_object* v_a_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1073_; 
v_a_1048_ = lean_ctor_get(v___x_1047_, 0);
v_a_1049_ = lean_ctor_get(v___x_1047_, 1);
v_isSharedCheck_1073_ = !lean_is_exclusive(v___x_1047_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1051_ = v___x_1047_;
v_isShared_1052_ = v_isSharedCheck_1073_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_a_1049_);
lean_inc(v_a_1048_);
lean_dec(v___x_1047_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1073_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v_fst_1053_; lean_object* v_snd_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1072_; 
v_fst_1053_ = lean_ctor_get(v_a_1048_, 0);
v_snd_1054_ = lean_ctor_get(v_a_1048_, 1);
v_isSharedCheck_1072_ = !lean_is_exclusive(v_a_1048_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1056_ = v_a_1048_;
v_isShared_1057_ = v_isSharedCheck_1072_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_snd_1054_);
lean_inc(v_fst_1053_);
lean_dec(v_a_1048_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1072_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
size_t v___x_1058_; size_t v___x_1059_; uint8_t v___x_1060_; 
v___x_1058_ = lean_ptr_addr(v_fn_1040_);
v___x_1059_ = lean_ptr_addr(v_fst_1045_);
v___x_1060_ = lean_usize_dec_eq(v___x_1058_, v___x_1059_);
if (v___x_1060_ == 0)
{
lean_object* v___x_1061_; 
lean_del_object(v___x_1056_);
lean_del_object(v___x_1051_);
lean_dec_ref_known(v_e_1034_, 2);
v___x_1061_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__2(v_fst_1045_, v_fst_1053_, v_snd_1054_, v_a_1037_, v_a_1038_, v_a_1049_);
return v___x_1061_;
}
else
{
size_t v___x_1062_; size_t v___x_1063_; uint8_t v___x_1064_; 
v___x_1062_ = lean_ptr_addr(v_arg_1041_);
v___x_1063_ = lean_ptr_addr(v_fst_1053_);
v___x_1064_ = lean_usize_dec_eq(v___x_1062_, v___x_1063_);
if (v___x_1064_ == 0)
{
lean_object* v___x_1065_; 
lean_del_object(v___x_1056_);
lean_del_object(v___x_1051_);
lean_dec_ref_known(v_e_1034_, 2);
v___x_1065_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__2(v_fst_1045_, v_fst_1053_, v_snd_1054_, v_a_1037_, v_a_1038_, v_a_1049_);
return v___x_1065_;
}
else
{
lean_object* v___x_1067_; 
lean_dec(v_fst_1053_);
lean_dec(v_fst_1045_);
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 0, v_e_1034_);
v___x_1067_ = v___x_1056_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v_e_1034_);
lean_ctor_set(v_reuseFailAlloc_1071_, 1, v_snd_1054_);
v___x_1067_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
lean_object* v___x_1069_; 
if (v_isShared_1052_ == 0)
{
lean_ctor_set(v___x_1051_, 0, v___x_1067_);
v___x_1069_ = v___x_1051_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1067_);
lean_ctor_set(v_reuseFailAlloc_1070_, 1, v_a_1049_);
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
lean_dec(v_fst_1045_);
lean_dec_ref_known(v_e_1034_, 2);
return v___x_1047_;
}
}
else
{
lean_dec_ref_known(v_e_1034_, 2);
lean_dec(v_offset_1035_);
return v___x_1042_;
}
}
case 6:
{
lean_object* v_binderName_1074_; lean_object* v_binderType_1075_; lean_object* v_body_1076_; uint8_t v_binderInfo_1077_; lean_object* v___x_1078_; 
v_binderName_1074_ = lean_ctor_get(v_e_1034_, 0);
v_binderType_1075_ = lean_ctor_get(v_e_1034_, 1);
v_body_1076_ = lean_ctor_get(v_e_1034_, 2);
v_binderInfo_1077_ = lean_ctor_get_uint8(v_e_1034_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1035_);
lean_inc_ref(v_binderType_1075_);
v___x_1078_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1031_, v_beginIdx_1032_, v_subst_1033_, v_binderType_1075_, v_offset_1035_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_);
if (lean_obj_tag(v___x_1078_) == 0)
{
lean_object* v_a_1079_; lean_object* v_a_1080_; lean_object* v_fst_1081_; lean_object* v_snd_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; 
v_a_1079_ = lean_ctor_get(v___x_1078_, 0);
lean_inc(v_a_1079_);
v_a_1080_ = lean_ctor_get(v___x_1078_, 1);
lean_inc(v_a_1080_);
lean_dec_ref_known(v___x_1078_, 2);
v_fst_1081_ = lean_ctor_get(v_a_1079_, 0);
lean_inc(v_fst_1081_);
v_snd_1082_ = lean_ctor_get(v_a_1079_, 1);
lean_inc(v_snd_1082_);
lean_dec(v_a_1079_);
v___x_1083_ = lean_unsigned_to_nat(1u);
v___x_1084_ = lean_nat_add(v_offset_1035_, v___x_1083_);
lean_dec(v_offset_1035_);
lean_inc_ref(v_body_1076_);
v___x_1085_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1031_, v_beginIdx_1032_, v_subst_1033_, v_body_1076_, v___x_1084_, v_snd_1082_, v_a_1037_, v_a_1038_, v_a_1080_);
if (lean_obj_tag(v___x_1085_) == 0)
{
lean_object* v_a_1086_; lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1111_; 
v_a_1086_ = lean_ctor_get(v___x_1085_, 0);
v_a_1087_ = lean_ctor_get(v___x_1085_, 1);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1089_ = v___x_1085_;
v_isShared_1090_ = v_isSharedCheck_1111_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_inc(v_a_1086_);
lean_dec(v___x_1085_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1111_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v_fst_1091_; lean_object* v_snd_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1110_; 
v_fst_1091_ = lean_ctor_get(v_a_1086_, 0);
v_snd_1092_ = lean_ctor_get(v_a_1086_, 1);
v_isSharedCheck_1110_ = !lean_is_exclusive(v_a_1086_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1094_ = v_a_1086_;
v_isShared_1095_ = v_isSharedCheck_1110_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_snd_1092_);
lean_inc(v_fst_1091_);
lean_dec(v_a_1086_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1110_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
size_t v___x_1096_; size_t v___x_1097_; uint8_t v___x_1098_; 
v___x_1096_ = lean_ptr_addr(v_binderType_1075_);
v___x_1097_ = lean_ptr_addr(v_fst_1081_);
v___x_1098_ = lean_usize_dec_eq(v___x_1096_, v___x_1097_);
if (v___x_1098_ == 0)
{
lean_object* v___x_1099_; 
lean_inc(v_binderName_1074_);
lean_del_object(v___x_1094_);
lean_del_object(v___x_1089_);
lean_dec_ref_known(v_e_1034_, 3);
v___x_1099_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__3(v_binderName_1074_, v_binderInfo_1077_, v_fst_1081_, v_fst_1091_, v_snd_1092_, v_a_1037_, v_a_1038_, v_a_1087_);
return v___x_1099_;
}
else
{
size_t v___x_1100_; size_t v___x_1101_; uint8_t v___x_1102_; 
v___x_1100_ = lean_ptr_addr(v_body_1076_);
v___x_1101_ = lean_ptr_addr(v_fst_1091_);
v___x_1102_ = lean_usize_dec_eq(v___x_1100_, v___x_1101_);
if (v___x_1102_ == 0)
{
lean_object* v___x_1103_; 
lean_inc(v_binderName_1074_);
lean_del_object(v___x_1094_);
lean_del_object(v___x_1089_);
lean_dec_ref_known(v_e_1034_, 3);
v___x_1103_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__3(v_binderName_1074_, v_binderInfo_1077_, v_fst_1081_, v_fst_1091_, v_snd_1092_, v_a_1037_, v_a_1038_, v_a_1087_);
return v___x_1103_;
}
else
{
lean_object* v___x_1105_; 
lean_dec(v_fst_1091_);
lean_dec(v_fst_1081_);
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 0, v_e_1034_);
v___x_1105_ = v___x_1094_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_e_1034_);
lean_ctor_set(v_reuseFailAlloc_1109_, 1, v_snd_1092_);
v___x_1105_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
lean_object* v___x_1107_; 
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 0, v___x_1105_);
v___x_1107_ = v___x_1089_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v___x_1105_);
lean_ctor_set(v_reuseFailAlloc_1108_, 1, v_a_1087_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
return v___x_1107_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1081_);
lean_dec_ref_known(v_e_1034_, 3);
return v___x_1085_;
}
}
else
{
lean_dec_ref_known(v_e_1034_, 3);
lean_dec(v_offset_1035_);
return v___x_1078_;
}
}
case 7:
{
lean_object* v_binderName_1112_; lean_object* v_binderType_1113_; lean_object* v_body_1114_; uint8_t v_binderInfo_1115_; lean_object* v___x_1116_; 
v_binderName_1112_ = lean_ctor_get(v_e_1034_, 0);
v_binderType_1113_ = lean_ctor_get(v_e_1034_, 1);
v_body_1114_ = lean_ctor_get(v_e_1034_, 2);
v_binderInfo_1115_ = lean_ctor_get_uint8(v_e_1034_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1035_);
lean_inc_ref(v_binderType_1113_);
v___x_1116_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1031_, v_beginIdx_1032_, v_subst_1033_, v_binderType_1113_, v_offset_1035_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_);
if (lean_obj_tag(v___x_1116_) == 0)
{
lean_object* v_a_1117_; lean_object* v_a_1118_; lean_object* v_fst_1119_; lean_object* v_snd_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
v_a_1117_ = lean_ctor_get(v___x_1116_, 0);
lean_inc(v_a_1117_);
v_a_1118_ = lean_ctor_get(v___x_1116_, 1);
lean_inc(v_a_1118_);
lean_dec_ref_known(v___x_1116_, 2);
v_fst_1119_ = lean_ctor_get(v_a_1117_, 0);
lean_inc(v_fst_1119_);
v_snd_1120_ = lean_ctor_get(v_a_1117_, 1);
lean_inc(v_snd_1120_);
lean_dec(v_a_1117_);
v___x_1121_ = lean_unsigned_to_nat(1u);
v___x_1122_ = lean_nat_add(v_offset_1035_, v___x_1121_);
lean_dec(v_offset_1035_);
lean_inc_ref(v_body_1114_);
v___x_1123_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1031_, v_beginIdx_1032_, v_subst_1033_, v_body_1114_, v___x_1122_, v_snd_1120_, v_a_1037_, v_a_1038_, v_a_1118_);
if (lean_obj_tag(v___x_1123_) == 0)
{
lean_object* v_a_1124_; lean_object* v_a_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1149_; 
v_a_1124_ = lean_ctor_get(v___x_1123_, 0);
v_a_1125_ = lean_ctor_get(v___x_1123_, 1);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1123_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1127_ = v___x_1123_;
v_isShared_1128_ = v_isSharedCheck_1149_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_a_1125_);
lean_inc(v_a_1124_);
lean_dec(v___x_1123_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1149_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v_fst_1129_; lean_object* v_snd_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1148_; 
v_fst_1129_ = lean_ctor_get(v_a_1124_, 0);
v_snd_1130_ = lean_ctor_get(v_a_1124_, 1);
v_isSharedCheck_1148_ = !lean_is_exclusive(v_a_1124_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1132_ = v_a_1124_;
v_isShared_1133_ = v_isSharedCheck_1148_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_snd_1130_);
lean_inc(v_fst_1129_);
lean_dec(v_a_1124_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1148_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
size_t v___x_1134_; size_t v___x_1135_; uint8_t v___x_1136_; 
v___x_1134_ = lean_ptr_addr(v_binderType_1113_);
v___x_1135_ = lean_ptr_addr(v_fst_1119_);
v___x_1136_ = lean_usize_dec_eq(v___x_1134_, v___x_1135_);
if (v___x_1136_ == 0)
{
lean_object* v___x_1137_; 
lean_inc(v_binderName_1112_);
lean_del_object(v___x_1132_);
lean_del_object(v___x_1127_);
lean_dec_ref_known(v_e_1034_, 3);
v___x_1137_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__4(v_binderName_1112_, v_binderInfo_1115_, v_fst_1119_, v_fst_1129_, v_snd_1130_, v_a_1037_, v_a_1038_, v_a_1125_);
return v___x_1137_;
}
else
{
size_t v___x_1138_; size_t v___x_1139_; uint8_t v___x_1140_; 
v___x_1138_ = lean_ptr_addr(v_body_1114_);
v___x_1139_ = lean_ptr_addr(v_fst_1129_);
v___x_1140_ = lean_usize_dec_eq(v___x_1138_, v___x_1139_);
if (v___x_1140_ == 0)
{
lean_object* v___x_1141_; 
lean_inc(v_binderName_1112_);
lean_del_object(v___x_1132_);
lean_del_object(v___x_1127_);
lean_dec_ref_known(v_e_1034_, 3);
v___x_1141_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__4(v_binderName_1112_, v_binderInfo_1115_, v_fst_1119_, v_fst_1129_, v_snd_1130_, v_a_1037_, v_a_1038_, v_a_1125_);
return v___x_1141_;
}
else
{
lean_object* v___x_1143_; 
lean_dec(v_fst_1129_);
lean_dec(v_fst_1119_);
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 0, v_e_1034_);
v___x_1143_ = v___x_1132_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_e_1034_);
lean_ctor_set(v_reuseFailAlloc_1147_, 1, v_snd_1130_);
v___x_1143_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
lean_object* v___x_1145_; 
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 0, v___x_1143_);
v___x_1145_ = v___x_1127_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v___x_1143_);
lean_ctor_set(v_reuseFailAlloc_1146_, 1, v_a_1125_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1119_);
lean_dec_ref_known(v_e_1034_, 3);
return v___x_1123_;
}
}
else
{
lean_dec_ref_known(v_e_1034_, 3);
lean_dec(v_offset_1035_);
return v___x_1116_;
}
}
case 8:
{
lean_object* v_declName_1150_; lean_object* v_type_1151_; lean_object* v_value_1152_; lean_object* v_body_1153_; uint8_t v_nondep_1154_; lean_object* v___x_1155_; 
v_declName_1150_ = lean_ctor_get(v_e_1034_, 0);
v_type_1151_ = lean_ctor_get(v_e_1034_, 1);
v_value_1152_ = lean_ctor_get(v_e_1034_, 2);
v_body_1153_ = lean_ctor_get(v_e_1034_, 3);
v_nondep_1154_ = lean_ctor_get_uint8(v_e_1034_, sizeof(void*)*4 + 8);
lean_inc(v_offset_1035_);
lean_inc_ref(v_type_1151_);
v___x_1155_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1031_, v_beginIdx_1032_, v_subst_1033_, v_type_1151_, v_offset_1035_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_);
if (lean_obj_tag(v___x_1155_) == 0)
{
lean_object* v_a_1156_; lean_object* v_a_1157_; lean_object* v_fst_1158_; lean_object* v_snd_1159_; lean_object* v___x_1160_; 
v_a_1156_ = lean_ctor_get(v___x_1155_, 0);
lean_inc(v_a_1156_);
v_a_1157_ = lean_ctor_get(v___x_1155_, 1);
lean_inc(v_a_1157_);
lean_dec_ref_known(v___x_1155_, 2);
v_fst_1158_ = lean_ctor_get(v_a_1156_, 0);
lean_inc(v_fst_1158_);
v_snd_1159_ = lean_ctor_get(v_a_1156_, 1);
lean_inc(v_snd_1159_);
lean_dec(v_a_1156_);
lean_inc(v_offset_1035_);
lean_inc_ref(v_value_1152_);
v___x_1160_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1031_, v_beginIdx_1032_, v_subst_1033_, v_value_1152_, v_offset_1035_, v_snd_1159_, v_a_1037_, v_a_1038_, v_a_1157_);
if (lean_obj_tag(v___x_1160_) == 0)
{
lean_object* v_a_1161_; lean_object* v_a_1162_; lean_object* v_fst_1163_; lean_object* v_snd_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; 
v_a_1161_ = lean_ctor_get(v___x_1160_, 0);
lean_inc(v_a_1161_);
v_a_1162_ = lean_ctor_get(v___x_1160_, 1);
lean_inc(v_a_1162_);
lean_dec_ref_known(v___x_1160_, 2);
v_fst_1163_ = lean_ctor_get(v_a_1161_, 0);
lean_inc(v_fst_1163_);
v_snd_1164_ = lean_ctor_get(v_a_1161_, 1);
lean_inc(v_snd_1164_);
lean_dec(v_a_1161_);
v___x_1165_ = lean_unsigned_to_nat(1u);
v___x_1166_ = lean_nat_add(v_offset_1035_, v___x_1165_);
lean_dec(v_offset_1035_);
lean_inc_ref(v_body_1153_);
v___x_1167_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1031_, v_beginIdx_1032_, v_subst_1033_, v_body_1153_, v___x_1166_, v_snd_1164_, v_a_1037_, v_a_1038_, v_a_1162_);
if (lean_obj_tag(v___x_1167_) == 0)
{
lean_object* v_a_1168_; lean_object* v_a_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1197_; 
v_a_1168_ = lean_ctor_get(v___x_1167_, 0);
v_a_1169_ = lean_ctor_get(v___x_1167_, 1);
v_isSharedCheck_1197_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1171_ = v___x_1167_;
v_isShared_1172_ = v_isSharedCheck_1197_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_a_1169_);
lean_inc(v_a_1168_);
lean_dec(v___x_1167_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1197_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v_fst_1173_; lean_object* v_snd_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1196_; 
v_fst_1173_ = lean_ctor_get(v_a_1168_, 0);
v_snd_1174_ = lean_ctor_get(v_a_1168_, 1);
v_isSharedCheck_1196_ = !lean_is_exclusive(v_a_1168_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1176_ = v_a_1168_;
v_isShared_1177_ = v_isSharedCheck_1196_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_snd_1174_);
lean_inc(v_fst_1173_);
lean_dec(v_a_1168_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1196_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
size_t v___x_1178_; size_t v___x_1179_; uint8_t v___x_1180_; 
v___x_1178_ = lean_ptr_addr(v_type_1151_);
v___x_1179_ = lean_ptr_addr(v_fst_1158_);
v___x_1180_ = lean_usize_dec_eq(v___x_1178_, v___x_1179_);
if (v___x_1180_ == 0)
{
lean_object* v___x_1181_; 
lean_inc(v_declName_1150_);
lean_del_object(v___x_1176_);
lean_del_object(v___x_1171_);
lean_dec_ref_known(v_e_1034_, 4);
v___x_1181_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__5(v_declName_1150_, v_fst_1158_, v_fst_1163_, v_fst_1173_, v_nondep_1154_, v_snd_1174_, v_a_1037_, v_a_1038_, v_a_1169_);
return v___x_1181_;
}
else
{
size_t v___x_1182_; size_t v___x_1183_; uint8_t v___x_1184_; 
v___x_1182_ = lean_ptr_addr(v_value_1152_);
v___x_1183_ = lean_ptr_addr(v_fst_1163_);
v___x_1184_ = lean_usize_dec_eq(v___x_1182_, v___x_1183_);
if (v___x_1184_ == 0)
{
lean_object* v___x_1185_; 
lean_inc(v_declName_1150_);
lean_del_object(v___x_1176_);
lean_del_object(v___x_1171_);
lean_dec_ref_known(v_e_1034_, 4);
v___x_1185_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__5(v_declName_1150_, v_fst_1158_, v_fst_1163_, v_fst_1173_, v_nondep_1154_, v_snd_1174_, v_a_1037_, v_a_1038_, v_a_1169_);
return v___x_1185_;
}
else
{
size_t v___x_1186_; size_t v___x_1187_; uint8_t v___x_1188_; 
v___x_1186_ = lean_ptr_addr(v_body_1153_);
v___x_1187_ = lean_ptr_addr(v_fst_1173_);
v___x_1188_ = lean_usize_dec_eq(v___x_1186_, v___x_1187_);
if (v___x_1188_ == 0)
{
lean_object* v___x_1189_; 
lean_inc(v_declName_1150_);
lean_del_object(v___x_1176_);
lean_del_object(v___x_1171_);
lean_dec_ref_known(v_e_1034_, 4);
v___x_1189_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__5(v_declName_1150_, v_fst_1158_, v_fst_1163_, v_fst_1173_, v_nondep_1154_, v_snd_1174_, v_a_1037_, v_a_1038_, v_a_1169_);
return v___x_1189_;
}
else
{
lean_object* v___x_1191_; 
lean_dec(v_fst_1173_);
lean_dec(v_fst_1163_);
lean_dec(v_fst_1158_);
if (v_isShared_1177_ == 0)
{
lean_ctor_set(v___x_1176_, 0, v_e_1034_);
v___x_1191_ = v___x_1176_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_e_1034_);
lean_ctor_set(v_reuseFailAlloc_1195_, 1, v_snd_1174_);
v___x_1191_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
lean_object* v___x_1193_; 
if (v_isShared_1172_ == 0)
{
lean_ctor_set(v___x_1171_, 0, v___x_1191_);
v___x_1193_ = v___x_1171_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v___x_1191_);
lean_ctor_set(v_reuseFailAlloc_1194_, 1, v_a_1169_);
v___x_1193_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
return v___x_1193_;
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
lean_dec(v_fst_1163_);
lean_dec(v_fst_1158_);
lean_dec_ref_known(v_e_1034_, 4);
return v___x_1167_;
}
}
else
{
lean_dec(v_fst_1158_);
lean_dec_ref_known(v_e_1034_, 4);
lean_dec(v_offset_1035_);
return v___x_1160_;
}
}
else
{
lean_dec_ref_known(v_e_1034_, 4);
lean_dec(v_offset_1035_);
return v___x_1155_;
}
}
case 10:
{
lean_object* v_data_1198_; lean_object* v_expr_1199_; lean_object* v___x_1200_; 
v_data_1198_ = lean_ctor_get(v_e_1034_, 0);
v_expr_1199_ = lean_ctor_get(v_e_1034_, 1);
lean_inc_ref(v_expr_1199_);
v___x_1200_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1031_, v_beginIdx_1032_, v_subst_1033_, v_expr_1199_, v_offset_1035_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_);
if (lean_obj_tag(v___x_1200_) == 0)
{
lean_object* v_a_1201_; lean_object* v_a_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1222_; 
v_a_1201_ = lean_ctor_get(v___x_1200_, 0);
v_a_1202_ = lean_ctor_get(v___x_1200_, 1);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1200_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1204_ = v___x_1200_;
v_isShared_1205_ = v_isSharedCheck_1222_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_a_1202_);
lean_inc(v_a_1201_);
lean_dec(v___x_1200_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1222_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v_fst_1206_; lean_object* v_snd_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1221_; 
v_fst_1206_ = lean_ctor_get(v_a_1201_, 0);
v_snd_1207_ = lean_ctor_get(v_a_1201_, 1);
v_isSharedCheck_1221_ = !lean_is_exclusive(v_a_1201_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1209_ = v_a_1201_;
v_isShared_1210_ = v_isSharedCheck_1221_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_snd_1207_);
lean_inc(v_fst_1206_);
lean_dec(v_a_1201_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1221_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
size_t v___x_1211_; size_t v___x_1212_; uint8_t v___x_1213_; 
v___x_1211_ = lean_ptr_addr(v_expr_1199_);
v___x_1212_ = lean_ptr_addr(v_fst_1206_);
v___x_1213_ = lean_usize_dec_eq(v___x_1211_, v___x_1212_);
if (v___x_1213_ == 0)
{
lean_object* v___x_1214_; 
lean_inc(v_data_1198_);
lean_del_object(v___x_1209_);
lean_del_object(v___x_1204_);
lean_dec_ref_known(v_e_1034_, 2);
v___x_1214_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__6(v_data_1198_, v_fst_1206_, v_snd_1207_, v_a_1037_, v_a_1038_, v_a_1202_);
return v___x_1214_;
}
else
{
lean_object* v___x_1216_; 
lean_dec(v_fst_1206_);
if (v_isShared_1210_ == 0)
{
lean_ctor_set(v___x_1209_, 0, v_e_1034_);
v___x_1216_ = v___x_1209_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_e_1034_);
lean_ctor_set(v_reuseFailAlloc_1220_, 1, v_snd_1207_);
v___x_1216_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
lean_object* v___x_1218_; 
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 0, v___x_1216_);
v___x_1218_ = v___x_1204_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v___x_1216_);
lean_ctor_set(v_reuseFailAlloc_1219_, 1, v_a_1202_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_1034_, 2);
return v___x_1200_;
}
}
case 11:
{
lean_object* v_typeName_1223_; lean_object* v_idx_1224_; lean_object* v_struct_1225_; lean_object* v___x_1226_; 
v_typeName_1223_ = lean_ctor_get(v_e_1034_, 0);
v_idx_1224_ = lean_ctor_get(v_e_1034_, 1);
v_struct_1225_ = lean_ctor_get(v_e_1034_, 2);
lean_inc_ref(v_struct_1225_);
v___x_1226_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1031_, v_beginIdx_1032_, v_subst_1033_, v_struct_1225_, v_offset_1035_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_);
if (lean_obj_tag(v___x_1226_) == 0)
{
lean_object* v_a_1227_; lean_object* v_a_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1248_; 
v_a_1227_ = lean_ctor_get(v___x_1226_, 0);
v_a_1228_ = lean_ctor_get(v___x_1226_, 1);
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1226_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1230_ = v___x_1226_;
v_isShared_1231_ = v_isSharedCheck_1248_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_a_1228_);
lean_inc(v_a_1227_);
lean_dec(v___x_1226_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1248_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v_fst_1232_; lean_object* v_snd_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1247_; 
v_fst_1232_ = lean_ctor_get(v_a_1227_, 0);
v_snd_1233_ = lean_ctor_get(v_a_1227_, 1);
v_isSharedCheck_1247_ = !lean_is_exclusive(v_a_1227_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1235_ = v_a_1227_;
v_isShared_1236_ = v_isSharedCheck_1247_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_snd_1233_);
lean_inc(v_fst_1232_);
lean_dec(v_a_1227_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1247_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
size_t v___x_1237_; size_t v___x_1238_; uint8_t v___x_1239_; 
v___x_1237_ = lean_ptr_addr(v_struct_1225_);
v___x_1238_ = lean_ptr_addr(v_fst_1232_);
v___x_1239_ = lean_usize_dec_eq(v___x_1237_, v___x_1238_);
if (v___x_1239_ == 0)
{
lean_object* v___x_1240_; 
lean_inc(v_idx_1224_);
lean_inc(v_typeName_1223_);
lean_del_object(v___x_1235_);
lean_del_object(v___x_1230_);
lean_dec_ref_known(v_e_1034_, 3);
v___x_1240_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__7(v_typeName_1223_, v_idx_1224_, v_fst_1232_, v_snd_1233_, v_a_1037_, v_a_1038_, v_a_1228_);
return v___x_1240_;
}
else
{
lean_object* v___x_1242_; 
lean_dec(v_fst_1232_);
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 0, v_e_1034_);
v___x_1242_ = v___x_1235_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_e_1034_);
lean_ctor_set(v_reuseFailAlloc_1246_, 1, v_snd_1233_);
v___x_1242_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
lean_object* v___x_1244_; 
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 0, v___x_1242_);
v___x_1244_ = v___x_1230_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v___x_1242_);
lean_ctor_set(v_reuseFailAlloc_1245_, 1, v_a_1228_);
v___x_1244_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
return v___x_1244_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_1034_, 3);
return v___x_1226_;
}
}
default: 
{
lean_object* v___x_1249_; lean_object* v___x_1250_; 
lean_dec(v_offset_1035_);
lean_dec_ref(v_e_1034_);
v___x_1249_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__3);
v___x_1250_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8(v___x_1249_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_);
return v___x_1250_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(lean_object* v_n_1251_, lean_object* v_beginIdx_1252_, lean_object* v_subst_1253_, lean_object* v_e_1254_, lean_object* v_offset_1255_, lean_object* v_a_1256_, uint8_t v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_){
_start:
{
lean_object* v_key_1260_; lean_object* v___x_1261_; 
lean_inc(v_offset_1255_);
lean_inc_ref(v_e_1254_);
v_key_1260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1260_, 0, v_e_1254_);
lean_ctor_set(v_key_1260_, 1, v_offset_1255_);
v___x_1261_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3___redArg(v_a_1256_, v_key_1260_);
if (lean_obj_tag(v___x_1261_) == 1)
{
lean_object* v_val_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
lean_dec_ref_known(v_key_1260_, 2);
lean_dec(v_offset_1255_);
lean_dec_ref(v_e_1254_);
v_val_1262_ = lean_ctor_get(v___x_1261_, 0);
lean_inc(v_val_1262_);
lean_dec_ref_known(v___x_1261_, 1);
v___x_1263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1263_, 0, v_val_1262_);
lean_ctor_set(v___x_1263_, 1, v_a_1256_);
v___x_1264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1263_);
lean_ctor_set(v___x_1264_, 1, v_a_1259_);
return v___x_1264_;
}
else
{
lean_dec(v___x_1261_);
switch(lean_obj_tag(v_e_1254_))
{
case 0:
{
lean_object* v_deBruijnIndex_1265_; uint8_t v___x_1266_; 
v_deBruijnIndex_1265_ = lean_ctor_get(v_e_1254_, 0);
v___x_1266_ = lean_nat_dec_le(v_offset_1255_, v_deBruijnIndex_1265_);
if (v___x_1266_ == 0)
{
lean_object* v___x_1267_; 
lean_dec(v_offset_1255_);
v___x_1267_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1260_, v_e_1254_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_);
return v___x_1267_;
}
else
{
lean_object* v___x_1268_; uint8_t v___x_1269_; 
lean_inc(v_deBruijnIndex_1265_);
lean_dec_ref_known(v_e_1254_, 1);
v___x_1268_ = lean_nat_add(v_offset_1255_, v_n_1251_);
v___x_1269_ = lean_nat_dec_lt(v_deBruijnIndex_1265_, v___x_1268_);
lean_dec(v___x_1268_);
if (v___x_1269_ == 0)
{
lean_object* v___x_1270_; lean_object* v___x_1271_; 
lean_dec(v_offset_1255_);
v___x_1270_ = lean_nat_sub(v_deBruijnIndex_1265_, v_n_1251_);
lean_dec(v_deBruijnIndex_1265_);
v___x_1271_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___redArg(v___x_1270_, v_a_1259_);
if (lean_obj_tag(v___x_1271_) == 0)
{
lean_object* v_a_1272_; lean_object* v_a_1273_; lean_object* v___x_1274_; 
v_a_1272_ = lean_ctor_get(v___x_1271_, 0);
lean_inc(v_a_1272_);
v_a_1273_ = lean_ctor_get(v___x_1271_, 1);
lean_inc(v_a_1273_);
lean_dec_ref_known(v___x_1271_, 2);
v___x_1274_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1260_, v_a_1272_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1273_);
return v___x_1274_;
}
else
{
lean_object* v_a_1275_; lean_object* v_a_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1283_; 
lean_dec_ref_known(v_key_1260_, 2);
lean_dec_ref(v_a_1256_);
v_a_1275_ = lean_ctor_get(v___x_1271_, 0);
v_a_1276_ = lean_ctor_get(v___x_1271_, 1);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1278_ = v___x_1271_;
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_a_1276_);
lean_inc(v_a_1275_);
lean_dec(v___x_1271_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1281_; 
if (v_isShared_1279_ == 0)
{
v___x_1281_ = v___x_1278_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v_a_1275_);
lean_ctor_set(v_reuseFailAlloc_1282_, 1, v_a_1276_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
return v___x_1281_;
}
}
}
}
else
{
lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v_v_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1284_ = lean_nat_add(v_beginIdx_1252_, v_deBruijnIndex_1265_);
lean_dec(v_deBruijnIndex_1265_);
v___x_1285_ = lean_nat_sub(v___x_1284_, v_offset_1255_);
lean_dec(v___x_1284_);
v_v_1286_ = lean_array_fget_borrowed(v_subst_1253_, v___x_1285_);
lean_dec(v___x_1285_);
v___x_1287_ = lean_unsigned_to_nat(0u);
lean_inc(v_v_1286_);
v___x_1288_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(v_v_1286_, v___x_1287_, v_offset_1255_, v_a_1257_, v_a_1258_, v_a_1259_);
lean_dec(v_offset_1255_);
if (lean_obj_tag(v___x_1288_) == 0)
{
lean_object* v_a_1289_; lean_object* v_a_1290_; lean_object* v___x_1291_; 
v_a_1289_ = lean_ctor_get(v___x_1288_, 0);
lean_inc(v_a_1289_);
v_a_1290_ = lean_ctor_get(v___x_1288_, 1);
lean_inc(v_a_1290_);
lean_dec_ref_known(v___x_1288_, 2);
v___x_1291_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1260_, v_a_1289_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1290_);
return v___x_1291_;
}
else
{
lean_object* v_a_1292_; lean_object* v_a_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1300_; 
lean_dec_ref_known(v_key_1260_, 2);
lean_dec_ref(v_a_1256_);
v_a_1292_ = lean_ctor_get(v___x_1288_, 0);
v_a_1293_ = lean_ctor_get(v___x_1288_, 1);
v_isSharedCheck_1300_ = !lean_is_exclusive(v___x_1288_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1295_ = v___x_1288_;
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_a_1293_);
lean_inc(v_a_1292_);
lean_dec(v___x_1288_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v___x_1298_; 
if (v_isShared_1296_ == 0)
{
v___x_1298_ = v___x_1295_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_a_1292_);
lean_ctor_set(v_reuseFailAlloc_1299_, 1, v_a_1293_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
return v___x_1298_;
}
}
}
}
}
}
case 9:
{
lean_object* v___x_1301_; 
lean_dec(v_offset_1255_);
v___x_1301_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1260_, v_e_1254_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_);
return v___x_1301_;
}
case 2:
{
lean_object* v___x_1302_; 
lean_dec(v_offset_1255_);
v___x_1302_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1260_, v_e_1254_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_);
return v___x_1302_;
}
case 1:
{
lean_object* v___x_1303_; 
lean_dec(v_offset_1255_);
v___x_1303_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1260_, v_e_1254_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_);
return v___x_1303_;
}
case 4:
{
lean_object* v___x_1304_; 
lean_dec(v_offset_1255_);
v___x_1304_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1260_, v_e_1254_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_);
return v___x_1304_;
}
case 3:
{
lean_object* v___x_1305_; 
lean_dec(v_offset_1255_);
v___x_1305_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1260_, v_e_1254_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_);
return v___x_1305_;
}
default: 
{
lean_object* v___x_1306_; uint8_t v___x_1307_; 
v___x_1306_ = l_Lean_Expr_looseBVarRange(v_e_1254_);
v___x_1307_ = lean_nat_dec_le(v___x_1306_, v_offset_1255_);
lean_dec(v___x_1306_);
if (v___x_1307_ == 0)
{
switch(lean_obj_tag(v_e_1254_))
{
case 9:
{
lean_object* v___x_1308_; 
lean_dec(v_offset_1255_);
v___x_1308_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1260_, v_e_1254_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_);
return v___x_1308_;
}
case 2:
{
lean_object* v___x_1309_; 
lean_dec(v_offset_1255_);
v___x_1309_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1260_, v_e_1254_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_);
return v___x_1309_;
}
case 0:
{
lean_object* v___x_1310_; 
lean_dec(v_offset_1255_);
v___x_1310_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1260_, v_e_1254_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_);
return v___x_1310_;
}
case 1:
{
lean_object* v___x_1311_; 
lean_dec(v_offset_1255_);
v___x_1311_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1260_, v_e_1254_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_);
return v___x_1311_;
}
case 4:
{
lean_object* v___x_1312_; 
lean_dec(v_offset_1255_);
v___x_1312_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1260_, v_e_1254_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_);
return v___x_1312_;
}
case 3:
{
lean_object* v___x_1313_; 
lean_dec(v_offset_1255_);
v___x_1313_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1260_, v_e_1254_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_);
return v___x_1313_;
}
default: 
{
lean_object* v___x_1314_; 
v___x_1314_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0(v_n_1251_, v_beginIdx_1252_, v_subst_1253_, v_e_1254_, v_offset_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_);
if (lean_obj_tag(v___x_1314_) == 0)
{
lean_object* v_a_1315_; lean_object* v_a_1316_; lean_object* v_fst_1317_; lean_object* v_snd_1318_; lean_object* v___x_1319_; 
v_a_1315_ = lean_ctor_get(v___x_1314_, 0);
lean_inc(v_a_1315_);
v_a_1316_ = lean_ctor_get(v___x_1314_, 1);
lean_inc(v_a_1316_);
lean_dec_ref_known(v___x_1314_, 2);
v_fst_1317_ = lean_ctor_get(v_a_1315_, 0);
lean_inc(v_fst_1317_);
v_snd_1318_ = lean_ctor_get(v_a_1315_, 1);
lean_inc(v_snd_1318_);
lean_dec(v_a_1315_);
v___x_1319_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1260_, v_fst_1317_, v_snd_1318_, v_a_1257_, v_a_1258_, v_a_1316_);
return v___x_1319_;
}
else
{
lean_dec_ref_known(v_key_1260_, 2);
return v___x_1314_;
}
}
}
}
else
{
lean_object* v___x_1320_; 
lean_dec(v_offset_1255_);
v___x_1320_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1260_, v_e_1254_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_);
return v___x_1320_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0___boxed(lean_object* v_n_1321_, lean_object* v_beginIdx_1322_, lean_object* v_subst_1323_, lean_object* v_e_1324_, lean_object* v_offset_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_){
_start:
{
uint8_t v_a_boxed_1330_; lean_object* v_res_1331_; 
v_a_boxed_1330_ = lean_unbox(v_a_1327_);
v_res_1331_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1321_, v_beginIdx_1322_, v_subst_1323_, v_e_1324_, v_offset_1325_, v_a_1326_, v_a_boxed_1330_, v_a_1328_, v_a_1329_);
lean_dec_ref(v_a_1328_);
lean_dec_ref(v_subst_1323_);
lean_dec(v_beginIdx_1322_);
lean_dec(v_n_1321_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0___boxed(lean_object* v_n_1332_, lean_object* v_beginIdx_1333_, lean_object* v_subst_1334_, lean_object* v_e_1335_, lean_object* v_offset_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_){
_start:
{
uint8_t v_a_boxed_1341_; lean_object* v_res_1342_; 
v_a_boxed_1341_ = lean_unbox(v_a_1338_);
v_res_1342_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0(v_n_1332_, v_beginIdx_1333_, v_subst_1334_, v_e_1335_, v_offset_1336_, v_a_1337_, v_a_boxed_1341_, v_a_1339_, v_a_1340_);
lean_dec_ref(v_a_1339_);
lean_dec_ref(v_subst_1334_);
lean_dec(v_beginIdx_1333_);
lean_dec(v_n_1332_);
return v_res_1342_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__1(void){
_start:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1344_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__2));
v___x_1345_ = lean_unsigned_to_nat(34u);
v___x_1346_ = lean_unsigned_to_nat(57u);
v___x_1347_ = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__0));
v___x_1348_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__3));
v___x_1349_ = l_mkPanicMessageWithDecl(v___x_1348_, v___x_1347_, v___x_1346_, v___x_1345_, v___x_1344_);
return v___x_1349_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__2(void){
_start:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1350_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__2));
v___x_1351_ = lean_unsigned_to_nat(32u);
v___x_1352_ = lean_unsigned_to_nat(56u);
v___x_1353_ = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__0));
v___x_1354_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__3));
v___x_1355_ = l_mkPanicMessageWithDecl(v___x_1354_, v___x_1353_, v___x_1352_, v___x_1351_, v___x_1350_);
return v___x_1355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27(lean_object* v_e_1356_, lean_object* v_beginIdx_1357_, lean_object* v_endIdx_1358_, lean_object* v_subst_1359_, uint8_t v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_){
_start:
{
uint8_t v___x_1363_; 
v___x_1363_ = lean_nat_dec_lt(v_endIdx_1358_, v_beginIdx_1357_);
if (v___x_1363_ == 0)
{
lean_object* v___x_1364_; uint8_t v___x_1365_; 
v___x_1364_ = lean_array_get_size(v_subst_1359_);
v___x_1365_ = lean_nat_dec_lt(v___x_1364_, v_endIdx_1358_);
if (v___x_1365_ == 0)
{
lean_object* v_n_1366_; lean_object* v___x_1367_; 
v_n_1366_ = lean_nat_sub(v_endIdx_1358_, v_beginIdx_1357_);
v___x_1367_ = lean_unsigned_to_nat(0u);
switch(lean_obj_tag(v_e_1356_))
{
case 0:
{
lean_object* v_deBruijnIndex_1368_; uint8_t v___x_1369_; 
v_deBruijnIndex_1368_ = lean_ctor_get(v_e_1356_, 0);
v___x_1369_ = lean_nat_dec_le(v___x_1367_, v_deBruijnIndex_1368_);
if (v___x_1369_ == 0)
{
lean_object* v___x_1370_; 
lean_dec(v_n_1366_);
v___x_1370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1370_, 0, v_e_1356_);
lean_ctor_set(v___x_1370_, 1, v_a_1362_);
return v___x_1370_;
}
else
{
uint8_t v___x_1371_; 
lean_inc(v_deBruijnIndex_1368_);
lean_dec_ref_known(v_e_1356_, 1);
v___x_1371_ = lean_nat_dec_lt(v_deBruijnIndex_1368_, v_n_1366_);
if (v___x_1371_ == 0)
{
lean_object* v___x_1372_; lean_object* v___x_1373_; 
v___x_1372_ = lean_nat_sub(v_deBruijnIndex_1368_, v_n_1366_);
lean_dec(v_n_1366_);
lean_dec(v_deBruijnIndex_1368_);
v___x_1373_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___redArg(v___x_1372_, v_a_1362_);
return v___x_1373_;
}
else
{
lean_object* v___x_1374_; lean_object* v_v_1375_; lean_object* v___x_1376_; 
lean_dec(v_n_1366_);
v___x_1374_ = lean_nat_add(v_beginIdx_1357_, v_deBruijnIndex_1368_);
lean_dec(v_deBruijnIndex_1368_);
v_v_1375_ = lean_array_fget_borrowed(v_subst_1359_, v___x_1374_);
lean_dec(v___x_1374_);
lean_inc(v_v_1375_);
v___x_1376_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(v_v_1375_, v___x_1367_, v___x_1367_, v_a_1360_, v_a_1361_, v_a_1362_);
return v___x_1376_;
}
}
}
case 9:
{
lean_object* v___x_1377_; 
lean_dec(v_n_1366_);
v___x_1377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1377_, 0, v_e_1356_);
lean_ctor_set(v___x_1377_, 1, v_a_1362_);
return v___x_1377_;
}
case 2:
{
lean_object* v___x_1378_; 
lean_dec(v_n_1366_);
v___x_1378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1378_, 0, v_e_1356_);
lean_ctor_set(v___x_1378_, 1, v_a_1362_);
return v___x_1378_;
}
case 1:
{
lean_object* v___x_1379_; 
lean_dec(v_n_1366_);
v___x_1379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1379_, 0, v_e_1356_);
lean_ctor_set(v___x_1379_, 1, v_a_1362_);
return v___x_1379_;
}
case 4:
{
lean_object* v___x_1380_; 
lean_dec(v_n_1366_);
v___x_1380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1380_, 0, v_e_1356_);
lean_ctor_set(v___x_1380_, 1, v_a_1362_);
return v___x_1380_;
}
case 3:
{
lean_object* v___x_1381_; 
lean_dec(v_n_1366_);
v___x_1381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1381_, 0, v_e_1356_);
lean_ctor_set(v___x_1381_, 1, v_a_1362_);
return v___x_1381_;
}
default: 
{
lean_object* v___x_1382_; uint8_t v___x_1383_; 
v___x_1382_ = l_Lean_Expr_looseBVarRange(v_e_1356_);
v___x_1383_ = lean_nat_dec_le(v___x_1382_, v___x_1367_);
lean_dec(v___x_1382_);
if (v___x_1383_ == 0)
{
switch(lean_obj_tag(v_e_1356_))
{
case 9:
{
lean_object* v___x_1384_; 
lean_dec(v_n_1366_);
v___x_1384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1384_, 0, v_e_1356_);
lean_ctor_set(v___x_1384_, 1, v_a_1362_);
return v___x_1384_;
}
case 2:
{
lean_object* v___x_1385_; 
lean_dec(v_n_1366_);
v___x_1385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1385_, 0, v_e_1356_);
lean_ctor_set(v___x_1385_, 1, v_a_1362_);
return v___x_1385_;
}
case 0:
{
lean_object* v___x_1386_; 
lean_dec(v_n_1366_);
v___x_1386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1386_, 0, v_e_1356_);
lean_ctor_set(v___x_1386_, 1, v_a_1362_);
return v___x_1386_;
}
case 1:
{
lean_object* v___x_1387_; 
lean_dec(v_n_1366_);
v___x_1387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1387_, 0, v_e_1356_);
lean_ctor_set(v___x_1387_, 1, v_a_1362_);
return v___x_1387_;
}
case 4:
{
lean_object* v___x_1388_; 
lean_dec(v_n_1366_);
v___x_1388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1388_, 0, v_e_1356_);
lean_ctor_set(v___x_1388_, 1, v_a_1362_);
return v___x_1388_;
}
case 3:
{
lean_object* v___x_1389_; 
lean_dec(v_n_1366_);
v___x_1389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1389_, 0, v_e_1356_);
lean_ctor_set(v___x_1389_, 1, v_a_1362_);
return v___x_1389_;
}
default: 
{
lean_object* v___x_1390_; lean_object* v___x_1391_; 
v___x_1390_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__1, &l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__1_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__1);
v___x_1391_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0(v_n_1366_, v_beginIdx_1357_, v_subst_1359_, v_e_1356_, v___x_1367_, v___x_1390_, v_a_1360_, v_a_1361_, v_a_1362_);
lean_dec(v_n_1366_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v_a_1392_; lean_object* v_a_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1401_; 
v_a_1392_ = lean_ctor_get(v___x_1391_, 0);
v_a_1393_ = lean_ctor_get(v___x_1391_, 1);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1395_ = v___x_1391_;
v_isShared_1396_ = v_isSharedCheck_1401_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_a_1393_);
lean_inc(v_a_1392_);
lean_dec(v___x_1391_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1401_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v_fst_1397_; lean_object* v___x_1399_; 
v_fst_1397_ = lean_ctor_get(v_a_1392_, 0);
lean_inc(v_fst_1397_);
lean_dec(v_a_1392_);
if (v_isShared_1396_ == 0)
{
lean_ctor_set(v___x_1395_, 0, v_fst_1397_);
v___x_1399_ = v___x_1395_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_fst_1397_);
lean_ctor_set(v_reuseFailAlloc_1400_, 1, v_a_1393_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
}
else
{
lean_object* v_a_1402_; lean_object* v_a_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1410_; 
v_a_1402_ = lean_ctor_get(v___x_1391_, 0);
v_a_1403_ = lean_ctor_get(v___x_1391_, 1);
v_isSharedCheck_1410_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1405_ = v___x_1391_;
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_a_1403_);
lean_inc(v_a_1402_);
lean_dec(v___x_1391_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v___x_1408_; 
if (v_isShared_1406_ == 0)
{
v___x_1408_ = v___x_1405_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v_a_1402_);
lean_ctor_set(v_reuseFailAlloc_1409_, 1, v_a_1403_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
}
}
}
}
else
{
lean_object* v___x_1411_; 
lean_dec(v_n_1366_);
v___x_1411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1411_, 0, v_e_1356_);
lean_ctor_set(v___x_1411_, 1, v_a_1362_);
return v___x_1411_;
}
}
}
}
else
{
lean_object* v___x_1412_; lean_object* v___x_1413_; 
lean_dec_ref(v_e_1356_);
v___x_1412_ = lean_obj_once(&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__1, &l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__1_once, _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__1);
v___x_1413_ = l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1(v___x_1412_, v_a_1360_, v_a_1361_, v_a_1362_);
return v___x_1413_;
}
}
else
{
lean_object* v___x_1414_; lean_object* v___x_1415_; 
lean_dec_ref(v_e_1356_);
v___x_1414_ = lean_obj_once(&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__2, &l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__2_once, _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__2);
v___x_1415_ = l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1(v___x_1414_, v_a_1360_, v_a_1361_, v_a_1362_);
return v___x_1415_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___boxed(lean_object* v_e_1416_, lean_object* v_beginIdx_1417_, lean_object* v_endIdx_1418_, lean_object* v_subst_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_){
_start:
{
uint8_t v_a_boxed_1423_; lean_object* v_res_1424_; 
v_a_boxed_1423_ = lean_unbox(v_a_1420_);
v_res_1424_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27(v_e_1416_, v_beginIdx_1417_, v_endIdx_1418_, v_subst_1419_, v_a_boxed_1423_, v_a_1421_, v_a_1422_);
lean_dec_ref(v_a_1421_);
lean_dec_ref(v_subst_1419_);
lean_dec(v_endIdx_1418_);
lean_dec(v_beginIdx_1417_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27(lean_object* v_e_1425_, lean_object* v_subst_1426_, uint8_t v_a_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_){
_start:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___x_1430_ = lean_unsigned_to_nat(0u);
v___x_1431_ = lean_array_get_size(v_subst_1426_);
v___x_1432_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27(v_e_1425_, v___x_1430_, v___x_1431_, v_subst_1426_, v_a_1427_, v_a_1428_, v_a_1429_);
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27___boxed(lean_object* v_e_1433_, lean_object* v_subst_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_){
_start:
{
uint8_t v_a_boxed_1438_; lean_object* v_res_1439_; 
v_a_boxed_1438_ = lean_unbox(v_a_1435_);
v_res_1439_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27(v_e_1433_, v_subst_1434_, v_a_boxed_1438_, v_a_1436_, v_a_1437_);
lean_dec_ref(v_a_1436_);
lean_dec_ref(v_subst_1434_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateS(lean_object* v_e_1440_, lean_object* v_subst_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_){
_start:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; uint8_t v_debug_1451_; lean_object* v_env_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; uint8_t v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1449_ = lean_st_ref_get(v_a_1443_);
v___x_1450_ = lean_st_ref_get(v_a_1447_);
v_debug_1451_ = lean_ctor_get_uint8(v___x_1449_, sizeof(void*)*11);
lean_dec(v___x_1449_);
v_env_1452_ = lean_ctor_get(v___x_1450_, 0);
lean_inc_ref(v_env_1452_);
lean_dec(v___x_1450_);
v___x_1453_ = lean_box(v_debug_1451_);
v___x_1454_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27___boxed), 5, 3);
lean_closure_set(v___x_1454_, 0, v_e_1440_);
lean_closure_set(v___x_1454_, 1, v_subst_1441_);
lean_closure_set(v___x_1454_, 2, v___x_1453_);
v___x_1455_ = 0;
v___x_1456_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_1456_, 0, v_env_1452_);
lean_ctor_set_uint8(v___x_1456_, sizeof(void*)*1, v___x_1455_);
lean_ctor_set_uint8(v___x_1456_, sizeof(void*)*1 + 1, v___x_1455_);
v___x_1457_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___x_1454_, v___x_1456_, v_a_1443_);
if (lean_obj_tag(v___x_1457_) == 0)
{
lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1468_; 
v_a_1458_ = lean_ctor_get(v___x_1457_, 0);
v_isSharedCheck_1468_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1460_ = v___x_1457_;
v_isShared_1461_ = v_isSharedCheck_1468_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1457_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1468_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
if (lean_obj_tag(v_a_1458_) == 0)
{
lean_object* v___x_1462_; lean_object* v___x_1463_; 
lean_dec_ref_known(v_a_1458_, 1);
lean_del_object(v___x_1460_);
v___x_1462_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__2, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__2_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__2);
v___x_1463_ = l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(v___x_1462_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_);
return v___x_1463_;
}
else
{
lean_object* v_a_1464_; lean_object* v___x_1466_; 
v_a_1464_ = lean_ctor_get(v_a_1458_, 0);
lean_inc(v_a_1464_);
lean_dec_ref_known(v_a_1458_, 1);
if (v_isShared_1461_ == 0)
{
lean_ctor_set(v___x_1460_, 0, v_a_1464_);
v___x_1466_ = v___x_1460_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_a_1464_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
return v___x_1466_;
}
}
}
}
else
{
lean_object* v_a_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1476_; 
v_a_1469_ = lean_ctor_get(v___x_1457_, 0);
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1471_ = v___x_1457_;
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_a_1469_);
lean_dec(v___x_1457_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1474_; 
if (v_isShared_1472_ == 0)
{
v___x_1474_ = v___x_1471_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_a_1469_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateS___boxed(lean_object* v_e_1477_, lean_object* v_subst_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_){
_start:
{
lean_object* v_res_1486_; 
v_res_1486_ = l_Lean_Meta_Sym_instantiateS(v_e_1477_, v_subst_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_);
lean_dec(v_a_1484_);
lean_dec_ref(v_a_1483_);
lean_dec(v_a_1482_);
lean_dec_ref(v_a_1481_);
lean_dec(v_a_1480_);
lean_dec_ref(v_a_1479_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0_spec__0(lean_object* v_f_1487_, lean_object* v_a_1488_, uint8_t v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_){
_start:
{
lean_object* v___y_1493_; 
if (v___y_1489_ == 0)
{
v___y_1493_ = v___y_1491_;
goto v___jp_1492_;
}
else
{
lean_object* v___x_1496_; 
v___x_1496_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_f_1487_, v___y_1489_, v___y_1490_, v___y_1491_);
if (lean_obj_tag(v___x_1496_) == 0)
{
lean_object* v_a_1497_; lean_object* v___x_1498_; 
v_a_1497_ = lean_ctor_get(v___x_1496_, 1);
lean_inc(v_a_1497_);
lean_dec_ref_known(v___x_1496_, 2);
v___x_1498_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_a_1488_, v___y_1489_, v___y_1490_, v_a_1497_);
if (lean_obj_tag(v___x_1498_) == 0)
{
lean_object* v_a_1499_; 
v_a_1499_ = lean_ctor_get(v___x_1498_, 1);
lean_inc(v_a_1499_);
lean_dec_ref_known(v___x_1498_, 2);
v___y_1493_ = v_a_1499_;
goto v___jp_1492_;
}
else
{
lean_object* v_a_1500_; lean_object* v_a_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1508_; 
lean_dec_ref(v_a_1488_);
lean_dec_ref(v_f_1487_);
v_a_1500_ = lean_ctor_get(v___x_1498_, 0);
v_a_1501_ = lean_ctor_get(v___x_1498_, 1);
v_isSharedCheck_1508_ = !lean_is_exclusive(v___x_1498_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1503_ = v___x_1498_;
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_a_1501_);
lean_inc(v_a_1500_);
lean_dec(v___x_1498_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___x_1506_; 
if (v_isShared_1504_ == 0)
{
v___x_1506_ = v___x_1503_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_a_1500_);
lean_ctor_set(v_reuseFailAlloc_1507_, 1, v_a_1501_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
}
}
else
{
lean_object* v_a_1509_; lean_object* v_a_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1517_; 
lean_dec_ref(v_a_1488_);
lean_dec_ref(v_f_1487_);
v_a_1509_ = lean_ctor_get(v___x_1496_, 0);
v_a_1510_ = lean_ctor_get(v___x_1496_, 1);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1496_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1512_ = v___x_1496_;
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_a_1510_);
lean_inc(v_a_1509_);
lean_dec(v___x_1496_);
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
v___jp_1492_:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1494_ = l_Lean_Expr_app___override(v_f_1487_, v_a_1488_);
v___x_1495_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1494_, v___y_1493_);
return v___x_1495_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0_spec__0___boxed(lean_object* v_f_1518_, lean_object* v_a_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_){
_start:
{
uint8_t v___y_1394__boxed_1523_; lean_object* v_res_1524_; 
v___y_1394__boxed_1523_ = lean_unbox(v___y_1520_);
v_res_1524_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0_spec__0(v_f_1518_, v_a_1519_, v___y_1394__boxed_1523_, v___y_1521_, v___y_1522_);
lean_dec_ref(v___y_1521_);
return v_res_1524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0(lean_object* v_revArgs_1525_, lean_object* v_start_1526_, lean_object* v_b_1527_, lean_object* v_i_1528_, uint8_t v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_){
_start:
{
uint8_t v___x_1532_; 
v___x_1532_ = lean_nat_dec_le(v_i_1528_, v_start_1526_);
if (v___x_1532_ == 0)
{
lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v_i_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1533_ = l_Lean_instInhabitedExpr;
v___x_1534_ = lean_unsigned_to_nat(1u);
v_i_1535_ = lean_nat_sub(v_i_1528_, v___x_1534_);
lean_dec(v_i_1528_);
v___x_1536_ = lean_array_get_borrowed(v___x_1533_, v_revArgs_1525_, v_i_1535_);
lean_inc(v___x_1536_);
v___x_1537_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0_spec__0(v_b_1527_, v___x_1536_, v___y_1529_, v___y_1530_, v___y_1531_);
if (lean_obj_tag(v___x_1537_) == 0)
{
lean_object* v_a_1538_; lean_object* v_a_1539_; 
v_a_1538_ = lean_ctor_get(v___x_1537_, 0);
lean_inc(v_a_1538_);
v_a_1539_ = lean_ctor_get(v___x_1537_, 1);
lean_inc(v_a_1539_);
lean_dec_ref_known(v___x_1537_, 2);
v_b_1527_ = v_a_1538_;
v_i_1528_ = v_i_1535_;
v___y_1531_ = v_a_1539_;
goto _start;
}
else
{
lean_dec(v_i_1535_);
return v___x_1537_;
}
}
else
{
lean_object* v___x_1541_; 
lean_dec(v_i_1528_);
v___x_1541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1541_, 0, v_b_1527_);
lean_ctor_set(v___x_1541_, 1, v___y_1531_);
return v___x_1541_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0___boxed(lean_object* v_revArgs_1542_, lean_object* v_start_1543_, lean_object* v_b_1544_, lean_object* v_i_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_){
_start:
{
uint8_t v___y_1457__boxed_1549_; lean_object* v_res_1550_; 
v___y_1457__boxed_1549_ = lean_unbox(v___y_1546_);
v_res_1550_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0(v_revArgs_1542_, v_start_1543_, v_b_1544_, v_i_1545_, v___y_1457__boxed_1549_, v___y_1547_, v___y_1548_);
lean_dec_ref(v___y_1547_);
lean_dec(v_start_1543_);
lean_dec_ref(v_revArgs_1542_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go(lean_object* v_revArgs_1551_, lean_object* v_sz_1552_, lean_object* v_e_1553_, lean_object* v_i_1554_, uint8_t v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_){
_start:
{
switch(lean_obj_tag(v_e_1553_))
{
case 6:
{
lean_object* v_body_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; uint8_t v___x_1561_; 
v_body_1558_ = lean_ctor_get(v_e_1553_, 2);
lean_inc_ref(v_body_1558_);
lean_dec_ref_known(v_e_1553_, 3);
v___x_1559_ = lean_unsigned_to_nat(1u);
v___x_1560_ = lean_nat_add(v_i_1554_, v___x_1559_);
lean_dec(v_i_1554_);
v___x_1561_ = lean_nat_dec_lt(v___x_1560_, v_sz_1552_);
if (v___x_1561_ == 0)
{
lean_object* v___x_1562_; 
lean_dec(v___x_1560_);
v___x_1562_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27(v_body_1558_, v_revArgs_1551_, v_a_1555_, v_a_1556_, v_a_1557_);
return v___x_1562_;
}
else
{
v_e_1553_ = v_body_1558_;
v_i_1554_ = v___x_1560_;
goto _start;
}
}
case 10:
{
lean_object* v_expr_1564_; 
v_expr_1564_ = lean_ctor_get(v_e_1553_, 1);
lean_inc_ref(v_expr_1564_);
lean_dec_ref_known(v_e_1553_, 2);
v_e_1553_ = v_expr_1564_;
goto _start;
}
default: 
{
lean_object* v_n_1566_; lean_object* v___x_1567_; 
v_n_1566_ = lean_nat_sub(v_sz_1552_, v_i_1554_);
lean_dec(v_i_1554_);
v___x_1567_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27(v_e_1553_, v_n_1566_, v_sz_1552_, v_revArgs_1551_, v_a_1555_, v_a_1556_, v_a_1557_);
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_object* v_a_1568_; lean_object* v_a_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
v_a_1568_ = lean_ctor_get(v___x_1567_, 0);
lean_inc(v_a_1568_);
v_a_1569_ = lean_ctor_get(v___x_1567_, 1);
lean_inc(v_a_1569_);
lean_dec_ref_known(v___x_1567_, 2);
v___x_1570_ = lean_unsigned_to_nat(0u);
v___x_1571_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0(v_revArgs_1551_, v___x_1570_, v_a_1568_, v_n_1566_, v_a_1555_, v_a_1556_, v_a_1569_);
return v___x_1571_;
}
else
{
lean_dec(v_n_1566_);
return v___x_1567_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go___boxed(lean_object* v_revArgs_1572_, lean_object* v_sz_1573_, lean_object* v_e_1574_, lean_object* v_i_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_){
_start:
{
uint8_t v_a_boxed_1579_; lean_object* v_res_1580_; 
v_a_boxed_1579_ = lean_unbox(v_a_1576_);
v_res_1580_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go(v_revArgs_1572_, v_sz_1573_, v_e_1574_, v_i_1575_, v_a_boxed_1579_, v_a_1577_, v_a_1578_);
lean_dec_ref(v_a_1577_);
lean_dec(v_sz_1573_);
lean_dec_ref(v_revArgs_1572_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27(lean_object* v_f_1581_, lean_object* v_revArgs_1582_, uint8_t v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_){
_start:
{
lean_object* v_sz_1586_; lean_object* v___x_1587_; uint8_t v___x_1588_; 
v_sz_1586_ = lean_array_get_size(v_revArgs_1582_);
v___x_1587_ = lean_unsigned_to_nat(0u);
v___x_1588_ = lean_nat_dec_eq(v_sz_1586_, v___x_1587_);
if (v___x_1588_ == 0)
{
lean_object* v___x_1589_; 
v___x_1589_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go(v_revArgs_1582_, v_sz_1586_, v_f_1581_, v___x_1587_, v_a_1583_, v_a_1584_, v_a_1585_);
return v___x_1589_;
}
else
{
lean_object* v___x_1590_; 
v___x_1590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1590_, 0, v_f_1581_);
lean_ctor_set(v___x_1590_, 1, v_a_1585_);
return v___x_1590_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27___boxed(lean_object* v_f_1591_, lean_object* v_revArgs_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_){
_start:
{
uint8_t v_a_boxed_1596_; lean_object* v_res_1597_; 
v_a_boxed_1596_ = lean_unbox(v_a_1593_);
v_res_1597_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27(v_f_1591_, v_revArgs_1592_, v_a_boxed_1596_, v_a_1594_, v_a_1595_);
lean_dec_ref(v_a_1594_);
lean_dec_ref(v_revArgs_1592_);
return v_res_1597_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_1598_, lean_object* v_x_1599_){
_start:
{
if (lean_obj_tag(v_x_1599_) == 0)
{
return v_x_1598_;
}
else
{
lean_object* v_key_1600_; lean_object* v_value_1601_; lean_object* v_tail_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1632_; 
v_key_1600_ = lean_ctor_get(v_x_1599_, 0);
v_value_1601_ = lean_ctor_get(v_x_1599_, 1);
v_tail_1602_ = lean_ctor_get(v_x_1599_, 2);
v_isSharedCheck_1632_ = !lean_is_exclusive(v_x_1599_);
if (v_isSharedCheck_1632_ == 0)
{
v___x_1604_ = v_x_1599_;
v_isShared_1605_ = v_isSharedCheck_1632_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_tail_1602_);
lean_inc(v_value_1601_);
lean_inc(v_key_1600_);
lean_dec(v_x_1599_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1632_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v_fst_1606_; lean_object* v_snd_1607_; lean_object* v___x_1608_; size_t v___x_1609_; size_t v___x_1610_; size_t v___x_1611_; uint64_t v___x_1612_; uint64_t v___x_1613_; uint64_t v___x_1614_; uint64_t v___x_1615_; uint64_t v___x_1616_; uint64_t v_fold_1617_; uint64_t v___x_1618_; uint64_t v___x_1619_; uint64_t v___x_1620_; size_t v___x_1621_; size_t v___x_1622_; size_t v___x_1623_; size_t v___x_1624_; size_t v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1628_; 
v_fst_1606_ = lean_ctor_get(v_key_1600_, 0);
v_snd_1607_ = lean_ctor_get(v_key_1600_, 1);
v___x_1608_ = lean_array_get_size(v_x_1598_);
v___x_1609_ = lean_ptr_addr(v_fst_1606_);
v___x_1610_ = ((size_t)3ULL);
v___x_1611_ = lean_usize_shift_right(v___x_1609_, v___x_1610_);
v___x_1612_ = lean_usize_to_uint64(v___x_1611_);
v___x_1613_ = lean_uint64_of_nat(v_snd_1607_);
v___x_1614_ = lean_uint64_mix_hash(v___x_1612_, v___x_1613_);
v___x_1615_ = 32ULL;
v___x_1616_ = lean_uint64_shift_right(v___x_1614_, v___x_1615_);
v_fold_1617_ = lean_uint64_xor(v___x_1614_, v___x_1616_);
v___x_1618_ = 16ULL;
v___x_1619_ = lean_uint64_shift_right(v_fold_1617_, v___x_1618_);
v___x_1620_ = lean_uint64_xor(v_fold_1617_, v___x_1619_);
v___x_1621_ = lean_uint64_to_usize(v___x_1620_);
v___x_1622_ = lean_usize_of_nat(v___x_1608_);
v___x_1623_ = ((size_t)1ULL);
v___x_1624_ = lean_usize_sub(v___x_1622_, v___x_1623_);
v___x_1625_ = lean_usize_land(v___x_1621_, v___x_1624_);
v___x_1626_ = lean_array_uget_borrowed(v_x_1598_, v___x_1625_);
lean_inc(v___x_1626_);
if (v_isShared_1605_ == 0)
{
lean_ctor_set(v___x_1604_, 2, v___x_1626_);
v___x_1628_ = v___x_1604_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v_key_1600_);
lean_ctor_set(v_reuseFailAlloc_1631_, 1, v_value_1601_);
lean_ctor_set(v_reuseFailAlloc_1631_, 2, v___x_1626_);
v___x_1628_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
lean_object* v___x_1629_; 
v___x_1629_ = lean_array_uset(v_x_1598_, v___x_1625_, v___x_1628_);
v_x_1598_ = v___x_1629_;
v_x_1599_ = v_tail_1602_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2___redArg(lean_object* v_i_1633_, lean_object* v_source_1634_, lean_object* v_target_1635_){
_start:
{
lean_object* v___x_1636_; uint8_t v___x_1637_; 
v___x_1636_ = lean_array_get_size(v_source_1634_);
v___x_1637_ = lean_nat_dec_lt(v_i_1633_, v___x_1636_);
if (v___x_1637_ == 0)
{
lean_dec_ref(v_source_1634_);
lean_dec(v_i_1633_);
return v_target_1635_;
}
else
{
lean_object* v_es_1638_; lean_object* v___x_1639_; lean_object* v_source_1640_; lean_object* v_target_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; 
v_es_1638_ = lean_array_fget(v_source_1634_, v_i_1633_);
v___x_1639_ = lean_box(0);
v_source_1640_ = lean_array_fset(v_source_1634_, v_i_1633_, v___x_1639_);
v_target_1641_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3___redArg(v_target_1635_, v_es_1638_);
v___x_1642_ = lean_unsigned_to_nat(1u);
v___x_1643_ = lean_nat_add(v_i_1633_, v___x_1642_);
lean_dec(v_i_1633_);
v_i_1633_ = v___x_1643_;
v_source_1634_ = v_source_1640_;
v_target_1635_ = v_target_1641_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1___redArg(lean_object* v_data_1645_){
_start:
{
lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v_nbuckets_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1646_ = lean_array_get_size(v_data_1645_);
v___x_1647_ = lean_unsigned_to_nat(2u);
v_nbuckets_1648_ = lean_nat_mul(v___x_1646_, v___x_1647_);
v___x_1649_ = lean_unsigned_to_nat(0u);
v___x_1650_ = lean_box(0);
v___x_1651_ = lean_mk_array(v_nbuckets_1648_, v___x_1650_);
v___x_1652_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2___redArg(v___x_1649_, v_data_1645_, v___x_1651_);
return v___x_1652_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(lean_object* v_a_1653_, lean_object* v_b_1654_, lean_object* v_x_1655_){
_start:
{
if (lean_obj_tag(v_x_1655_) == 0)
{
lean_dec(v_b_1654_);
lean_dec_ref(v_a_1653_);
return v_x_1655_;
}
else
{
lean_object* v_key_1656_; lean_object* v_value_1657_; lean_object* v_tail_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1676_; 
v_key_1656_ = lean_ctor_get(v_x_1655_, 0);
v_value_1657_ = lean_ctor_get(v_x_1655_, 1);
v_tail_1658_ = lean_ctor_get(v_x_1655_, 2);
v_isSharedCheck_1676_ = !lean_is_exclusive(v_x_1655_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1660_ = v_x_1655_;
v_isShared_1661_ = v_isSharedCheck_1676_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_tail_1658_);
lean_inc(v_value_1657_);
lean_inc(v_key_1656_);
lean_dec(v_x_1655_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1676_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v_fst_1667_; lean_object* v_snd_1668_; lean_object* v_fst_1669_; lean_object* v_snd_1670_; size_t v___x_1671_; size_t v___x_1672_; uint8_t v___x_1673_; 
v_fst_1667_ = lean_ctor_get(v_key_1656_, 0);
v_snd_1668_ = lean_ctor_get(v_key_1656_, 1);
v_fst_1669_ = lean_ctor_get(v_a_1653_, 0);
v_snd_1670_ = lean_ctor_get(v_a_1653_, 1);
v___x_1671_ = lean_ptr_addr(v_fst_1667_);
v___x_1672_ = lean_ptr_addr(v_fst_1669_);
v___x_1673_ = lean_usize_dec_eq(v___x_1671_, v___x_1672_);
if (v___x_1673_ == 0)
{
goto v___jp_1662_;
}
else
{
uint8_t v___x_1674_; 
v___x_1674_ = lean_nat_dec_eq(v_snd_1668_, v_snd_1670_);
if (v___x_1674_ == 0)
{
goto v___jp_1662_;
}
else
{
lean_object* v___x_1675_; 
lean_del_object(v___x_1660_);
lean_dec(v_value_1657_);
lean_dec(v_key_1656_);
v___x_1675_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1675_, 0, v_a_1653_);
lean_ctor_set(v___x_1675_, 1, v_b_1654_);
lean_ctor_set(v___x_1675_, 2, v_tail_1658_);
return v___x_1675_;
}
}
v___jp_1662_:
{
lean_object* v___x_1663_; lean_object* v___x_1665_; 
v___x_1663_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(v_a_1653_, v_b_1654_, v_tail_1658_);
if (v_isShared_1661_ == 0)
{
lean_ctor_set(v___x_1660_, 2, v___x_1663_);
v___x_1665_ = v___x_1660_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_key_1656_);
lean_ctor_set(v_reuseFailAlloc_1666_, 1, v_value_1657_);
lean_ctor_set(v_reuseFailAlloc_1666_, 2, v___x_1663_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(lean_object* v_a_1677_, lean_object* v_x_1678_){
_start:
{
if (lean_obj_tag(v_x_1678_) == 0)
{
uint8_t v___x_1679_; 
v___x_1679_ = 0;
return v___x_1679_;
}
else
{
lean_object* v_key_1680_; lean_object* v_tail_1681_; lean_object* v_fst_1682_; lean_object* v_snd_1683_; lean_object* v_fst_1684_; lean_object* v_snd_1685_; size_t v___x_1686_; size_t v___x_1687_; uint8_t v___x_1688_; 
v_key_1680_ = lean_ctor_get(v_x_1678_, 0);
v_tail_1681_ = lean_ctor_get(v_x_1678_, 2);
v_fst_1682_ = lean_ctor_get(v_key_1680_, 0);
v_snd_1683_ = lean_ctor_get(v_key_1680_, 1);
v_fst_1684_ = lean_ctor_get(v_a_1677_, 0);
v_snd_1685_ = lean_ctor_get(v_a_1677_, 1);
v___x_1686_ = lean_ptr_addr(v_fst_1682_);
v___x_1687_ = lean_ptr_addr(v_fst_1684_);
v___x_1688_ = lean_usize_dec_eq(v___x_1686_, v___x_1687_);
if (v___x_1688_ == 0)
{
v_x_1678_ = v_tail_1681_;
goto _start;
}
else
{
uint8_t v___x_1690_; 
v___x_1690_ = lean_nat_dec_eq(v_snd_1683_, v_snd_1685_);
if (v___x_1690_ == 0)
{
v_x_1678_ = v_tail_1681_;
goto _start;
}
else
{
return v___x_1690_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg___boxed(lean_object* v_a_1692_, lean_object* v_x_1693_){
_start:
{
uint8_t v_res_1694_; lean_object* v_r_1695_; 
v_res_1694_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_a_1692_, v_x_1693_);
lean_dec(v_x_1693_);
lean_dec_ref(v_a_1692_);
v_r_1695_ = lean_box(v_res_1694_);
return v_r_1695_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0___redArg(lean_object* v_m_1696_, lean_object* v_a_1697_, lean_object* v_b_1698_){
_start:
{
lean_object* v_size_1699_; lean_object* v_buckets_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1750_; 
v_size_1699_ = lean_ctor_get(v_m_1696_, 0);
v_buckets_1700_ = lean_ctor_get(v_m_1696_, 1);
v_isSharedCheck_1750_ = !lean_is_exclusive(v_m_1696_);
if (v_isSharedCheck_1750_ == 0)
{
v___x_1702_ = v_m_1696_;
v_isShared_1703_ = v_isSharedCheck_1750_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_buckets_1700_);
lean_inc(v_size_1699_);
lean_dec(v_m_1696_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1750_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v_fst_1704_; lean_object* v_snd_1705_; lean_object* v___x_1706_; size_t v___x_1707_; size_t v___x_1708_; size_t v___x_1709_; uint64_t v___x_1710_; uint64_t v___x_1711_; uint64_t v___x_1712_; uint64_t v___x_1713_; uint64_t v___x_1714_; uint64_t v_fold_1715_; uint64_t v___x_1716_; uint64_t v___x_1717_; uint64_t v___x_1718_; size_t v___x_1719_; size_t v___x_1720_; size_t v___x_1721_; size_t v___x_1722_; size_t v___x_1723_; lean_object* v_bkt_1724_; uint8_t v___x_1725_; 
v_fst_1704_ = lean_ctor_get(v_a_1697_, 0);
v_snd_1705_ = lean_ctor_get(v_a_1697_, 1);
v___x_1706_ = lean_array_get_size(v_buckets_1700_);
v___x_1707_ = lean_ptr_addr(v_fst_1704_);
v___x_1708_ = ((size_t)3ULL);
v___x_1709_ = lean_usize_shift_right(v___x_1707_, v___x_1708_);
v___x_1710_ = lean_usize_to_uint64(v___x_1709_);
v___x_1711_ = lean_uint64_of_nat(v_snd_1705_);
v___x_1712_ = lean_uint64_mix_hash(v___x_1710_, v___x_1711_);
v___x_1713_ = 32ULL;
v___x_1714_ = lean_uint64_shift_right(v___x_1712_, v___x_1713_);
v_fold_1715_ = lean_uint64_xor(v___x_1712_, v___x_1714_);
v___x_1716_ = 16ULL;
v___x_1717_ = lean_uint64_shift_right(v_fold_1715_, v___x_1716_);
v___x_1718_ = lean_uint64_xor(v_fold_1715_, v___x_1717_);
v___x_1719_ = lean_uint64_to_usize(v___x_1718_);
v___x_1720_ = lean_usize_of_nat(v___x_1706_);
v___x_1721_ = ((size_t)1ULL);
v___x_1722_ = lean_usize_sub(v___x_1720_, v___x_1721_);
v___x_1723_ = lean_usize_land(v___x_1719_, v___x_1722_);
v_bkt_1724_ = lean_array_uget_borrowed(v_buckets_1700_, v___x_1723_);
v___x_1725_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_a_1697_, v_bkt_1724_);
if (v___x_1725_ == 0)
{
lean_object* v___x_1726_; lean_object* v_size_x27_1727_; lean_object* v___x_1728_; lean_object* v_buckets_x27_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; uint8_t v___x_1735_; 
v___x_1726_ = lean_unsigned_to_nat(1u);
v_size_x27_1727_ = lean_nat_add(v_size_1699_, v___x_1726_);
lean_dec(v_size_1699_);
lean_inc(v_bkt_1724_);
v___x_1728_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1728_, 0, v_a_1697_);
lean_ctor_set(v___x_1728_, 1, v_b_1698_);
lean_ctor_set(v___x_1728_, 2, v_bkt_1724_);
v_buckets_x27_1729_ = lean_array_uset(v_buckets_1700_, v___x_1723_, v___x_1728_);
v___x_1730_ = lean_unsigned_to_nat(4u);
v___x_1731_ = lean_nat_mul(v_size_x27_1727_, v___x_1730_);
v___x_1732_ = lean_unsigned_to_nat(3u);
v___x_1733_ = lean_nat_div(v___x_1731_, v___x_1732_);
lean_dec(v___x_1731_);
v___x_1734_ = lean_array_get_size(v_buckets_x27_1729_);
v___x_1735_ = lean_nat_dec_le(v___x_1733_, v___x_1734_);
lean_dec(v___x_1733_);
if (v___x_1735_ == 0)
{
lean_object* v_val_1736_; lean_object* v___x_1738_; 
v_val_1736_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1___redArg(v_buckets_x27_1729_);
if (v_isShared_1703_ == 0)
{
lean_ctor_set(v___x_1702_, 1, v_val_1736_);
lean_ctor_set(v___x_1702_, 0, v_size_x27_1727_);
v___x_1738_ = v___x_1702_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_size_x27_1727_);
lean_ctor_set(v_reuseFailAlloc_1739_, 1, v_val_1736_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
return v___x_1738_;
}
}
else
{
lean_object* v___x_1741_; 
if (v_isShared_1703_ == 0)
{
lean_ctor_set(v___x_1702_, 1, v_buckets_x27_1729_);
lean_ctor_set(v___x_1702_, 0, v_size_x27_1727_);
v___x_1741_ = v___x_1702_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_size_x27_1727_);
lean_ctor_set(v_reuseFailAlloc_1742_, 1, v_buckets_x27_1729_);
v___x_1741_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
return v___x_1741_;
}
}
}
else
{
lean_object* v___x_1743_; lean_object* v_buckets_x27_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1748_; 
lean_inc(v_bkt_1724_);
v___x_1743_ = lean_box(0);
v_buckets_x27_1744_ = lean_array_uset(v_buckets_1700_, v___x_1723_, v___x_1743_);
v___x_1745_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(v_a_1697_, v_b_1698_, v_bkt_1724_);
v___x_1746_ = lean_array_uset(v_buckets_x27_1744_, v___x_1723_, v___x_1745_);
if (v_isShared_1703_ == 0)
{
lean_ctor_set(v___x_1702_, 1, v___x_1746_);
v___x_1748_ = v___x_1702_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v_size_1699_);
lean_ctor_set(v_reuseFailAlloc_1749_, 1, v___x_1746_);
v___x_1748_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1747_;
}
v_reusejp_1747_:
{
return v___x_1748_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(lean_object* v_key_1751_, lean_object* v_r_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_){
_start:
{
lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; 
lean_inc_ref(v_r_1752_);
v___x_1755_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1753_, v_key_1751_, v_r_1752_);
v___x_1756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1756_, 0, v_r_1752_);
lean_ctor_set(v___x_1756_, 1, v___x_1755_);
v___x_1757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1757_, 0, v___x_1756_);
lean_ctor_set(v___x_1757_, 1, v_a_1754_);
return v___x_1757_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save(lean_object* v_key_1758_, lean_object* v_r_1759_, lean_object* v_a_1760_, uint8_t v_a_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_){
_start:
{
lean_object* v___x_1764_; 
v___x_1764_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_1758_, v_r_1759_, v_a_1760_, v_a_1763_);
return v___x_1764_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___boxed(lean_object* v_key_1765_, lean_object* v_r_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_){
_start:
{
uint8_t v_a_boxed_1771_; lean_object* v_res_1772_; 
v_a_boxed_1771_ = lean_unbox(v_a_1768_);
v_res_1772_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save(v_key_1765_, v_r_1766_, v_a_1767_, v_a_boxed_1771_, v_a_1769_, v_a_1770_);
lean_dec_ref(v_a_1769_);
return v_res_1772_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0(lean_object* v_00_u03b2_1773_, lean_object* v_m_1774_, lean_object* v_a_1775_, lean_object* v_b_1776_){
_start:
{
lean_object* v___x_1777_; 
v___x_1777_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0___redArg(v_m_1774_, v_a_1775_, v_b_1776_);
return v___x_1777_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0(lean_object* v_00_u03b2_1778_, lean_object* v_a_1779_, lean_object* v_x_1780_){
_start:
{
uint8_t v___x_1781_; 
v___x_1781_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_a_1779_, v_x_1780_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1782_, lean_object* v_a_1783_, lean_object* v_x_1784_){
_start:
{
uint8_t v_res_1785_; lean_object* v_r_1786_; 
v_res_1785_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0(v_00_u03b2_1782_, v_a_1783_, v_x_1784_);
lean_dec(v_x_1784_);
lean_dec_ref(v_a_1783_);
v_r_1786_ = lean_box(v_res_1785_);
return v_r_1786_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1(lean_object* v_00_u03b2_1787_, lean_object* v_data_1788_){
_start:
{
lean_object* v___x_1789_; 
v___x_1789_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1___redArg(v_data_1788_);
return v___x_1789_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2(lean_object* v_00_u03b2_1790_, lean_object* v_a_1791_, lean_object* v_b_1792_, lean_object* v_x_1793_){
_start:
{
lean_object* v___x_1794_; 
v___x_1794_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(v_a_1791_, v_b_1792_, v_x_1793_);
return v___x_1794_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1795_, lean_object* v_i_1796_, lean_object* v_source_1797_, lean_object* v_target_1798_){
_start:
{
lean_object* v___x_1799_; 
v___x_1799_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2___redArg(v_i_1796_, v_source_1797_, v_target_1798_);
return v___x_1799_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1800_, lean_object* v_x_1801_, lean_object* v_x_1802_){
_start:
{
lean_object* v___x_1803_; 
v___x_1803_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1801_, v_x_1802_);
return v___x_1803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0___redArg(lean_object* v_idx_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_){
_start:
{
lean_object* v___x_1807_; lean_object* v___x_1808_; 
v___x_1807_ = l_Lean_Expr_bvar___override(v_idx_1804_);
v___x_1808_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1807_, v___y_1806_);
if (lean_obj_tag(v___x_1808_) == 0)
{
lean_object* v_a_1809_; lean_object* v_a_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1818_; 
v_a_1809_ = lean_ctor_get(v___x_1808_, 0);
v_a_1810_ = lean_ctor_get(v___x_1808_, 1);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1812_ = v___x_1808_;
v_isShared_1813_ = v_isSharedCheck_1818_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_a_1810_);
lean_inc(v_a_1809_);
lean_dec(v___x_1808_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1818_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v___x_1814_; lean_object* v___x_1816_; 
v___x_1814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1814_, 0, v_a_1809_);
lean_ctor_set(v___x_1814_, 1, v___y_1805_);
if (v_isShared_1813_ == 0)
{
lean_ctor_set(v___x_1812_, 0, v___x_1814_);
v___x_1816_ = v___x_1812_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v___x_1814_);
lean_ctor_set(v_reuseFailAlloc_1817_, 1, v_a_1810_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
}
else
{
lean_object* v_a_1819_; lean_object* v_a_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1827_; 
lean_dec_ref(v___y_1805_);
v_a_1819_ = lean_ctor_get(v___x_1808_, 0);
v_a_1820_ = lean_ctor_get(v___x_1808_, 1);
v_isSharedCheck_1827_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1822_ = v___x_1808_;
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_a_1820_);
lean_inc(v_a_1819_);
lean_dec(v___x_1808_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1825_; 
if (v_isShared_1823_ == 0)
{
v___x_1825_ = v___x_1822_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_a_1819_);
lean_ctor_set(v_reuseFailAlloc_1826_, 1, v_a_1820_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
return v___x_1825_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0(lean_object* v_idx_1828_, lean_object* v___y_1829_, uint8_t v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_){
_start:
{
lean_object* v___x_1833_; 
v___x_1833_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0___redArg(v_idx_1828_, v___y_1829_, v___y_1832_);
return v___x_1833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0___boxed(lean_object* v_idx_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_){
_start:
{
uint8_t v___y_1111__boxed_1839_; lean_object* v_res_1840_; 
v___y_1111__boxed_1839_ = lean_unbox(v___y_1836_);
v_res_1840_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0(v_idx_1834_, v___y_1835_, v___y_1111__boxed_1839_, v___y_1837_, v___y_1838_);
lean_dec_ref(v___y_1837_);
return v_res_1840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(lean_object* v_subst_1841_, lean_object* v_e_1842_, lean_object* v_bidx_1843_, lean_object* v_offset_1844_, lean_object* v_a_1845_, uint8_t v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_){
_start:
{
uint8_t v___x_1849_; 
v___x_1849_ = lean_nat_dec_le(v_offset_1844_, v_bidx_1843_);
if (v___x_1849_ == 0)
{
lean_object* v___x_1850_; lean_object* v___x_1851_; 
v___x_1850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1850_, 0, v_e_1842_);
lean_ctor_set(v___x_1850_, 1, v_a_1845_);
v___x_1851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1850_);
lean_ctor_set(v___x_1851_, 1, v_a_1848_);
return v___x_1851_;
}
else
{
lean_object* v_n_1852_; lean_object* v___x_1853_; uint8_t v___x_1854_; 
lean_dec_ref(v_e_1842_);
v_n_1852_ = lean_array_get_size(v_subst_1841_);
v___x_1853_ = lean_nat_add(v_offset_1844_, v_n_1852_);
v___x_1854_ = lean_nat_dec_lt(v_bidx_1843_, v___x_1853_);
lean_dec(v___x_1853_);
if (v___x_1854_ == 0)
{
lean_object* v___x_1855_; lean_object* v___x_1856_; 
v___x_1855_ = lean_nat_sub(v_bidx_1843_, v_n_1852_);
v___x_1856_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0___redArg(v___x_1855_, v_a_1845_, v_a_1848_);
return v___x_1856_;
}
else
{
lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v_v_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; 
v___x_1857_ = lean_nat_sub(v_bidx_1843_, v_offset_1844_);
v___x_1858_ = lean_nat_sub(v_n_1852_, v___x_1857_);
lean_dec(v___x_1857_);
v___x_1859_ = lean_unsigned_to_nat(1u);
v___x_1860_ = lean_nat_sub(v___x_1858_, v___x_1859_);
lean_dec(v___x_1858_);
v_v_1861_ = lean_array_fget_borrowed(v_subst_1841_, v___x_1860_);
lean_dec(v___x_1860_);
v___x_1862_ = lean_unsigned_to_nat(0u);
lean_inc(v_v_1861_);
v___x_1863_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(v_v_1861_, v___x_1862_, v_offset_1844_, v_a_1846_, v_a_1847_, v_a_1848_);
if (lean_obj_tag(v___x_1863_) == 0)
{
lean_object* v_a_1864_; lean_object* v_a_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1873_; 
v_a_1864_ = lean_ctor_get(v___x_1863_, 0);
v_a_1865_ = lean_ctor_get(v___x_1863_, 1);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1863_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1867_ = v___x_1863_;
v_isShared_1868_ = v_isSharedCheck_1873_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_a_1865_);
lean_inc(v_a_1864_);
lean_dec(v___x_1863_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1873_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
lean_object* v___x_1869_; lean_object* v___x_1871_; 
v___x_1869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1869_, 0, v_a_1864_);
lean_ctor_set(v___x_1869_, 1, v_a_1845_);
if (v_isShared_1868_ == 0)
{
lean_ctor_set(v___x_1867_, 0, v___x_1869_);
v___x_1871_ = v___x_1867_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v___x_1869_);
lean_ctor_set(v_reuseFailAlloc_1872_, 1, v_a_1865_);
v___x_1871_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
return v___x_1871_;
}
}
}
else
{
lean_object* v_a_1874_; lean_object* v_a_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1882_; 
lean_dec_ref(v_a_1845_);
v_a_1874_ = lean_ctor_get(v___x_1863_, 0);
v_a_1875_ = lean_ctor_get(v___x_1863_, 1);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___x_1863_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1877_ = v___x_1863_;
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_a_1875_);
lean_inc(v_a_1874_);
lean_dec(v___x_1863_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v___x_1880_; 
if (v_isShared_1878_ == 0)
{
v___x_1880_ = v___x_1877_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v_a_1874_);
lean_ctor_set(v_reuseFailAlloc_1881_, 1, v_a_1875_);
v___x_1880_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
return v___x_1880_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar___boxed(lean_object* v_subst_1883_, lean_object* v_e_1884_, lean_object* v_bidx_1885_, lean_object* v_offset_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_){
_start:
{
uint8_t v_a_boxed_1891_; lean_object* v_res_1892_; 
v_a_boxed_1891_ = lean_unbox(v_a_1888_);
v_res_1892_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(v_subst_1883_, v_e_1884_, v_bidx_1885_, v_offset_1886_, v_a_1887_, v_a_boxed_1891_, v_a_1889_, v_a_1890_);
lean_dec_ref(v_a_1889_);
lean_dec(v_offset_1886_);
lean_dec(v_bidx_1885_);
lean_dec_ref(v_subst_1883_);
return v_res_1892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault(lean_object* v_subst_1893_, lean_object* v_e_1894_, lean_object* v_offset_1895_, lean_object* v_a_1896_, uint8_t v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_){
_start:
{
if (lean_obj_tag(v_e_1894_) == 5)
{
lean_object* v_fn_1900_; lean_object* v_arg_1901_; lean_object* v_key_1902_; lean_object* v___y_1904_; lean_object* v___x_1910_; 
v_fn_1900_ = lean_ctor_get(v_e_1894_, 0);
v_arg_1901_ = lean_ctor_get(v_e_1894_, 1);
lean_inc(v_offset_1895_);
lean_inc_ref(v_e_1894_);
v_key_1902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1902_, 0, v_e_1894_);
lean_ctor_set(v_key_1902_, 1, v_offset_1895_);
v___x_1910_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3___redArg(v_a_1896_, v_key_1902_);
if (lean_obj_tag(v___x_1910_) == 1)
{
lean_object* v_val_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; 
lean_dec_ref_known(v_key_1902_, 2);
lean_dec_ref_known(v_e_1894_, 2);
lean_dec(v_offset_1895_);
v_val_1911_ = lean_ctor_get(v___x_1910_, 0);
lean_inc(v_val_1911_);
lean_dec_ref_known(v___x_1910_, 1);
v___x_1912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1912_, 0, v_val_1911_);
lean_ctor_set(v___x_1912_, 1, v_a_1896_);
v___x_1913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1912_);
lean_ctor_set(v___x_1913_, 1, v_a_1899_);
return v___x_1913_;
}
else
{
lean_object* v___x_1914_; 
lean_dec(v___x_1910_);
lean_inc(v_offset_1895_);
lean_inc_ref(v_fn_1900_);
v___x_1914_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault(v_subst_1893_, v_fn_1900_, v_offset_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_);
if (lean_obj_tag(v___x_1914_) == 0)
{
lean_object* v_a_1915_; lean_object* v_a_1916_; lean_object* v_fst_1917_; lean_object* v_snd_1918_; lean_object* v___x_1919_; 
v_a_1915_ = lean_ctor_get(v___x_1914_, 0);
lean_inc(v_a_1915_);
v_a_1916_ = lean_ctor_get(v___x_1914_, 1);
lean_inc(v_a_1916_);
lean_dec_ref_known(v___x_1914_, 2);
v_fst_1917_ = lean_ctor_get(v_a_1915_, 0);
lean_inc(v_fst_1917_);
v_snd_1918_ = lean_ctor_get(v_a_1915_, 1);
lean_inc(v_snd_1918_);
lean_dec(v_a_1915_);
lean_inc_ref(v_arg_1901_);
v___x_1919_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1893_, v_arg_1901_, v_offset_1895_, v_snd_1918_, v_a_1897_, v_a_1898_, v_a_1916_);
if (lean_obj_tag(v___x_1919_) == 0)
{
lean_object* v_a_1920_; lean_object* v_a_1921_; lean_object* v_fst_1922_; lean_object* v_snd_1923_; size_t v___x_1924_; size_t v___x_1925_; uint8_t v___x_1926_; 
v_a_1920_ = lean_ctor_get(v___x_1919_, 0);
lean_inc(v_a_1920_);
v_a_1921_ = lean_ctor_get(v___x_1919_, 1);
lean_inc(v_a_1921_);
lean_dec_ref_known(v___x_1919_, 2);
v_fst_1922_ = lean_ctor_get(v_a_1920_, 0);
lean_inc(v_fst_1922_);
v_snd_1923_ = lean_ctor_get(v_a_1920_, 1);
lean_inc(v_snd_1923_);
lean_dec(v_a_1920_);
v___x_1924_ = lean_ptr_addr(v_fn_1900_);
v___x_1925_ = lean_ptr_addr(v_fst_1917_);
v___x_1926_ = lean_usize_dec_eq(v___x_1924_, v___x_1925_);
if (v___x_1926_ == 0)
{
lean_object* v___x_1927_; 
lean_dec_ref_known(v_e_1894_, 2);
v___x_1927_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__2(v_fst_1917_, v_fst_1922_, v_snd_1923_, v_a_1897_, v_a_1898_, v_a_1921_);
v___y_1904_ = v___x_1927_;
goto v___jp_1903_;
}
else
{
size_t v___x_1928_; size_t v___x_1929_; uint8_t v___x_1930_; 
v___x_1928_ = lean_ptr_addr(v_arg_1901_);
v___x_1929_ = lean_ptr_addr(v_fst_1922_);
v___x_1930_ = lean_usize_dec_eq(v___x_1928_, v___x_1929_);
if (v___x_1930_ == 0)
{
lean_object* v___x_1931_; 
lean_dec_ref_known(v_e_1894_, 2);
v___x_1931_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__2(v_fst_1917_, v_fst_1922_, v_snd_1923_, v_a_1897_, v_a_1898_, v_a_1921_);
v___y_1904_ = v___x_1931_;
goto v___jp_1903_;
}
else
{
lean_object* v___x_1932_; 
lean_dec(v_fst_1922_);
lean_dec(v_fst_1917_);
v___x_1932_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_1902_, v_e_1894_, v_snd_1923_, v_a_1921_);
return v___x_1932_;
}
}
}
else
{
lean_dec(v_fst_1917_);
lean_dec_ref_known(v_key_1902_, 2);
lean_dec_ref_known(v_e_1894_, 2);
return v___x_1919_;
}
}
else
{
lean_dec_ref_known(v_key_1902_, 2);
lean_dec_ref_known(v_e_1894_, 2);
lean_dec(v_offset_1895_);
return v___x_1914_;
}
}
v___jp_1903_:
{
if (lean_obj_tag(v___y_1904_) == 0)
{
lean_object* v_a_1905_; lean_object* v_a_1906_; lean_object* v_fst_1907_; lean_object* v_snd_1908_; lean_object* v___x_1909_; 
v_a_1905_ = lean_ctor_get(v___y_1904_, 0);
lean_inc(v_a_1905_);
v_a_1906_ = lean_ctor_get(v___y_1904_, 1);
lean_inc(v_a_1906_);
lean_dec_ref_known(v___y_1904_, 2);
v_fst_1907_ = lean_ctor_get(v_a_1905_, 0);
lean_inc(v_fst_1907_);
v_snd_1908_ = lean_ctor_get(v_a_1905_, 1);
lean_inc(v_snd_1908_);
lean_dec(v_a_1905_);
v___x_1909_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_1902_, v_fst_1907_, v_snd_1908_, v_a_1906_);
return v___x_1909_;
}
else
{
lean_dec_ref_known(v_key_1902_, 2);
return v___y_1904_;
}
}
}
else
{
lean_object* v___x_1933_; 
v___x_1933_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1893_, v_e_1894_, v_offset_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_);
return v___x_1933_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__2(void){
_start:
{
lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; 
v___x_1936_ = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__1));
v___x_1937_ = lean_unsigned_to_nat(25u);
v___x_1938_ = lean_unsigned_to_nat(148u);
v___x_1939_ = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__0));
v___x_1940_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__0));
v___x_1941_ = l_mkPanicMessageWithDecl(v___x_1940_, v___x_1939_, v___x_1938_, v___x_1937_, v___x_1936_);
return v___x_1941_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__1(void){
_start:
{
lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; 
v___x_1943_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__2));
v___x_1944_ = lean_unsigned_to_nat(11u);
v___x_1945_ = lean_unsigned_to_nat(165u);
v___x_1946_ = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__0));
v___x_1947_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__3));
v___x_1948_ = l_mkPanicMessageWithDecl(v___x_1947_, v___x_1946_, v___x_1945_, v___x_1944_, v___x_1943_);
return v___x_1948_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta(lean_object* v_subst_1949_, lean_object* v_e_1950_, lean_object* v_f_1951_, lean_object* v_argsRev_1952_, lean_object* v_offset_1953_, uint8_t v_modified_1954_, lean_object* v_a_1955_, uint8_t v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_){
_start:
{
switch(lean_obj_tag(v_f_1951_))
{
case 5:
{
lean_object* v_fn_1959_; lean_object* v_arg_1960_; lean_object* v___x_1961_; 
v_fn_1959_ = lean_ctor_get(v_f_1951_, 0);
lean_inc_ref(v_fn_1959_);
v_arg_1960_ = lean_ctor_get(v_f_1951_, 1);
lean_inc_ref_n(v_arg_1960_, 2);
lean_dec_ref_known(v_f_1951_, 2);
lean_inc(v_offset_1953_);
v___x_1961_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1949_, v_arg_1960_, v_offset_1953_, v_a_1955_, v_a_1956_, v_a_1957_, v_a_1958_);
if (lean_obj_tag(v___x_1961_) == 0)
{
lean_object* v_a_1962_; lean_object* v_a_1963_; lean_object* v_fst_1964_; lean_object* v_snd_1965_; lean_object* v___x_1966_; 
v_a_1962_ = lean_ctor_get(v___x_1961_, 0);
lean_inc(v_a_1962_);
v_a_1963_ = lean_ctor_get(v___x_1961_, 1);
lean_inc(v_a_1963_);
lean_dec_ref_known(v___x_1961_, 2);
v_fst_1964_ = lean_ctor_get(v_a_1962_, 0);
lean_inc_n(v_fst_1964_, 2);
v_snd_1965_ = lean_ctor_get(v_a_1962_, 1);
lean_inc(v_snd_1965_);
lean_dec(v_a_1962_);
v___x_1966_ = lean_array_push(v_argsRev_1952_, v_fst_1964_);
if (v_modified_1954_ == 0)
{
size_t v___x_1967_; size_t v___x_1968_; uint8_t v___x_1969_; 
v___x_1967_ = lean_ptr_addr(v_arg_1960_);
lean_dec_ref(v_arg_1960_);
v___x_1968_ = lean_ptr_addr(v_fst_1964_);
lean_dec(v_fst_1964_);
v___x_1969_ = lean_usize_dec_eq(v___x_1967_, v___x_1968_);
if (v___x_1969_ == 0)
{
uint8_t v___x_1970_; 
v___x_1970_ = 1;
v_f_1951_ = v_fn_1959_;
v_argsRev_1952_ = v___x_1966_;
v_modified_1954_ = v___x_1970_;
v_a_1955_ = v_snd_1965_;
v_a_1958_ = v_a_1963_;
goto _start;
}
else
{
v_f_1951_ = v_fn_1959_;
v_argsRev_1952_ = v___x_1966_;
v_a_1955_ = v_snd_1965_;
v_a_1958_ = v_a_1963_;
goto _start;
}
}
else
{
lean_dec(v_fst_1964_);
lean_dec_ref(v_arg_1960_);
v_f_1951_ = v_fn_1959_;
v_argsRev_1952_ = v___x_1966_;
v_a_1955_ = v_snd_1965_;
v_a_1958_ = v_a_1963_;
goto _start;
}
}
else
{
lean_dec_ref(v_arg_1960_);
lean_dec_ref(v_fn_1959_);
lean_dec(v_offset_1953_);
lean_dec_ref(v_argsRev_1952_);
lean_dec_ref(v_e_1950_);
return v___x_1961_;
}
}
case 0:
{
lean_object* v_deBruijnIndex_1974_; lean_object* v___x_1975_; 
v_deBruijnIndex_1974_ = lean_ctor_get(v_f_1951_, 0);
lean_inc_ref(v_f_1951_);
v___x_1975_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(v_subst_1949_, v_f_1951_, v_deBruijnIndex_1974_, v_offset_1953_, v_a_1955_, v_a_1956_, v_a_1957_, v_a_1958_);
lean_dec(v_offset_1953_);
if (lean_obj_tag(v___x_1975_) == 0)
{
lean_object* v_a_1976_; lean_object* v_a_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_2017_; 
v_a_1976_ = lean_ctor_get(v___x_1975_, 0);
v_a_1977_ = lean_ctor_get(v___x_1975_, 1);
v_isSharedCheck_2017_ = !lean_is_exclusive(v___x_1975_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_1979_ = v___x_1975_;
v_isShared_1980_ = v_isSharedCheck_2017_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_a_1977_);
lean_inc(v_a_1976_);
lean_dec(v___x_1975_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_2017_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v_fst_1981_; lean_object* v_snd_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_2016_; 
v_fst_1981_ = lean_ctor_get(v_a_1976_, 0);
v_snd_1982_ = lean_ctor_get(v_a_1976_, 1);
v_isSharedCheck_2016_ = !lean_is_exclusive(v_a_1976_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_1984_ = v_a_1976_;
v_isShared_1985_ = v_isSharedCheck_2016_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_snd_1982_);
lean_inc(v_fst_1981_);
lean_dec(v_a_1976_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_2016_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
if (v_modified_1954_ == 0)
{
size_t v___x_2009_; size_t v___x_2010_; uint8_t v___x_2011_; 
v___x_2009_ = lean_ptr_addr(v_f_1951_);
lean_dec_ref_known(v_f_1951_, 1);
v___x_2010_ = lean_ptr_addr(v_fst_1981_);
v___x_2011_ = lean_usize_dec_eq(v___x_2009_, v___x_2010_);
if (v___x_2011_ == 0)
{
lean_del_object(v___x_1979_);
lean_dec_ref(v_e_1950_);
goto v___jp_1986_;
}
else
{
lean_object* v___x_2012_; lean_object* v___x_2014_; 
lean_del_object(v___x_1984_);
lean_dec(v_fst_1981_);
lean_dec_ref(v_argsRev_1952_);
v___x_2012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2012_, 0, v_e_1950_);
lean_ctor_set(v___x_2012_, 1, v_snd_1982_);
if (v_isShared_1980_ == 0)
{
lean_ctor_set(v___x_1979_, 0, v___x_2012_);
v___x_2014_ = v___x_1979_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v___x_2012_);
lean_ctor_set(v_reuseFailAlloc_2015_, 1, v_a_1977_);
v___x_2014_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
return v___x_2014_;
}
}
}
else
{
lean_del_object(v___x_1979_);
lean_dec_ref_known(v_f_1951_, 1);
lean_dec_ref(v_e_1950_);
goto v___jp_1986_;
}
v___jp_1986_:
{
lean_object* v___x_1987_; 
v___x_1987_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27(v_fst_1981_, v_argsRev_1952_, v_a_1956_, v_a_1957_, v_a_1977_);
lean_dec_ref(v_argsRev_1952_);
if (lean_obj_tag(v___x_1987_) == 0)
{
lean_object* v_a_1988_; lean_object* v_a_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_1999_; 
v_a_1988_ = lean_ctor_get(v___x_1987_, 0);
v_a_1989_ = lean_ctor_get(v___x_1987_, 1);
v_isSharedCheck_1999_ = !lean_is_exclusive(v___x_1987_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1991_ = v___x_1987_;
v_isShared_1992_ = v_isSharedCheck_1999_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_a_1989_);
lean_inc(v_a_1988_);
lean_dec(v___x_1987_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_1999_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v___x_1994_; 
if (v_isShared_1985_ == 0)
{
lean_ctor_set(v___x_1984_, 0, v_a_1988_);
v___x_1994_ = v___x_1984_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v_a_1988_);
lean_ctor_set(v_reuseFailAlloc_1998_, 1, v_snd_1982_);
v___x_1994_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
lean_object* v___x_1996_; 
if (v_isShared_1992_ == 0)
{
lean_ctor_set(v___x_1991_, 0, v___x_1994_);
v___x_1996_ = v___x_1991_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v___x_1994_);
lean_ctor_set(v_reuseFailAlloc_1997_, 1, v_a_1989_);
v___x_1996_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
return v___x_1996_;
}
}
}
}
else
{
lean_object* v_a_2000_; lean_object* v_a_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2008_; 
lean_del_object(v___x_1984_);
lean_dec(v_snd_1982_);
v_a_2000_ = lean_ctor_get(v___x_1987_, 0);
v_a_2001_ = lean_ctor_get(v___x_1987_, 1);
v_isSharedCheck_2008_ = !lean_is_exclusive(v___x_1987_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_2003_ = v___x_1987_;
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_a_2001_);
lean_inc(v_a_2000_);
lean_dec(v___x_1987_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2006_; 
if (v_isShared_2004_ == 0)
{
v___x_2006_ = v___x_2003_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v_a_2000_);
lean_ctor_set(v_reuseFailAlloc_2007_, 1, v_a_2001_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
return v___x_2006_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_f_1951_, 1);
lean_dec_ref(v_argsRev_1952_);
lean_dec_ref(v_e_1950_);
return v___x_1975_;
}
}
default: 
{
lean_object* v___x_2018_; lean_object* v___x_2019_; 
lean_dec(v_offset_1953_);
lean_dec_ref(v_argsRev_1952_);
lean_dec_ref(v_f_1951_);
lean_dec_ref(v_e_1950_);
v___x_2018_ = lean_obj_once(&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__1, &l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__1_once, _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__1);
v___x_2019_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8(v___x_2018_, v_a_1955_, v_a_1956_, v_a_1957_, v_a_1958_);
return v___x_2019_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg(lean_object* v_subst_2020_, lean_object* v_e_2021_, lean_object* v_f_2022_, lean_object* v_arg_2023_, lean_object* v_offset_2024_, lean_object* v_a_2025_, uint8_t v_a_2026_, lean_object* v_a_2027_, lean_object* v_a_2028_){
_start:
{
lean_object* v___x_2029_; 
lean_inc(v_offset_2024_);
lean_inc_ref(v_arg_2023_);
v___x_2029_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_2020_, v_arg_2023_, v_offset_2024_, v_a_2025_, v_a_2026_, v_a_2027_, v_a_2028_);
if (lean_obj_tag(v___x_2029_) == 0)
{
lean_object* v_a_2030_; lean_object* v_a_2031_; lean_object* v_fst_2032_; lean_object* v_snd_2033_; lean_object* v___x_2034_; uint8_t v___x_2035_; 
v_a_2030_ = lean_ctor_get(v___x_2029_, 0);
lean_inc(v_a_2030_);
v_a_2031_ = lean_ctor_get(v___x_2029_, 1);
lean_inc(v_a_2031_);
lean_dec_ref_known(v___x_2029_, 2);
v_fst_2032_ = lean_ctor_get(v_a_2030_, 0);
lean_inc(v_fst_2032_);
v_snd_2033_ = lean_ctor_get(v_a_2030_, 1);
lean_inc(v_snd_2033_);
lean_dec(v_a_2030_);
v___x_2034_ = l_Lean_Expr_getAppFn(v_f_2022_);
v___x_2035_ = l_Lean_Expr_isBVar(v___x_2034_);
lean_dec_ref(v___x_2034_);
if (v___x_2035_ == 0)
{
lean_object* v___x_2036_; 
lean_dec_ref(v_arg_2023_);
v___x_2036_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault(v_subst_2020_, v_f_2022_, v_offset_2024_, v_snd_2033_, v_a_2026_, v_a_2027_, v_a_2031_);
if (lean_obj_tag(v___x_2036_) == 0)
{
lean_object* v_a_2037_; 
v_a_2037_ = lean_ctor_get(v___x_2036_, 0);
lean_inc(v_a_2037_);
if (lean_obj_tag(v_e_2021_) == 5)
{
lean_object* v_a_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2064_; 
v_a_2038_ = lean_ctor_get(v___x_2036_, 1);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2064_ == 0)
{
lean_object* v_unused_2065_; 
v_unused_2065_ = lean_ctor_get(v___x_2036_, 0);
lean_dec(v_unused_2065_);
v___x_2040_ = v___x_2036_;
v_isShared_2041_ = v_isSharedCheck_2064_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_a_2038_);
lean_dec(v___x_2036_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2064_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v_fst_2042_; lean_object* v_snd_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2063_; 
v_fst_2042_ = lean_ctor_get(v_a_2037_, 0);
v_snd_2043_ = lean_ctor_get(v_a_2037_, 1);
v_isSharedCheck_2063_ = !lean_is_exclusive(v_a_2037_);
if (v_isSharedCheck_2063_ == 0)
{
v___x_2045_ = v_a_2037_;
v_isShared_2046_ = v_isSharedCheck_2063_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_snd_2043_);
lean_inc(v_fst_2042_);
lean_dec(v_a_2037_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2063_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v_fn_2047_; lean_object* v_arg_2048_; size_t v___x_2049_; size_t v___x_2050_; uint8_t v___x_2051_; 
v_fn_2047_ = lean_ctor_get(v_e_2021_, 0);
v_arg_2048_ = lean_ctor_get(v_e_2021_, 1);
v___x_2049_ = lean_ptr_addr(v_fn_2047_);
v___x_2050_ = lean_ptr_addr(v_fst_2042_);
v___x_2051_ = lean_usize_dec_eq(v___x_2049_, v___x_2050_);
if (v___x_2051_ == 0)
{
lean_object* v___x_2052_; 
lean_del_object(v___x_2045_);
lean_del_object(v___x_2040_);
lean_dec_ref_known(v_e_2021_, 2);
v___x_2052_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__2(v_fst_2042_, v_fst_2032_, v_snd_2043_, v_a_2026_, v_a_2027_, v_a_2038_);
return v___x_2052_;
}
else
{
size_t v___x_2053_; size_t v___x_2054_; uint8_t v___x_2055_; 
v___x_2053_ = lean_ptr_addr(v_arg_2048_);
v___x_2054_ = lean_ptr_addr(v_fst_2032_);
v___x_2055_ = lean_usize_dec_eq(v___x_2053_, v___x_2054_);
if (v___x_2055_ == 0)
{
lean_object* v___x_2056_; 
lean_del_object(v___x_2045_);
lean_del_object(v___x_2040_);
lean_dec_ref_known(v_e_2021_, 2);
v___x_2056_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__2(v_fst_2042_, v_fst_2032_, v_snd_2043_, v_a_2026_, v_a_2027_, v_a_2038_);
return v___x_2056_;
}
else
{
lean_object* v___x_2058_; 
lean_dec(v_fst_2042_);
lean_dec(v_fst_2032_);
if (v_isShared_2046_ == 0)
{
lean_ctor_set(v___x_2045_, 0, v_e_2021_);
v___x_2058_ = v___x_2045_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_e_2021_);
lean_ctor_set(v_reuseFailAlloc_2062_, 1, v_snd_2043_);
v___x_2058_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
lean_object* v___x_2060_; 
if (v_isShared_2041_ == 0)
{
lean_ctor_set(v___x_2040_, 0, v___x_2058_);
v___x_2060_ = v___x_2040_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v___x_2058_);
lean_ctor_set(v_reuseFailAlloc_2061_, 1, v_a_2038_);
v___x_2060_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
return v___x_2060_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2066_; lean_object* v_snd_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; 
lean_dec(v_fst_2032_);
lean_dec_ref(v_e_2021_);
v_a_2066_ = lean_ctor_get(v___x_2036_, 1);
lean_inc(v_a_2066_);
lean_dec_ref_known(v___x_2036_, 2);
v_snd_2067_ = lean_ctor_get(v_a_2037_, 1);
lean_inc(v_snd_2067_);
lean_dec(v_a_2037_);
v___x_2068_ = lean_obj_once(&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__2, &l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__2_once, _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__2);
v___x_2069_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8(v___x_2068_, v_snd_2067_, v_a_2026_, v_a_2027_, v_a_2066_);
return v___x_2069_;
}
}
else
{
lean_dec(v_fst_2032_);
lean_dec_ref(v_e_2021_);
return v___x_2036_;
}
}
else
{
lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; size_t v___x_2073_; size_t v___x_2074_; uint8_t v___x_2075_; 
v___x_2070_ = lean_unsigned_to_nat(1u);
v___x_2071_ = lean_mk_empty_array_with_capacity(v___x_2070_);
lean_inc(v_fst_2032_);
v___x_2072_ = lean_array_push(v___x_2071_, v_fst_2032_);
v___x_2073_ = lean_ptr_addr(v_arg_2023_);
lean_dec_ref(v_arg_2023_);
v___x_2074_ = lean_ptr_addr(v_fst_2032_);
lean_dec(v_fst_2032_);
v___x_2075_ = lean_usize_dec_eq(v___x_2073_, v___x_2074_);
if (v___x_2075_ == 0)
{
lean_object* v___x_2076_; 
v___x_2076_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta(v_subst_2020_, v_e_2021_, v_f_2022_, v___x_2072_, v_offset_2024_, v___x_2035_, v_snd_2033_, v_a_2026_, v_a_2027_, v_a_2031_);
return v___x_2076_;
}
else
{
uint8_t v___x_2077_; lean_object* v___x_2078_; 
v___x_2077_ = 0;
v___x_2078_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta(v_subst_2020_, v_e_2021_, v_f_2022_, v___x_2072_, v_offset_2024_, v___x_2077_, v_snd_2033_, v_a_2026_, v_a_2027_, v_a_2031_);
return v___x_2078_;
}
}
}
else
{
lean_dec(v_offset_2024_);
lean_dec_ref(v_arg_2023_);
lean_dec_ref(v_f_2022_);
lean_dec_ref(v_e_2021_);
return v___x_2029_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__1(void){
_start:
{
lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___x_2080_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__2));
v___x_2081_ = lean_unsigned_to_nat(59u);
v___x_2082_ = lean_unsigned_to_nat(176u);
v___x_2083_ = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__0));
v___x_2084_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__3));
v___x_2085_ = l_mkPanicMessageWithDecl(v___x_2084_, v___x_2083_, v___x_2082_, v___x_2081_, v___x_2080_);
return v___x_2085_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit(lean_object* v_subst_2086_, lean_object* v_e_2087_, lean_object* v_offset_2088_, lean_object* v_a_2089_, uint8_t v_a_2090_, lean_object* v_a_2091_, lean_object* v_a_2092_){
_start:
{
switch(lean_obj_tag(v_e_2087_))
{
case 0:
{
lean_object* v_deBruijnIndex_2093_; lean_object* v___x_2094_; 
v_deBruijnIndex_2093_ = lean_ctor_get(v_e_2087_, 0);
lean_inc(v_deBruijnIndex_2093_);
v___x_2094_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(v_subst_2086_, v_e_2087_, v_deBruijnIndex_2093_, v_offset_2088_, v_a_2089_, v_a_2090_, v_a_2091_, v_a_2092_);
lean_dec(v_offset_2088_);
lean_dec(v_deBruijnIndex_2093_);
return v___x_2094_;
}
case 5:
{
lean_object* v_fn_2095_; lean_object* v_arg_2096_; lean_object* v___x_2097_; 
v_fn_2095_ = lean_ctor_get(v_e_2087_, 0);
lean_inc_ref(v_fn_2095_);
v_arg_2096_ = lean_ctor_get(v_e_2087_, 1);
lean_inc_ref(v_arg_2096_);
v___x_2097_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg(v_subst_2086_, v_e_2087_, v_fn_2095_, v_arg_2096_, v_offset_2088_, v_a_2089_, v_a_2090_, v_a_2091_, v_a_2092_);
return v___x_2097_;
}
case 6:
{
lean_object* v_binderName_2098_; lean_object* v_binderType_2099_; lean_object* v_body_2100_; uint8_t v_binderInfo_2101_; lean_object* v___x_2102_; 
v_binderName_2098_ = lean_ctor_get(v_e_2087_, 0);
v_binderType_2099_ = lean_ctor_get(v_e_2087_, 1);
v_body_2100_ = lean_ctor_get(v_e_2087_, 2);
v_binderInfo_2101_ = lean_ctor_get_uint8(v_e_2087_, sizeof(void*)*3 + 8);
lean_inc(v_offset_2088_);
lean_inc_ref(v_binderType_2099_);
v___x_2102_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_2086_, v_binderType_2099_, v_offset_2088_, v_a_2089_, v_a_2090_, v_a_2091_, v_a_2092_);
if (lean_obj_tag(v___x_2102_) == 0)
{
lean_object* v_a_2103_; lean_object* v_a_2104_; lean_object* v_fst_2105_; lean_object* v_snd_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; 
v_a_2103_ = lean_ctor_get(v___x_2102_, 0);
lean_inc(v_a_2103_);
v_a_2104_ = lean_ctor_get(v___x_2102_, 1);
lean_inc(v_a_2104_);
lean_dec_ref_known(v___x_2102_, 2);
v_fst_2105_ = lean_ctor_get(v_a_2103_, 0);
lean_inc(v_fst_2105_);
v_snd_2106_ = lean_ctor_get(v_a_2103_, 1);
lean_inc(v_snd_2106_);
lean_dec(v_a_2103_);
v___x_2107_ = lean_unsigned_to_nat(1u);
v___x_2108_ = lean_nat_add(v_offset_2088_, v___x_2107_);
lean_dec(v_offset_2088_);
lean_inc_ref(v_body_2100_);
v___x_2109_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_2086_, v_body_2100_, v___x_2108_, v_snd_2106_, v_a_2090_, v_a_2091_, v_a_2104_);
if (lean_obj_tag(v___x_2109_) == 0)
{
lean_object* v_a_2110_; lean_object* v_a_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2135_; 
v_a_2110_ = lean_ctor_get(v___x_2109_, 0);
v_a_2111_ = lean_ctor_get(v___x_2109_, 1);
v_isSharedCheck_2135_ = !lean_is_exclusive(v___x_2109_);
if (v_isSharedCheck_2135_ == 0)
{
v___x_2113_ = v___x_2109_;
v_isShared_2114_ = v_isSharedCheck_2135_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_a_2111_);
lean_inc(v_a_2110_);
lean_dec(v___x_2109_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2135_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v_fst_2115_; lean_object* v_snd_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2134_; 
v_fst_2115_ = lean_ctor_get(v_a_2110_, 0);
v_snd_2116_ = lean_ctor_get(v_a_2110_, 1);
v_isSharedCheck_2134_ = !lean_is_exclusive(v_a_2110_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2118_ = v_a_2110_;
v_isShared_2119_ = v_isSharedCheck_2134_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_snd_2116_);
lean_inc(v_fst_2115_);
lean_dec(v_a_2110_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2134_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
size_t v___x_2120_; size_t v___x_2121_; uint8_t v___x_2122_; 
v___x_2120_ = lean_ptr_addr(v_binderType_2099_);
v___x_2121_ = lean_ptr_addr(v_fst_2105_);
v___x_2122_ = lean_usize_dec_eq(v___x_2120_, v___x_2121_);
if (v___x_2122_ == 0)
{
lean_object* v___x_2123_; 
lean_inc(v_binderName_2098_);
lean_del_object(v___x_2118_);
lean_del_object(v___x_2113_);
lean_dec_ref_known(v_e_2087_, 3);
v___x_2123_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__3(v_binderName_2098_, v_binderInfo_2101_, v_fst_2105_, v_fst_2115_, v_snd_2116_, v_a_2090_, v_a_2091_, v_a_2111_);
return v___x_2123_;
}
else
{
size_t v___x_2124_; size_t v___x_2125_; uint8_t v___x_2126_; 
v___x_2124_ = lean_ptr_addr(v_body_2100_);
v___x_2125_ = lean_ptr_addr(v_fst_2115_);
v___x_2126_ = lean_usize_dec_eq(v___x_2124_, v___x_2125_);
if (v___x_2126_ == 0)
{
lean_object* v___x_2127_; 
lean_inc(v_binderName_2098_);
lean_del_object(v___x_2118_);
lean_del_object(v___x_2113_);
lean_dec_ref_known(v_e_2087_, 3);
v___x_2127_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__3(v_binderName_2098_, v_binderInfo_2101_, v_fst_2105_, v_fst_2115_, v_snd_2116_, v_a_2090_, v_a_2091_, v_a_2111_);
return v___x_2127_;
}
else
{
lean_object* v___x_2129_; 
lean_dec(v_fst_2115_);
lean_dec(v_fst_2105_);
if (v_isShared_2119_ == 0)
{
lean_ctor_set(v___x_2118_, 0, v_e_2087_);
v___x_2129_ = v___x_2118_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_e_2087_);
lean_ctor_set(v_reuseFailAlloc_2133_, 1, v_snd_2116_);
v___x_2129_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
lean_object* v___x_2131_; 
if (v_isShared_2114_ == 0)
{
lean_ctor_set(v___x_2113_, 0, v___x_2129_);
v___x_2131_ = v___x_2113_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v___x_2129_);
lean_ctor_set(v_reuseFailAlloc_2132_, 1, v_a_2111_);
v___x_2131_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
return v___x_2131_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_2105_);
lean_dec_ref_known(v_e_2087_, 3);
return v___x_2109_;
}
}
else
{
lean_dec_ref_known(v_e_2087_, 3);
lean_dec(v_offset_2088_);
return v___x_2102_;
}
}
case 7:
{
lean_object* v_binderName_2136_; lean_object* v_binderType_2137_; lean_object* v_body_2138_; uint8_t v_binderInfo_2139_; lean_object* v___x_2140_; 
v_binderName_2136_ = lean_ctor_get(v_e_2087_, 0);
v_binderType_2137_ = lean_ctor_get(v_e_2087_, 1);
v_body_2138_ = lean_ctor_get(v_e_2087_, 2);
v_binderInfo_2139_ = lean_ctor_get_uint8(v_e_2087_, sizeof(void*)*3 + 8);
lean_inc(v_offset_2088_);
lean_inc_ref(v_binderType_2137_);
v___x_2140_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_2086_, v_binderType_2137_, v_offset_2088_, v_a_2089_, v_a_2090_, v_a_2091_, v_a_2092_);
if (lean_obj_tag(v___x_2140_) == 0)
{
lean_object* v_a_2141_; lean_object* v_a_2142_; lean_object* v_fst_2143_; lean_object* v_snd_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; 
v_a_2141_ = lean_ctor_get(v___x_2140_, 0);
lean_inc(v_a_2141_);
v_a_2142_ = lean_ctor_get(v___x_2140_, 1);
lean_inc(v_a_2142_);
lean_dec_ref_known(v___x_2140_, 2);
v_fst_2143_ = lean_ctor_get(v_a_2141_, 0);
lean_inc(v_fst_2143_);
v_snd_2144_ = lean_ctor_get(v_a_2141_, 1);
lean_inc(v_snd_2144_);
lean_dec(v_a_2141_);
v___x_2145_ = lean_unsigned_to_nat(1u);
v___x_2146_ = lean_nat_add(v_offset_2088_, v___x_2145_);
lean_dec(v_offset_2088_);
lean_inc_ref(v_body_2138_);
v___x_2147_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_2086_, v_body_2138_, v___x_2146_, v_snd_2144_, v_a_2090_, v_a_2091_, v_a_2142_);
if (lean_obj_tag(v___x_2147_) == 0)
{
lean_object* v_a_2148_; lean_object* v_a_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2173_; 
v_a_2148_ = lean_ctor_get(v___x_2147_, 0);
v_a_2149_ = lean_ctor_get(v___x_2147_, 1);
v_isSharedCheck_2173_ = !lean_is_exclusive(v___x_2147_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2151_ = v___x_2147_;
v_isShared_2152_ = v_isSharedCheck_2173_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_a_2149_);
lean_inc(v_a_2148_);
lean_dec(v___x_2147_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2173_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v_fst_2153_; lean_object* v_snd_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2172_; 
v_fst_2153_ = lean_ctor_get(v_a_2148_, 0);
v_snd_2154_ = lean_ctor_get(v_a_2148_, 1);
v_isSharedCheck_2172_ = !lean_is_exclusive(v_a_2148_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2156_ = v_a_2148_;
v_isShared_2157_ = v_isSharedCheck_2172_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_snd_2154_);
lean_inc(v_fst_2153_);
lean_dec(v_a_2148_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2172_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
size_t v___x_2158_; size_t v___x_2159_; uint8_t v___x_2160_; 
v___x_2158_ = lean_ptr_addr(v_binderType_2137_);
v___x_2159_ = lean_ptr_addr(v_fst_2143_);
v___x_2160_ = lean_usize_dec_eq(v___x_2158_, v___x_2159_);
if (v___x_2160_ == 0)
{
lean_object* v___x_2161_; 
lean_inc(v_binderName_2136_);
lean_del_object(v___x_2156_);
lean_del_object(v___x_2151_);
lean_dec_ref_known(v_e_2087_, 3);
v___x_2161_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__4(v_binderName_2136_, v_binderInfo_2139_, v_fst_2143_, v_fst_2153_, v_snd_2154_, v_a_2090_, v_a_2091_, v_a_2149_);
return v___x_2161_;
}
else
{
size_t v___x_2162_; size_t v___x_2163_; uint8_t v___x_2164_; 
v___x_2162_ = lean_ptr_addr(v_body_2138_);
v___x_2163_ = lean_ptr_addr(v_fst_2153_);
v___x_2164_ = lean_usize_dec_eq(v___x_2162_, v___x_2163_);
if (v___x_2164_ == 0)
{
lean_object* v___x_2165_; 
lean_inc(v_binderName_2136_);
lean_del_object(v___x_2156_);
lean_del_object(v___x_2151_);
lean_dec_ref_known(v_e_2087_, 3);
v___x_2165_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__4(v_binderName_2136_, v_binderInfo_2139_, v_fst_2143_, v_fst_2153_, v_snd_2154_, v_a_2090_, v_a_2091_, v_a_2149_);
return v___x_2165_;
}
else
{
lean_object* v___x_2167_; 
lean_dec(v_fst_2153_);
lean_dec(v_fst_2143_);
if (v_isShared_2157_ == 0)
{
lean_ctor_set(v___x_2156_, 0, v_e_2087_);
v___x_2167_ = v___x_2156_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v_e_2087_);
lean_ctor_set(v_reuseFailAlloc_2171_, 1, v_snd_2154_);
v___x_2167_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
lean_object* v___x_2169_; 
if (v_isShared_2152_ == 0)
{
lean_ctor_set(v___x_2151_, 0, v___x_2167_);
v___x_2169_ = v___x_2151_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v___x_2167_);
lean_ctor_set(v_reuseFailAlloc_2170_, 1, v_a_2149_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
return v___x_2169_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_2143_);
lean_dec_ref_known(v_e_2087_, 3);
return v___x_2147_;
}
}
else
{
lean_dec_ref_known(v_e_2087_, 3);
lean_dec(v_offset_2088_);
return v___x_2140_;
}
}
case 8:
{
lean_object* v_declName_2174_; lean_object* v_type_2175_; lean_object* v_value_2176_; lean_object* v_body_2177_; uint8_t v_nondep_2178_; lean_object* v___x_2179_; 
v_declName_2174_ = lean_ctor_get(v_e_2087_, 0);
v_type_2175_ = lean_ctor_get(v_e_2087_, 1);
v_value_2176_ = lean_ctor_get(v_e_2087_, 2);
v_body_2177_ = lean_ctor_get(v_e_2087_, 3);
v_nondep_2178_ = lean_ctor_get_uint8(v_e_2087_, sizeof(void*)*4 + 8);
lean_inc(v_offset_2088_);
lean_inc_ref(v_type_2175_);
v___x_2179_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_2086_, v_type_2175_, v_offset_2088_, v_a_2089_, v_a_2090_, v_a_2091_, v_a_2092_);
if (lean_obj_tag(v___x_2179_) == 0)
{
lean_object* v_a_2180_; lean_object* v_a_2181_; lean_object* v_fst_2182_; lean_object* v_snd_2183_; lean_object* v___x_2184_; 
v_a_2180_ = lean_ctor_get(v___x_2179_, 0);
lean_inc(v_a_2180_);
v_a_2181_ = lean_ctor_get(v___x_2179_, 1);
lean_inc(v_a_2181_);
lean_dec_ref_known(v___x_2179_, 2);
v_fst_2182_ = lean_ctor_get(v_a_2180_, 0);
lean_inc(v_fst_2182_);
v_snd_2183_ = lean_ctor_get(v_a_2180_, 1);
lean_inc(v_snd_2183_);
lean_dec(v_a_2180_);
lean_inc(v_offset_2088_);
lean_inc_ref(v_value_2176_);
v___x_2184_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_2086_, v_value_2176_, v_offset_2088_, v_snd_2183_, v_a_2090_, v_a_2091_, v_a_2181_);
if (lean_obj_tag(v___x_2184_) == 0)
{
lean_object* v_a_2185_; lean_object* v_a_2186_; lean_object* v_fst_2187_; lean_object* v_snd_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; 
v_a_2185_ = lean_ctor_get(v___x_2184_, 0);
lean_inc(v_a_2185_);
v_a_2186_ = lean_ctor_get(v___x_2184_, 1);
lean_inc(v_a_2186_);
lean_dec_ref_known(v___x_2184_, 2);
v_fst_2187_ = lean_ctor_get(v_a_2185_, 0);
lean_inc(v_fst_2187_);
v_snd_2188_ = lean_ctor_get(v_a_2185_, 1);
lean_inc(v_snd_2188_);
lean_dec(v_a_2185_);
v___x_2189_ = lean_unsigned_to_nat(1u);
v___x_2190_ = lean_nat_add(v_offset_2088_, v___x_2189_);
lean_dec(v_offset_2088_);
lean_inc_ref(v_body_2177_);
v___x_2191_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_2086_, v_body_2177_, v___x_2190_, v_snd_2188_, v_a_2090_, v_a_2091_, v_a_2186_);
if (lean_obj_tag(v___x_2191_) == 0)
{
lean_object* v_a_2192_; lean_object* v_a_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2221_; 
v_a_2192_ = lean_ctor_get(v___x_2191_, 0);
v_a_2193_ = lean_ctor_get(v___x_2191_, 1);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2191_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2195_ = v___x_2191_;
v_isShared_2196_ = v_isSharedCheck_2221_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_a_2193_);
lean_inc(v_a_2192_);
lean_dec(v___x_2191_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2221_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
lean_object* v_fst_2197_; lean_object* v_snd_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2220_; 
v_fst_2197_ = lean_ctor_get(v_a_2192_, 0);
v_snd_2198_ = lean_ctor_get(v_a_2192_, 1);
v_isSharedCheck_2220_ = !lean_is_exclusive(v_a_2192_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2200_ = v_a_2192_;
v_isShared_2201_ = v_isSharedCheck_2220_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_snd_2198_);
lean_inc(v_fst_2197_);
lean_dec(v_a_2192_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2220_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
size_t v___x_2202_; size_t v___x_2203_; uint8_t v___x_2204_; 
v___x_2202_ = lean_ptr_addr(v_type_2175_);
v___x_2203_ = lean_ptr_addr(v_fst_2182_);
v___x_2204_ = lean_usize_dec_eq(v___x_2202_, v___x_2203_);
if (v___x_2204_ == 0)
{
lean_object* v___x_2205_; 
lean_inc(v_declName_2174_);
lean_del_object(v___x_2200_);
lean_del_object(v___x_2195_);
lean_dec_ref_known(v_e_2087_, 4);
v___x_2205_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__5(v_declName_2174_, v_fst_2182_, v_fst_2187_, v_fst_2197_, v_nondep_2178_, v_snd_2198_, v_a_2090_, v_a_2091_, v_a_2193_);
return v___x_2205_;
}
else
{
size_t v___x_2206_; size_t v___x_2207_; uint8_t v___x_2208_; 
v___x_2206_ = lean_ptr_addr(v_value_2176_);
v___x_2207_ = lean_ptr_addr(v_fst_2187_);
v___x_2208_ = lean_usize_dec_eq(v___x_2206_, v___x_2207_);
if (v___x_2208_ == 0)
{
lean_object* v___x_2209_; 
lean_inc(v_declName_2174_);
lean_del_object(v___x_2200_);
lean_del_object(v___x_2195_);
lean_dec_ref_known(v_e_2087_, 4);
v___x_2209_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__5(v_declName_2174_, v_fst_2182_, v_fst_2187_, v_fst_2197_, v_nondep_2178_, v_snd_2198_, v_a_2090_, v_a_2091_, v_a_2193_);
return v___x_2209_;
}
else
{
size_t v___x_2210_; size_t v___x_2211_; uint8_t v___x_2212_; 
v___x_2210_ = lean_ptr_addr(v_body_2177_);
v___x_2211_ = lean_ptr_addr(v_fst_2197_);
v___x_2212_ = lean_usize_dec_eq(v___x_2210_, v___x_2211_);
if (v___x_2212_ == 0)
{
lean_object* v___x_2213_; 
lean_inc(v_declName_2174_);
lean_del_object(v___x_2200_);
lean_del_object(v___x_2195_);
lean_dec_ref_known(v_e_2087_, 4);
v___x_2213_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__5(v_declName_2174_, v_fst_2182_, v_fst_2187_, v_fst_2197_, v_nondep_2178_, v_snd_2198_, v_a_2090_, v_a_2091_, v_a_2193_);
return v___x_2213_;
}
else
{
lean_object* v___x_2215_; 
lean_dec(v_fst_2197_);
lean_dec(v_fst_2187_);
lean_dec(v_fst_2182_);
if (v_isShared_2201_ == 0)
{
lean_ctor_set(v___x_2200_, 0, v_e_2087_);
v___x_2215_ = v___x_2200_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v_e_2087_);
lean_ctor_set(v_reuseFailAlloc_2219_, 1, v_snd_2198_);
v___x_2215_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
lean_object* v___x_2217_; 
if (v_isShared_2196_ == 0)
{
lean_ctor_set(v___x_2195_, 0, v___x_2215_);
v___x_2217_ = v___x_2195_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v___x_2215_);
lean_ctor_set(v_reuseFailAlloc_2218_, 1, v_a_2193_);
v___x_2217_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
return v___x_2217_;
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
lean_dec(v_fst_2187_);
lean_dec(v_fst_2182_);
lean_dec_ref_known(v_e_2087_, 4);
return v___x_2191_;
}
}
else
{
lean_dec(v_fst_2182_);
lean_dec_ref_known(v_e_2087_, 4);
lean_dec(v_offset_2088_);
return v___x_2184_;
}
}
else
{
lean_dec_ref_known(v_e_2087_, 4);
lean_dec(v_offset_2088_);
return v___x_2179_;
}
}
case 10:
{
lean_object* v_data_2222_; lean_object* v_expr_2223_; lean_object* v___x_2224_; 
v_data_2222_ = lean_ctor_get(v_e_2087_, 0);
v_expr_2223_ = lean_ctor_get(v_e_2087_, 1);
lean_inc_ref(v_expr_2223_);
v___x_2224_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_2086_, v_expr_2223_, v_offset_2088_, v_a_2089_, v_a_2090_, v_a_2091_, v_a_2092_);
if (lean_obj_tag(v___x_2224_) == 0)
{
lean_object* v_a_2225_; lean_object* v_a_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2246_; 
v_a_2225_ = lean_ctor_get(v___x_2224_, 0);
v_a_2226_ = lean_ctor_get(v___x_2224_, 1);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2224_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2228_ = v___x_2224_;
v_isShared_2229_ = v_isSharedCheck_2246_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_a_2226_);
lean_inc(v_a_2225_);
lean_dec(v___x_2224_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2246_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
lean_object* v_fst_2230_; lean_object* v_snd_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2245_; 
v_fst_2230_ = lean_ctor_get(v_a_2225_, 0);
v_snd_2231_ = lean_ctor_get(v_a_2225_, 1);
v_isSharedCheck_2245_ = !lean_is_exclusive(v_a_2225_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2233_ = v_a_2225_;
v_isShared_2234_ = v_isSharedCheck_2245_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_snd_2231_);
lean_inc(v_fst_2230_);
lean_dec(v_a_2225_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2245_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
size_t v___x_2235_; size_t v___x_2236_; uint8_t v___x_2237_; 
v___x_2235_ = lean_ptr_addr(v_expr_2223_);
v___x_2236_ = lean_ptr_addr(v_fst_2230_);
v___x_2237_ = lean_usize_dec_eq(v___x_2235_, v___x_2236_);
if (v___x_2237_ == 0)
{
lean_object* v___x_2238_; 
lean_inc(v_data_2222_);
lean_del_object(v___x_2233_);
lean_del_object(v___x_2228_);
lean_dec_ref_known(v_e_2087_, 2);
v___x_2238_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__6(v_data_2222_, v_fst_2230_, v_snd_2231_, v_a_2090_, v_a_2091_, v_a_2226_);
return v___x_2238_;
}
else
{
lean_object* v___x_2240_; 
lean_dec(v_fst_2230_);
if (v_isShared_2234_ == 0)
{
lean_ctor_set(v___x_2233_, 0, v_e_2087_);
v___x_2240_ = v___x_2233_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_e_2087_);
lean_ctor_set(v_reuseFailAlloc_2244_, 1, v_snd_2231_);
v___x_2240_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
lean_object* v___x_2242_; 
if (v_isShared_2229_ == 0)
{
lean_ctor_set(v___x_2228_, 0, v___x_2240_);
v___x_2242_ = v___x_2228_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v___x_2240_);
lean_ctor_set(v_reuseFailAlloc_2243_, 1, v_a_2226_);
v___x_2242_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
return v___x_2242_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2087_, 2);
return v___x_2224_;
}
}
case 11:
{
lean_object* v_typeName_2247_; lean_object* v_idx_2248_; lean_object* v_struct_2249_; lean_object* v___x_2250_; 
v_typeName_2247_ = lean_ctor_get(v_e_2087_, 0);
v_idx_2248_ = lean_ctor_get(v_e_2087_, 1);
v_struct_2249_ = lean_ctor_get(v_e_2087_, 2);
lean_inc_ref(v_struct_2249_);
v___x_2250_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_2086_, v_struct_2249_, v_offset_2088_, v_a_2089_, v_a_2090_, v_a_2091_, v_a_2092_);
if (lean_obj_tag(v___x_2250_) == 0)
{
lean_object* v_a_2251_; lean_object* v_a_2252_; lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2272_; 
v_a_2251_ = lean_ctor_get(v___x_2250_, 0);
v_a_2252_ = lean_ctor_get(v___x_2250_, 1);
v_isSharedCheck_2272_ = !lean_is_exclusive(v___x_2250_);
if (v_isSharedCheck_2272_ == 0)
{
v___x_2254_ = v___x_2250_;
v_isShared_2255_ = v_isSharedCheck_2272_;
goto v_resetjp_2253_;
}
else
{
lean_inc(v_a_2252_);
lean_inc(v_a_2251_);
lean_dec(v___x_2250_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2272_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
lean_object* v_fst_2256_; lean_object* v_snd_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2271_; 
v_fst_2256_ = lean_ctor_get(v_a_2251_, 0);
v_snd_2257_ = lean_ctor_get(v_a_2251_, 1);
v_isSharedCheck_2271_ = !lean_is_exclusive(v_a_2251_);
if (v_isSharedCheck_2271_ == 0)
{
v___x_2259_ = v_a_2251_;
v_isShared_2260_ = v_isSharedCheck_2271_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_snd_2257_);
lean_inc(v_fst_2256_);
lean_dec(v_a_2251_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2271_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
size_t v___x_2261_; size_t v___x_2262_; uint8_t v___x_2263_; 
v___x_2261_ = lean_ptr_addr(v_struct_2249_);
v___x_2262_ = lean_ptr_addr(v_fst_2256_);
v___x_2263_ = lean_usize_dec_eq(v___x_2261_, v___x_2262_);
if (v___x_2263_ == 0)
{
lean_object* v___x_2264_; 
lean_inc(v_idx_2248_);
lean_inc(v_typeName_2247_);
lean_del_object(v___x_2259_);
lean_del_object(v___x_2254_);
lean_dec_ref_known(v_e_2087_, 3);
v___x_2264_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__7(v_typeName_2247_, v_idx_2248_, v_fst_2256_, v_snd_2257_, v_a_2090_, v_a_2091_, v_a_2252_);
return v___x_2264_;
}
else
{
lean_object* v___x_2266_; 
lean_dec(v_fst_2256_);
if (v_isShared_2260_ == 0)
{
lean_ctor_set(v___x_2259_, 0, v_e_2087_);
v___x_2266_ = v___x_2259_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v_e_2087_);
lean_ctor_set(v_reuseFailAlloc_2270_, 1, v_snd_2257_);
v___x_2266_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
lean_object* v___x_2268_; 
if (v_isShared_2255_ == 0)
{
lean_ctor_set(v___x_2254_, 0, v___x_2266_);
v___x_2268_ = v___x_2254_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v___x_2266_);
lean_ctor_set(v_reuseFailAlloc_2269_, 1, v_a_2252_);
v___x_2268_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
return v___x_2268_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2087_, 3);
return v___x_2250_;
}
}
default: 
{
lean_object* v___x_2273_; lean_object* v___x_2274_; 
lean_dec(v_offset_2088_);
lean_dec_ref(v_e_2087_);
v___x_2273_ = lean_obj_once(&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__1, &l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__1_once, _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__1);
v___x_2274_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8(v___x_2273_, v_a_2089_, v_a_2090_, v_a_2091_, v_a_2092_);
return v___x_2274_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(lean_object* v_subst_2275_, lean_object* v_e_2276_, lean_object* v_offset_2277_, lean_object* v_a_2278_, uint8_t v_a_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_){
_start:
{
lean_object* v___x_2282_; uint8_t v___x_2283_; 
v___x_2282_ = l_Lean_Expr_looseBVarRange(v_e_2276_);
v___x_2283_ = lean_nat_dec_le(v___x_2282_, v_offset_2277_);
lean_dec(v___x_2282_);
if (v___x_2283_ == 0)
{
lean_object* v_key_2284_; lean_object* v___x_2285_; 
lean_inc(v_offset_2277_);
lean_inc_ref(v_e_2276_);
v_key_2284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_2284_, 0, v_e_2276_);
lean_ctor_set(v_key_2284_, 1, v_offset_2277_);
v___x_2285_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3___redArg(v_a_2278_, v_key_2284_);
if (lean_obj_tag(v___x_2285_) == 1)
{
lean_object* v_val_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; 
lean_dec_ref_known(v_key_2284_, 2);
lean_dec(v_offset_2277_);
lean_dec_ref(v_e_2276_);
v_val_2286_ = lean_ctor_get(v___x_2285_, 0);
lean_inc(v_val_2286_);
lean_dec_ref_known(v___x_2285_, 1);
v___x_2287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2287_, 0, v_val_2286_);
lean_ctor_set(v___x_2287_, 1, v_a_2278_);
v___x_2288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2288_, 0, v___x_2287_);
lean_ctor_set(v___x_2288_, 1, v_a_2281_);
return v___x_2288_;
}
else
{
lean_dec(v___x_2285_);
switch(lean_obj_tag(v_e_2276_))
{
case 0:
{
lean_object* v_deBruijnIndex_2289_; lean_object* v___x_2290_; 
v_deBruijnIndex_2289_ = lean_ctor_get(v_e_2276_, 0);
lean_inc(v_deBruijnIndex_2289_);
v___x_2290_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(v_subst_2275_, v_e_2276_, v_deBruijnIndex_2289_, v_offset_2277_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_);
lean_dec(v_offset_2277_);
lean_dec(v_deBruijnIndex_2289_);
if (lean_obj_tag(v___x_2290_) == 0)
{
lean_object* v_a_2291_; lean_object* v_a_2292_; lean_object* v_fst_2293_; lean_object* v_snd_2294_; lean_object* v___x_2295_; 
v_a_2291_ = lean_ctor_get(v___x_2290_, 0);
lean_inc(v_a_2291_);
v_a_2292_ = lean_ctor_get(v___x_2290_, 1);
lean_inc(v_a_2292_);
lean_dec_ref_known(v___x_2290_, 2);
v_fst_2293_ = lean_ctor_get(v_a_2291_, 0);
lean_inc(v_fst_2293_);
v_snd_2294_ = lean_ctor_get(v_a_2291_, 1);
lean_inc(v_snd_2294_);
lean_dec(v_a_2291_);
v___x_2295_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_2284_, v_fst_2293_, v_snd_2294_, v_a_2292_);
return v___x_2295_;
}
else
{
lean_dec_ref_known(v_key_2284_, 2);
return v___x_2290_;
}
}
case 9:
{
lean_object* v___x_2296_; 
lean_dec(v_offset_2277_);
v___x_2296_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_2284_, v_e_2276_, v_a_2278_, v_a_2281_);
return v___x_2296_;
}
case 2:
{
lean_object* v___x_2297_; 
lean_dec(v_offset_2277_);
v___x_2297_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_2284_, v_e_2276_, v_a_2278_, v_a_2281_);
return v___x_2297_;
}
case 1:
{
lean_object* v___x_2298_; 
lean_dec(v_offset_2277_);
v___x_2298_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_2284_, v_e_2276_, v_a_2278_, v_a_2281_);
return v___x_2298_;
}
case 4:
{
lean_object* v___x_2299_; 
lean_dec(v_offset_2277_);
v___x_2299_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_2284_, v_e_2276_, v_a_2278_, v_a_2281_);
return v___x_2299_;
}
case 3:
{
lean_object* v___x_2300_; 
lean_dec(v_offset_2277_);
v___x_2300_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_2284_, v_e_2276_, v_a_2278_, v_a_2281_);
return v___x_2300_;
}
default: 
{
lean_object* v___x_2301_; 
v___x_2301_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit(v_subst_2275_, v_e_2276_, v_offset_2277_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_);
if (lean_obj_tag(v___x_2301_) == 0)
{
lean_object* v_a_2302_; lean_object* v_a_2303_; lean_object* v_fst_2304_; lean_object* v_snd_2305_; lean_object* v___x_2306_; 
v_a_2302_ = lean_ctor_get(v___x_2301_, 0);
lean_inc(v_a_2302_);
v_a_2303_ = lean_ctor_get(v___x_2301_, 1);
lean_inc(v_a_2303_);
lean_dec_ref_known(v___x_2301_, 2);
v_fst_2304_ = lean_ctor_get(v_a_2302_, 0);
lean_inc(v_fst_2304_);
v_snd_2305_ = lean_ctor_get(v_a_2302_, 1);
lean_inc(v_snd_2305_);
lean_dec(v_a_2302_);
v___x_2306_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_2284_, v_fst_2304_, v_snd_2305_, v_a_2303_);
return v___x_2306_;
}
else
{
lean_dec_ref_known(v_key_2284_, 2);
return v___x_2301_;
}
}
}
}
}
else
{
lean_object* v___x_2307_; lean_object* v___x_2308_; 
lean_dec(v_offset_2277_);
v___x_2307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2307_, 0, v_e_2276_);
lean_ctor_set(v___x_2307_, 1, v_a_2278_);
v___x_2308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2308_, 0, v___x_2307_);
lean_ctor_set(v___x_2308_, 1, v_a_2281_);
return v___x_2308_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild___boxed(lean_object* v_subst_2309_, lean_object* v_e_2310_, lean_object* v_offset_2311_, lean_object* v_a_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_){
_start:
{
uint8_t v_a_boxed_2316_; lean_object* v_res_2317_; 
v_a_boxed_2316_ = lean_unbox(v_a_2313_);
v_res_2317_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_2309_, v_e_2310_, v_offset_2311_, v_a_2312_, v_a_boxed_2316_, v_a_2314_, v_a_2315_);
lean_dec_ref(v_a_2314_);
lean_dec_ref(v_subst_2309_);
return v_res_2317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault___boxed(lean_object* v_subst_2318_, lean_object* v_e_2319_, lean_object* v_offset_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_){
_start:
{
uint8_t v_a_boxed_2325_; lean_object* v_res_2326_; 
v_a_boxed_2325_ = lean_unbox(v_a_2322_);
v_res_2326_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault(v_subst_2318_, v_e_2319_, v_offset_2320_, v_a_2321_, v_a_boxed_2325_, v_a_2323_, v_a_2324_);
lean_dec_ref(v_a_2323_);
lean_dec_ref(v_subst_2318_);
return v_res_2326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___boxed(lean_object* v_subst_2327_, lean_object* v_e_2328_, lean_object* v_f_2329_, lean_object* v_arg_2330_, lean_object* v_offset_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_){
_start:
{
uint8_t v_a_boxed_2336_; lean_object* v_res_2337_; 
v_a_boxed_2336_ = lean_unbox(v_a_2333_);
v_res_2337_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg(v_subst_2327_, v_e_2328_, v_f_2329_, v_arg_2330_, v_offset_2331_, v_a_2332_, v_a_boxed_2336_, v_a_2334_, v_a_2335_);
lean_dec_ref(v_a_2334_);
lean_dec_ref(v_subst_2327_);
return v_res_2337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___boxed(lean_object* v_subst_2338_, lean_object* v_e_2339_, lean_object* v_f_2340_, lean_object* v_argsRev_2341_, lean_object* v_offset_2342_, lean_object* v_modified_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_){
_start:
{
uint8_t v_modified_boxed_2348_; uint8_t v_a_boxed_2349_; lean_object* v_res_2350_; 
v_modified_boxed_2348_ = lean_unbox(v_modified_2343_);
v_a_boxed_2349_ = lean_unbox(v_a_2345_);
v_res_2350_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta(v_subst_2338_, v_e_2339_, v_f_2340_, v_argsRev_2341_, v_offset_2342_, v_modified_boxed_2348_, v_a_2344_, v_a_boxed_2349_, v_a_2346_, v_a_2347_);
lean_dec_ref(v_a_2346_);
lean_dec_ref(v_subst_2338_);
return v_res_2350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___boxed(lean_object* v_subst_2351_, lean_object* v_e_2352_, lean_object* v_offset_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_){
_start:
{
uint8_t v_a_boxed_2358_; lean_object* v_res_2359_; 
v_a_boxed_2358_ = lean_unbox(v_a_2355_);
v_res_2359_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit(v_subst_2351_, v_e_2352_, v_offset_2353_, v_a_2354_, v_a_boxed_2358_, v_a_2356_, v_a_2357_);
lean_dec_ref(v_a_2356_);
lean_dec_ref(v_subst_2351_);
return v_res_2359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp(lean_object* v_subst_2360_, lean_object* v_e_2361_, lean_object* v_f_2362_, lean_object* v_arg_2363_, lean_object* v_offset_2364_, lean_object* v_x_2365_, lean_object* v_a_2366_, uint8_t v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_){
_start:
{
lean_object* v___x_2370_; 
v___x_2370_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg(v_subst_2360_, v_e_2361_, v_f_2362_, v_arg_2363_, v_offset_2364_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_);
return v___x_2370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___boxed(lean_object* v_subst_2371_, lean_object* v_e_2372_, lean_object* v_f_2373_, lean_object* v_arg_2374_, lean_object* v_offset_2375_, lean_object* v_x_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_){
_start:
{
uint8_t v_a_boxed_2381_; lean_object* v_res_2382_; 
v_a_boxed_2381_ = lean_unbox(v_a_2378_);
v_res_2382_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp(v_subst_2371_, v_e_2372_, v_f_2373_, v_arg_2374_, v_offset_2375_, v_x_2376_, v_a_2377_, v_a_boxed_2381_, v_a_2379_, v_a_2380_);
lean_dec_ref(v_a_2379_);
lean_dec_ref(v_subst_2371_);
return v_res_2382_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27(lean_object* v_e_2383_, lean_object* v_subst_2384_, uint8_t v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_){
_start:
{
lean_object* v___x_2388_; lean_object* v___x_2389_; uint8_t v___x_2390_; 
v___x_2388_ = lean_array_get_size(v_subst_2384_);
v___x_2389_ = lean_unsigned_to_nat(0u);
v___x_2390_ = lean_nat_dec_eq(v___x_2388_, v___x_2389_);
if (v___x_2390_ == 0)
{
uint8_t v___x_2391_; 
v___x_2391_ = l_Lean_Expr_hasLooseBVars(v_e_2383_);
if (v___x_2391_ == 0)
{
lean_object* v___x_2392_; 
v___x_2392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2392_, 0, v_e_2383_);
lean_ctor_set(v___x_2392_, 1, v_a_2387_);
return v___x_2392_;
}
else
{
lean_object* v___x_2393_; lean_object* v___x_2394_; 
v___x_2393_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__1, &l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__1_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__1);
v___x_2394_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit(v_subst_2384_, v_e_2383_, v___x_2389_, v___x_2393_, v_a_2385_, v_a_2386_, v_a_2387_);
if (lean_obj_tag(v___x_2394_) == 0)
{
lean_object* v_a_2395_; lean_object* v_a_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2404_; 
v_a_2395_ = lean_ctor_get(v___x_2394_, 0);
v_a_2396_ = lean_ctor_get(v___x_2394_, 1);
v_isSharedCheck_2404_ = !lean_is_exclusive(v___x_2394_);
if (v_isSharedCheck_2404_ == 0)
{
v___x_2398_ = v___x_2394_;
v_isShared_2399_ = v_isSharedCheck_2404_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_a_2396_);
lean_inc(v_a_2395_);
lean_dec(v___x_2394_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2404_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
lean_object* v_fst_2400_; lean_object* v___x_2402_; 
v_fst_2400_ = lean_ctor_get(v_a_2395_, 0);
lean_inc(v_fst_2400_);
lean_dec(v_a_2395_);
if (v_isShared_2399_ == 0)
{
lean_ctor_set(v___x_2398_, 0, v_fst_2400_);
v___x_2402_ = v___x_2398_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v_fst_2400_);
lean_ctor_set(v_reuseFailAlloc_2403_, 1, v_a_2396_);
v___x_2402_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2401_;
}
v_reusejp_2401_:
{
return v___x_2402_;
}
}
}
else
{
lean_object* v_a_2405_; lean_object* v_a_2406_; lean_object* v___x_2408_; uint8_t v_isShared_2409_; uint8_t v_isSharedCheck_2413_; 
v_a_2405_ = lean_ctor_get(v___x_2394_, 0);
v_a_2406_ = lean_ctor_get(v___x_2394_, 1);
v_isSharedCheck_2413_ = !lean_is_exclusive(v___x_2394_);
if (v_isSharedCheck_2413_ == 0)
{
v___x_2408_ = v___x_2394_;
v_isShared_2409_ = v_isSharedCheck_2413_;
goto v_resetjp_2407_;
}
else
{
lean_inc(v_a_2406_);
lean_inc(v_a_2405_);
lean_dec(v___x_2394_);
v___x_2408_ = lean_box(0);
v_isShared_2409_ = v_isSharedCheck_2413_;
goto v_resetjp_2407_;
}
v_resetjp_2407_:
{
lean_object* v___x_2411_; 
if (v_isShared_2409_ == 0)
{
v___x_2411_ = v___x_2408_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v_a_2405_);
lean_ctor_set(v_reuseFailAlloc_2412_, 1, v_a_2406_);
v___x_2411_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
return v___x_2411_;
}
}
}
}
}
else
{
lean_object* v___x_2414_; 
v___x_2414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2414_, 0, v_e_2383_);
lean_ctor_set(v___x_2414_, 1, v_a_2387_);
return v___x_2414_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27___boxed(lean_object* v_e_2415_, lean_object* v_subst_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_){
_start:
{
uint8_t v_a_boxed_2420_; lean_object* v_res_2421_; 
v_a_boxed_2420_ = lean_unbox(v_a_2417_);
v_res_2421_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27(v_e_2415_, v_subst_2416_, v_a_boxed_2420_, v_a_2418_, v_a_2419_);
lean_dec_ref(v_a_2418_);
lean_dec_ref(v_subst_2416_);
return v_res_2421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevBetaS(lean_object* v_e_2422_, lean_object* v_subst_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_){
_start:
{
uint8_t v___x_2431_; 
v___x_2431_ = l_Lean_Expr_hasLooseBVars(v_e_2422_);
if (v___x_2431_ == 0)
{
lean_object* v___x_2432_; 
lean_dec_ref(v_subst_2423_);
v___x_2432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2432_, 0, v_e_2422_);
return v___x_2432_;
}
else
{
lean_object* v___x_2433_; lean_object* v___x_2434_; uint8_t v___x_2435_; 
v___x_2433_ = lean_array_get_size(v_subst_2423_);
v___x_2434_ = lean_unsigned_to_nat(0u);
v___x_2435_ = lean_nat_dec_eq(v___x_2433_, v___x_2434_);
if (v___x_2435_ == 0)
{
lean_object* v___x_2436_; lean_object* v___x_2437_; uint8_t v_debug_2438_; lean_object* v_env_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; 
v___x_2436_ = lean_st_ref_get(v_a_2425_);
v___x_2437_ = lean_st_ref_get(v_a_2429_);
v_debug_2438_ = lean_ctor_get_uint8(v___x_2436_, sizeof(void*)*11);
lean_dec(v___x_2436_);
v_env_2439_ = lean_ctor_get(v___x_2437_, 0);
lean_inc_ref(v_env_2439_);
lean_dec(v___x_2437_);
v___x_2440_ = lean_box(v_debug_2438_);
v___x_2441_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27___boxed), 5, 3);
lean_closure_set(v___x_2441_, 0, v_e_2422_);
lean_closure_set(v___x_2441_, 1, v_subst_2423_);
lean_closure_set(v___x_2441_, 2, v___x_2440_);
v___x_2442_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2442_, 0, v_env_2439_);
lean_ctor_set_uint8(v___x_2442_, sizeof(void*)*1, v___x_2435_);
lean_ctor_set_uint8(v___x_2442_, sizeof(void*)*1 + 1, v___x_2435_);
v___x_2443_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___x_2441_, v___x_2442_, v_a_2425_);
if (lean_obj_tag(v___x_2443_) == 0)
{
lean_object* v_a_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2454_; 
v_a_2444_ = lean_ctor_get(v___x_2443_, 0);
v_isSharedCheck_2454_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2454_ == 0)
{
v___x_2446_ = v___x_2443_;
v_isShared_2447_ = v_isSharedCheck_2454_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_a_2444_);
lean_dec(v___x_2443_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2454_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
if (lean_obj_tag(v_a_2444_) == 0)
{
lean_object* v___x_2448_; lean_object* v___x_2449_; 
lean_dec_ref_known(v_a_2444_, 1);
lean_del_object(v___x_2446_);
v___x_2448_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__2, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__2_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__2);
v___x_2449_ = l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(v___x_2448_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_, v_a_2429_);
return v___x_2449_;
}
else
{
lean_object* v_a_2450_; lean_object* v___x_2452_; 
v_a_2450_ = lean_ctor_get(v_a_2444_, 0);
lean_inc(v_a_2450_);
lean_dec_ref_known(v_a_2444_, 1);
if (v_isShared_2447_ == 0)
{
lean_ctor_set(v___x_2446_, 0, v_a_2450_);
v___x_2452_ = v___x_2446_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2453_; 
v_reuseFailAlloc_2453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2453_, 0, v_a_2450_);
v___x_2452_ = v_reuseFailAlloc_2453_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
return v___x_2452_;
}
}
}
}
else
{
lean_object* v_a_2455_; lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2462_; 
v_a_2455_ = lean_ctor_get(v___x_2443_, 0);
v_isSharedCheck_2462_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2462_ == 0)
{
v___x_2457_ = v___x_2443_;
v_isShared_2458_ = v_isSharedCheck_2462_;
goto v_resetjp_2456_;
}
else
{
lean_inc(v_a_2455_);
lean_dec(v___x_2443_);
v___x_2457_ = lean_box(0);
v_isShared_2458_ = v_isSharedCheck_2462_;
goto v_resetjp_2456_;
}
v_resetjp_2456_:
{
lean_object* v___x_2460_; 
if (v_isShared_2458_ == 0)
{
v___x_2460_ = v___x_2457_;
goto v_reusejp_2459_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v_a_2455_);
v___x_2460_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2459_;
}
v_reusejp_2459_:
{
return v___x_2460_;
}
}
}
}
else
{
lean_object* v___x_2463_; 
lean_dec_ref(v_subst_2423_);
v___x_2463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2463_, 0, v_e_2422_);
return v___x_2463_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevBetaS___boxed(lean_object* v_e_2464_, lean_object* v_subst_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_){
_start:
{
lean_object* v_res_2473_; 
v_res_2473_ = l_Lean_Meta_Sym_instantiateRevBetaS(v_e_2464_, v_subst_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_);
lean_dec(v_a_2471_);
lean_dec_ref(v_a_2470_);
lean_dec(v_a_2469_);
lean_dec_ref(v_a_2468_);
lean_dec(v_a_2467_);
lean_dec_ref(v_a_2466_);
return v_res_2473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_betaRevS(lean_object* v_f_2474_, lean_object* v_revArgs_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_){
_start:
{
lean_object* v___x_2483_; lean_object* v___x_2484_; uint8_t v_debug_2485_; lean_object* v_env_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; uint8_t v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; 
v___x_2483_ = lean_st_ref_get(v_a_2477_);
v___x_2484_ = lean_st_ref_get(v_a_2481_);
v_debug_2485_ = lean_ctor_get_uint8(v___x_2483_, sizeof(void*)*11);
lean_dec(v___x_2483_);
v_env_2486_ = lean_ctor_get(v___x_2484_, 0);
lean_inc_ref(v_env_2486_);
lean_dec(v___x_2484_);
v___x_2487_ = lean_box(v_debug_2485_);
v___x_2488_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27___boxed), 5, 3);
lean_closure_set(v___x_2488_, 0, v_f_2474_);
lean_closure_set(v___x_2488_, 1, v_revArgs_2475_);
lean_closure_set(v___x_2488_, 2, v___x_2487_);
v___x_2489_ = 0;
v___x_2490_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2490_, 0, v_env_2486_);
lean_ctor_set_uint8(v___x_2490_, sizeof(void*)*1, v___x_2489_);
lean_ctor_set_uint8(v___x_2490_, sizeof(void*)*1 + 1, v___x_2489_);
v___x_2491_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___x_2488_, v___x_2490_, v_a_2477_);
if (lean_obj_tag(v___x_2491_) == 0)
{
lean_object* v_a_2492_; lean_object* v___x_2494_; uint8_t v_isShared_2495_; uint8_t v_isSharedCheck_2502_; 
v_a_2492_ = lean_ctor_get(v___x_2491_, 0);
v_isSharedCheck_2502_ = !lean_is_exclusive(v___x_2491_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2494_ = v___x_2491_;
v_isShared_2495_ = v_isSharedCheck_2502_;
goto v_resetjp_2493_;
}
else
{
lean_inc(v_a_2492_);
lean_dec(v___x_2491_);
v___x_2494_ = lean_box(0);
v_isShared_2495_ = v_isSharedCheck_2502_;
goto v_resetjp_2493_;
}
v_resetjp_2493_:
{
if (lean_obj_tag(v_a_2492_) == 0)
{
lean_object* v___x_2496_; lean_object* v___x_2497_; 
lean_dec_ref_known(v_a_2492_, 1);
lean_del_object(v___x_2494_);
v___x_2496_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__2, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__2_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__2);
v___x_2497_ = l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(v___x_2496_, v_a_2476_, v_a_2477_, v_a_2478_, v_a_2479_, v_a_2480_, v_a_2481_);
return v___x_2497_;
}
else
{
lean_object* v_a_2498_; lean_object* v___x_2500_; 
v_a_2498_ = lean_ctor_get(v_a_2492_, 0);
lean_inc(v_a_2498_);
lean_dec_ref_known(v_a_2492_, 1);
if (v_isShared_2495_ == 0)
{
lean_ctor_set(v___x_2494_, 0, v_a_2498_);
v___x_2500_ = v___x_2494_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v_a_2498_);
v___x_2500_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
return v___x_2500_;
}
}
}
}
else
{
lean_object* v_a_2503_; lean_object* v___x_2505_; uint8_t v_isShared_2506_; uint8_t v_isSharedCheck_2510_; 
v_a_2503_ = lean_ctor_get(v___x_2491_, 0);
v_isSharedCheck_2510_ = !lean_is_exclusive(v___x_2491_);
if (v_isSharedCheck_2510_ == 0)
{
v___x_2505_ = v___x_2491_;
v_isShared_2506_ = v_isSharedCheck_2510_;
goto v_resetjp_2504_;
}
else
{
lean_inc(v_a_2503_);
lean_dec(v___x_2491_);
v___x_2505_ = lean_box(0);
v_isShared_2506_ = v_isSharedCheck_2510_;
goto v_resetjp_2504_;
}
v_resetjp_2504_:
{
lean_object* v___x_2508_; 
if (v_isShared_2506_ == 0)
{
v___x_2508_ = v___x_2505_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v_a_2503_);
v___x_2508_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
return v___x_2508_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_betaRevS___boxed(lean_object* v_f_2511_, lean_object* v_revArgs_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_){
_start:
{
lean_object* v_res_2520_; 
v_res_2520_ = l_Lean_Meta_Sym_betaRevS(v_f_2511_, v_revArgs_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_);
lean_dec(v_a_2518_);
lean_dec_ref(v_a_2517_);
lean_dec(v_a_2516_);
lean_dec_ref(v_a_2515_);
lean_dec(v_a_2514_);
lean_dec_ref(v_a_2513_);
return v_res_2520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_betaS(lean_object* v_f_2521_, lean_object* v_args_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_){
_start:
{
lean_object* v___x_2530_; lean_object* v___x_2531_; 
v___x_2530_ = l_Array_reverse___redArg(v_args_2522_);
v___x_2531_ = l_Lean_Meta_Sym_betaRevS(v_f_2521_, v___x_2530_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_);
return v___x_2531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_betaS___boxed(lean_object* v_f_2532_, lean_object* v_args_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_){
_start:
{
lean_object* v_res_2541_; 
v_res_2541_ = l_Lean_Meta_Sym_betaS(v_f_2532_, v_args_2533_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_, v_a_2539_);
lean_dec(v_a_2539_);
lean_dec_ref(v_a_2538_);
lean_dec(v_a_2537_);
lean_dec_ref(v_a_2536_);
lean_dec(v_a_2535_);
lean_dec_ref(v_a_2534_);
return v_res_2541_;
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
