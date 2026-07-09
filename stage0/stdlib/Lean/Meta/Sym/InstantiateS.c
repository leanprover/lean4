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
lean_object* l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_hashPtrExpr_unsafe__1___boxed(lean_object*);
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
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
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
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1___closed__0_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_hashPtrExpr_unsafe__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___y_25842__boxed_14_; lean_object* v_res_15_; 
v___y_25842__boxed_14_ = lean_unbox(v___y_11_);
v_res_15_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0(v_idx_10_, v___y_25842__boxed_14_, v___y_12_, v___y_13_);
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
lean_object* v___x_25_; lean_object* v___x_2908__overap_26_; lean_object* v___x_27_; 
v___x_25_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__0, &l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__0);
v___x_2908__overap_26_ = lean_panic_fn_borrowed(v___x_25_, v_msg_17_);
lean_inc(v___y_23_);
lean_inc_ref(v___y_22_);
lean_inc(v___y_21_);
lean_inc_ref(v___y_20_);
lean_inc(v___y_19_);
lean_inc_ref(v___y_18_);
v___x_27_ = lean_apply_7(v___x_2908__overap_26_, v___y_18_, v___y_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_, lean_box(0));
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
uint8_t v___y_25882__boxed_95_; lean_object* v_res_96_; 
v___y_25882__boxed_95_ = lean_unbox(v___y_92_);
v_res_96_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__2(v_f_89_, v_a_90_, v___y_91_, v___y_25882__boxed_95_, v___y_93_, v___y_94_);
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
uint8_t v_bi_boxed_159_; uint8_t v___y_25988__boxed_160_; lean_object* v_res_161_; 
v_bi_boxed_159_ = lean_unbox(v_bi_152_);
v___y_25988__boxed_160_ = lean_unbox(v___y_156_);
v_res_161_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__4(v_x_151_, v_bi_boxed_159_, v_t_153_, v_b_154_, v___y_155_, v___y_25988__boxed_160_, v___y_157_, v___y_158_);
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
uint8_t v___y_26094__boxed_211_; lean_object* v_res_212_; 
v___y_26094__boxed_211_ = lean_unbox(v___y_208_);
v_res_212_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__7(v_structName_204_, v_idx_205_, v_struct_206_, v___y_207_, v___y_26094__boxed_211_, v___y_209_, v___y_210_);
lean_dec_ref(v___y_209_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8(lean_object* v_msg_220_, lean_object* v___y_221_, uint8_t v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_){
_start:
{
lean_object* v___f_225_; lean_object* v___f_226_; lean_object* v___f_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___f_237_; lean_object* v___f_238_; lean_object* v___f_239_; lean_object* v___f_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_25462__overap_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
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
v___x_25462__overap_249_ = lean_panic_fn_borrowed(v___x_248_, v_msg_220_);
lean_dec(v___x_248_);
v___x_250_ = lean_box(v___y_222_);
lean_inc_ref(v___y_223_);
v___x_251_ = lean_apply_4(v___x_25462__overap_249_, v___y_221_, v___x_250_, v___y_223_, v___y_224_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8___boxed(lean_object* v_msg_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_){
_start:
{
uint8_t v___y_26191__boxed_257_; lean_object* v_res_258_; 
v___y_26191__boxed_257_ = lean_unbox(v___y_254_);
v_res_258_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8(v_msg_252_, v___y_253_, v___y_26191__boxed_257_, v___y_255_, v___y_256_);
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
lean_object* v_key_262_; lean_object* v_value_263_; lean_object* v_tail_264_; uint8_t v___y_266_; lean_object* v_fst_269_; lean_object* v_snd_270_; lean_object* v_fst_271_; lean_object* v_snd_272_; uint8_t v___x_273_; 
v_key_262_ = lean_ctor_get(v_x_260_, 0);
v_value_263_ = lean_ctor_get(v_x_260_, 1);
v_tail_264_ = lean_ctor_get(v_x_260_, 2);
v_fst_269_ = lean_ctor_get(v_key_262_, 0);
v_snd_270_ = lean_ctor_get(v_key_262_, 1);
v_fst_271_ = lean_ctor_get(v_a_259_, 0);
v_snd_272_ = lean_ctor_get(v_a_259_, 1);
v___x_273_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_269_, v_fst_271_);
if (v___x_273_ == 0)
{
v___y_266_ = v___x_273_;
goto v___jp_265_;
}
else
{
uint8_t v___x_274_; 
v___x_274_ = lean_nat_dec_eq(v_snd_270_, v_snd_272_);
v___y_266_ = v___x_274_;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11___redArg___boxed(lean_object* v_a_275_, lean_object* v_x_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11___redArg(v_a_275_, v_x_276_);
lean_dec(v_x_276_);
lean_dec_ref(v_a_275_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3___redArg(lean_object* v_m_278_, lean_object* v_a_279_){
_start:
{
lean_object* v_buckets_280_; lean_object* v_fst_281_; lean_object* v_snd_282_; lean_object* v___x_283_; uint64_t v___x_284_; uint64_t v___x_285_; uint64_t v___x_286_; uint64_t v___x_287_; uint64_t v___x_288_; uint64_t v_fold_289_; uint64_t v___x_290_; uint64_t v___x_291_; uint64_t v___x_292_; size_t v___x_293_; size_t v___x_294_; size_t v___x_295_; size_t v___x_296_; size_t v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v_buckets_280_ = lean_ctor_get(v_m_278_, 1);
v_fst_281_ = lean_ctor_get(v_a_279_, 0);
v_snd_282_ = lean_ctor_get(v_a_279_, 1);
v___x_283_ = lean_array_get_size(v_buckets_280_);
v___x_284_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_281_);
v___x_285_ = lean_uint64_of_nat(v_snd_282_);
v___x_286_ = lean_uint64_mix_hash(v___x_284_, v___x_285_);
v___x_287_ = 32ULL;
v___x_288_ = lean_uint64_shift_right(v___x_286_, v___x_287_);
v_fold_289_ = lean_uint64_xor(v___x_286_, v___x_288_);
v___x_290_ = 16ULL;
v___x_291_ = lean_uint64_shift_right(v_fold_289_, v___x_290_);
v___x_292_ = lean_uint64_xor(v_fold_289_, v___x_291_);
v___x_293_ = lean_uint64_to_usize(v___x_292_);
v___x_294_ = lean_usize_of_nat(v___x_283_);
v___x_295_ = ((size_t)1ULL);
v___x_296_ = lean_usize_sub(v___x_294_, v___x_295_);
v___x_297_ = lean_usize_land(v___x_293_, v___x_296_);
v___x_298_ = lean_array_uget_borrowed(v_buckets_280_, v___x_297_);
v___x_299_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11___redArg(v_a_279_, v___x_298_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_m_300_, lean_object* v_a_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3___redArg(v_m_300_, v_a_301_);
lean_dec_ref(v_a_301_);
lean_dec_ref(v_m_300_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__3(lean_object* v_x_303_, uint8_t v_bi_304_, lean_object* v_t_305_, lean_object* v_b_306_, lean_object* v___y_307_, uint8_t v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_){
_start:
{
lean_object* v___y_312_; lean_object* v___y_313_; 
if (v___y_308_ == 0)
{
v___y_312_ = v___y_307_;
v___y_313_ = v___y_310_;
goto v___jp_311_;
}
else
{
lean_object* v___x_335_; 
lean_inc_ref(v_t_305_);
v___x_335_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_305_, v___y_308_, v___y_309_, v___y_310_);
if (lean_obj_tag(v___x_335_) == 0)
{
lean_object* v_a_336_; lean_object* v___x_337_; 
v_a_336_ = lean_ctor_get(v___x_335_, 1);
lean_inc(v_a_336_);
lean_dec_ref_known(v___x_335_, 2);
lean_inc_ref(v_b_306_);
v___x_337_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_306_, v___y_308_, v___y_309_, v_a_336_);
if (lean_obj_tag(v___x_337_) == 0)
{
lean_object* v_a_338_; 
v_a_338_ = lean_ctor_get(v___x_337_, 1);
lean_inc(v_a_338_);
lean_dec_ref_known(v___x_337_, 2);
v___y_312_ = v___y_307_;
v___y_313_ = v_a_338_;
goto v___jp_311_;
}
else
{
lean_object* v_a_339_; lean_object* v_a_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_347_; 
lean_dec_ref(v___y_307_);
lean_dec_ref(v_b_306_);
lean_dec_ref(v_t_305_);
lean_dec(v_x_303_);
v_a_339_ = lean_ctor_get(v___x_337_, 0);
v_a_340_ = lean_ctor_get(v___x_337_, 1);
v_isSharedCheck_347_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_347_ == 0)
{
v___x_342_ = v___x_337_;
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_a_340_);
lean_inc(v_a_339_);
lean_dec(v___x_337_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_345_; 
if (v_isShared_343_ == 0)
{
v___x_345_ = v___x_342_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v_a_339_);
lean_ctor_set(v_reuseFailAlloc_346_, 1, v_a_340_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
}
else
{
lean_object* v_a_348_; lean_object* v_a_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_356_; 
lean_dec_ref(v___y_307_);
lean_dec_ref(v_b_306_);
lean_dec_ref(v_t_305_);
lean_dec(v_x_303_);
v_a_348_ = lean_ctor_get(v___x_335_, 0);
v_a_349_ = lean_ctor_get(v___x_335_, 1);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_356_ == 0)
{
v___x_351_ = v___x_335_;
v_isShared_352_ = v_isSharedCheck_356_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_a_349_);
lean_inc(v_a_348_);
lean_dec(v___x_335_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_356_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v___x_354_; 
if (v_isShared_352_ == 0)
{
v___x_354_ = v___x_351_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_a_348_);
lean_ctor_set(v_reuseFailAlloc_355_, 1, v_a_349_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
}
}
v___jp_311_:
{
lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_314_ = l_Lean_Expr_lam___override(v_x_303_, v_t_305_, v_b_306_, v_bi_304_);
v___x_315_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_314_, v___y_313_);
if (lean_obj_tag(v___x_315_) == 0)
{
lean_object* v_a_316_; lean_object* v_a_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_325_; 
v_a_316_ = lean_ctor_get(v___x_315_, 0);
v_a_317_ = lean_ctor_get(v___x_315_, 1);
v_isSharedCheck_325_ = !lean_is_exclusive(v___x_315_);
if (v_isSharedCheck_325_ == 0)
{
v___x_319_ = v___x_315_;
v_isShared_320_ = v_isSharedCheck_325_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_a_317_);
lean_inc(v_a_316_);
lean_dec(v___x_315_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_325_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_321_; lean_object* v___x_323_; 
v___x_321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_321_, 0, v_a_316_);
lean_ctor_set(v___x_321_, 1, v___y_312_);
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 0, v___x_321_);
v___x_323_ = v___x_319_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v___x_321_);
lean_ctor_set(v_reuseFailAlloc_324_, 1, v_a_317_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
}
else
{
lean_object* v_a_326_; lean_object* v_a_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_334_; 
lean_dec_ref(v___y_312_);
v_a_326_ = lean_ctor_get(v___x_315_, 0);
v_a_327_ = lean_ctor_get(v___x_315_, 1);
v_isSharedCheck_334_ = !lean_is_exclusive(v___x_315_);
if (v_isSharedCheck_334_ == 0)
{
v___x_329_ = v___x_315_;
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_a_327_);
lean_inc(v_a_326_);
lean_dec(v___x_315_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_332_; 
if (v_isShared_330_ == 0)
{
v___x_332_ = v___x_329_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_a_326_);
lean_ctor_set(v_reuseFailAlloc_333_, 1, v_a_327_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__3___boxed(lean_object* v_x_357_, lean_object* v_bi_358_, lean_object* v_t_359_, lean_object* v_b_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_){
_start:
{
uint8_t v_bi_boxed_365_; uint8_t v___y_26331__boxed_366_; lean_object* v_res_367_; 
v_bi_boxed_365_ = lean_unbox(v_bi_358_);
v___y_26331__boxed_366_ = lean_unbox(v___y_362_);
v_res_367_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__3(v_x_357_, v_bi_boxed_365_, v_t_359_, v_b_360_, v___y_361_, v___y_26331__boxed_366_, v___y_363_, v___y_364_);
lean_dec_ref(v___y_363_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__5(lean_object* v_x_368_, lean_object* v_t_369_, lean_object* v_v_370_, lean_object* v_b_371_, uint8_t v_nondep_372_, lean_object* v___y_373_, uint8_t v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_){
_start:
{
lean_object* v___y_378_; lean_object* v___y_379_; 
if (v___y_374_ == 0)
{
v___y_378_ = v___y_373_;
v___y_379_ = v___y_376_;
goto v___jp_377_;
}
else
{
lean_object* v___x_401_; 
lean_inc_ref(v_t_369_);
v___x_401_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_369_, v___y_374_, v___y_375_, v___y_376_);
if (lean_obj_tag(v___x_401_) == 0)
{
lean_object* v_a_402_; lean_object* v___x_403_; 
v_a_402_ = lean_ctor_get(v___x_401_, 1);
lean_inc(v_a_402_);
lean_dec_ref_known(v___x_401_, 2);
lean_inc_ref(v_v_370_);
v___x_403_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_v_370_, v___y_374_, v___y_375_, v_a_402_);
if (lean_obj_tag(v___x_403_) == 0)
{
lean_object* v_a_404_; lean_object* v___x_405_; 
v_a_404_ = lean_ctor_get(v___x_403_, 1);
lean_inc(v_a_404_);
lean_dec_ref_known(v___x_403_, 2);
lean_inc_ref(v_b_371_);
v___x_405_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_371_, v___y_374_, v___y_375_, v_a_404_);
if (lean_obj_tag(v___x_405_) == 0)
{
lean_object* v_a_406_; 
v_a_406_ = lean_ctor_get(v___x_405_, 1);
lean_inc(v_a_406_);
lean_dec_ref_known(v___x_405_, 2);
v___y_378_ = v___y_373_;
v___y_379_ = v_a_406_;
goto v___jp_377_;
}
else
{
lean_object* v_a_407_; lean_object* v_a_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_415_; 
lean_dec_ref(v___y_373_);
lean_dec_ref(v_b_371_);
lean_dec_ref(v_v_370_);
lean_dec_ref(v_t_369_);
lean_dec(v_x_368_);
v_a_407_ = lean_ctor_get(v___x_405_, 0);
v_a_408_ = lean_ctor_get(v___x_405_, 1);
v_isSharedCheck_415_ = !lean_is_exclusive(v___x_405_);
if (v_isSharedCheck_415_ == 0)
{
v___x_410_ = v___x_405_;
v_isShared_411_ = v_isSharedCheck_415_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_a_408_);
lean_inc(v_a_407_);
lean_dec(v___x_405_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_415_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v___x_413_; 
if (v_isShared_411_ == 0)
{
v___x_413_ = v___x_410_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v_a_407_);
lean_ctor_set(v_reuseFailAlloc_414_, 1, v_a_408_);
v___x_413_ = v_reuseFailAlloc_414_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
return v___x_413_;
}
}
}
}
else
{
lean_object* v_a_416_; lean_object* v_a_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_424_; 
lean_dec_ref(v___y_373_);
lean_dec_ref(v_b_371_);
lean_dec_ref(v_v_370_);
lean_dec_ref(v_t_369_);
lean_dec(v_x_368_);
v_a_416_ = lean_ctor_get(v___x_403_, 0);
v_a_417_ = lean_ctor_get(v___x_403_, 1);
v_isSharedCheck_424_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_424_ == 0)
{
v___x_419_ = v___x_403_;
v_isShared_420_ = v_isSharedCheck_424_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_a_417_);
lean_inc(v_a_416_);
lean_dec(v___x_403_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_424_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v___x_422_; 
if (v_isShared_420_ == 0)
{
v___x_422_ = v___x_419_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v_a_416_);
lean_ctor_set(v_reuseFailAlloc_423_, 1, v_a_417_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
return v___x_422_;
}
}
}
}
else
{
lean_object* v_a_425_; lean_object* v_a_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_433_; 
lean_dec_ref(v___y_373_);
lean_dec_ref(v_b_371_);
lean_dec_ref(v_v_370_);
lean_dec_ref(v_t_369_);
lean_dec(v_x_368_);
v_a_425_ = lean_ctor_get(v___x_401_, 0);
v_a_426_ = lean_ctor_get(v___x_401_, 1);
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_401_);
if (v_isSharedCheck_433_ == 0)
{
v___x_428_ = v___x_401_;
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_a_426_);
lean_inc(v_a_425_);
lean_dec(v___x_401_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_431_; 
if (v_isShared_429_ == 0)
{
v___x_431_ = v___x_428_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_a_425_);
lean_ctor_set(v_reuseFailAlloc_432_, 1, v_a_426_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
}
}
v___jp_377_:
{
lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_380_ = l_Lean_Expr_letE___override(v_x_368_, v_t_369_, v_v_370_, v_b_371_, v_nondep_372_);
v___x_381_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_380_, v___y_379_);
if (lean_obj_tag(v___x_381_) == 0)
{
lean_object* v_a_382_; lean_object* v_a_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_391_; 
v_a_382_ = lean_ctor_get(v___x_381_, 0);
v_a_383_ = lean_ctor_get(v___x_381_, 1);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_391_ == 0)
{
v___x_385_ = v___x_381_;
v_isShared_386_ = v_isSharedCheck_391_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_a_383_);
lean_inc(v_a_382_);
lean_dec(v___x_381_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_391_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_387_; lean_object* v___x_389_; 
v___x_387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_387_, 0, v_a_382_);
lean_ctor_set(v___x_387_, 1, v___y_378_);
if (v_isShared_386_ == 0)
{
lean_ctor_set(v___x_385_, 0, v___x_387_);
v___x_389_ = v___x_385_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v___x_387_);
lean_ctor_set(v_reuseFailAlloc_390_, 1, v_a_383_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
}
else
{
lean_object* v_a_392_; lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_400_; 
lean_dec_ref(v___y_378_);
v_a_392_ = lean_ctor_get(v___x_381_, 0);
v_a_393_ = lean_ctor_get(v___x_381_, 1);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_400_ == 0)
{
v___x_395_ = v___x_381_;
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_inc(v_a_392_);
lean_dec(v___x_381_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_398_; 
if (v_isShared_396_ == 0)
{
v___x_398_ = v___x_395_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_a_392_);
lean_ctor_set(v_reuseFailAlloc_399_, 1, v_a_393_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__5___boxed(lean_object* v_x_434_, lean_object* v_t_435_, lean_object* v_v_436_, lean_object* v_b_437_, lean_object* v_nondep_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
uint8_t v_nondep_boxed_443_; uint8_t v___y_26437__boxed_444_; lean_object* v_res_445_; 
v_nondep_boxed_443_ = lean_unbox(v_nondep_438_);
v___y_26437__boxed_444_ = lean_unbox(v___y_440_);
v_res_445_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__5(v_x_434_, v_t_435_, v_v_436_, v_b_437_, v_nondep_boxed_443_, v___y_439_, v___y_26437__boxed_444_, v___y_441_, v___y_442_);
lean_dec_ref(v___y_441_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__6(lean_object* v_d_446_, lean_object* v_e_447_, lean_object* v___y_448_, uint8_t v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_){
_start:
{
lean_object* v___y_453_; lean_object* v___y_454_; 
if (v___y_449_ == 0)
{
v___y_453_ = v___y_448_;
v___y_454_ = v___y_451_;
goto v___jp_452_;
}
else
{
lean_object* v___x_476_; 
lean_inc_ref(v_e_447_);
v___x_476_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_e_447_, v___y_449_, v___y_450_, v___y_451_);
if (lean_obj_tag(v___x_476_) == 0)
{
lean_object* v_a_477_; 
v_a_477_ = lean_ctor_get(v___x_476_, 1);
lean_inc(v_a_477_);
lean_dec_ref_known(v___x_476_, 2);
v___y_453_ = v___y_448_;
v___y_454_ = v_a_477_;
goto v___jp_452_;
}
else
{
lean_object* v_a_478_; lean_object* v_a_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_486_; 
lean_dec_ref(v___y_448_);
lean_dec_ref(v_e_447_);
lean_dec(v_d_446_);
v_a_478_ = lean_ctor_get(v___x_476_, 0);
v_a_479_ = lean_ctor_get(v___x_476_, 1);
v_isSharedCheck_486_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_486_ == 0)
{
v___x_481_ = v___x_476_;
v_isShared_482_ = v_isSharedCheck_486_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_a_479_);
lean_inc(v_a_478_);
lean_dec(v___x_476_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_486_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v___x_484_; 
if (v_isShared_482_ == 0)
{
v___x_484_ = v___x_481_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v_a_478_);
lean_ctor_set(v_reuseFailAlloc_485_, 1, v_a_479_);
v___x_484_ = v_reuseFailAlloc_485_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
return v___x_484_;
}
}
}
}
v___jp_452_:
{
lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_455_ = l_Lean_Expr_mdata___override(v_d_446_, v_e_447_);
v___x_456_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_455_, v___y_454_);
if (lean_obj_tag(v___x_456_) == 0)
{
lean_object* v_a_457_; lean_object* v_a_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_466_; 
v_a_457_ = lean_ctor_get(v___x_456_, 0);
v_a_458_ = lean_ctor_get(v___x_456_, 1);
v_isSharedCheck_466_ = !lean_is_exclusive(v___x_456_);
if (v_isSharedCheck_466_ == 0)
{
v___x_460_ = v___x_456_;
v_isShared_461_ = v_isSharedCheck_466_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_a_458_);
lean_inc(v_a_457_);
lean_dec(v___x_456_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_466_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_462_; lean_object* v___x_464_; 
v___x_462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_462_, 0, v_a_457_);
lean_ctor_set(v___x_462_, 1, v___y_453_);
if (v_isShared_461_ == 0)
{
lean_ctor_set(v___x_460_, 0, v___x_462_);
v___x_464_ = v___x_460_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v___x_462_);
lean_ctor_set(v_reuseFailAlloc_465_, 1, v_a_458_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
}
else
{
lean_object* v_a_467_; lean_object* v_a_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_475_; 
lean_dec_ref(v___y_453_);
v_a_467_ = lean_ctor_get(v___x_456_, 0);
v_a_468_ = lean_ctor_get(v___x_456_, 1);
v_isSharedCheck_475_ = !lean_is_exclusive(v___x_456_);
if (v_isSharedCheck_475_ == 0)
{
v___x_470_ = v___x_456_;
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_a_468_);
lean_inc(v_a_467_);
lean_dec(v___x_456_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_473_; 
if (v_isShared_471_ == 0)
{
v___x_473_ = v___x_470_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_a_467_);
lean_ctor_set(v_reuseFailAlloc_474_, 1, v_a_468_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__6___boxed(lean_object* v_d_487_, lean_object* v_e_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_){
_start:
{
uint8_t v___y_26566__boxed_493_; lean_object* v_res_494_; 
v___y_26566__boxed_493_ = lean_unbox(v___y_490_);
v_res_494_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__6(v_d_487_, v_e_488_, v___y_489_, v___y_26566__boxed_493_, v___y_491_, v___y_492_);
lean_dec_ref(v___y_491_);
return v_res_494_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__3(void){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_498_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__2));
v___x_499_ = lean_unsigned_to_nat(67u);
v___x_500_ = lean_unsigned_to_nat(35u);
v___x_501_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__1));
v___x_502_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__0));
v___x_503_ = l_mkPanicMessageWithDecl(v___x_502_, v___x_501_, v___x_500_, v___x_499_, v___x_498_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1(lean_object* v_beginIdx_504_, lean_object* v_n_505_, lean_object* v_subst_506_, lean_object* v_e_507_, lean_object* v_offset_508_, lean_object* v_a_509_, uint8_t v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_){
_start:
{
switch(lean_obj_tag(v_e_507_))
{
case 5:
{
lean_object* v_fn_513_; lean_object* v_arg_514_; lean_object* v___x_515_; 
v_fn_513_ = lean_ctor_get(v_e_507_, 0);
v_arg_514_ = lean_ctor_get(v_e_507_, 1);
lean_inc(v_offset_508_);
lean_inc_ref(v_fn_513_);
v___x_515_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(v_beginIdx_504_, v_n_505_, v_subst_506_, v_fn_513_, v_offset_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_);
if (lean_obj_tag(v___x_515_) == 0)
{
lean_object* v_a_516_; lean_object* v_a_517_; lean_object* v_fst_518_; lean_object* v_snd_519_; lean_object* v___x_520_; 
v_a_516_ = lean_ctor_get(v___x_515_, 0);
lean_inc(v_a_516_);
v_a_517_ = lean_ctor_get(v___x_515_, 1);
lean_inc(v_a_517_);
lean_dec_ref_known(v___x_515_, 2);
v_fst_518_ = lean_ctor_get(v_a_516_, 0);
lean_inc(v_fst_518_);
v_snd_519_ = lean_ctor_get(v_a_516_, 1);
lean_inc(v_snd_519_);
lean_dec(v_a_516_);
lean_inc_ref(v_arg_514_);
v___x_520_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(v_beginIdx_504_, v_n_505_, v_subst_506_, v_arg_514_, v_offset_508_, v_snd_519_, v_a_510_, v_a_511_, v_a_517_);
if (lean_obj_tag(v___x_520_) == 0)
{
lean_object* v_a_521_; lean_object* v_a_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_543_; 
v_a_521_ = lean_ctor_get(v___x_520_, 0);
v_a_522_ = lean_ctor_get(v___x_520_, 1);
v_isSharedCheck_543_ = !lean_is_exclusive(v___x_520_);
if (v_isSharedCheck_543_ == 0)
{
v___x_524_ = v___x_520_;
v_isShared_525_ = v_isSharedCheck_543_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_a_522_);
lean_inc(v_a_521_);
lean_dec(v___x_520_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_543_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v_fst_526_; lean_object* v_snd_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_542_; 
v_fst_526_ = lean_ctor_get(v_a_521_, 0);
v_snd_527_ = lean_ctor_get(v_a_521_, 1);
v_isSharedCheck_542_ = !lean_is_exclusive(v_a_521_);
if (v_isSharedCheck_542_ == 0)
{
v___x_529_ = v_a_521_;
v_isShared_530_ = v_isSharedCheck_542_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_snd_527_);
lean_inc(v_fst_526_);
lean_dec(v_a_521_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_542_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
uint8_t v___y_532_; uint8_t v___x_540_; 
v___x_540_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_513_, v_fst_518_);
if (v___x_540_ == 0)
{
v___y_532_ = v___x_540_;
goto v___jp_531_;
}
else
{
uint8_t v___x_541_; 
v___x_541_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_514_, v_fst_526_);
v___y_532_ = v___x_541_;
goto v___jp_531_;
}
v___jp_531_:
{
if (v___y_532_ == 0)
{
lean_object* v___x_533_; 
lean_del_object(v___x_529_);
lean_del_object(v___x_524_);
lean_dec_ref_known(v_e_507_, 2);
v___x_533_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__2(v_fst_518_, v_fst_526_, v_snd_527_, v_a_510_, v_a_511_, v_a_522_);
return v___x_533_;
}
else
{
lean_object* v___x_535_; 
lean_dec(v_fst_526_);
lean_dec(v_fst_518_);
if (v_isShared_530_ == 0)
{
lean_ctor_set(v___x_529_, 0, v_e_507_);
v___x_535_ = v___x_529_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_e_507_);
lean_ctor_set(v_reuseFailAlloc_539_, 1, v_snd_527_);
v___x_535_ = v_reuseFailAlloc_539_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
lean_object* v___x_537_; 
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 0, v___x_535_);
v___x_537_ = v___x_524_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v___x_535_);
lean_ctor_set(v_reuseFailAlloc_538_, 1, v_a_522_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_518_);
lean_dec_ref_known(v_e_507_, 2);
return v___x_520_;
}
}
else
{
lean_dec_ref_known(v_e_507_, 2);
lean_dec(v_offset_508_);
return v___x_515_;
}
}
case 6:
{
lean_object* v_binderName_544_; lean_object* v_binderType_545_; lean_object* v_body_546_; uint8_t v_binderInfo_547_; lean_object* v___x_548_; 
v_binderName_544_ = lean_ctor_get(v_e_507_, 0);
v_binderType_545_ = lean_ctor_get(v_e_507_, 1);
v_body_546_ = lean_ctor_get(v_e_507_, 2);
v_binderInfo_547_ = lean_ctor_get_uint8(v_e_507_, sizeof(void*)*3 + 8);
lean_inc(v_offset_508_);
lean_inc_ref(v_binderType_545_);
v___x_548_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(v_beginIdx_504_, v_n_505_, v_subst_506_, v_binderType_545_, v_offset_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_);
if (lean_obj_tag(v___x_548_) == 0)
{
lean_object* v_a_549_; lean_object* v_a_550_; lean_object* v_fst_551_; lean_object* v_snd_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v_a_549_ = lean_ctor_get(v___x_548_, 0);
lean_inc(v_a_549_);
v_a_550_ = lean_ctor_get(v___x_548_, 1);
lean_inc(v_a_550_);
lean_dec_ref_known(v___x_548_, 2);
v_fst_551_ = lean_ctor_get(v_a_549_, 0);
lean_inc(v_fst_551_);
v_snd_552_ = lean_ctor_get(v_a_549_, 1);
lean_inc(v_snd_552_);
lean_dec(v_a_549_);
v___x_553_ = lean_unsigned_to_nat(1u);
v___x_554_ = lean_nat_add(v_offset_508_, v___x_553_);
lean_dec(v_offset_508_);
lean_inc_ref(v_body_546_);
v___x_555_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(v_beginIdx_504_, v_n_505_, v_subst_506_, v_body_546_, v___x_554_, v_snd_552_, v_a_510_, v_a_511_, v_a_550_);
if (lean_obj_tag(v___x_555_) == 0)
{
lean_object* v_a_556_; lean_object* v_a_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_578_; 
v_a_556_ = lean_ctor_get(v___x_555_, 0);
v_a_557_ = lean_ctor_get(v___x_555_, 1);
v_isSharedCheck_578_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_578_ == 0)
{
v___x_559_ = v___x_555_;
v_isShared_560_ = v_isSharedCheck_578_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_a_557_);
lean_inc(v_a_556_);
lean_dec(v___x_555_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_578_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v_fst_561_; lean_object* v_snd_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_577_; 
v_fst_561_ = lean_ctor_get(v_a_556_, 0);
v_snd_562_ = lean_ctor_get(v_a_556_, 1);
v_isSharedCheck_577_ = !lean_is_exclusive(v_a_556_);
if (v_isSharedCheck_577_ == 0)
{
v___x_564_ = v_a_556_;
v_isShared_565_ = v_isSharedCheck_577_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_snd_562_);
lean_inc(v_fst_561_);
lean_dec(v_a_556_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_577_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
uint8_t v___y_567_; uint8_t v___x_575_; 
v___x_575_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_545_, v_fst_551_);
if (v___x_575_ == 0)
{
v___y_567_ = v___x_575_;
goto v___jp_566_;
}
else
{
uint8_t v___x_576_; 
v___x_576_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_546_, v_fst_561_);
v___y_567_ = v___x_576_;
goto v___jp_566_;
}
v___jp_566_:
{
if (v___y_567_ == 0)
{
lean_object* v___x_568_; 
lean_inc(v_binderName_544_);
lean_del_object(v___x_564_);
lean_del_object(v___x_559_);
lean_dec_ref_known(v_e_507_, 3);
v___x_568_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__3(v_binderName_544_, v_binderInfo_547_, v_fst_551_, v_fst_561_, v_snd_562_, v_a_510_, v_a_511_, v_a_557_);
return v___x_568_;
}
else
{
lean_object* v___x_570_; 
lean_dec(v_fst_561_);
lean_dec(v_fst_551_);
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 0, v_e_507_);
v___x_570_ = v___x_564_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v_e_507_);
lean_ctor_set(v_reuseFailAlloc_574_, 1, v_snd_562_);
v___x_570_ = v_reuseFailAlloc_574_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
lean_object* v___x_572_; 
if (v_isShared_560_ == 0)
{
lean_ctor_set(v___x_559_, 0, v___x_570_);
v___x_572_ = v___x_559_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v___x_570_);
lean_ctor_set(v_reuseFailAlloc_573_, 1, v_a_557_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_551_);
lean_dec_ref_known(v_e_507_, 3);
return v___x_555_;
}
}
else
{
lean_dec_ref_known(v_e_507_, 3);
lean_dec(v_offset_508_);
return v___x_548_;
}
}
case 7:
{
lean_object* v_binderName_579_; lean_object* v_binderType_580_; lean_object* v_body_581_; uint8_t v_binderInfo_582_; lean_object* v___x_583_; 
v_binderName_579_ = lean_ctor_get(v_e_507_, 0);
v_binderType_580_ = lean_ctor_get(v_e_507_, 1);
v_body_581_ = lean_ctor_get(v_e_507_, 2);
v_binderInfo_582_ = lean_ctor_get_uint8(v_e_507_, sizeof(void*)*3 + 8);
lean_inc(v_offset_508_);
lean_inc_ref(v_binderType_580_);
v___x_583_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(v_beginIdx_504_, v_n_505_, v_subst_506_, v_binderType_580_, v_offset_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_);
if (lean_obj_tag(v___x_583_) == 0)
{
lean_object* v_a_584_; lean_object* v_a_585_; lean_object* v_fst_586_; lean_object* v_snd_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v_a_584_ = lean_ctor_get(v___x_583_, 0);
lean_inc(v_a_584_);
v_a_585_ = lean_ctor_get(v___x_583_, 1);
lean_inc(v_a_585_);
lean_dec_ref_known(v___x_583_, 2);
v_fst_586_ = lean_ctor_get(v_a_584_, 0);
lean_inc(v_fst_586_);
v_snd_587_ = lean_ctor_get(v_a_584_, 1);
lean_inc(v_snd_587_);
lean_dec(v_a_584_);
v___x_588_ = lean_unsigned_to_nat(1u);
v___x_589_ = lean_nat_add(v_offset_508_, v___x_588_);
lean_dec(v_offset_508_);
lean_inc_ref(v_body_581_);
v___x_590_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(v_beginIdx_504_, v_n_505_, v_subst_506_, v_body_581_, v___x_589_, v_snd_587_, v_a_510_, v_a_511_, v_a_585_);
if (lean_obj_tag(v___x_590_) == 0)
{
lean_object* v_a_591_; lean_object* v_a_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_613_; 
v_a_591_ = lean_ctor_get(v___x_590_, 0);
v_a_592_ = lean_ctor_get(v___x_590_, 1);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_613_ == 0)
{
v___x_594_ = v___x_590_;
v_isShared_595_ = v_isSharedCheck_613_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_a_592_);
lean_inc(v_a_591_);
lean_dec(v___x_590_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_613_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v_fst_596_; lean_object* v_snd_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_612_; 
v_fst_596_ = lean_ctor_get(v_a_591_, 0);
v_snd_597_ = lean_ctor_get(v_a_591_, 1);
v_isSharedCheck_612_ = !lean_is_exclusive(v_a_591_);
if (v_isSharedCheck_612_ == 0)
{
v___x_599_ = v_a_591_;
v_isShared_600_ = v_isSharedCheck_612_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_snd_597_);
lean_inc(v_fst_596_);
lean_dec(v_a_591_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_612_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
uint8_t v___y_602_; uint8_t v___x_610_; 
v___x_610_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_580_, v_fst_586_);
if (v___x_610_ == 0)
{
v___y_602_ = v___x_610_;
goto v___jp_601_;
}
else
{
uint8_t v___x_611_; 
v___x_611_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_581_, v_fst_596_);
v___y_602_ = v___x_611_;
goto v___jp_601_;
}
v___jp_601_:
{
if (v___y_602_ == 0)
{
lean_object* v___x_603_; 
lean_inc(v_binderName_579_);
lean_del_object(v___x_599_);
lean_del_object(v___x_594_);
lean_dec_ref_known(v_e_507_, 3);
v___x_603_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__4(v_binderName_579_, v_binderInfo_582_, v_fst_586_, v_fst_596_, v_snd_597_, v_a_510_, v_a_511_, v_a_592_);
return v___x_603_;
}
else
{
lean_object* v___x_605_; 
lean_dec(v_fst_596_);
lean_dec(v_fst_586_);
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 0, v_e_507_);
v___x_605_ = v___x_599_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_e_507_);
lean_ctor_set(v_reuseFailAlloc_609_, 1, v_snd_597_);
v___x_605_ = v_reuseFailAlloc_609_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
lean_object* v___x_607_; 
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 0, v___x_605_);
v___x_607_ = v___x_594_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v___x_605_);
lean_ctor_set(v_reuseFailAlloc_608_, 1, v_a_592_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_586_);
lean_dec_ref_known(v_e_507_, 3);
return v___x_590_;
}
}
else
{
lean_dec_ref_known(v_e_507_, 3);
lean_dec(v_offset_508_);
return v___x_583_;
}
}
case 8:
{
lean_object* v_declName_614_; lean_object* v_type_615_; lean_object* v_value_616_; lean_object* v_body_617_; uint8_t v_nondep_618_; lean_object* v___x_619_; 
v_declName_614_ = lean_ctor_get(v_e_507_, 0);
v_type_615_ = lean_ctor_get(v_e_507_, 1);
v_value_616_ = lean_ctor_get(v_e_507_, 2);
v_body_617_ = lean_ctor_get(v_e_507_, 3);
v_nondep_618_ = lean_ctor_get_uint8(v_e_507_, sizeof(void*)*4 + 8);
lean_inc(v_offset_508_);
lean_inc_ref(v_type_615_);
v___x_619_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(v_beginIdx_504_, v_n_505_, v_subst_506_, v_type_615_, v_offset_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_);
if (lean_obj_tag(v___x_619_) == 0)
{
lean_object* v_a_620_; lean_object* v_a_621_; lean_object* v_fst_622_; lean_object* v_snd_623_; lean_object* v___x_624_; 
v_a_620_ = lean_ctor_get(v___x_619_, 0);
lean_inc(v_a_620_);
v_a_621_ = lean_ctor_get(v___x_619_, 1);
lean_inc(v_a_621_);
lean_dec_ref_known(v___x_619_, 2);
v_fst_622_ = lean_ctor_get(v_a_620_, 0);
lean_inc(v_fst_622_);
v_snd_623_ = lean_ctor_get(v_a_620_, 1);
lean_inc(v_snd_623_);
lean_dec(v_a_620_);
lean_inc(v_offset_508_);
lean_inc_ref(v_value_616_);
v___x_624_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(v_beginIdx_504_, v_n_505_, v_subst_506_, v_value_616_, v_offset_508_, v_snd_623_, v_a_510_, v_a_511_, v_a_621_);
if (lean_obj_tag(v___x_624_) == 0)
{
lean_object* v_a_625_; lean_object* v_a_626_; lean_object* v_fst_627_; lean_object* v_snd_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
v_a_625_ = lean_ctor_get(v___x_624_, 0);
lean_inc(v_a_625_);
v_a_626_ = lean_ctor_get(v___x_624_, 1);
lean_inc(v_a_626_);
lean_dec_ref_known(v___x_624_, 2);
v_fst_627_ = lean_ctor_get(v_a_625_, 0);
lean_inc(v_fst_627_);
v_snd_628_ = lean_ctor_get(v_a_625_, 1);
lean_inc(v_snd_628_);
lean_dec(v_a_625_);
v___x_629_ = lean_unsigned_to_nat(1u);
v___x_630_ = lean_nat_add(v_offset_508_, v___x_629_);
lean_dec(v_offset_508_);
lean_inc_ref(v_body_617_);
v___x_631_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(v_beginIdx_504_, v_n_505_, v_subst_506_, v_body_617_, v___x_630_, v_snd_628_, v_a_510_, v_a_511_, v_a_626_);
if (lean_obj_tag(v___x_631_) == 0)
{
lean_object* v_a_632_; lean_object* v_a_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_656_; 
v_a_632_ = lean_ctor_get(v___x_631_, 0);
v_a_633_ = lean_ctor_get(v___x_631_, 1);
v_isSharedCheck_656_ = !lean_is_exclusive(v___x_631_);
if (v_isSharedCheck_656_ == 0)
{
v___x_635_ = v___x_631_;
v_isShared_636_ = v_isSharedCheck_656_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_a_633_);
lean_inc(v_a_632_);
lean_dec(v___x_631_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_656_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v_fst_637_; lean_object* v_snd_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_655_; 
v_fst_637_ = lean_ctor_get(v_a_632_, 0);
v_snd_638_ = lean_ctor_get(v_a_632_, 1);
v_isSharedCheck_655_ = !lean_is_exclusive(v_a_632_);
if (v_isSharedCheck_655_ == 0)
{
v___x_640_ = v_a_632_;
v_isShared_641_ = v_isSharedCheck_655_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_snd_638_);
lean_inc(v_fst_637_);
lean_dec(v_a_632_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_655_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
uint8_t v___y_643_; uint8_t v___x_653_; 
v___x_653_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_type_615_, v_fst_622_);
if (v___x_653_ == 0)
{
v___y_643_ = v___x_653_;
goto v___jp_642_;
}
else
{
uint8_t v___x_654_; 
v___x_654_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_value_616_, v_fst_627_);
v___y_643_ = v___x_654_;
goto v___jp_642_;
}
v___jp_642_:
{
if (v___y_643_ == 0)
{
lean_object* v___x_644_; 
lean_inc(v_declName_614_);
lean_del_object(v___x_640_);
lean_del_object(v___x_635_);
lean_dec_ref_known(v_e_507_, 4);
v___x_644_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__5(v_declName_614_, v_fst_622_, v_fst_627_, v_fst_637_, v_nondep_618_, v_snd_638_, v_a_510_, v_a_511_, v_a_633_);
return v___x_644_;
}
else
{
uint8_t v___x_645_; 
v___x_645_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_617_, v_fst_637_);
if (v___x_645_ == 0)
{
lean_object* v___x_646_; 
lean_inc(v_declName_614_);
lean_del_object(v___x_640_);
lean_del_object(v___x_635_);
lean_dec_ref_known(v_e_507_, 4);
v___x_646_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__5(v_declName_614_, v_fst_622_, v_fst_627_, v_fst_637_, v_nondep_618_, v_snd_638_, v_a_510_, v_a_511_, v_a_633_);
return v___x_646_;
}
else
{
lean_object* v___x_648_; 
lean_dec(v_fst_637_);
lean_dec(v_fst_627_);
lean_dec(v_fst_622_);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 0, v_e_507_);
v___x_648_ = v___x_640_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_e_507_);
lean_ctor_set(v_reuseFailAlloc_652_, 1, v_snd_638_);
v___x_648_ = v_reuseFailAlloc_652_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
lean_object* v___x_650_; 
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 0, v___x_648_);
v___x_650_ = v___x_635_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v___x_648_);
lean_ctor_set(v_reuseFailAlloc_651_, 1, v_a_633_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
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
lean_dec(v_fst_627_);
lean_dec(v_fst_622_);
lean_dec_ref_known(v_e_507_, 4);
return v___x_631_;
}
}
else
{
lean_dec(v_fst_622_);
lean_dec_ref_known(v_e_507_, 4);
lean_dec(v_offset_508_);
return v___x_624_;
}
}
else
{
lean_dec_ref_known(v_e_507_, 4);
lean_dec(v_offset_508_);
return v___x_619_;
}
}
case 10:
{
lean_object* v_data_657_; lean_object* v_expr_658_; lean_object* v___x_659_; 
v_data_657_ = lean_ctor_get(v_e_507_, 0);
v_expr_658_ = lean_ctor_get(v_e_507_, 1);
lean_inc_ref(v_expr_658_);
v___x_659_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(v_beginIdx_504_, v_n_505_, v_subst_506_, v_expr_658_, v_offset_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_);
if (lean_obj_tag(v___x_659_) == 0)
{
lean_object* v_a_660_; lean_object* v_a_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_679_; 
v_a_660_ = lean_ctor_get(v___x_659_, 0);
v_a_661_ = lean_ctor_get(v___x_659_, 1);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_679_ == 0)
{
v___x_663_ = v___x_659_;
v_isShared_664_ = v_isSharedCheck_679_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_a_661_);
lean_inc(v_a_660_);
lean_dec(v___x_659_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_679_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v_fst_665_; lean_object* v_snd_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_678_; 
v_fst_665_ = lean_ctor_get(v_a_660_, 0);
v_snd_666_ = lean_ctor_get(v_a_660_, 1);
v_isSharedCheck_678_ = !lean_is_exclusive(v_a_660_);
if (v_isSharedCheck_678_ == 0)
{
v___x_668_ = v_a_660_;
v_isShared_669_ = v_isSharedCheck_678_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_snd_666_);
lean_inc(v_fst_665_);
lean_dec(v_a_660_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_678_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
uint8_t v___x_670_; 
v___x_670_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_expr_658_, v_fst_665_);
if (v___x_670_ == 0)
{
lean_object* v___x_671_; 
lean_inc(v_data_657_);
lean_del_object(v___x_668_);
lean_del_object(v___x_663_);
lean_dec_ref_known(v_e_507_, 2);
v___x_671_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__6(v_data_657_, v_fst_665_, v_snd_666_, v_a_510_, v_a_511_, v_a_661_);
return v___x_671_;
}
else
{
lean_object* v___x_673_; 
lean_dec(v_fst_665_);
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 0, v_e_507_);
v___x_673_ = v___x_668_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_e_507_);
lean_ctor_set(v_reuseFailAlloc_677_, 1, v_snd_666_);
v___x_673_ = v_reuseFailAlloc_677_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
lean_object* v___x_675_; 
if (v_isShared_664_ == 0)
{
lean_ctor_set(v___x_663_, 0, v___x_673_);
v___x_675_ = v___x_663_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v___x_673_);
lean_ctor_set(v_reuseFailAlloc_676_, 1, v_a_661_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_507_, 2);
return v___x_659_;
}
}
case 11:
{
lean_object* v_typeName_680_; lean_object* v_idx_681_; lean_object* v_struct_682_; lean_object* v___x_683_; 
v_typeName_680_ = lean_ctor_get(v_e_507_, 0);
v_idx_681_ = lean_ctor_get(v_e_507_, 1);
v_struct_682_ = lean_ctor_get(v_e_507_, 2);
lean_inc_ref(v_struct_682_);
v___x_683_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(v_beginIdx_504_, v_n_505_, v_subst_506_, v_struct_682_, v_offset_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_);
if (lean_obj_tag(v___x_683_) == 0)
{
lean_object* v_a_684_; lean_object* v_a_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_703_; 
v_a_684_ = lean_ctor_get(v___x_683_, 0);
v_a_685_ = lean_ctor_get(v___x_683_, 1);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_703_ == 0)
{
v___x_687_ = v___x_683_;
v_isShared_688_ = v_isSharedCheck_703_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_a_685_);
lean_inc(v_a_684_);
lean_dec(v___x_683_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_703_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v_fst_689_; lean_object* v_snd_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_702_; 
v_fst_689_ = lean_ctor_get(v_a_684_, 0);
v_snd_690_ = lean_ctor_get(v_a_684_, 1);
v_isSharedCheck_702_ = !lean_is_exclusive(v_a_684_);
if (v_isSharedCheck_702_ == 0)
{
v___x_692_ = v_a_684_;
v_isShared_693_ = v_isSharedCheck_702_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_snd_690_);
lean_inc(v_fst_689_);
lean_dec(v_a_684_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_702_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
uint8_t v___x_694_; 
v___x_694_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_682_, v_fst_689_);
if (v___x_694_ == 0)
{
lean_object* v___x_695_; 
lean_inc(v_idx_681_);
lean_inc(v_typeName_680_);
lean_del_object(v___x_692_);
lean_del_object(v___x_687_);
lean_dec_ref_known(v_e_507_, 3);
v___x_695_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__7(v_typeName_680_, v_idx_681_, v_fst_689_, v_snd_690_, v_a_510_, v_a_511_, v_a_685_);
return v___x_695_;
}
else
{
lean_object* v___x_697_; 
lean_dec(v_fst_689_);
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 0, v_e_507_);
v___x_697_ = v___x_692_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_e_507_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v_snd_690_);
v___x_697_ = v_reuseFailAlloc_701_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
lean_object* v___x_699_; 
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 0, v___x_697_);
v___x_699_ = v___x_687_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v___x_697_);
lean_ctor_set(v_reuseFailAlloc_700_, 1, v_a_685_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_507_, 3);
return v___x_683_;
}
}
default: 
{
lean_object* v___x_704_; lean_object* v___x_705_; 
lean_dec(v_offset_508_);
lean_dec_ref(v_e_507_);
v___x_704_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__3);
v___x_705_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8(v___x_704_, v_a_509_, v_a_510_, v_a_511_, v_a_512_);
return v___x_705_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(lean_object* v_beginIdx_706_, lean_object* v_n_707_, lean_object* v_subst_708_, lean_object* v_e_709_, lean_object* v_offset_710_, lean_object* v_a_711_, uint8_t v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_){
_start:
{
lean_object* v_key_715_; lean_object* v___x_716_; 
lean_inc(v_offset_710_);
lean_inc_ref(v_e_709_);
v_key_715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_715_, 0, v_e_709_);
lean_ctor_set(v_key_715_, 1, v_offset_710_);
v___x_716_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3___redArg(v_a_711_, v_key_715_);
if (lean_obj_tag(v___x_716_) == 1)
{
lean_object* v_val_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
lean_dec_ref_known(v_key_715_, 2);
lean_dec(v_offset_710_);
lean_dec_ref(v_e_709_);
v_val_717_ = lean_ctor_get(v___x_716_, 0);
lean_inc(v_val_717_);
lean_dec_ref_known(v___x_716_, 1);
v___x_718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_718_, 0, v_val_717_);
lean_ctor_set(v___x_718_, 1, v_a_711_);
v___x_719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_719_, 0, v___x_718_);
lean_ctor_set(v___x_719_, 1, v_a_714_);
return v___x_719_;
}
else
{
lean_object* v_s_u2081_720_; 
lean_dec(v___x_716_);
v_s_u2081_720_ = lean_nat_add(v_beginIdx_706_, v_offset_710_);
switch(lean_obj_tag(v_e_709_))
{
case 0:
{
lean_object* v_deBruijnIndex_721_; uint8_t v___x_722_; 
v_deBruijnIndex_721_ = lean_ctor_get(v_e_709_, 0);
v___x_722_ = lean_nat_dec_le(v_s_u2081_720_, v_deBruijnIndex_721_);
lean_dec(v_s_u2081_720_);
if (v___x_722_ == 0)
{
lean_object* v___x_723_; 
lean_dec(v_offset_710_);
v___x_723_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_715_, v_e_709_, v_a_711_, v_a_712_, v_a_713_, v_a_714_);
return v___x_723_;
}
else
{
lean_object* v___x_724_; uint8_t v___x_725_; 
lean_inc(v_deBruijnIndex_721_);
lean_dec_ref_known(v_e_709_, 1);
v___x_724_ = lean_nat_add(v_offset_710_, v_n_707_);
v___x_725_ = lean_nat_dec_lt(v_deBruijnIndex_721_, v___x_724_);
lean_dec(v___x_724_);
if (v___x_725_ == 0)
{
lean_object* v___x_726_; lean_object* v___x_727_; 
lean_dec(v_offset_710_);
v___x_726_ = lean_nat_sub(v_deBruijnIndex_721_, v_n_707_);
lean_dec(v_deBruijnIndex_721_);
v___x_727_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___redArg(v___x_726_, v_a_714_);
if (lean_obj_tag(v___x_727_) == 0)
{
lean_object* v_a_728_; lean_object* v_a_729_; lean_object* v___x_730_; 
v_a_728_ = lean_ctor_get(v___x_727_, 0);
lean_inc(v_a_728_);
v_a_729_ = lean_ctor_get(v___x_727_, 1);
lean_inc(v_a_729_);
lean_dec_ref_known(v___x_727_, 2);
v___x_730_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_715_, v_a_728_, v_a_711_, v_a_712_, v_a_713_, v_a_729_);
return v___x_730_;
}
else
{
lean_object* v_a_731_; lean_object* v_a_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_739_; 
lean_dec_ref_known(v_key_715_, 2);
lean_dec_ref(v_a_711_);
v_a_731_ = lean_ctor_get(v___x_727_, 0);
v_a_732_ = lean_ctor_get(v___x_727_, 1);
v_isSharedCheck_739_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_739_ == 0)
{
v___x_734_ = v___x_727_;
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_a_732_);
lean_inc(v_a_731_);
lean_dec(v___x_727_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_737_; 
if (v_isShared_735_ == 0)
{
v___x_737_ = v___x_734_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_a_731_);
lean_ctor_set(v_reuseFailAlloc_738_, 1, v_a_732_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
}
}
else
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v_v_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_740_ = lean_nat_sub(v_deBruijnIndex_721_, v_offset_710_);
lean_dec(v_deBruijnIndex_721_);
v___x_741_ = lean_nat_sub(v_n_707_, v___x_740_);
lean_dec(v___x_740_);
v___x_742_ = lean_unsigned_to_nat(1u);
v___x_743_ = lean_nat_sub(v___x_741_, v___x_742_);
lean_dec(v___x_741_);
v_v_744_ = lean_array_fget_borrowed(v_subst_708_, v___x_743_);
lean_dec(v___x_743_);
v___x_745_ = lean_unsigned_to_nat(0u);
lean_inc(v_v_744_);
v___x_746_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(v_v_744_, v___x_745_, v_offset_710_, v_a_712_, v_a_713_, v_a_714_);
lean_dec(v_offset_710_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_object* v_a_747_; lean_object* v_a_748_; lean_object* v___x_749_; 
v_a_747_ = lean_ctor_get(v___x_746_, 0);
lean_inc(v_a_747_);
v_a_748_ = lean_ctor_get(v___x_746_, 1);
lean_inc(v_a_748_);
lean_dec_ref_known(v___x_746_, 2);
v___x_749_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_715_, v_a_747_, v_a_711_, v_a_712_, v_a_713_, v_a_748_);
return v___x_749_;
}
else
{
lean_object* v_a_750_; lean_object* v_a_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_758_; 
lean_dec_ref_known(v_key_715_, 2);
lean_dec_ref(v_a_711_);
v_a_750_ = lean_ctor_get(v___x_746_, 0);
v_a_751_ = lean_ctor_get(v___x_746_, 1);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_758_ == 0)
{
v___x_753_ = v___x_746_;
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_a_751_);
lean_inc(v_a_750_);
lean_dec(v___x_746_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_756_; 
if (v_isShared_754_ == 0)
{
v___x_756_ = v___x_753_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_a_750_);
lean_ctor_set(v_reuseFailAlloc_757_, 1, v_a_751_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
}
}
}
case 9:
{
lean_object* v___x_759_; 
lean_dec(v_s_u2081_720_);
lean_dec(v_offset_710_);
v___x_759_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_715_, v_e_709_, v_a_711_, v_a_712_, v_a_713_, v_a_714_);
return v___x_759_;
}
case 2:
{
lean_object* v___x_760_; 
lean_dec(v_s_u2081_720_);
lean_dec(v_offset_710_);
v___x_760_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_715_, v_e_709_, v_a_711_, v_a_712_, v_a_713_, v_a_714_);
return v___x_760_;
}
case 1:
{
lean_object* v___x_761_; 
lean_dec(v_s_u2081_720_);
lean_dec(v_offset_710_);
v___x_761_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_715_, v_e_709_, v_a_711_, v_a_712_, v_a_713_, v_a_714_);
return v___x_761_;
}
case 4:
{
lean_object* v___x_762_; 
lean_dec(v_s_u2081_720_);
lean_dec(v_offset_710_);
v___x_762_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_715_, v_e_709_, v_a_711_, v_a_712_, v_a_713_, v_a_714_);
return v___x_762_;
}
case 3:
{
lean_object* v___x_763_; 
lean_dec(v_s_u2081_720_);
lean_dec(v_offset_710_);
v___x_763_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_715_, v_e_709_, v_a_711_, v_a_712_, v_a_713_, v_a_714_);
return v___x_763_;
}
default: 
{
lean_object* v___x_764_; uint8_t v___x_765_; 
v___x_764_ = l_Lean_Expr_looseBVarRange(v_e_709_);
v___x_765_ = lean_nat_dec_le(v___x_764_, v_s_u2081_720_);
lean_dec(v_s_u2081_720_);
lean_dec(v___x_764_);
if (v___x_765_ == 0)
{
switch(lean_obj_tag(v_e_709_))
{
case 9:
{
lean_object* v___x_766_; 
lean_dec(v_offset_710_);
v___x_766_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_715_, v_e_709_, v_a_711_, v_a_712_, v_a_713_, v_a_714_);
return v___x_766_;
}
case 2:
{
lean_object* v___x_767_; 
lean_dec(v_offset_710_);
v___x_767_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_715_, v_e_709_, v_a_711_, v_a_712_, v_a_713_, v_a_714_);
return v___x_767_;
}
case 0:
{
lean_object* v___x_768_; 
lean_dec(v_offset_710_);
v___x_768_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_715_, v_e_709_, v_a_711_, v_a_712_, v_a_713_, v_a_714_);
return v___x_768_;
}
case 1:
{
lean_object* v___x_769_; 
lean_dec(v_offset_710_);
v___x_769_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_715_, v_e_709_, v_a_711_, v_a_712_, v_a_713_, v_a_714_);
return v___x_769_;
}
case 4:
{
lean_object* v___x_770_; 
lean_dec(v_offset_710_);
v___x_770_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_715_, v_e_709_, v_a_711_, v_a_712_, v_a_713_, v_a_714_);
return v___x_770_;
}
case 3:
{
lean_object* v___x_771_; 
lean_dec(v_offset_710_);
v___x_771_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_715_, v_e_709_, v_a_711_, v_a_712_, v_a_713_, v_a_714_);
return v___x_771_;
}
default: 
{
lean_object* v___x_772_; 
v___x_772_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1(v_beginIdx_706_, v_n_707_, v_subst_708_, v_e_709_, v_offset_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_);
if (lean_obj_tag(v___x_772_) == 0)
{
lean_object* v_a_773_; lean_object* v_a_774_; lean_object* v_fst_775_; lean_object* v_snd_776_; lean_object* v___x_777_; 
v_a_773_ = lean_ctor_get(v___x_772_, 0);
lean_inc(v_a_773_);
v_a_774_ = lean_ctor_get(v___x_772_, 1);
lean_inc(v_a_774_);
lean_dec_ref_known(v___x_772_, 2);
v_fst_775_ = lean_ctor_get(v_a_773_, 0);
lean_inc(v_fst_775_);
v_snd_776_ = lean_ctor_get(v_a_773_, 1);
lean_inc(v_snd_776_);
lean_dec(v_a_773_);
v___x_777_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_715_, v_fst_775_, v_snd_776_, v_a_712_, v_a_713_, v_a_774_);
return v___x_777_;
}
else
{
lean_dec_ref_known(v_key_715_, 2);
return v___x_772_;
}
}
}
}
else
{
lean_object* v___x_778_; 
lean_dec(v_offset_710_);
v___x_778_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_715_, v_e_709_, v_a_711_, v_a_712_, v_a_713_, v_a_714_);
return v___x_778_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1___boxed(lean_object* v_beginIdx_779_, lean_object* v_n_780_, lean_object* v_subst_781_, lean_object* v_e_782_, lean_object* v_offset_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_){
_start:
{
uint8_t v_a_boxed_788_; lean_object* v_res_789_; 
v_a_boxed_788_ = lean_unbox(v_a_785_);
v_res_789_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(v_beginIdx_779_, v_n_780_, v_subst_781_, v_e_782_, v_offset_783_, v_a_784_, v_a_boxed_788_, v_a_786_, v_a_787_);
lean_dec_ref(v_a_786_);
lean_dec_ref(v_subst_781_);
lean_dec(v_n_780_);
lean_dec(v_beginIdx_779_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___boxed(lean_object* v_beginIdx_790_, lean_object* v_n_791_, lean_object* v_subst_792_, lean_object* v_e_793_, lean_object* v_offset_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_){
_start:
{
uint8_t v_a_boxed_799_; lean_object* v_res_800_; 
v_a_boxed_799_ = lean_unbox(v_a_796_);
v_res_800_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1(v_beginIdx_790_, v_n_791_, v_subst_792_, v_e_793_, v_offset_794_, v_a_795_, v_a_boxed_799_, v_a_797_, v_a_798_);
lean_dec_ref(v_a_797_);
lean_dec_ref(v_subst_792_);
lean_dec(v_n_791_);
lean_dec(v_beginIdx_790_);
return v_res_800_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__0(void){
_start:
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_801_ = lean_box(0);
v___x_802_ = lean_unsigned_to_nat(16u);
v___x_803_ = lean_mk_array(v___x_802_, v___x_801_);
return v___x_803_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__1(void){
_start:
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_804_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__0, &l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__0_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__0);
v___x_805_ = lean_unsigned_to_nat(0u);
v___x_806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_806_, 0, v___x_805_);
lean_ctor_set(v___x_806_, 1, v___x_804_);
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevRangeS___lam__0(lean_object* v_e_807_, lean_object* v_beginIdx_808_, lean_object* v_n_809_, lean_object* v_subst_810_, uint8_t v_debug_811_, lean_object* v___y_812_, lean_object* v___y_813_){
_start:
{
lean_object* v___x_814_; 
v___x_814_ = lean_unsigned_to_nat(0u);
switch(lean_obj_tag(v_e_807_))
{
case 0:
{
lean_object* v_deBruijnIndex_815_; uint8_t v___x_816_; 
v_deBruijnIndex_815_ = lean_ctor_get(v_e_807_, 0);
v___x_816_ = lean_nat_dec_le(v_beginIdx_808_, v_deBruijnIndex_815_);
if (v___x_816_ == 0)
{
lean_object* v___x_817_; 
v___x_817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_817_, 0, v_e_807_);
lean_ctor_set(v___x_817_, 1, v___y_813_);
return v___x_817_;
}
else
{
uint8_t v___x_818_; 
lean_inc(v_deBruijnIndex_815_);
lean_dec_ref_known(v_e_807_, 1);
v___x_818_ = lean_nat_dec_lt(v_deBruijnIndex_815_, v_n_809_);
if (v___x_818_ == 0)
{
lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_819_ = lean_nat_sub(v_deBruijnIndex_815_, v_n_809_);
lean_dec(v_deBruijnIndex_815_);
v___x_820_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___redArg(v___x_819_, v___y_813_);
return v___x_820_;
}
else
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v_v_824_; lean_object* v___x_825_; 
v___x_821_ = lean_nat_sub(v_n_809_, v_deBruijnIndex_815_);
lean_dec(v_deBruijnIndex_815_);
v___x_822_ = lean_unsigned_to_nat(1u);
v___x_823_ = lean_nat_sub(v___x_821_, v___x_822_);
lean_dec(v___x_821_);
v_v_824_ = lean_array_fget_borrowed(v_subst_810_, v___x_823_);
lean_dec(v___x_823_);
lean_inc(v_v_824_);
v___x_825_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(v_v_824_, v___x_814_, v___x_814_, v_debug_811_, v___y_812_, v___y_813_);
return v___x_825_;
}
}
}
case 9:
{
lean_object* v___x_826_; 
v___x_826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_826_, 0, v_e_807_);
lean_ctor_set(v___x_826_, 1, v___y_813_);
return v___x_826_;
}
case 2:
{
lean_object* v___x_827_; 
v___x_827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_827_, 0, v_e_807_);
lean_ctor_set(v___x_827_, 1, v___y_813_);
return v___x_827_;
}
case 1:
{
lean_object* v___x_828_; 
v___x_828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_828_, 0, v_e_807_);
lean_ctor_set(v___x_828_, 1, v___y_813_);
return v___x_828_;
}
case 4:
{
lean_object* v___x_829_; 
v___x_829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_829_, 0, v_e_807_);
lean_ctor_set(v___x_829_, 1, v___y_813_);
return v___x_829_;
}
case 3:
{
lean_object* v___x_830_; 
v___x_830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_830_, 0, v_e_807_);
lean_ctor_set(v___x_830_, 1, v___y_813_);
return v___x_830_;
}
default: 
{
lean_object* v___x_831_; uint8_t v___x_832_; 
v___x_831_ = l_Lean_Expr_looseBVarRange(v_e_807_);
v___x_832_ = lean_nat_dec_le(v___x_831_, v_beginIdx_808_);
lean_dec(v___x_831_);
if (v___x_832_ == 0)
{
switch(lean_obj_tag(v_e_807_))
{
case 9:
{
lean_object* v___x_833_; 
v___x_833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_833_, 0, v_e_807_);
lean_ctor_set(v___x_833_, 1, v___y_813_);
return v___x_833_;
}
case 2:
{
lean_object* v___x_834_; 
v___x_834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_834_, 0, v_e_807_);
lean_ctor_set(v___x_834_, 1, v___y_813_);
return v___x_834_;
}
case 0:
{
lean_object* v___x_835_; 
v___x_835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_835_, 0, v_e_807_);
lean_ctor_set(v___x_835_, 1, v___y_813_);
return v___x_835_;
}
case 1:
{
lean_object* v___x_836_; 
v___x_836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_836_, 0, v_e_807_);
lean_ctor_set(v___x_836_, 1, v___y_813_);
return v___x_836_;
}
case 4:
{
lean_object* v___x_837_; 
v___x_837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_837_, 0, v_e_807_);
lean_ctor_set(v___x_837_, 1, v___y_813_);
return v___x_837_;
}
case 3:
{
lean_object* v___x_838_; 
v___x_838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_838_, 0, v_e_807_);
lean_ctor_set(v___x_838_, 1, v___y_813_);
return v___x_838_;
}
default: 
{
lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_839_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__1, &l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__1_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__1);
v___x_840_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1(v_beginIdx_808_, v_n_809_, v_subst_810_, v_e_807_, v___x_814_, v___x_839_, v_debug_811_, v___y_812_, v___y_813_);
if (lean_obj_tag(v___x_840_) == 0)
{
lean_object* v_a_841_; lean_object* v_a_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_850_; 
v_a_841_ = lean_ctor_get(v___x_840_, 0);
v_a_842_ = lean_ctor_get(v___x_840_, 1);
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_850_ == 0)
{
v___x_844_ = v___x_840_;
v_isShared_845_ = v_isSharedCheck_850_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_a_842_);
lean_inc(v_a_841_);
lean_dec(v___x_840_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_850_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v_fst_846_; lean_object* v___x_848_; 
v_fst_846_ = lean_ctor_get(v_a_841_, 0);
lean_inc(v_fst_846_);
lean_dec(v_a_841_);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 0, v_fst_846_);
v___x_848_ = v___x_844_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_fst_846_);
lean_ctor_set(v_reuseFailAlloc_849_, 1, v_a_842_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
else
{
lean_object* v_a_851_; lean_object* v_a_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_859_; 
v_a_851_ = lean_ctor_get(v___x_840_, 0);
v_a_852_ = lean_ctor_get(v___x_840_, 1);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_859_ == 0)
{
v___x_854_ = v___x_840_;
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_a_852_);
lean_inc(v_a_851_);
lean_dec(v___x_840_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_857_; 
if (v_isShared_855_ == 0)
{
v___x_857_ = v___x_854_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v_a_851_);
lean_ctor_set(v_reuseFailAlloc_858_, 1, v_a_852_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
}
}
}
else
{
lean_object* v___x_860_; 
v___x_860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_860_, 0, v_e_807_);
lean_ctor_set(v___x_860_, 1, v___y_813_);
return v___x_860_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___boxed(lean_object* v_e_861_, lean_object* v_beginIdx_862_, lean_object* v_n_863_, lean_object* v_subst_864_, lean_object* v_debug_865_, lean_object* v___y_866_, lean_object* v___y_867_){
_start:
{
uint8_t v_debug_boxed_868_; lean_object* v_res_869_; 
v_debug_boxed_868_ = lean_unbox(v_debug_865_);
v_res_869_ = l_Lean_Meta_Sym_instantiateRevRangeS___lam__0(v_e_861_, v_beginIdx_862_, v_n_863_, v_subst_864_, v_debug_boxed_868_, v___y_866_, v___y_867_);
lean_dec_ref(v___y_866_);
lean_dec_ref(v_subst_864_);
lean_dec(v_n_863_);
lean_dec(v_beginIdx_862_);
return v_res_869_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__2(void){
_start:
{
lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_872_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__2));
v___x_873_ = lean_unsigned_to_nat(16u);
v___x_874_ = lean_unsigned_to_nat(62u);
v___x_875_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__1));
v___x_876_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__0));
v___x_877_ = l_mkPanicMessageWithDecl(v___x_876_, v___x_875_, v___x_874_, v___x_873_, v___x_872_);
return v___x_877_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__5(void){
_start:
{
lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_880_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__2));
v___x_881_ = lean_unsigned_to_nat(34u);
v___x_882_ = lean_unsigned_to_nat(20u);
v___x_883_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__4));
v___x_884_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__3));
v___x_885_ = l_mkPanicMessageWithDecl(v___x_884_, v___x_883_, v___x_882_, v___x_881_, v___x_880_);
return v___x_885_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__6(void){
_start:
{
lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_886_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__2));
v___x_887_ = lean_unsigned_to_nat(32u);
v___x_888_ = lean_unsigned_to_nat(19u);
v___x_889_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__4));
v___x_890_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__3));
v___x_891_ = l_mkPanicMessageWithDecl(v___x_890_, v___x_889_, v___x_888_, v___x_887_, v___x_886_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevRangeS(lean_object* v_e_892_, lean_object* v_beginIdx_893_, lean_object* v_endIdx_894_, lean_object* v_subst_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_){
_start:
{
uint8_t v___x_903_; 
v___x_903_ = lean_nat_dec_lt(v_endIdx_894_, v_beginIdx_893_);
if (v___x_903_ == 0)
{
lean_object* v___x_904_; uint8_t v___x_905_; 
v___x_904_ = lean_array_get_size(v_subst_895_);
v___x_905_ = lean_nat_dec_lt(v___x_904_, v_endIdx_894_);
if (v___x_905_ == 0)
{
lean_object* v___x_906_; lean_object* v___x_907_; uint8_t v_debug_908_; lean_object* v_env_909_; lean_object* v_n_910_; lean_object* v___x_911_; lean_object* v___f_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_906_ = lean_st_ref_get(v_a_897_);
v___x_907_ = lean_st_ref_get(v_a_901_);
v_debug_908_ = lean_ctor_get_uint8(v___x_906_, sizeof(void*)*10);
lean_dec(v___x_906_);
v_env_909_ = lean_ctor_get(v___x_907_, 0);
lean_inc_ref(v_env_909_);
lean_dec(v___x_907_);
v_n_910_ = lean_nat_sub(v_endIdx_894_, v_beginIdx_893_);
v___x_911_ = lean_box(v_debug_908_);
v___f_912_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___boxed), 7, 5);
lean_closure_set(v___f_912_, 0, v_e_892_);
lean_closure_set(v___f_912_, 1, v_beginIdx_893_);
lean_closure_set(v___f_912_, 2, v_n_910_);
lean_closure_set(v___f_912_, 3, v_subst_895_);
lean_closure_set(v___f_912_, 4, v___x_911_);
v___x_913_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_913_, 0, v_env_909_);
lean_ctor_set_uint8(v___x_913_, sizeof(void*)*1, v___x_905_);
lean_ctor_set_uint8(v___x_913_, sizeof(void*)*1 + 1, v___x_905_);
v___x_914_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_912_, v___x_913_, v_a_897_);
if (lean_obj_tag(v___x_914_) == 0)
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_925_; 
v_a_915_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_925_ == 0)
{
v___x_917_ = v___x_914_;
v_isShared_918_ = v_isSharedCheck_925_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_914_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_925_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
if (lean_obj_tag(v_a_915_) == 0)
{
lean_object* v___x_919_; lean_object* v___x_920_; 
lean_dec_ref_known(v_a_915_, 1);
lean_del_object(v___x_917_);
v___x_919_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__2, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__2_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__2);
v___x_920_ = l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(v___x_919_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_);
return v___x_920_;
}
else
{
lean_object* v_a_921_; lean_object* v___x_923_; 
v_a_921_ = lean_ctor_get(v_a_915_, 0);
lean_inc(v_a_921_);
lean_dec_ref_known(v_a_915_, 1);
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 0, v_a_921_);
v___x_923_ = v___x_917_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v_a_921_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
}
else
{
lean_object* v_a_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_933_; 
v_a_926_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_933_ == 0)
{
v___x_928_ = v___x_914_;
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_a_926_);
lean_dec(v___x_914_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_931_; 
if (v_isShared_929_ == 0)
{
v___x_931_ = v___x_928_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_a_926_);
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
lean_object* v___x_934_; lean_object* v___x_935_; 
lean_dec_ref(v_subst_895_);
lean_dec(v_beginIdx_893_);
lean_dec_ref(v_e_892_);
v___x_934_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__5, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__5_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__5);
v___x_935_ = l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(v___x_934_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_);
return v___x_935_;
}
}
else
{
lean_object* v___x_936_; lean_object* v___x_937_; 
lean_dec_ref(v_subst_895_);
lean_dec(v_beginIdx_893_);
lean_dec_ref(v_e_892_);
v___x_936_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__6, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__6_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__6);
v___x_937_ = l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(v___x_936_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_);
return v___x_937_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevRangeS___boxed(lean_object* v_e_938_, lean_object* v_beginIdx_939_, lean_object* v_endIdx_940_, lean_object* v_subst_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_e_938_, v_beginIdx_939_, v_endIdx_940_, v_subst_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_);
lean_dec(v_a_947_);
lean_dec_ref(v_a_946_);
lean_dec(v_a_945_);
lean_dec_ref(v_a_944_);
lean_dec(v_a_943_);
lean_dec_ref(v_a_942_);
lean_dec(v_endIdx_940_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_950_, lean_object* v_m_951_, lean_object* v_a_952_){
_start:
{
lean_object* v___x_953_; 
v___x_953_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3___redArg(v_m_951_, v_a_952_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_954_, lean_object* v_m_955_, lean_object* v_a_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3(v_00_u03b2_954_, v_m_955_, v_a_956_);
lean_dec_ref(v_a_956_);
lean_dec_ref(v_m_955_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11(lean_object* v_00_u03b2_958_, lean_object* v_a_959_, lean_object* v_x_960_){
_start:
{
lean_object* v___x_961_; 
v___x_961_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11___redArg(v_a_959_, v_x_960_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11___boxed(lean_object* v_00_u03b2_962_, lean_object* v_a_963_, lean_object* v_x_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11(v_00_u03b2_962_, v_a_963_, v_x_964_);
lean_dec(v_x_964_);
lean_dec_ref(v_a_963_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevS(lean_object* v_e_966_, lean_object* v_subst_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_){
_start:
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_975_ = lean_unsigned_to_nat(0u);
v___x_976_ = lean_array_get_size(v_subst_967_);
v___x_977_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_e_966_, v___x_975_, v___x_976_, v_subst_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevS___boxed(lean_object* v_e_978_, lean_object* v_subst_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_){
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l_Lean_Meta_Sym_instantiateRevS(v_e_978_, v_subst_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_);
lean_dec(v_a_985_);
lean_dec_ref(v_a_984_);
lean_dec(v_a_983_);
lean_dec_ref(v_a_982_);
lean_dec(v_a_981_);
lean_dec_ref(v_a_980_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1(lean_object* v_msg_990_, uint8_t v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_){
_start:
{
lean_object* v___f_994_; lean_object* v___f_995_; lean_object* v___x_996_; lean_object* v___f_997_; lean_object* v___f_998_; lean_object* v___f_999_; lean_object* v___x_2853__overap_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___f_994_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1___closed__0));
v___f_995_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1___closed__1));
v___x_996_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___f_994_, v___f_995_);
v___f_997_ = lean_alloc_closure((void*)(l_EStateM_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_997_, 0, v___x_996_);
v___f_998_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_998_, 0, v___f_997_);
v___f_999_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_999_, 0, v___f_998_);
v___x_2853__overap_1000_ = lean_panic_fn_borrowed(v___f_999_, v_msg_990_);
lean_dec_ref(v___f_999_);
v___x_1001_ = lean_box(v___y_991_);
lean_inc_ref(v___y_992_);
v___x_1002_ = lean_apply_3(v___x_2853__overap_1000_, v___x_1001_, v___y_992_, v___y_993_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1___boxed(lean_object* v_msg_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_){
_start:
{
uint8_t v___y_3329__boxed_1007_; lean_object* v_res_1008_; 
v___y_3329__boxed_1007_ = lean_unbox(v___y_1004_);
v_res_1008_ = l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1(v_msg_1003_, v___y_3329__boxed_1007_, v___y_1005_, v___y_1006_);
lean_dec_ref(v___y_1005_);
return v_res_1008_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0(lean_object* v_n_1009_, lean_object* v_beginIdx_1010_, lean_object* v_subst_1011_, lean_object* v_e_1012_, lean_object* v_offset_1013_, lean_object* v_a_1014_, uint8_t v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_){
_start:
{
switch(lean_obj_tag(v_e_1012_))
{
case 5:
{
lean_object* v_fn_1018_; lean_object* v_arg_1019_; lean_object* v___x_1020_; 
v_fn_1018_ = lean_ctor_get(v_e_1012_, 0);
v_arg_1019_ = lean_ctor_get(v_e_1012_, 1);
lean_inc(v_offset_1013_);
lean_inc_ref(v_fn_1018_);
v___x_1020_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1009_, v_beginIdx_1010_, v_subst_1011_, v_fn_1018_, v_offset_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_);
if (lean_obj_tag(v___x_1020_) == 0)
{
lean_object* v_a_1021_; lean_object* v_a_1022_; lean_object* v_fst_1023_; lean_object* v_snd_1024_; lean_object* v___x_1025_; 
v_a_1021_ = lean_ctor_get(v___x_1020_, 0);
lean_inc(v_a_1021_);
v_a_1022_ = lean_ctor_get(v___x_1020_, 1);
lean_inc(v_a_1022_);
lean_dec_ref_known(v___x_1020_, 2);
v_fst_1023_ = lean_ctor_get(v_a_1021_, 0);
lean_inc(v_fst_1023_);
v_snd_1024_ = lean_ctor_get(v_a_1021_, 1);
lean_inc(v_snd_1024_);
lean_dec(v_a_1021_);
lean_inc_ref(v_arg_1019_);
v___x_1025_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1009_, v_beginIdx_1010_, v_subst_1011_, v_arg_1019_, v_offset_1013_, v_snd_1024_, v_a_1015_, v_a_1016_, v_a_1022_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_object* v_a_1026_; lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1048_; 
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
v_a_1027_ = lean_ctor_get(v___x_1025_, 1);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1029_ = v___x_1025_;
v_isShared_1030_ = v_isSharedCheck_1048_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_inc(v_a_1026_);
lean_dec(v___x_1025_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1048_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v_fst_1031_; lean_object* v_snd_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1047_; 
v_fst_1031_ = lean_ctor_get(v_a_1026_, 0);
v_snd_1032_ = lean_ctor_get(v_a_1026_, 1);
v_isSharedCheck_1047_ = !lean_is_exclusive(v_a_1026_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1034_ = v_a_1026_;
v_isShared_1035_ = v_isSharedCheck_1047_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_snd_1032_);
lean_inc(v_fst_1031_);
lean_dec(v_a_1026_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1047_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
uint8_t v___y_1037_; uint8_t v___x_1045_; 
v___x_1045_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_1018_, v_fst_1023_);
if (v___x_1045_ == 0)
{
v___y_1037_ = v___x_1045_;
goto v___jp_1036_;
}
else
{
uint8_t v___x_1046_; 
v___x_1046_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_1019_, v_fst_1031_);
v___y_1037_ = v___x_1046_;
goto v___jp_1036_;
}
v___jp_1036_:
{
if (v___y_1037_ == 0)
{
lean_object* v___x_1038_; 
lean_del_object(v___x_1034_);
lean_del_object(v___x_1029_);
lean_dec_ref_known(v_e_1012_, 2);
v___x_1038_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__2(v_fst_1023_, v_fst_1031_, v_snd_1032_, v_a_1015_, v_a_1016_, v_a_1027_);
return v___x_1038_;
}
else
{
lean_object* v___x_1040_; 
lean_dec(v_fst_1031_);
lean_dec(v_fst_1023_);
if (v_isShared_1035_ == 0)
{
lean_ctor_set(v___x_1034_, 0, v_e_1012_);
v___x_1040_ = v___x_1034_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v_e_1012_);
lean_ctor_set(v_reuseFailAlloc_1044_, 1, v_snd_1032_);
v___x_1040_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
lean_object* v___x_1042_; 
if (v_isShared_1030_ == 0)
{
lean_ctor_set(v___x_1029_, 0, v___x_1040_);
v___x_1042_ = v___x_1029_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v___x_1040_);
lean_ctor_set(v_reuseFailAlloc_1043_, 1, v_a_1027_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1023_);
lean_dec_ref_known(v_e_1012_, 2);
return v___x_1025_;
}
}
else
{
lean_dec_ref_known(v_e_1012_, 2);
lean_dec(v_offset_1013_);
return v___x_1020_;
}
}
case 6:
{
lean_object* v_binderName_1049_; lean_object* v_binderType_1050_; lean_object* v_body_1051_; uint8_t v_binderInfo_1052_; lean_object* v___x_1053_; 
v_binderName_1049_ = lean_ctor_get(v_e_1012_, 0);
v_binderType_1050_ = lean_ctor_get(v_e_1012_, 1);
v_body_1051_ = lean_ctor_get(v_e_1012_, 2);
v_binderInfo_1052_ = lean_ctor_get_uint8(v_e_1012_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1013_);
lean_inc_ref(v_binderType_1050_);
v___x_1053_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1009_, v_beginIdx_1010_, v_subst_1011_, v_binderType_1050_, v_offset_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_);
if (lean_obj_tag(v___x_1053_) == 0)
{
lean_object* v_a_1054_; lean_object* v_a_1055_; lean_object* v_fst_1056_; lean_object* v_snd_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; 
v_a_1054_ = lean_ctor_get(v___x_1053_, 0);
lean_inc(v_a_1054_);
v_a_1055_ = lean_ctor_get(v___x_1053_, 1);
lean_inc(v_a_1055_);
lean_dec_ref_known(v___x_1053_, 2);
v_fst_1056_ = lean_ctor_get(v_a_1054_, 0);
lean_inc(v_fst_1056_);
v_snd_1057_ = lean_ctor_get(v_a_1054_, 1);
lean_inc(v_snd_1057_);
lean_dec(v_a_1054_);
v___x_1058_ = lean_unsigned_to_nat(1u);
v___x_1059_ = lean_nat_add(v_offset_1013_, v___x_1058_);
lean_dec(v_offset_1013_);
lean_inc_ref(v_body_1051_);
v___x_1060_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1009_, v_beginIdx_1010_, v_subst_1011_, v_body_1051_, v___x_1059_, v_snd_1057_, v_a_1015_, v_a_1016_, v_a_1055_);
if (lean_obj_tag(v___x_1060_) == 0)
{
lean_object* v_a_1061_; lean_object* v_a_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1083_; 
v_a_1061_ = lean_ctor_get(v___x_1060_, 0);
v_a_1062_ = lean_ctor_get(v___x_1060_, 1);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1064_ = v___x_1060_;
v_isShared_1065_ = v_isSharedCheck_1083_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_a_1062_);
lean_inc(v_a_1061_);
lean_dec(v___x_1060_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1083_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v_fst_1066_; lean_object* v_snd_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1082_; 
v_fst_1066_ = lean_ctor_get(v_a_1061_, 0);
v_snd_1067_ = lean_ctor_get(v_a_1061_, 1);
v_isSharedCheck_1082_ = !lean_is_exclusive(v_a_1061_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1069_ = v_a_1061_;
v_isShared_1070_ = v_isSharedCheck_1082_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_snd_1067_);
lean_inc(v_fst_1066_);
lean_dec(v_a_1061_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1082_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
uint8_t v___y_1072_; uint8_t v___x_1080_; 
v___x_1080_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_1050_, v_fst_1056_);
if (v___x_1080_ == 0)
{
v___y_1072_ = v___x_1080_;
goto v___jp_1071_;
}
else
{
uint8_t v___x_1081_; 
v___x_1081_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1051_, v_fst_1066_);
v___y_1072_ = v___x_1081_;
goto v___jp_1071_;
}
v___jp_1071_:
{
if (v___y_1072_ == 0)
{
lean_object* v___x_1073_; 
lean_inc(v_binderName_1049_);
lean_del_object(v___x_1069_);
lean_del_object(v___x_1064_);
lean_dec_ref_known(v_e_1012_, 3);
v___x_1073_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__3(v_binderName_1049_, v_binderInfo_1052_, v_fst_1056_, v_fst_1066_, v_snd_1067_, v_a_1015_, v_a_1016_, v_a_1062_);
return v___x_1073_;
}
else
{
lean_object* v___x_1075_; 
lean_dec(v_fst_1066_);
lean_dec(v_fst_1056_);
if (v_isShared_1070_ == 0)
{
lean_ctor_set(v___x_1069_, 0, v_e_1012_);
v___x_1075_ = v___x_1069_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_e_1012_);
lean_ctor_set(v_reuseFailAlloc_1079_, 1, v_snd_1067_);
v___x_1075_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
lean_object* v___x_1077_; 
if (v_isShared_1065_ == 0)
{
lean_ctor_set(v___x_1064_, 0, v___x_1075_);
v___x_1077_ = v___x_1064_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v___x_1075_);
lean_ctor_set(v_reuseFailAlloc_1078_, 1, v_a_1062_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
return v___x_1077_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1056_);
lean_dec_ref_known(v_e_1012_, 3);
return v___x_1060_;
}
}
else
{
lean_dec_ref_known(v_e_1012_, 3);
lean_dec(v_offset_1013_);
return v___x_1053_;
}
}
case 7:
{
lean_object* v_binderName_1084_; lean_object* v_binderType_1085_; lean_object* v_body_1086_; uint8_t v_binderInfo_1087_; lean_object* v___x_1088_; 
v_binderName_1084_ = lean_ctor_get(v_e_1012_, 0);
v_binderType_1085_ = lean_ctor_get(v_e_1012_, 1);
v_body_1086_ = lean_ctor_get(v_e_1012_, 2);
v_binderInfo_1087_ = lean_ctor_get_uint8(v_e_1012_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1013_);
lean_inc_ref(v_binderType_1085_);
v___x_1088_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1009_, v_beginIdx_1010_, v_subst_1011_, v_binderType_1085_, v_offset_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_);
if (lean_obj_tag(v___x_1088_) == 0)
{
lean_object* v_a_1089_; lean_object* v_a_1090_; lean_object* v_fst_1091_; lean_object* v_snd_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v_a_1089_ = lean_ctor_get(v___x_1088_, 0);
lean_inc(v_a_1089_);
v_a_1090_ = lean_ctor_get(v___x_1088_, 1);
lean_inc(v_a_1090_);
lean_dec_ref_known(v___x_1088_, 2);
v_fst_1091_ = lean_ctor_get(v_a_1089_, 0);
lean_inc(v_fst_1091_);
v_snd_1092_ = lean_ctor_get(v_a_1089_, 1);
lean_inc(v_snd_1092_);
lean_dec(v_a_1089_);
v___x_1093_ = lean_unsigned_to_nat(1u);
v___x_1094_ = lean_nat_add(v_offset_1013_, v___x_1093_);
lean_dec(v_offset_1013_);
lean_inc_ref(v_body_1086_);
v___x_1095_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1009_, v_beginIdx_1010_, v_subst_1011_, v_body_1086_, v___x_1094_, v_snd_1092_, v_a_1015_, v_a_1016_, v_a_1090_);
if (lean_obj_tag(v___x_1095_) == 0)
{
lean_object* v_a_1096_; lean_object* v_a_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1118_; 
v_a_1096_ = lean_ctor_get(v___x_1095_, 0);
v_a_1097_ = lean_ctor_get(v___x_1095_, 1);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1095_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1099_ = v___x_1095_;
v_isShared_1100_ = v_isSharedCheck_1118_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_a_1097_);
lean_inc(v_a_1096_);
lean_dec(v___x_1095_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1118_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v_fst_1101_; lean_object* v_snd_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1117_; 
v_fst_1101_ = lean_ctor_get(v_a_1096_, 0);
v_snd_1102_ = lean_ctor_get(v_a_1096_, 1);
v_isSharedCheck_1117_ = !lean_is_exclusive(v_a_1096_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1104_ = v_a_1096_;
v_isShared_1105_ = v_isSharedCheck_1117_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_snd_1102_);
lean_inc(v_fst_1101_);
lean_dec(v_a_1096_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1117_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
uint8_t v___y_1107_; uint8_t v___x_1115_; 
v___x_1115_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_1085_, v_fst_1091_);
if (v___x_1115_ == 0)
{
v___y_1107_ = v___x_1115_;
goto v___jp_1106_;
}
else
{
uint8_t v___x_1116_; 
v___x_1116_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1086_, v_fst_1101_);
v___y_1107_ = v___x_1116_;
goto v___jp_1106_;
}
v___jp_1106_:
{
if (v___y_1107_ == 0)
{
lean_object* v___x_1108_; 
lean_inc(v_binderName_1084_);
lean_del_object(v___x_1104_);
lean_del_object(v___x_1099_);
lean_dec_ref_known(v_e_1012_, 3);
v___x_1108_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__4(v_binderName_1084_, v_binderInfo_1087_, v_fst_1091_, v_fst_1101_, v_snd_1102_, v_a_1015_, v_a_1016_, v_a_1097_);
return v___x_1108_;
}
else
{
lean_object* v___x_1110_; 
lean_dec(v_fst_1101_);
lean_dec(v_fst_1091_);
if (v_isShared_1105_ == 0)
{
lean_ctor_set(v___x_1104_, 0, v_e_1012_);
v___x_1110_ = v___x_1104_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_e_1012_);
lean_ctor_set(v_reuseFailAlloc_1114_, 1, v_snd_1102_);
v___x_1110_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
lean_object* v___x_1112_; 
if (v_isShared_1100_ == 0)
{
lean_ctor_set(v___x_1099_, 0, v___x_1110_);
v___x_1112_ = v___x_1099_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v___x_1110_);
lean_ctor_set(v_reuseFailAlloc_1113_, 1, v_a_1097_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1091_);
lean_dec_ref_known(v_e_1012_, 3);
return v___x_1095_;
}
}
else
{
lean_dec_ref_known(v_e_1012_, 3);
lean_dec(v_offset_1013_);
return v___x_1088_;
}
}
case 8:
{
lean_object* v_declName_1119_; lean_object* v_type_1120_; lean_object* v_value_1121_; lean_object* v_body_1122_; uint8_t v_nondep_1123_; lean_object* v___x_1124_; 
v_declName_1119_ = lean_ctor_get(v_e_1012_, 0);
v_type_1120_ = lean_ctor_get(v_e_1012_, 1);
v_value_1121_ = lean_ctor_get(v_e_1012_, 2);
v_body_1122_ = lean_ctor_get(v_e_1012_, 3);
v_nondep_1123_ = lean_ctor_get_uint8(v_e_1012_, sizeof(void*)*4 + 8);
lean_inc(v_offset_1013_);
lean_inc_ref(v_type_1120_);
v___x_1124_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1009_, v_beginIdx_1010_, v_subst_1011_, v_type_1120_, v_offset_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_);
if (lean_obj_tag(v___x_1124_) == 0)
{
lean_object* v_a_1125_; lean_object* v_a_1126_; lean_object* v_fst_1127_; lean_object* v_snd_1128_; lean_object* v___x_1129_; 
v_a_1125_ = lean_ctor_get(v___x_1124_, 0);
lean_inc(v_a_1125_);
v_a_1126_ = lean_ctor_get(v___x_1124_, 1);
lean_inc(v_a_1126_);
lean_dec_ref_known(v___x_1124_, 2);
v_fst_1127_ = lean_ctor_get(v_a_1125_, 0);
lean_inc(v_fst_1127_);
v_snd_1128_ = lean_ctor_get(v_a_1125_, 1);
lean_inc(v_snd_1128_);
lean_dec(v_a_1125_);
lean_inc(v_offset_1013_);
lean_inc_ref(v_value_1121_);
v___x_1129_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1009_, v_beginIdx_1010_, v_subst_1011_, v_value_1121_, v_offset_1013_, v_snd_1128_, v_a_1015_, v_a_1016_, v_a_1126_);
if (lean_obj_tag(v___x_1129_) == 0)
{
lean_object* v_a_1130_; lean_object* v_a_1131_; lean_object* v_fst_1132_; lean_object* v_snd_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; 
v_a_1130_ = lean_ctor_get(v___x_1129_, 0);
lean_inc(v_a_1130_);
v_a_1131_ = lean_ctor_get(v___x_1129_, 1);
lean_inc(v_a_1131_);
lean_dec_ref_known(v___x_1129_, 2);
v_fst_1132_ = lean_ctor_get(v_a_1130_, 0);
lean_inc(v_fst_1132_);
v_snd_1133_ = lean_ctor_get(v_a_1130_, 1);
lean_inc(v_snd_1133_);
lean_dec(v_a_1130_);
v___x_1134_ = lean_unsigned_to_nat(1u);
v___x_1135_ = lean_nat_add(v_offset_1013_, v___x_1134_);
lean_dec(v_offset_1013_);
lean_inc_ref(v_body_1122_);
v___x_1136_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1009_, v_beginIdx_1010_, v_subst_1011_, v_body_1122_, v___x_1135_, v_snd_1133_, v_a_1015_, v_a_1016_, v_a_1131_);
if (lean_obj_tag(v___x_1136_) == 0)
{
lean_object* v_a_1137_; lean_object* v_a_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1161_; 
v_a_1137_ = lean_ctor_get(v___x_1136_, 0);
v_a_1138_ = lean_ctor_get(v___x_1136_, 1);
v_isSharedCheck_1161_ = !lean_is_exclusive(v___x_1136_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1140_ = v___x_1136_;
v_isShared_1141_ = v_isSharedCheck_1161_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_a_1138_);
lean_inc(v_a_1137_);
lean_dec(v___x_1136_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1161_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v_fst_1142_; lean_object* v_snd_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1160_; 
v_fst_1142_ = lean_ctor_get(v_a_1137_, 0);
v_snd_1143_ = lean_ctor_get(v_a_1137_, 1);
v_isSharedCheck_1160_ = !lean_is_exclusive(v_a_1137_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1145_ = v_a_1137_;
v_isShared_1146_ = v_isSharedCheck_1160_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_snd_1143_);
lean_inc(v_fst_1142_);
lean_dec(v_a_1137_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1160_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
uint8_t v___y_1148_; uint8_t v___x_1158_; 
v___x_1158_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_type_1120_, v_fst_1127_);
if (v___x_1158_ == 0)
{
v___y_1148_ = v___x_1158_;
goto v___jp_1147_;
}
else
{
uint8_t v___x_1159_; 
v___x_1159_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_value_1121_, v_fst_1132_);
v___y_1148_ = v___x_1159_;
goto v___jp_1147_;
}
v___jp_1147_:
{
if (v___y_1148_ == 0)
{
lean_object* v___x_1149_; 
lean_inc(v_declName_1119_);
lean_del_object(v___x_1145_);
lean_del_object(v___x_1140_);
lean_dec_ref_known(v_e_1012_, 4);
v___x_1149_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__5(v_declName_1119_, v_fst_1127_, v_fst_1132_, v_fst_1142_, v_nondep_1123_, v_snd_1143_, v_a_1015_, v_a_1016_, v_a_1138_);
return v___x_1149_;
}
else
{
uint8_t v___x_1150_; 
v___x_1150_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1122_, v_fst_1142_);
if (v___x_1150_ == 0)
{
lean_object* v___x_1151_; 
lean_inc(v_declName_1119_);
lean_del_object(v___x_1145_);
lean_del_object(v___x_1140_);
lean_dec_ref_known(v_e_1012_, 4);
v___x_1151_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__5(v_declName_1119_, v_fst_1127_, v_fst_1132_, v_fst_1142_, v_nondep_1123_, v_snd_1143_, v_a_1015_, v_a_1016_, v_a_1138_);
return v___x_1151_;
}
else
{
lean_object* v___x_1153_; 
lean_dec(v_fst_1142_);
lean_dec(v_fst_1132_);
lean_dec(v_fst_1127_);
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 0, v_e_1012_);
v___x_1153_ = v___x_1145_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v_e_1012_);
lean_ctor_set(v_reuseFailAlloc_1157_, 1, v_snd_1143_);
v___x_1153_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
lean_object* v___x_1155_; 
if (v_isShared_1141_ == 0)
{
lean_ctor_set(v___x_1140_, 0, v___x_1153_);
v___x_1155_ = v___x_1140_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v___x_1153_);
lean_ctor_set(v_reuseFailAlloc_1156_, 1, v_a_1138_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
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
lean_dec(v_fst_1132_);
lean_dec(v_fst_1127_);
lean_dec_ref_known(v_e_1012_, 4);
return v___x_1136_;
}
}
else
{
lean_dec(v_fst_1127_);
lean_dec_ref_known(v_e_1012_, 4);
lean_dec(v_offset_1013_);
return v___x_1129_;
}
}
else
{
lean_dec_ref_known(v_e_1012_, 4);
lean_dec(v_offset_1013_);
return v___x_1124_;
}
}
case 10:
{
lean_object* v_data_1162_; lean_object* v_expr_1163_; lean_object* v___x_1164_; 
v_data_1162_ = lean_ctor_get(v_e_1012_, 0);
v_expr_1163_ = lean_ctor_get(v_e_1012_, 1);
lean_inc_ref(v_expr_1163_);
v___x_1164_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1009_, v_beginIdx_1010_, v_subst_1011_, v_expr_1163_, v_offset_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_);
if (lean_obj_tag(v___x_1164_) == 0)
{
lean_object* v_a_1165_; lean_object* v_a_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1184_; 
v_a_1165_ = lean_ctor_get(v___x_1164_, 0);
v_a_1166_ = lean_ctor_get(v___x_1164_, 1);
v_isSharedCheck_1184_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1184_ == 0)
{
v___x_1168_ = v___x_1164_;
v_isShared_1169_ = v_isSharedCheck_1184_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_a_1166_);
lean_inc(v_a_1165_);
lean_dec(v___x_1164_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1184_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v_fst_1170_; lean_object* v_snd_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1183_; 
v_fst_1170_ = lean_ctor_get(v_a_1165_, 0);
v_snd_1171_ = lean_ctor_get(v_a_1165_, 1);
v_isSharedCheck_1183_ = !lean_is_exclusive(v_a_1165_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1173_ = v_a_1165_;
v_isShared_1174_ = v_isSharedCheck_1183_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_snd_1171_);
lean_inc(v_fst_1170_);
lean_dec(v_a_1165_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1183_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
uint8_t v___x_1175_; 
v___x_1175_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_expr_1163_, v_fst_1170_);
if (v___x_1175_ == 0)
{
lean_object* v___x_1176_; 
lean_inc(v_data_1162_);
lean_del_object(v___x_1173_);
lean_del_object(v___x_1168_);
lean_dec_ref_known(v_e_1012_, 2);
v___x_1176_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__6(v_data_1162_, v_fst_1170_, v_snd_1171_, v_a_1015_, v_a_1016_, v_a_1166_);
return v___x_1176_;
}
else
{
lean_object* v___x_1178_; 
lean_dec(v_fst_1170_);
if (v_isShared_1174_ == 0)
{
lean_ctor_set(v___x_1173_, 0, v_e_1012_);
v___x_1178_ = v___x_1173_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_e_1012_);
lean_ctor_set(v_reuseFailAlloc_1182_, 1, v_snd_1171_);
v___x_1178_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
lean_object* v___x_1180_; 
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 0, v___x_1178_);
v___x_1180_ = v___x_1168_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v___x_1178_);
lean_ctor_set(v_reuseFailAlloc_1181_, 1, v_a_1166_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_1012_, 2);
return v___x_1164_;
}
}
case 11:
{
lean_object* v_typeName_1185_; lean_object* v_idx_1186_; lean_object* v_struct_1187_; lean_object* v___x_1188_; 
v_typeName_1185_ = lean_ctor_get(v_e_1012_, 0);
v_idx_1186_ = lean_ctor_get(v_e_1012_, 1);
v_struct_1187_ = lean_ctor_get(v_e_1012_, 2);
lean_inc_ref(v_struct_1187_);
v___x_1188_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1009_, v_beginIdx_1010_, v_subst_1011_, v_struct_1187_, v_offset_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_);
if (lean_obj_tag(v___x_1188_) == 0)
{
lean_object* v_a_1189_; lean_object* v_a_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1208_; 
v_a_1189_ = lean_ctor_get(v___x_1188_, 0);
v_a_1190_ = lean_ctor_get(v___x_1188_, 1);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1188_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1192_ = v___x_1188_;
v_isShared_1193_ = v_isSharedCheck_1208_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_a_1190_);
lean_inc(v_a_1189_);
lean_dec(v___x_1188_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1208_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v_fst_1194_; lean_object* v_snd_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1207_; 
v_fst_1194_ = lean_ctor_get(v_a_1189_, 0);
v_snd_1195_ = lean_ctor_get(v_a_1189_, 1);
v_isSharedCheck_1207_ = !lean_is_exclusive(v_a_1189_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1197_ = v_a_1189_;
v_isShared_1198_ = v_isSharedCheck_1207_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_snd_1195_);
lean_inc(v_fst_1194_);
lean_dec(v_a_1189_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1207_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
uint8_t v___x_1199_; 
v___x_1199_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_1187_, v_fst_1194_);
if (v___x_1199_ == 0)
{
lean_object* v___x_1200_; 
lean_inc(v_idx_1186_);
lean_inc(v_typeName_1185_);
lean_del_object(v___x_1197_);
lean_del_object(v___x_1192_);
lean_dec_ref_known(v_e_1012_, 3);
v___x_1200_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__7(v_typeName_1185_, v_idx_1186_, v_fst_1194_, v_snd_1195_, v_a_1015_, v_a_1016_, v_a_1190_);
return v___x_1200_;
}
else
{
lean_object* v___x_1202_; 
lean_dec(v_fst_1194_);
if (v_isShared_1198_ == 0)
{
lean_ctor_set(v___x_1197_, 0, v_e_1012_);
v___x_1202_ = v___x_1197_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_e_1012_);
lean_ctor_set(v_reuseFailAlloc_1206_, 1, v_snd_1195_);
v___x_1202_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
lean_object* v___x_1204_; 
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 0, v___x_1202_);
v___x_1204_ = v___x_1192_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v___x_1202_);
lean_ctor_set(v_reuseFailAlloc_1205_, 1, v_a_1190_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_1012_, 3);
return v___x_1188_;
}
}
default: 
{
lean_object* v___x_1209_; lean_object* v___x_1210_; 
lean_dec(v_offset_1013_);
lean_dec_ref(v_e_1012_);
v___x_1209_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__3);
v___x_1210_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8(v___x_1209_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_);
return v___x_1210_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(lean_object* v_n_1211_, lean_object* v_beginIdx_1212_, lean_object* v_subst_1213_, lean_object* v_e_1214_, lean_object* v_offset_1215_, lean_object* v_a_1216_, uint8_t v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_){
_start:
{
lean_object* v_key_1220_; lean_object* v___x_1221_; 
lean_inc(v_offset_1215_);
lean_inc_ref(v_e_1214_);
v_key_1220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1220_, 0, v_e_1214_);
lean_ctor_set(v_key_1220_, 1, v_offset_1215_);
v___x_1221_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3___redArg(v_a_1216_, v_key_1220_);
if (lean_obj_tag(v___x_1221_) == 1)
{
lean_object* v_val_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
lean_dec_ref_known(v_key_1220_, 2);
lean_dec(v_offset_1215_);
lean_dec_ref(v_e_1214_);
v_val_1222_ = lean_ctor_get(v___x_1221_, 0);
lean_inc(v_val_1222_);
lean_dec_ref_known(v___x_1221_, 1);
v___x_1223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1223_, 0, v_val_1222_);
lean_ctor_set(v___x_1223_, 1, v_a_1216_);
v___x_1224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1223_);
lean_ctor_set(v___x_1224_, 1, v_a_1219_);
return v___x_1224_;
}
else
{
lean_dec(v___x_1221_);
switch(lean_obj_tag(v_e_1214_))
{
case 0:
{
lean_object* v_deBruijnIndex_1225_; uint8_t v___x_1226_; 
v_deBruijnIndex_1225_ = lean_ctor_get(v_e_1214_, 0);
v___x_1226_ = lean_nat_dec_le(v_offset_1215_, v_deBruijnIndex_1225_);
if (v___x_1226_ == 0)
{
lean_object* v___x_1227_; 
lean_dec(v_offset_1215_);
v___x_1227_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1220_, v_e_1214_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_);
return v___x_1227_;
}
else
{
lean_object* v___x_1228_; uint8_t v___x_1229_; 
lean_inc(v_deBruijnIndex_1225_);
lean_dec_ref_known(v_e_1214_, 1);
v___x_1228_ = lean_nat_add(v_offset_1215_, v_n_1211_);
v___x_1229_ = lean_nat_dec_lt(v_deBruijnIndex_1225_, v___x_1228_);
lean_dec(v___x_1228_);
if (v___x_1229_ == 0)
{
lean_object* v___x_1230_; lean_object* v___x_1231_; 
lean_dec(v_offset_1215_);
v___x_1230_ = lean_nat_sub(v_deBruijnIndex_1225_, v_n_1211_);
lean_dec(v_deBruijnIndex_1225_);
v___x_1231_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___redArg(v___x_1230_, v_a_1219_);
if (lean_obj_tag(v___x_1231_) == 0)
{
lean_object* v_a_1232_; lean_object* v_a_1233_; lean_object* v___x_1234_; 
v_a_1232_ = lean_ctor_get(v___x_1231_, 0);
lean_inc(v_a_1232_);
v_a_1233_ = lean_ctor_get(v___x_1231_, 1);
lean_inc(v_a_1233_);
lean_dec_ref_known(v___x_1231_, 2);
v___x_1234_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1220_, v_a_1232_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1233_);
return v___x_1234_;
}
else
{
lean_object* v_a_1235_; lean_object* v_a_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1243_; 
lean_dec_ref_known(v_key_1220_, 2);
lean_dec_ref(v_a_1216_);
v_a_1235_ = lean_ctor_get(v___x_1231_, 0);
v_a_1236_ = lean_ctor_get(v___x_1231_, 1);
v_isSharedCheck_1243_ = !lean_is_exclusive(v___x_1231_);
if (v_isSharedCheck_1243_ == 0)
{
v___x_1238_ = v___x_1231_;
v_isShared_1239_ = v_isSharedCheck_1243_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_a_1236_);
lean_inc(v_a_1235_);
lean_dec(v___x_1231_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1243_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v___x_1241_; 
if (v_isShared_1239_ == 0)
{
v___x_1241_ = v___x_1238_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v_a_1235_);
lean_ctor_set(v_reuseFailAlloc_1242_, 1, v_a_1236_);
v___x_1241_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
return v___x_1241_;
}
}
}
}
else
{
lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v_v_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___x_1244_ = lean_nat_add(v_beginIdx_1212_, v_deBruijnIndex_1225_);
lean_dec(v_deBruijnIndex_1225_);
v___x_1245_ = lean_nat_sub(v___x_1244_, v_offset_1215_);
lean_dec(v___x_1244_);
v_v_1246_ = lean_array_fget_borrowed(v_subst_1213_, v___x_1245_);
lean_dec(v___x_1245_);
v___x_1247_ = lean_unsigned_to_nat(0u);
lean_inc(v_v_1246_);
v___x_1248_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(v_v_1246_, v___x_1247_, v_offset_1215_, v_a_1217_, v_a_1218_, v_a_1219_);
lean_dec(v_offset_1215_);
if (lean_obj_tag(v___x_1248_) == 0)
{
lean_object* v_a_1249_; lean_object* v_a_1250_; lean_object* v___x_1251_; 
v_a_1249_ = lean_ctor_get(v___x_1248_, 0);
lean_inc(v_a_1249_);
v_a_1250_ = lean_ctor_get(v___x_1248_, 1);
lean_inc(v_a_1250_);
lean_dec_ref_known(v___x_1248_, 2);
v___x_1251_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1220_, v_a_1249_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1250_);
return v___x_1251_;
}
else
{
lean_object* v_a_1252_; lean_object* v_a_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1260_; 
lean_dec_ref_known(v_key_1220_, 2);
lean_dec_ref(v_a_1216_);
v_a_1252_ = lean_ctor_get(v___x_1248_, 0);
v_a_1253_ = lean_ctor_get(v___x_1248_, 1);
v_isSharedCheck_1260_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1255_ = v___x_1248_;
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_a_1253_);
lean_inc(v_a_1252_);
lean_dec(v___x_1248_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v___x_1258_; 
if (v_isShared_1256_ == 0)
{
v___x_1258_ = v___x_1255_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_a_1252_);
lean_ctor_set(v_reuseFailAlloc_1259_, 1, v_a_1253_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
}
}
}
}
case 9:
{
lean_object* v___x_1261_; 
lean_dec(v_offset_1215_);
v___x_1261_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1220_, v_e_1214_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_);
return v___x_1261_;
}
case 2:
{
lean_object* v___x_1262_; 
lean_dec(v_offset_1215_);
v___x_1262_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1220_, v_e_1214_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_);
return v___x_1262_;
}
case 1:
{
lean_object* v___x_1263_; 
lean_dec(v_offset_1215_);
v___x_1263_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1220_, v_e_1214_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_);
return v___x_1263_;
}
case 4:
{
lean_object* v___x_1264_; 
lean_dec(v_offset_1215_);
v___x_1264_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1220_, v_e_1214_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_);
return v___x_1264_;
}
case 3:
{
lean_object* v___x_1265_; 
lean_dec(v_offset_1215_);
v___x_1265_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1220_, v_e_1214_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_);
return v___x_1265_;
}
default: 
{
lean_object* v___x_1266_; uint8_t v___x_1267_; 
v___x_1266_ = l_Lean_Expr_looseBVarRange(v_e_1214_);
v___x_1267_ = lean_nat_dec_le(v___x_1266_, v_offset_1215_);
lean_dec(v___x_1266_);
if (v___x_1267_ == 0)
{
switch(lean_obj_tag(v_e_1214_))
{
case 9:
{
lean_object* v___x_1268_; 
lean_dec(v_offset_1215_);
v___x_1268_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1220_, v_e_1214_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_);
return v___x_1268_;
}
case 2:
{
lean_object* v___x_1269_; 
lean_dec(v_offset_1215_);
v___x_1269_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1220_, v_e_1214_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_);
return v___x_1269_;
}
case 0:
{
lean_object* v___x_1270_; 
lean_dec(v_offset_1215_);
v___x_1270_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1220_, v_e_1214_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_);
return v___x_1270_;
}
case 1:
{
lean_object* v___x_1271_; 
lean_dec(v_offset_1215_);
v___x_1271_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1220_, v_e_1214_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_);
return v___x_1271_;
}
case 4:
{
lean_object* v___x_1272_; 
lean_dec(v_offset_1215_);
v___x_1272_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1220_, v_e_1214_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_);
return v___x_1272_;
}
case 3:
{
lean_object* v___x_1273_; 
lean_dec(v_offset_1215_);
v___x_1273_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1220_, v_e_1214_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_);
return v___x_1273_;
}
default: 
{
lean_object* v___x_1274_; 
v___x_1274_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0(v_n_1211_, v_beginIdx_1212_, v_subst_1213_, v_e_1214_, v_offset_1215_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v_a_1275_; lean_object* v_a_1276_; lean_object* v_fst_1277_; lean_object* v_snd_1278_; lean_object* v___x_1279_; 
v_a_1275_ = lean_ctor_get(v___x_1274_, 0);
lean_inc(v_a_1275_);
v_a_1276_ = lean_ctor_get(v___x_1274_, 1);
lean_inc(v_a_1276_);
lean_dec_ref_known(v___x_1274_, 2);
v_fst_1277_ = lean_ctor_get(v_a_1275_, 0);
lean_inc(v_fst_1277_);
v_snd_1278_ = lean_ctor_get(v_a_1275_, 1);
lean_inc(v_snd_1278_);
lean_dec(v_a_1275_);
v___x_1279_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1220_, v_fst_1277_, v_snd_1278_, v_a_1217_, v_a_1218_, v_a_1276_);
return v___x_1279_;
}
else
{
lean_dec_ref_known(v_key_1220_, 2);
return v___x_1274_;
}
}
}
}
else
{
lean_object* v___x_1280_; 
lean_dec(v_offset_1215_);
v___x_1280_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1220_, v_e_1214_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_);
return v___x_1280_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0___boxed(lean_object* v_n_1281_, lean_object* v_beginIdx_1282_, lean_object* v_subst_1283_, lean_object* v_e_1284_, lean_object* v_offset_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_){
_start:
{
uint8_t v_a_boxed_1290_; lean_object* v_res_1291_; 
v_a_boxed_1290_ = lean_unbox(v_a_1287_);
v_res_1291_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1281_, v_beginIdx_1282_, v_subst_1283_, v_e_1284_, v_offset_1285_, v_a_1286_, v_a_boxed_1290_, v_a_1288_, v_a_1289_);
lean_dec_ref(v_a_1288_);
lean_dec_ref(v_subst_1283_);
lean_dec(v_beginIdx_1282_);
lean_dec(v_n_1281_);
return v_res_1291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0___boxed(lean_object* v_n_1292_, lean_object* v_beginIdx_1293_, lean_object* v_subst_1294_, lean_object* v_e_1295_, lean_object* v_offset_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_){
_start:
{
uint8_t v_a_boxed_1301_; lean_object* v_res_1302_; 
v_a_boxed_1301_ = lean_unbox(v_a_1298_);
v_res_1302_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0(v_n_1292_, v_beginIdx_1293_, v_subst_1294_, v_e_1295_, v_offset_1296_, v_a_1297_, v_a_boxed_1301_, v_a_1299_, v_a_1300_);
lean_dec_ref(v_a_1299_);
lean_dec_ref(v_subst_1294_);
lean_dec(v_beginIdx_1293_);
lean_dec(v_n_1292_);
return v_res_1302_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__1(void){
_start:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1304_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__2));
v___x_1305_ = lean_unsigned_to_nat(34u);
v___x_1306_ = lean_unsigned_to_nat(57u);
v___x_1307_ = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__0));
v___x_1308_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__3));
v___x_1309_ = l_mkPanicMessageWithDecl(v___x_1308_, v___x_1307_, v___x_1306_, v___x_1305_, v___x_1304_);
return v___x_1309_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__2(void){
_start:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1310_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__2));
v___x_1311_ = lean_unsigned_to_nat(32u);
v___x_1312_ = lean_unsigned_to_nat(56u);
v___x_1313_ = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__0));
v___x_1314_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__3));
v___x_1315_ = l_mkPanicMessageWithDecl(v___x_1314_, v___x_1313_, v___x_1312_, v___x_1311_, v___x_1310_);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27(lean_object* v_e_1316_, lean_object* v_beginIdx_1317_, lean_object* v_endIdx_1318_, lean_object* v_subst_1319_, uint8_t v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_){
_start:
{
uint8_t v___x_1323_; 
v___x_1323_ = lean_nat_dec_lt(v_endIdx_1318_, v_beginIdx_1317_);
if (v___x_1323_ == 0)
{
lean_object* v___x_1324_; uint8_t v___x_1325_; 
v___x_1324_ = lean_array_get_size(v_subst_1319_);
v___x_1325_ = lean_nat_dec_lt(v___x_1324_, v_endIdx_1318_);
if (v___x_1325_ == 0)
{
lean_object* v_n_1326_; lean_object* v___x_1327_; 
v_n_1326_ = lean_nat_sub(v_endIdx_1318_, v_beginIdx_1317_);
v___x_1327_ = lean_unsigned_to_nat(0u);
switch(lean_obj_tag(v_e_1316_))
{
case 0:
{
lean_object* v_deBruijnIndex_1328_; uint8_t v___x_1329_; 
v_deBruijnIndex_1328_ = lean_ctor_get(v_e_1316_, 0);
v___x_1329_ = lean_nat_dec_le(v___x_1327_, v_deBruijnIndex_1328_);
if (v___x_1329_ == 0)
{
lean_object* v___x_1330_; 
lean_dec(v_n_1326_);
v___x_1330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1330_, 0, v_e_1316_);
lean_ctor_set(v___x_1330_, 1, v_a_1322_);
return v___x_1330_;
}
else
{
uint8_t v___x_1331_; 
lean_inc(v_deBruijnIndex_1328_);
lean_dec_ref_known(v_e_1316_, 1);
v___x_1331_ = lean_nat_dec_lt(v_deBruijnIndex_1328_, v_n_1326_);
if (v___x_1331_ == 0)
{
lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1332_ = lean_nat_sub(v_deBruijnIndex_1328_, v_n_1326_);
lean_dec(v_n_1326_);
lean_dec(v_deBruijnIndex_1328_);
v___x_1333_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___redArg(v___x_1332_, v_a_1322_);
return v___x_1333_;
}
else
{
lean_object* v___x_1334_; lean_object* v_v_1335_; lean_object* v___x_1336_; 
lean_dec(v_n_1326_);
v___x_1334_ = lean_nat_add(v_beginIdx_1317_, v_deBruijnIndex_1328_);
lean_dec(v_deBruijnIndex_1328_);
v_v_1335_ = lean_array_fget_borrowed(v_subst_1319_, v___x_1334_);
lean_dec(v___x_1334_);
lean_inc(v_v_1335_);
v___x_1336_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(v_v_1335_, v___x_1327_, v___x_1327_, v_a_1320_, v_a_1321_, v_a_1322_);
return v___x_1336_;
}
}
}
case 9:
{
lean_object* v___x_1337_; 
lean_dec(v_n_1326_);
v___x_1337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1337_, 0, v_e_1316_);
lean_ctor_set(v___x_1337_, 1, v_a_1322_);
return v___x_1337_;
}
case 2:
{
lean_object* v___x_1338_; 
lean_dec(v_n_1326_);
v___x_1338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1338_, 0, v_e_1316_);
lean_ctor_set(v___x_1338_, 1, v_a_1322_);
return v___x_1338_;
}
case 1:
{
lean_object* v___x_1339_; 
lean_dec(v_n_1326_);
v___x_1339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1339_, 0, v_e_1316_);
lean_ctor_set(v___x_1339_, 1, v_a_1322_);
return v___x_1339_;
}
case 4:
{
lean_object* v___x_1340_; 
lean_dec(v_n_1326_);
v___x_1340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1340_, 0, v_e_1316_);
lean_ctor_set(v___x_1340_, 1, v_a_1322_);
return v___x_1340_;
}
case 3:
{
lean_object* v___x_1341_; 
lean_dec(v_n_1326_);
v___x_1341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1341_, 0, v_e_1316_);
lean_ctor_set(v___x_1341_, 1, v_a_1322_);
return v___x_1341_;
}
default: 
{
lean_object* v___x_1342_; uint8_t v___x_1343_; 
v___x_1342_ = l_Lean_Expr_looseBVarRange(v_e_1316_);
v___x_1343_ = lean_nat_dec_le(v___x_1342_, v___x_1327_);
lean_dec(v___x_1342_);
if (v___x_1343_ == 0)
{
switch(lean_obj_tag(v_e_1316_))
{
case 9:
{
lean_object* v___x_1344_; 
lean_dec(v_n_1326_);
v___x_1344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1344_, 0, v_e_1316_);
lean_ctor_set(v___x_1344_, 1, v_a_1322_);
return v___x_1344_;
}
case 2:
{
lean_object* v___x_1345_; 
lean_dec(v_n_1326_);
v___x_1345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1345_, 0, v_e_1316_);
lean_ctor_set(v___x_1345_, 1, v_a_1322_);
return v___x_1345_;
}
case 0:
{
lean_object* v___x_1346_; 
lean_dec(v_n_1326_);
v___x_1346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1346_, 0, v_e_1316_);
lean_ctor_set(v___x_1346_, 1, v_a_1322_);
return v___x_1346_;
}
case 1:
{
lean_object* v___x_1347_; 
lean_dec(v_n_1326_);
v___x_1347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1347_, 0, v_e_1316_);
lean_ctor_set(v___x_1347_, 1, v_a_1322_);
return v___x_1347_;
}
case 4:
{
lean_object* v___x_1348_; 
lean_dec(v_n_1326_);
v___x_1348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1348_, 0, v_e_1316_);
lean_ctor_set(v___x_1348_, 1, v_a_1322_);
return v___x_1348_;
}
case 3:
{
lean_object* v___x_1349_; 
lean_dec(v_n_1326_);
v___x_1349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1349_, 0, v_e_1316_);
lean_ctor_set(v___x_1349_, 1, v_a_1322_);
return v___x_1349_;
}
default: 
{
lean_object* v___x_1350_; lean_object* v___x_1351_; 
v___x_1350_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__1, &l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__1_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__1);
v___x_1351_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0(v_n_1326_, v_beginIdx_1317_, v_subst_1319_, v_e_1316_, v___x_1327_, v___x_1350_, v_a_1320_, v_a_1321_, v_a_1322_);
lean_dec(v_n_1326_);
if (lean_obj_tag(v___x_1351_) == 0)
{
lean_object* v_a_1352_; lean_object* v_a_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1361_; 
v_a_1352_ = lean_ctor_get(v___x_1351_, 0);
v_a_1353_ = lean_ctor_get(v___x_1351_, 1);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1355_ = v___x_1351_;
v_isShared_1356_ = v_isSharedCheck_1361_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_a_1353_);
lean_inc(v_a_1352_);
lean_dec(v___x_1351_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1361_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v_fst_1357_; lean_object* v___x_1359_; 
v_fst_1357_ = lean_ctor_get(v_a_1352_, 0);
lean_inc(v_fst_1357_);
lean_dec(v_a_1352_);
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 0, v_fst_1357_);
v___x_1359_ = v___x_1355_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_fst_1357_);
lean_ctor_set(v_reuseFailAlloc_1360_, 1, v_a_1353_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
}
else
{
lean_object* v_a_1362_; lean_object* v_a_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1370_; 
v_a_1362_ = lean_ctor_get(v___x_1351_, 0);
v_a_1363_ = lean_ctor_get(v___x_1351_, 1);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1365_ = v___x_1351_;
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_a_1363_);
lean_inc(v_a_1362_);
lean_dec(v___x_1351_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1368_; 
if (v_isShared_1366_ == 0)
{
v___x_1368_ = v___x_1365_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_a_1362_);
lean_ctor_set(v_reuseFailAlloc_1369_, 1, v_a_1363_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
}
}
}
else
{
lean_object* v___x_1371_; 
lean_dec(v_n_1326_);
v___x_1371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1371_, 0, v_e_1316_);
lean_ctor_set(v___x_1371_, 1, v_a_1322_);
return v___x_1371_;
}
}
}
}
else
{
lean_object* v___x_1372_; lean_object* v___x_1373_; 
lean_dec_ref(v_e_1316_);
v___x_1372_ = lean_obj_once(&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__1, &l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__1_once, _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__1);
v___x_1373_ = l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1(v___x_1372_, v_a_1320_, v_a_1321_, v_a_1322_);
return v___x_1373_;
}
}
else
{
lean_object* v___x_1374_; lean_object* v___x_1375_; 
lean_dec_ref(v_e_1316_);
v___x_1374_ = lean_obj_once(&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__2, &l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__2_once, _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__2);
v___x_1375_ = l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1(v___x_1374_, v_a_1320_, v_a_1321_, v_a_1322_);
return v___x_1375_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___boxed(lean_object* v_e_1376_, lean_object* v_beginIdx_1377_, lean_object* v_endIdx_1378_, lean_object* v_subst_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_){
_start:
{
uint8_t v_a_boxed_1383_; lean_object* v_res_1384_; 
v_a_boxed_1383_ = lean_unbox(v_a_1380_);
v_res_1384_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27(v_e_1376_, v_beginIdx_1377_, v_endIdx_1378_, v_subst_1379_, v_a_boxed_1383_, v_a_1381_, v_a_1382_);
lean_dec_ref(v_a_1381_);
lean_dec_ref(v_subst_1379_);
lean_dec(v_endIdx_1378_);
lean_dec(v_beginIdx_1377_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27(lean_object* v_e_1385_, lean_object* v_subst_1386_, uint8_t v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_){
_start:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1390_ = lean_unsigned_to_nat(0u);
v___x_1391_ = lean_array_get_size(v_subst_1386_);
v___x_1392_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27(v_e_1385_, v___x_1390_, v___x_1391_, v_subst_1386_, v_a_1387_, v_a_1388_, v_a_1389_);
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27___boxed(lean_object* v_e_1393_, lean_object* v_subst_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_){
_start:
{
uint8_t v_a_boxed_1398_; lean_object* v_res_1399_; 
v_a_boxed_1398_ = lean_unbox(v_a_1395_);
v_res_1399_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27(v_e_1393_, v_subst_1394_, v_a_boxed_1398_, v_a_1396_, v_a_1397_);
lean_dec_ref(v_a_1396_);
lean_dec_ref(v_subst_1394_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateS(lean_object* v_e_1400_, lean_object* v_subst_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_){
_start:
{
lean_object* v___x_1409_; lean_object* v___x_1410_; uint8_t v_debug_1411_; lean_object* v_env_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; uint8_t v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; 
v___x_1409_ = lean_st_ref_get(v_a_1403_);
v___x_1410_ = lean_st_ref_get(v_a_1407_);
v_debug_1411_ = lean_ctor_get_uint8(v___x_1409_, sizeof(void*)*10);
lean_dec(v___x_1409_);
v_env_1412_ = lean_ctor_get(v___x_1410_, 0);
lean_inc_ref(v_env_1412_);
lean_dec(v___x_1410_);
v___x_1413_ = lean_box(v_debug_1411_);
v___x_1414_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27___boxed), 5, 3);
lean_closure_set(v___x_1414_, 0, v_e_1400_);
lean_closure_set(v___x_1414_, 1, v_subst_1401_);
lean_closure_set(v___x_1414_, 2, v___x_1413_);
v___x_1415_ = 0;
v___x_1416_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_1416_, 0, v_env_1412_);
lean_ctor_set_uint8(v___x_1416_, sizeof(void*)*1, v___x_1415_);
lean_ctor_set_uint8(v___x_1416_, sizeof(void*)*1 + 1, v___x_1415_);
v___x_1417_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___x_1414_, v___x_1416_, v_a_1403_);
if (lean_obj_tag(v___x_1417_) == 0)
{
lean_object* v_a_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1428_; 
v_a_1418_ = lean_ctor_get(v___x_1417_, 0);
v_isSharedCheck_1428_ = !lean_is_exclusive(v___x_1417_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1420_ = v___x_1417_;
v_isShared_1421_ = v_isSharedCheck_1428_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_a_1418_);
lean_dec(v___x_1417_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1428_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
if (lean_obj_tag(v_a_1418_) == 0)
{
lean_object* v___x_1422_; lean_object* v___x_1423_; 
lean_dec_ref_known(v_a_1418_, 1);
lean_del_object(v___x_1420_);
v___x_1422_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__2, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__2_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__2);
v___x_1423_ = l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(v___x_1422_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_);
return v___x_1423_;
}
else
{
lean_object* v_a_1424_; lean_object* v___x_1426_; 
v_a_1424_ = lean_ctor_get(v_a_1418_, 0);
lean_inc(v_a_1424_);
lean_dec_ref_known(v_a_1418_, 1);
if (v_isShared_1421_ == 0)
{
lean_ctor_set(v___x_1420_, 0, v_a_1424_);
v___x_1426_ = v___x_1420_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_a_1424_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
}
}
else
{
lean_object* v_a_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1436_; 
v_a_1429_ = lean_ctor_get(v___x_1417_, 0);
v_isSharedCheck_1436_ = !lean_is_exclusive(v___x_1417_);
if (v_isSharedCheck_1436_ == 0)
{
v___x_1431_ = v___x_1417_;
v_isShared_1432_ = v_isSharedCheck_1436_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_a_1429_);
lean_dec(v___x_1417_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1436_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1434_; 
if (v_isShared_1432_ == 0)
{
v___x_1434_ = v___x_1431_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v_a_1429_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateS___boxed(lean_object* v_e_1437_, lean_object* v_subst_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_){
_start:
{
lean_object* v_res_1446_; 
v_res_1446_ = l_Lean_Meta_Sym_instantiateS(v_e_1437_, v_subst_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_);
lean_dec(v_a_1444_);
lean_dec_ref(v_a_1443_);
lean_dec(v_a_1442_);
lean_dec_ref(v_a_1441_);
lean_dec(v_a_1440_);
lean_dec_ref(v_a_1439_);
return v_res_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0_spec__0(lean_object* v_f_1447_, lean_object* v_a_1448_, uint8_t v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_){
_start:
{
lean_object* v___y_1453_; 
if (v___y_1449_ == 0)
{
v___y_1453_ = v___y_1451_;
goto v___jp_1452_;
}
else
{
lean_object* v___x_1456_; 
lean_inc_ref(v_f_1447_);
v___x_1456_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_f_1447_, v___y_1449_, v___y_1450_, v___y_1451_);
if (lean_obj_tag(v___x_1456_) == 0)
{
lean_object* v_a_1457_; lean_object* v___x_1458_; 
v_a_1457_ = lean_ctor_get(v___x_1456_, 1);
lean_inc(v_a_1457_);
lean_dec_ref_known(v___x_1456_, 2);
lean_inc_ref(v_a_1448_);
v___x_1458_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_a_1448_, v___y_1449_, v___y_1450_, v_a_1457_);
if (lean_obj_tag(v___x_1458_) == 0)
{
lean_object* v_a_1459_; 
v_a_1459_ = lean_ctor_get(v___x_1458_, 1);
lean_inc(v_a_1459_);
lean_dec_ref_known(v___x_1458_, 2);
v___y_1453_ = v_a_1459_;
goto v___jp_1452_;
}
else
{
lean_object* v_a_1460_; lean_object* v_a_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1468_; 
lean_dec_ref(v_a_1448_);
lean_dec_ref(v_f_1447_);
v_a_1460_ = lean_ctor_get(v___x_1458_, 0);
v_a_1461_ = lean_ctor_get(v___x_1458_, 1);
v_isSharedCheck_1468_ = !lean_is_exclusive(v___x_1458_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1463_ = v___x_1458_;
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_a_1461_);
lean_inc(v_a_1460_);
lean_dec(v___x_1458_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1466_; 
if (v_isShared_1464_ == 0)
{
v___x_1466_ = v___x_1463_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_a_1460_);
lean_ctor_set(v_reuseFailAlloc_1467_, 1, v_a_1461_);
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
lean_object* v_a_1469_; lean_object* v_a_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1477_; 
lean_dec_ref(v_a_1448_);
lean_dec_ref(v_f_1447_);
v_a_1469_ = lean_ctor_get(v___x_1456_, 0);
v_a_1470_ = lean_ctor_get(v___x_1456_, 1);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1456_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1472_ = v___x_1456_;
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_a_1470_);
lean_inc(v_a_1469_);
lean_dec(v___x_1456_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1475_; 
if (v_isShared_1473_ == 0)
{
v___x_1475_ = v___x_1472_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_a_1469_);
lean_ctor_set(v_reuseFailAlloc_1476_, 1, v_a_1470_);
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
v___jp_1452_:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1454_ = l_Lean_Expr_app___override(v_f_1447_, v_a_1448_);
v___x_1455_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1454_, v___y_1453_);
return v___x_1455_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0_spec__0___boxed(lean_object* v_f_1478_, lean_object* v_a_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_){
_start:
{
uint8_t v___y_1405__boxed_1483_; lean_object* v_res_1484_; 
v___y_1405__boxed_1483_ = lean_unbox(v___y_1480_);
v_res_1484_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0_spec__0(v_f_1478_, v_a_1479_, v___y_1405__boxed_1483_, v___y_1481_, v___y_1482_);
lean_dec_ref(v___y_1481_);
return v_res_1484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0(lean_object* v_revArgs_1485_, lean_object* v_start_1486_, lean_object* v_b_1487_, lean_object* v_i_1488_, uint8_t v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_){
_start:
{
uint8_t v___x_1492_; 
v___x_1492_ = lean_nat_dec_le(v_i_1488_, v_start_1486_);
if (v___x_1492_ == 0)
{
lean_object* v___x_1493_; lean_object* v_i_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1493_ = lean_unsigned_to_nat(1u);
v_i_1494_ = lean_nat_sub(v_i_1488_, v___x_1493_);
lean_dec(v_i_1488_);
v___x_1495_ = l_Lean_instInhabitedExpr;
v___x_1496_ = lean_array_get_borrowed(v___x_1495_, v_revArgs_1485_, v_i_1494_);
lean_inc(v___x_1496_);
v___x_1497_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0_spec__0(v_b_1487_, v___x_1496_, v___y_1489_, v___y_1490_, v___y_1491_);
if (lean_obj_tag(v___x_1497_) == 0)
{
lean_object* v_a_1498_; lean_object* v_a_1499_; 
v_a_1498_ = lean_ctor_get(v___x_1497_, 0);
lean_inc(v_a_1498_);
v_a_1499_ = lean_ctor_get(v___x_1497_, 1);
lean_inc(v_a_1499_);
lean_dec_ref_known(v___x_1497_, 2);
v_b_1487_ = v_a_1498_;
v_i_1488_ = v_i_1494_;
v___y_1491_ = v_a_1499_;
goto _start;
}
else
{
lean_dec(v_i_1494_);
return v___x_1497_;
}
}
else
{
lean_object* v___x_1501_; 
lean_dec(v_i_1488_);
v___x_1501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1501_, 0, v_b_1487_);
lean_ctor_set(v___x_1501_, 1, v___y_1491_);
return v___x_1501_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0___boxed(lean_object* v_revArgs_1502_, lean_object* v_start_1503_, lean_object* v_b_1504_, lean_object* v_i_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
uint8_t v___y_1468__boxed_1509_; lean_object* v_res_1510_; 
v___y_1468__boxed_1509_ = lean_unbox(v___y_1506_);
v_res_1510_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0(v_revArgs_1502_, v_start_1503_, v_b_1504_, v_i_1505_, v___y_1468__boxed_1509_, v___y_1507_, v___y_1508_);
lean_dec_ref(v___y_1507_);
lean_dec(v_start_1503_);
lean_dec_ref(v_revArgs_1502_);
return v_res_1510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go(lean_object* v_revArgs_1511_, lean_object* v_sz_1512_, lean_object* v_e_1513_, lean_object* v_i_1514_, uint8_t v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_){
_start:
{
switch(lean_obj_tag(v_e_1513_))
{
case 6:
{
lean_object* v_body_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; uint8_t v___x_1521_; 
v_body_1518_ = lean_ctor_get(v_e_1513_, 2);
lean_inc_ref(v_body_1518_);
lean_dec_ref_known(v_e_1513_, 3);
v___x_1519_ = lean_unsigned_to_nat(1u);
v___x_1520_ = lean_nat_add(v_i_1514_, v___x_1519_);
lean_dec(v_i_1514_);
v___x_1521_ = lean_nat_dec_lt(v___x_1520_, v_sz_1512_);
if (v___x_1521_ == 0)
{
lean_object* v___x_1522_; 
lean_dec(v___x_1520_);
v___x_1522_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27(v_body_1518_, v_revArgs_1511_, v_a_1515_, v_a_1516_, v_a_1517_);
return v___x_1522_;
}
else
{
v_e_1513_ = v_body_1518_;
v_i_1514_ = v___x_1520_;
goto _start;
}
}
case 10:
{
lean_object* v_expr_1524_; 
v_expr_1524_ = lean_ctor_get(v_e_1513_, 1);
lean_inc_ref(v_expr_1524_);
lean_dec_ref_known(v_e_1513_, 2);
v_e_1513_ = v_expr_1524_;
goto _start;
}
default: 
{
lean_object* v_n_1526_; lean_object* v___x_1527_; 
v_n_1526_ = lean_nat_sub(v_sz_1512_, v_i_1514_);
lean_dec(v_i_1514_);
v___x_1527_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27(v_e_1513_, v_n_1526_, v_sz_1512_, v_revArgs_1511_, v_a_1515_, v_a_1516_, v_a_1517_);
if (lean_obj_tag(v___x_1527_) == 0)
{
lean_object* v_a_1528_; lean_object* v_a_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; 
v_a_1528_ = lean_ctor_get(v___x_1527_, 0);
lean_inc(v_a_1528_);
v_a_1529_ = lean_ctor_get(v___x_1527_, 1);
lean_inc(v_a_1529_);
lean_dec_ref_known(v___x_1527_, 2);
v___x_1530_ = lean_unsigned_to_nat(0u);
v___x_1531_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0(v_revArgs_1511_, v___x_1530_, v_a_1528_, v_n_1526_, v_a_1515_, v_a_1516_, v_a_1529_);
return v___x_1531_;
}
else
{
lean_dec(v_n_1526_);
return v___x_1527_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go___boxed(lean_object* v_revArgs_1532_, lean_object* v_sz_1533_, lean_object* v_e_1534_, lean_object* v_i_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_){
_start:
{
uint8_t v_a_boxed_1539_; lean_object* v_res_1540_; 
v_a_boxed_1539_ = lean_unbox(v_a_1536_);
v_res_1540_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go(v_revArgs_1532_, v_sz_1533_, v_e_1534_, v_i_1535_, v_a_boxed_1539_, v_a_1537_, v_a_1538_);
lean_dec_ref(v_a_1537_);
lean_dec(v_sz_1533_);
lean_dec_ref(v_revArgs_1532_);
return v_res_1540_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27(lean_object* v_f_1541_, lean_object* v_revArgs_1542_, uint8_t v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_){
_start:
{
lean_object* v_sz_1546_; lean_object* v___x_1547_; uint8_t v___x_1548_; 
v_sz_1546_ = lean_array_get_size(v_revArgs_1542_);
v___x_1547_ = lean_unsigned_to_nat(0u);
v___x_1548_ = lean_nat_dec_eq(v_sz_1546_, v___x_1547_);
if (v___x_1548_ == 0)
{
lean_object* v___x_1549_; 
v___x_1549_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go(v_revArgs_1542_, v_sz_1546_, v_f_1541_, v___x_1547_, v_a_1543_, v_a_1544_, v_a_1545_);
return v___x_1549_;
}
else
{
lean_object* v___x_1550_; 
v___x_1550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1550_, 0, v_f_1541_);
lean_ctor_set(v___x_1550_, 1, v_a_1545_);
return v___x_1550_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27___boxed(lean_object* v_f_1551_, lean_object* v_revArgs_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_){
_start:
{
uint8_t v_a_boxed_1556_; lean_object* v_res_1557_; 
v_a_boxed_1556_ = lean_unbox(v_a_1553_);
v_res_1557_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27(v_f_1551_, v_revArgs_1552_, v_a_boxed_1556_, v_a_1554_, v_a_1555_);
lean_dec_ref(v_a_1554_);
lean_dec_ref(v_revArgs_1552_);
return v_res_1557_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_1558_, lean_object* v_x_1559_){
_start:
{
if (lean_obj_tag(v_x_1559_) == 0)
{
return v_x_1558_;
}
else
{
lean_object* v_key_1560_; lean_object* v_value_1561_; lean_object* v_tail_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1589_; 
v_key_1560_ = lean_ctor_get(v_x_1559_, 0);
v_value_1561_ = lean_ctor_get(v_x_1559_, 1);
v_tail_1562_ = lean_ctor_get(v_x_1559_, 2);
v_isSharedCheck_1589_ = !lean_is_exclusive(v_x_1559_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1564_ = v_x_1559_;
v_isShared_1565_ = v_isSharedCheck_1589_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_tail_1562_);
lean_inc(v_value_1561_);
lean_inc(v_key_1560_);
lean_dec(v_x_1559_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1589_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v_fst_1566_; lean_object* v_snd_1567_; lean_object* v___x_1568_; uint64_t v___x_1569_; uint64_t v___x_1570_; uint64_t v___x_1571_; uint64_t v___x_1572_; uint64_t v___x_1573_; uint64_t v_fold_1574_; uint64_t v___x_1575_; uint64_t v___x_1576_; uint64_t v___x_1577_; size_t v___x_1578_; size_t v___x_1579_; size_t v___x_1580_; size_t v___x_1581_; size_t v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1585_; 
v_fst_1566_ = lean_ctor_get(v_key_1560_, 0);
v_snd_1567_ = lean_ctor_get(v_key_1560_, 1);
v___x_1568_ = lean_array_get_size(v_x_1558_);
v___x_1569_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_1566_);
v___x_1570_ = lean_uint64_of_nat(v_snd_1567_);
v___x_1571_ = lean_uint64_mix_hash(v___x_1569_, v___x_1570_);
v___x_1572_ = 32ULL;
v___x_1573_ = lean_uint64_shift_right(v___x_1571_, v___x_1572_);
v_fold_1574_ = lean_uint64_xor(v___x_1571_, v___x_1573_);
v___x_1575_ = 16ULL;
v___x_1576_ = lean_uint64_shift_right(v_fold_1574_, v___x_1575_);
v___x_1577_ = lean_uint64_xor(v_fold_1574_, v___x_1576_);
v___x_1578_ = lean_uint64_to_usize(v___x_1577_);
v___x_1579_ = lean_usize_of_nat(v___x_1568_);
v___x_1580_ = ((size_t)1ULL);
v___x_1581_ = lean_usize_sub(v___x_1579_, v___x_1580_);
v___x_1582_ = lean_usize_land(v___x_1578_, v___x_1581_);
v___x_1583_ = lean_array_uget_borrowed(v_x_1558_, v___x_1582_);
lean_inc(v___x_1583_);
if (v_isShared_1565_ == 0)
{
lean_ctor_set(v___x_1564_, 2, v___x_1583_);
v___x_1585_ = v___x_1564_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_key_1560_);
lean_ctor_set(v_reuseFailAlloc_1588_, 1, v_value_1561_);
lean_ctor_set(v_reuseFailAlloc_1588_, 2, v___x_1583_);
v___x_1585_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
lean_object* v___x_1586_; 
v___x_1586_ = lean_array_uset(v_x_1558_, v___x_1582_, v___x_1585_);
v_x_1558_ = v___x_1586_;
v_x_1559_ = v_tail_1562_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2___redArg(lean_object* v_i_1590_, lean_object* v_source_1591_, lean_object* v_target_1592_){
_start:
{
lean_object* v___x_1593_; uint8_t v___x_1594_; 
v___x_1593_ = lean_array_get_size(v_source_1591_);
v___x_1594_ = lean_nat_dec_lt(v_i_1590_, v___x_1593_);
if (v___x_1594_ == 0)
{
lean_dec_ref(v_source_1591_);
lean_dec(v_i_1590_);
return v_target_1592_;
}
else
{
lean_object* v_es_1595_; lean_object* v___x_1596_; lean_object* v_source_1597_; lean_object* v_target_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; 
v_es_1595_ = lean_array_fget(v_source_1591_, v_i_1590_);
v___x_1596_ = lean_box(0);
v_source_1597_ = lean_array_fset(v_source_1591_, v_i_1590_, v___x_1596_);
v_target_1598_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3___redArg(v_target_1592_, v_es_1595_);
v___x_1599_ = lean_unsigned_to_nat(1u);
v___x_1600_ = lean_nat_add(v_i_1590_, v___x_1599_);
lean_dec(v_i_1590_);
v_i_1590_ = v___x_1600_;
v_source_1591_ = v_source_1597_;
v_target_1592_ = v_target_1598_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1___redArg(lean_object* v_data_1602_){
_start:
{
lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v_nbuckets_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; 
v___x_1603_ = lean_array_get_size(v_data_1602_);
v___x_1604_ = lean_unsigned_to_nat(2u);
v_nbuckets_1605_ = lean_nat_mul(v___x_1603_, v___x_1604_);
v___x_1606_ = lean_unsigned_to_nat(0u);
v___x_1607_ = lean_box(0);
v___x_1608_ = lean_mk_array(v_nbuckets_1605_, v___x_1607_);
v___x_1609_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2___redArg(v___x_1606_, v_data_1602_, v___x_1608_);
return v___x_1609_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(lean_object* v_a_1610_, lean_object* v_b_1611_, lean_object* v_x_1612_){
_start:
{
if (lean_obj_tag(v_x_1612_) == 0)
{
lean_dec(v_b_1611_);
lean_dec_ref(v_a_1610_);
return v_x_1612_;
}
else
{
lean_object* v_key_1613_; lean_object* v_value_1614_; lean_object* v_tail_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1634_; 
v_key_1613_ = lean_ctor_get(v_x_1612_, 0);
v_value_1614_ = lean_ctor_get(v_x_1612_, 1);
v_tail_1615_ = lean_ctor_get(v_x_1612_, 2);
v_isSharedCheck_1634_ = !lean_is_exclusive(v_x_1612_);
if (v_isSharedCheck_1634_ == 0)
{
v___x_1617_ = v_x_1612_;
v_isShared_1618_ = v_isSharedCheck_1634_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_tail_1615_);
lean_inc(v_value_1614_);
lean_inc(v_key_1613_);
lean_dec(v_x_1612_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1634_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
uint8_t v___y_1620_; lean_object* v_fst_1628_; lean_object* v_snd_1629_; lean_object* v_fst_1630_; lean_object* v_snd_1631_; uint8_t v___x_1632_; 
v_fst_1628_ = lean_ctor_get(v_key_1613_, 0);
v_snd_1629_ = lean_ctor_get(v_key_1613_, 1);
v_fst_1630_ = lean_ctor_get(v_a_1610_, 0);
v_snd_1631_ = lean_ctor_get(v_a_1610_, 1);
v___x_1632_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_1628_, v_fst_1630_);
if (v___x_1632_ == 0)
{
v___y_1620_ = v___x_1632_;
goto v___jp_1619_;
}
else
{
uint8_t v___x_1633_; 
v___x_1633_ = lean_nat_dec_eq(v_snd_1629_, v_snd_1631_);
v___y_1620_ = v___x_1633_;
goto v___jp_1619_;
}
v___jp_1619_:
{
if (v___y_1620_ == 0)
{
lean_object* v___x_1621_; lean_object* v___x_1623_; 
v___x_1621_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(v_a_1610_, v_b_1611_, v_tail_1615_);
if (v_isShared_1618_ == 0)
{
lean_ctor_set(v___x_1617_, 2, v___x_1621_);
v___x_1623_ = v___x_1617_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v_key_1613_);
lean_ctor_set(v_reuseFailAlloc_1624_, 1, v_value_1614_);
lean_ctor_set(v_reuseFailAlloc_1624_, 2, v___x_1621_);
v___x_1623_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
return v___x_1623_;
}
}
else
{
lean_object* v___x_1626_; 
lean_dec(v_value_1614_);
lean_dec(v_key_1613_);
if (v_isShared_1618_ == 0)
{
lean_ctor_set(v___x_1617_, 1, v_b_1611_);
lean_ctor_set(v___x_1617_, 0, v_a_1610_);
v___x_1626_ = v___x_1617_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_a_1610_);
lean_ctor_set(v_reuseFailAlloc_1627_, 1, v_b_1611_);
lean_ctor_set(v_reuseFailAlloc_1627_, 2, v_tail_1615_);
v___x_1626_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
return v___x_1626_;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(lean_object* v_a_1635_, lean_object* v_x_1636_){
_start:
{
if (lean_obj_tag(v_x_1636_) == 0)
{
uint8_t v___x_1637_; 
v___x_1637_ = 0;
return v___x_1637_;
}
else
{
lean_object* v_key_1638_; lean_object* v_tail_1639_; uint8_t v___y_1641_; lean_object* v_fst_1643_; lean_object* v_snd_1644_; lean_object* v_fst_1645_; lean_object* v_snd_1646_; uint8_t v___x_1647_; 
v_key_1638_ = lean_ctor_get(v_x_1636_, 0);
v_tail_1639_ = lean_ctor_get(v_x_1636_, 2);
v_fst_1643_ = lean_ctor_get(v_key_1638_, 0);
v_snd_1644_ = lean_ctor_get(v_key_1638_, 1);
v_fst_1645_ = lean_ctor_get(v_a_1635_, 0);
v_snd_1646_ = lean_ctor_get(v_a_1635_, 1);
v___x_1647_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_1643_, v_fst_1645_);
if (v___x_1647_ == 0)
{
v___y_1641_ = v___x_1647_;
goto v___jp_1640_;
}
else
{
uint8_t v___x_1648_; 
v___x_1648_ = lean_nat_dec_eq(v_snd_1644_, v_snd_1646_);
v___y_1641_ = v___x_1648_;
goto v___jp_1640_;
}
v___jp_1640_:
{
if (v___y_1641_ == 0)
{
v_x_1636_ = v_tail_1639_;
goto _start;
}
else
{
return v___y_1641_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg___boxed(lean_object* v_a_1649_, lean_object* v_x_1650_){
_start:
{
uint8_t v_res_1651_; lean_object* v_r_1652_; 
v_res_1651_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_a_1649_, v_x_1650_);
lean_dec(v_x_1650_);
lean_dec_ref(v_a_1649_);
v_r_1652_ = lean_box(v_res_1651_);
return v_r_1652_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0___redArg(lean_object* v_m_1653_, lean_object* v_a_1654_, lean_object* v_b_1655_){
_start:
{
lean_object* v_size_1656_; lean_object* v_buckets_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1704_; 
v_size_1656_ = lean_ctor_get(v_m_1653_, 0);
v_buckets_1657_ = lean_ctor_get(v_m_1653_, 1);
v_isSharedCheck_1704_ = !lean_is_exclusive(v_m_1653_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1659_ = v_m_1653_;
v_isShared_1660_ = v_isSharedCheck_1704_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_buckets_1657_);
lean_inc(v_size_1656_);
lean_dec(v_m_1653_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1704_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v_fst_1661_; lean_object* v_snd_1662_; lean_object* v___x_1663_; uint64_t v___x_1664_; uint64_t v___x_1665_; uint64_t v___x_1666_; uint64_t v___x_1667_; uint64_t v___x_1668_; uint64_t v_fold_1669_; uint64_t v___x_1670_; uint64_t v___x_1671_; uint64_t v___x_1672_; size_t v___x_1673_; size_t v___x_1674_; size_t v___x_1675_; size_t v___x_1676_; size_t v___x_1677_; lean_object* v_bkt_1678_; uint8_t v___x_1679_; 
v_fst_1661_ = lean_ctor_get(v_a_1654_, 0);
v_snd_1662_ = lean_ctor_get(v_a_1654_, 1);
v___x_1663_ = lean_array_get_size(v_buckets_1657_);
v___x_1664_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_1661_);
v___x_1665_ = lean_uint64_of_nat(v_snd_1662_);
v___x_1666_ = lean_uint64_mix_hash(v___x_1664_, v___x_1665_);
v___x_1667_ = 32ULL;
v___x_1668_ = lean_uint64_shift_right(v___x_1666_, v___x_1667_);
v_fold_1669_ = lean_uint64_xor(v___x_1666_, v___x_1668_);
v___x_1670_ = 16ULL;
v___x_1671_ = lean_uint64_shift_right(v_fold_1669_, v___x_1670_);
v___x_1672_ = lean_uint64_xor(v_fold_1669_, v___x_1671_);
v___x_1673_ = lean_uint64_to_usize(v___x_1672_);
v___x_1674_ = lean_usize_of_nat(v___x_1663_);
v___x_1675_ = ((size_t)1ULL);
v___x_1676_ = lean_usize_sub(v___x_1674_, v___x_1675_);
v___x_1677_ = lean_usize_land(v___x_1673_, v___x_1676_);
v_bkt_1678_ = lean_array_uget_borrowed(v_buckets_1657_, v___x_1677_);
v___x_1679_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_a_1654_, v_bkt_1678_);
if (v___x_1679_ == 0)
{
lean_object* v___x_1680_; lean_object* v_size_x27_1681_; lean_object* v___x_1682_; lean_object* v_buckets_x27_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; uint8_t v___x_1689_; 
v___x_1680_ = lean_unsigned_to_nat(1u);
v_size_x27_1681_ = lean_nat_add(v_size_1656_, v___x_1680_);
lean_dec(v_size_1656_);
lean_inc(v_bkt_1678_);
v___x_1682_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1682_, 0, v_a_1654_);
lean_ctor_set(v___x_1682_, 1, v_b_1655_);
lean_ctor_set(v___x_1682_, 2, v_bkt_1678_);
v_buckets_x27_1683_ = lean_array_uset(v_buckets_1657_, v___x_1677_, v___x_1682_);
v___x_1684_ = lean_unsigned_to_nat(4u);
v___x_1685_ = lean_nat_mul(v_size_x27_1681_, v___x_1684_);
v___x_1686_ = lean_unsigned_to_nat(3u);
v___x_1687_ = lean_nat_div(v___x_1685_, v___x_1686_);
lean_dec(v___x_1685_);
v___x_1688_ = lean_array_get_size(v_buckets_x27_1683_);
v___x_1689_ = lean_nat_dec_le(v___x_1687_, v___x_1688_);
lean_dec(v___x_1687_);
if (v___x_1689_ == 0)
{
lean_object* v_val_1690_; lean_object* v___x_1692_; 
v_val_1690_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1___redArg(v_buckets_x27_1683_);
if (v_isShared_1660_ == 0)
{
lean_ctor_set(v___x_1659_, 1, v_val_1690_);
lean_ctor_set(v___x_1659_, 0, v_size_x27_1681_);
v___x_1692_ = v___x_1659_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_size_x27_1681_);
lean_ctor_set(v_reuseFailAlloc_1693_, 1, v_val_1690_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
else
{
lean_object* v___x_1695_; 
if (v_isShared_1660_ == 0)
{
lean_ctor_set(v___x_1659_, 1, v_buckets_x27_1683_);
lean_ctor_set(v___x_1659_, 0, v_size_x27_1681_);
v___x_1695_ = v___x_1659_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_size_x27_1681_);
lean_ctor_set(v_reuseFailAlloc_1696_, 1, v_buckets_x27_1683_);
v___x_1695_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
return v___x_1695_;
}
}
}
else
{
lean_object* v___x_1697_; lean_object* v_buckets_x27_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1702_; 
lean_inc(v_bkt_1678_);
v___x_1697_ = lean_box(0);
v_buckets_x27_1698_ = lean_array_uset(v_buckets_1657_, v___x_1677_, v___x_1697_);
v___x_1699_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(v_a_1654_, v_b_1655_, v_bkt_1678_);
v___x_1700_ = lean_array_uset(v_buckets_x27_1698_, v___x_1677_, v___x_1699_);
if (v_isShared_1660_ == 0)
{
lean_ctor_set(v___x_1659_, 1, v___x_1700_);
v___x_1702_ = v___x_1659_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v_size_1656_);
lean_ctor_set(v_reuseFailAlloc_1703_, 1, v___x_1700_);
v___x_1702_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
return v___x_1702_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(lean_object* v_key_1705_, lean_object* v_r_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_){
_start:
{
lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; 
lean_inc_ref(v_r_1706_);
v___x_1709_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1707_, v_key_1705_, v_r_1706_);
v___x_1710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1710_, 0, v_r_1706_);
lean_ctor_set(v___x_1710_, 1, v___x_1709_);
v___x_1711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1711_, 0, v___x_1710_);
lean_ctor_set(v___x_1711_, 1, v_a_1708_);
return v___x_1711_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save(lean_object* v_key_1712_, lean_object* v_r_1713_, lean_object* v_a_1714_, uint8_t v_a_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_){
_start:
{
lean_object* v___x_1718_; 
v___x_1718_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_1712_, v_r_1713_, v_a_1714_, v_a_1717_);
return v___x_1718_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___boxed(lean_object* v_key_1719_, lean_object* v_r_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_){
_start:
{
uint8_t v_a_boxed_1725_; lean_object* v_res_1726_; 
v_a_boxed_1725_ = lean_unbox(v_a_1722_);
v_res_1726_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save(v_key_1719_, v_r_1720_, v_a_1721_, v_a_boxed_1725_, v_a_1723_, v_a_1724_);
lean_dec_ref(v_a_1723_);
return v_res_1726_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0(lean_object* v_00_u03b2_1727_, lean_object* v_m_1728_, lean_object* v_a_1729_, lean_object* v_b_1730_){
_start:
{
lean_object* v___x_1731_; 
v___x_1731_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0___redArg(v_m_1728_, v_a_1729_, v_b_1730_);
return v___x_1731_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0(lean_object* v_00_u03b2_1732_, lean_object* v_a_1733_, lean_object* v_x_1734_){
_start:
{
uint8_t v___x_1735_; 
v___x_1735_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_a_1733_, v_x_1734_);
return v___x_1735_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1736_, lean_object* v_a_1737_, lean_object* v_x_1738_){
_start:
{
uint8_t v_res_1739_; lean_object* v_r_1740_; 
v_res_1739_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0(v_00_u03b2_1736_, v_a_1737_, v_x_1738_);
lean_dec(v_x_1738_);
lean_dec_ref(v_a_1737_);
v_r_1740_ = lean_box(v_res_1739_);
return v_r_1740_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1(lean_object* v_00_u03b2_1741_, lean_object* v_data_1742_){
_start:
{
lean_object* v___x_1743_; 
v___x_1743_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1___redArg(v_data_1742_);
return v___x_1743_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2(lean_object* v_00_u03b2_1744_, lean_object* v_a_1745_, lean_object* v_b_1746_, lean_object* v_x_1747_){
_start:
{
lean_object* v___x_1748_; 
v___x_1748_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(v_a_1745_, v_b_1746_, v_x_1747_);
return v___x_1748_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1749_, lean_object* v_i_1750_, lean_object* v_source_1751_, lean_object* v_target_1752_){
_start:
{
lean_object* v___x_1753_; 
v___x_1753_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2___redArg(v_i_1750_, v_source_1751_, v_target_1752_);
return v___x_1753_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1754_, lean_object* v_x_1755_, lean_object* v_x_1756_){
_start:
{
lean_object* v___x_1757_; 
v___x_1757_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1755_, v_x_1756_);
return v___x_1757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0___redArg(lean_object* v_idx_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_){
_start:
{
lean_object* v___x_1761_; lean_object* v___x_1762_; 
v___x_1761_ = l_Lean_Expr_bvar___override(v_idx_1758_);
v___x_1762_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1761_, v___y_1760_);
if (lean_obj_tag(v___x_1762_) == 0)
{
lean_object* v_a_1763_; lean_object* v_a_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1772_; 
v_a_1763_ = lean_ctor_get(v___x_1762_, 0);
v_a_1764_ = lean_ctor_get(v___x_1762_, 1);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1762_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1766_ = v___x_1762_;
v_isShared_1767_ = v_isSharedCheck_1772_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_a_1764_);
lean_inc(v_a_1763_);
lean_dec(v___x_1762_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1772_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___x_1768_; lean_object* v___x_1770_; 
v___x_1768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1768_, 0, v_a_1763_);
lean_ctor_set(v___x_1768_, 1, v___y_1759_);
if (v_isShared_1767_ == 0)
{
lean_ctor_set(v___x_1766_, 0, v___x_1768_);
v___x_1770_ = v___x_1766_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v___x_1768_);
lean_ctor_set(v_reuseFailAlloc_1771_, 1, v_a_1764_);
v___x_1770_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
return v___x_1770_;
}
}
}
else
{
lean_object* v_a_1773_; lean_object* v_a_1774_; lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1781_; 
lean_dec_ref(v___y_1759_);
v_a_1773_ = lean_ctor_get(v___x_1762_, 0);
v_a_1774_ = lean_ctor_get(v___x_1762_, 1);
v_isSharedCheck_1781_ = !lean_is_exclusive(v___x_1762_);
if (v_isSharedCheck_1781_ == 0)
{
v___x_1776_ = v___x_1762_;
v_isShared_1777_ = v_isSharedCheck_1781_;
goto v_resetjp_1775_;
}
else
{
lean_inc(v_a_1774_);
lean_inc(v_a_1773_);
lean_dec(v___x_1762_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1781_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
lean_object* v___x_1779_; 
if (v_isShared_1777_ == 0)
{
v___x_1779_ = v___x_1776_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v_a_1773_);
lean_ctor_set(v_reuseFailAlloc_1780_, 1, v_a_1774_);
v___x_1779_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
return v___x_1779_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0(lean_object* v_idx_1782_, lean_object* v___y_1783_, uint8_t v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_){
_start:
{
lean_object* v___x_1787_; 
v___x_1787_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0___redArg(v_idx_1782_, v___y_1783_, v___y_1786_);
return v___x_1787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0___boxed(lean_object* v_idx_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_){
_start:
{
uint8_t v___y_1133__boxed_1793_; lean_object* v_res_1794_; 
v___y_1133__boxed_1793_ = lean_unbox(v___y_1790_);
v_res_1794_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0(v_idx_1788_, v___y_1789_, v___y_1133__boxed_1793_, v___y_1791_, v___y_1792_);
lean_dec_ref(v___y_1791_);
return v_res_1794_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(lean_object* v_subst_1795_, lean_object* v_e_1796_, lean_object* v_bidx_1797_, lean_object* v_offset_1798_, lean_object* v_a_1799_, uint8_t v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_){
_start:
{
uint8_t v___x_1803_; 
v___x_1803_ = lean_nat_dec_le(v_offset_1798_, v_bidx_1797_);
if (v___x_1803_ == 0)
{
lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1804_, 0, v_e_1796_);
lean_ctor_set(v___x_1804_, 1, v_a_1799_);
v___x_1805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1805_, 0, v___x_1804_);
lean_ctor_set(v___x_1805_, 1, v_a_1802_);
return v___x_1805_;
}
else
{
lean_object* v_n_1806_; lean_object* v___x_1807_; uint8_t v___x_1808_; 
lean_dec_ref(v_e_1796_);
v_n_1806_ = lean_array_get_size(v_subst_1795_);
v___x_1807_ = lean_nat_add(v_offset_1798_, v_n_1806_);
v___x_1808_ = lean_nat_dec_lt(v_bidx_1797_, v___x_1807_);
lean_dec(v___x_1807_);
if (v___x_1808_ == 0)
{
lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1809_ = lean_nat_sub(v_bidx_1797_, v_n_1806_);
v___x_1810_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0___redArg(v___x_1809_, v_a_1799_, v_a_1802_);
return v___x_1810_;
}
else
{
lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v_v_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; 
v___x_1811_ = lean_nat_sub(v_bidx_1797_, v_offset_1798_);
v___x_1812_ = lean_nat_sub(v_n_1806_, v___x_1811_);
lean_dec(v___x_1811_);
v___x_1813_ = lean_unsigned_to_nat(1u);
v___x_1814_ = lean_nat_sub(v___x_1812_, v___x_1813_);
lean_dec(v___x_1812_);
v_v_1815_ = lean_array_fget_borrowed(v_subst_1795_, v___x_1814_);
lean_dec(v___x_1814_);
v___x_1816_ = lean_unsigned_to_nat(0u);
lean_inc(v_v_1815_);
v___x_1817_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(v_v_1815_, v___x_1816_, v_offset_1798_, v_a_1800_, v_a_1801_, v_a_1802_);
if (lean_obj_tag(v___x_1817_) == 0)
{
lean_object* v_a_1818_; lean_object* v_a_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1827_; 
v_a_1818_ = lean_ctor_get(v___x_1817_, 0);
v_a_1819_ = lean_ctor_get(v___x_1817_, 1);
v_isSharedCheck_1827_ = !lean_is_exclusive(v___x_1817_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1821_ = v___x_1817_;
v_isShared_1822_ = v_isSharedCheck_1827_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_a_1819_);
lean_inc(v_a_1818_);
lean_dec(v___x_1817_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1827_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v___x_1823_; lean_object* v___x_1825_; 
v___x_1823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1823_, 0, v_a_1818_);
lean_ctor_set(v___x_1823_, 1, v_a_1799_);
if (v_isShared_1822_ == 0)
{
lean_ctor_set(v___x_1821_, 0, v___x_1823_);
v___x_1825_ = v___x_1821_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v___x_1823_);
lean_ctor_set(v_reuseFailAlloc_1826_, 1, v_a_1819_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
return v___x_1825_;
}
}
}
else
{
lean_object* v_a_1828_; lean_object* v_a_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1836_; 
lean_dec_ref(v_a_1799_);
v_a_1828_ = lean_ctor_get(v___x_1817_, 0);
v_a_1829_ = lean_ctor_get(v___x_1817_, 1);
v_isSharedCheck_1836_ = !lean_is_exclusive(v___x_1817_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1831_ = v___x_1817_;
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_a_1829_);
lean_inc(v_a_1828_);
lean_dec(v___x_1817_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1834_; 
if (v_isShared_1832_ == 0)
{
v___x_1834_ = v___x_1831_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v_a_1828_);
lean_ctor_set(v_reuseFailAlloc_1835_, 1, v_a_1829_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
return v___x_1834_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar___boxed(lean_object* v_subst_1837_, lean_object* v_e_1838_, lean_object* v_bidx_1839_, lean_object* v_offset_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_){
_start:
{
uint8_t v_a_boxed_1845_; lean_object* v_res_1846_; 
v_a_boxed_1845_ = lean_unbox(v_a_1842_);
v_res_1846_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(v_subst_1837_, v_e_1838_, v_bidx_1839_, v_offset_1840_, v_a_1841_, v_a_boxed_1845_, v_a_1843_, v_a_1844_);
lean_dec_ref(v_a_1843_);
lean_dec(v_offset_1840_);
lean_dec(v_bidx_1839_);
lean_dec_ref(v_subst_1837_);
return v_res_1846_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__2(void){
_start:
{
lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1849_ = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__1));
v___x_1850_ = lean_unsigned_to_nat(25u);
v___x_1851_ = lean_unsigned_to_nat(148u);
v___x_1852_ = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__0));
v___x_1853_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__0));
v___x_1854_ = l_mkPanicMessageWithDecl(v___x_1853_, v___x_1852_, v___x_1851_, v___x_1850_, v___x_1849_);
return v___x_1854_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__1(void){
_start:
{
lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___x_1856_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__2));
v___x_1857_ = lean_unsigned_to_nat(11u);
v___x_1858_ = lean_unsigned_to_nat(165u);
v___x_1859_ = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__0));
v___x_1860_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__3));
v___x_1861_ = l_mkPanicMessageWithDecl(v___x_1860_, v___x_1859_, v___x_1858_, v___x_1857_, v___x_1856_);
return v___x_1861_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta(lean_object* v_subst_1862_, lean_object* v_e_1863_, lean_object* v_f_1864_, lean_object* v_argsRev_1865_, lean_object* v_offset_1866_, uint8_t v_modified_1867_, lean_object* v_a_1868_, uint8_t v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_){
_start:
{
switch(lean_obj_tag(v_f_1864_))
{
case 5:
{
lean_object* v_fn_1872_; lean_object* v_arg_1873_; lean_object* v___x_1874_; 
v_fn_1872_ = lean_ctor_get(v_f_1864_, 0);
lean_inc_ref(v_fn_1872_);
v_arg_1873_ = lean_ctor_get(v_f_1864_, 1);
lean_inc_ref_n(v_arg_1873_, 2);
lean_dec_ref_known(v_f_1864_, 2);
lean_inc(v_offset_1866_);
v___x_1874_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1862_, v_arg_1873_, v_offset_1866_, v_a_1868_, v_a_1869_, v_a_1870_, v_a_1871_);
if (lean_obj_tag(v___x_1874_) == 0)
{
lean_object* v_a_1875_; lean_object* v_a_1876_; lean_object* v_fst_1877_; lean_object* v_snd_1878_; lean_object* v___x_1879_; 
v_a_1875_ = lean_ctor_get(v___x_1874_, 0);
lean_inc(v_a_1875_);
v_a_1876_ = lean_ctor_get(v___x_1874_, 1);
lean_inc(v_a_1876_);
lean_dec_ref_known(v___x_1874_, 2);
v_fst_1877_ = lean_ctor_get(v_a_1875_, 0);
lean_inc_n(v_fst_1877_, 2);
v_snd_1878_ = lean_ctor_get(v_a_1875_, 1);
lean_inc(v_snd_1878_);
lean_dec(v_a_1875_);
v___x_1879_ = lean_array_push(v_argsRev_1865_, v_fst_1877_);
if (v_modified_1867_ == 0)
{
uint8_t v___x_1880_; 
v___x_1880_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_1873_, v_fst_1877_);
lean_dec(v_fst_1877_);
lean_dec_ref(v_arg_1873_);
if (v___x_1880_ == 0)
{
uint8_t v___x_1881_; 
v___x_1881_ = 1;
v_f_1864_ = v_fn_1872_;
v_argsRev_1865_ = v___x_1879_;
v_modified_1867_ = v___x_1881_;
v_a_1868_ = v_snd_1878_;
v_a_1871_ = v_a_1876_;
goto _start;
}
else
{
v_f_1864_ = v_fn_1872_;
v_argsRev_1865_ = v___x_1879_;
v_a_1868_ = v_snd_1878_;
v_a_1871_ = v_a_1876_;
goto _start;
}
}
else
{
lean_dec(v_fst_1877_);
lean_dec_ref(v_arg_1873_);
v_f_1864_ = v_fn_1872_;
v_argsRev_1865_ = v___x_1879_;
v_a_1868_ = v_snd_1878_;
v_a_1871_ = v_a_1876_;
goto _start;
}
}
else
{
lean_dec_ref(v_arg_1873_);
lean_dec_ref(v_fn_1872_);
lean_dec(v_offset_1866_);
lean_dec_ref(v_argsRev_1865_);
lean_dec_ref(v_e_1863_);
return v___x_1874_;
}
}
case 0:
{
lean_object* v_deBruijnIndex_1885_; lean_object* v___x_1886_; 
v_deBruijnIndex_1885_ = lean_ctor_get(v_f_1864_, 0);
lean_inc_ref(v_f_1864_);
v___x_1886_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(v_subst_1862_, v_f_1864_, v_deBruijnIndex_1885_, v_offset_1866_, v_a_1868_, v_a_1869_, v_a_1870_, v_a_1871_);
lean_dec(v_offset_1866_);
if (lean_obj_tag(v___x_1886_) == 0)
{
lean_object* v_a_1887_; lean_object* v_a_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1926_; 
v_a_1887_ = lean_ctor_get(v___x_1886_, 0);
v_a_1888_ = lean_ctor_get(v___x_1886_, 1);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1890_ = v___x_1886_;
v_isShared_1891_ = v_isSharedCheck_1926_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_a_1888_);
lean_inc(v_a_1887_);
lean_dec(v___x_1886_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1926_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v_fst_1892_; lean_object* v_snd_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1925_; 
v_fst_1892_ = lean_ctor_get(v_a_1887_, 0);
v_snd_1893_ = lean_ctor_get(v_a_1887_, 1);
v_isSharedCheck_1925_ = !lean_is_exclusive(v_a_1887_);
if (v_isSharedCheck_1925_ == 0)
{
v___x_1895_ = v_a_1887_;
v_isShared_1896_ = v_isSharedCheck_1925_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_snd_1893_);
lean_inc(v_fst_1892_);
lean_dec(v_a_1887_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1925_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
if (v_modified_1867_ == 0)
{
uint8_t v___x_1920_; 
v___x_1920_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_f_1864_, v_fst_1892_);
lean_dec_ref_known(v_f_1864_, 1);
if (v___x_1920_ == 0)
{
lean_del_object(v___x_1890_);
lean_dec_ref(v_e_1863_);
goto v___jp_1897_;
}
else
{
lean_object* v___x_1921_; lean_object* v___x_1923_; 
lean_del_object(v___x_1895_);
lean_dec(v_fst_1892_);
lean_dec_ref(v_argsRev_1865_);
v___x_1921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1921_, 0, v_e_1863_);
lean_ctor_set(v___x_1921_, 1, v_snd_1893_);
if (v_isShared_1891_ == 0)
{
lean_ctor_set(v___x_1890_, 0, v___x_1921_);
v___x_1923_ = v___x_1890_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v___x_1921_);
lean_ctor_set(v_reuseFailAlloc_1924_, 1, v_a_1888_);
v___x_1923_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
return v___x_1923_;
}
}
}
else
{
lean_del_object(v___x_1890_);
lean_dec_ref_known(v_f_1864_, 1);
lean_dec_ref(v_e_1863_);
goto v___jp_1897_;
}
v___jp_1897_:
{
lean_object* v___x_1898_; 
v___x_1898_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27(v_fst_1892_, v_argsRev_1865_, v_a_1869_, v_a_1870_, v_a_1888_);
lean_dec_ref(v_argsRev_1865_);
if (lean_obj_tag(v___x_1898_) == 0)
{
lean_object* v_a_1899_; lean_object* v_a_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1910_; 
v_a_1899_ = lean_ctor_get(v___x_1898_, 0);
v_a_1900_ = lean_ctor_get(v___x_1898_, 1);
v_isSharedCheck_1910_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1910_ == 0)
{
v___x_1902_ = v___x_1898_;
v_isShared_1903_ = v_isSharedCheck_1910_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_a_1900_);
lean_inc(v_a_1899_);
lean_dec(v___x_1898_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1910_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v___x_1905_; 
if (v_isShared_1896_ == 0)
{
lean_ctor_set(v___x_1895_, 0, v_a_1899_);
v___x_1905_ = v___x_1895_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v_a_1899_);
lean_ctor_set(v_reuseFailAlloc_1909_, 1, v_snd_1893_);
v___x_1905_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
lean_object* v___x_1907_; 
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 0, v___x_1905_);
v___x_1907_ = v___x_1902_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v___x_1905_);
lean_ctor_set(v_reuseFailAlloc_1908_, 1, v_a_1900_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
return v___x_1907_;
}
}
}
}
else
{
lean_object* v_a_1911_; lean_object* v_a_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1919_; 
lean_del_object(v___x_1895_);
lean_dec(v_snd_1893_);
v_a_1911_ = lean_ctor_get(v___x_1898_, 0);
v_a_1912_ = lean_ctor_get(v___x_1898_, 1);
v_isSharedCheck_1919_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1914_ = v___x_1898_;
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_a_1912_);
lean_inc(v_a_1911_);
lean_dec(v___x_1898_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v___x_1917_; 
if (v_isShared_1915_ == 0)
{
v___x_1917_ = v___x_1914_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_a_1911_);
lean_ctor_set(v_reuseFailAlloc_1918_, 1, v_a_1912_);
v___x_1917_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
return v___x_1917_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_f_1864_, 1);
lean_dec_ref(v_argsRev_1865_);
lean_dec_ref(v_e_1863_);
return v___x_1886_;
}
}
default: 
{
lean_object* v___x_1927_; lean_object* v___x_1928_; 
lean_dec(v_offset_1866_);
lean_dec_ref(v_argsRev_1865_);
lean_dec_ref(v_f_1864_);
lean_dec_ref(v_e_1863_);
v___x_1927_ = lean_obj_once(&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__1, &l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__1_once, _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__1);
v___x_1928_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8(v___x_1927_, v_a_1868_, v_a_1869_, v_a_1870_, v_a_1871_);
return v___x_1928_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg(lean_object* v_subst_1929_, lean_object* v_e_1930_, lean_object* v_f_1931_, lean_object* v_arg_1932_, lean_object* v_offset_1933_, lean_object* v_a_1934_, uint8_t v_a_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_){
_start:
{
lean_object* v___x_1938_; 
lean_inc(v_offset_1933_);
lean_inc_ref(v_arg_1932_);
v___x_1938_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1929_, v_arg_1932_, v_offset_1933_, v_a_1934_, v_a_1935_, v_a_1936_, v_a_1937_);
if (lean_obj_tag(v___x_1938_) == 0)
{
lean_object* v_a_1939_; lean_object* v_a_1940_; lean_object* v_fst_1941_; lean_object* v_snd_1942_; lean_object* v___x_1943_; uint8_t v___x_1944_; 
v_a_1939_ = lean_ctor_get(v___x_1938_, 0);
lean_inc(v_a_1939_);
v_a_1940_ = lean_ctor_get(v___x_1938_, 1);
lean_inc(v_a_1940_);
lean_dec_ref_known(v___x_1938_, 2);
v_fst_1941_ = lean_ctor_get(v_a_1939_, 0);
lean_inc(v_fst_1941_);
v_snd_1942_ = lean_ctor_get(v_a_1939_, 1);
lean_inc(v_snd_1942_);
lean_dec(v_a_1939_);
v___x_1943_ = l_Lean_Expr_getAppFn(v_f_1931_);
v___x_1944_ = l_Lean_Expr_isBVar(v___x_1943_);
lean_dec_ref(v___x_1943_);
if (v___x_1944_ == 0)
{
lean_object* v___x_1945_; 
lean_dec_ref(v_arg_1932_);
v___x_1945_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault(v_subst_1929_, v_f_1931_, v_offset_1933_, v_snd_1942_, v_a_1935_, v_a_1936_, v_a_1940_);
if (lean_obj_tag(v___x_1945_) == 0)
{
lean_object* v_a_1946_; lean_object* v_a_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1972_; 
v_a_1946_ = lean_ctor_get(v___x_1945_, 0);
v_a_1947_ = lean_ctor_get(v___x_1945_, 1);
v_isSharedCheck_1972_ = !lean_is_exclusive(v___x_1945_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1949_ = v___x_1945_;
v_isShared_1950_ = v_isSharedCheck_1972_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_a_1947_);
lean_inc(v_a_1946_);
lean_dec(v___x_1945_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1972_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v_fst_1951_; lean_object* v_snd_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1971_; 
v_fst_1951_ = lean_ctor_get(v_a_1946_, 0);
v_snd_1952_ = lean_ctor_get(v_a_1946_, 1);
v_isSharedCheck_1971_ = !lean_is_exclusive(v_a_1946_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1954_ = v_a_1946_;
v_isShared_1955_ = v_isSharedCheck_1971_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_snd_1952_);
lean_inc(v_fst_1951_);
lean_dec(v_a_1946_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1971_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
uint8_t v___y_1957_; 
if (lean_obj_tag(v_e_1930_) == 5)
{
lean_object* v_fn_1965_; lean_object* v_arg_1966_; uint8_t v___x_1967_; 
v_fn_1965_ = lean_ctor_get(v_e_1930_, 0);
v_arg_1966_ = lean_ctor_get(v_e_1930_, 1);
v___x_1967_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_1965_, v_fst_1951_);
if (v___x_1967_ == 0)
{
v___y_1957_ = v___x_1967_;
goto v___jp_1956_;
}
else
{
uint8_t v___x_1968_; 
v___x_1968_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_1966_, v_fst_1941_);
v___y_1957_ = v___x_1968_;
goto v___jp_1956_;
}
}
else
{
lean_object* v___x_1969_; lean_object* v___x_1970_; 
lean_del_object(v___x_1954_);
lean_dec(v_fst_1951_);
lean_del_object(v___x_1949_);
lean_dec(v_fst_1941_);
lean_dec_ref(v_e_1930_);
v___x_1969_ = lean_obj_once(&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__2, &l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__2_once, _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__2);
v___x_1970_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8(v___x_1969_, v_snd_1952_, v_a_1935_, v_a_1936_, v_a_1947_);
return v___x_1970_;
}
v___jp_1956_:
{
if (v___y_1957_ == 0)
{
lean_object* v___x_1958_; 
lean_del_object(v___x_1954_);
lean_del_object(v___x_1949_);
lean_dec_ref(v_e_1930_);
v___x_1958_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__2(v_fst_1951_, v_fst_1941_, v_snd_1952_, v_a_1935_, v_a_1936_, v_a_1947_);
return v___x_1958_;
}
else
{
lean_object* v___x_1960_; 
lean_dec(v_fst_1951_);
lean_dec(v_fst_1941_);
if (v_isShared_1955_ == 0)
{
lean_ctor_set(v___x_1954_, 0, v_e_1930_);
v___x_1960_ = v___x_1954_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_e_1930_);
lean_ctor_set(v_reuseFailAlloc_1964_, 1, v_snd_1952_);
v___x_1960_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
lean_object* v___x_1962_; 
if (v_isShared_1950_ == 0)
{
lean_ctor_set(v___x_1949_, 0, v___x_1960_);
v___x_1962_ = v___x_1949_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v___x_1960_);
lean_ctor_set(v_reuseFailAlloc_1963_, 1, v_a_1947_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
return v___x_1962_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1941_);
lean_dec_ref(v_e_1930_);
return v___x_1945_;
}
}
else
{
lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; uint8_t v___x_1976_; 
v___x_1973_ = lean_unsigned_to_nat(1u);
v___x_1974_ = lean_mk_empty_array_with_capacity(v___x_1973_);
lean_inc(v_fst_1941_);
v___x_1975_ = lean_array_push(v___x_1974_, v_fst_1941_);
v___x_1976_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_1932_, v_fst_1941_);
lean_dec(v_fst_1941_);
lean_dec_ref(v_arg_1932_);
if (v___x_1976_ == 0)
{
lean_object* v___x_1977_; 
v___x_1977_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta(v_subst_1929_, v_e_1930_, v_f_1931_, v___x_1975_, v_offset_1933_, v___x_1944_, v_snd_1942_, v_a_1935_, v_a_1936_, v_a_1940_);
return v___x_1977_;
}
else
{
uint8_t v___x_1978_; lean_object* v___x_1979_; 
v___x_1978_ = 0;
v___x_1979_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta(v_subst_1929_, v_e_1930_, v_f_1931_, v___x_1975_, v_offset_1933_, v___x_1978_, v_snd_1942_, v_a_1935_, v_a_1936_, v_a_1940_);
return v___x_1979_;
}
}
}
else
{
lean_dec(v_offset_1933_);
lean_dec_ref(v_arg_1932_);
lean_dec_ref(v_f_1931_);
lean_dec_ref(v_e_1930_);
return v___x_1938_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__1(void){
_start:
{
lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; 
v___x_1981_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__2));
v___x_1982_ = lean_unsigned_to_nat(59u);
v___x_1983_ = lean_unsigned_to_nat(176u);
v___x_1984_ = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__0));
v___x_1985_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__3));
v___x_1986_ = l_mkPanicMessageWithDecl(v___x_1985_, v___x_1984_, v___x_1983_, v___x_1982_, v___x_1981_);
return v___x_1986_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit(lean_object* v_subst_1987_, lean_object* v_e_1988_, lean_object* v_offset_1989_, lean_object* v_a_1990_, uint8_t v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_){
_start:
{
switch(lean_obj_tag(v_e_1988_))
{
case 0:
{
lean_object* v_deBruijnIndex_1994_; lean_object* v___x_1995_; 
v_deBruijnIndex_1994_ = lean_ctor_get(v_e_1988_, 0);
lean_inc(v_deBruijnIndex_1994_);
v___x_1995_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(v_subst_1987_, v_e_1988_, v_deBruijnIndex_1994_, v_offset_1989_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_);
lean_dec(v_offset_1989_);
lean_dec(v_deBruijnIndex_1994_);
return v___x_1995_;
}
case 5:
{
lean_object* v_fn_1996_; lean_object* v_arg_1997_; lean_object* v___x_1998_; 
v_fn_1996_ = lean_ctor_get(v_e_1988_, 0);
lean_inc_ref(v_fn_1996_);
v_arg_1997_ = lean_ctor_get(v_e_1988_, 1);
lean_inc_ref(v_arg_1997_);
v___x_1998_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg(v_subst_1987_, v_e_1988_, v_fn_1996_, v_arg_1997_, v_offset_1989_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_);
return v___x_1998_;
}
case 6:
{
lean_object* v_binderName_1999_; lean_object* v_binderType_2000_; lean_object* v_body_2001_; uint8_t v_binderInfo_2002_; lean_object* v___x_2003_; 
v_binderName_1999_ = lean_ctor_get(v_e_1988_, 0);
v_binderType_2000_ = lean_ctor_get(v_e_1988_, 1);
v_body_2001_ = lean_ctor_get(v_e_1988_, 2);
v_binderInfo_2002_ = lean_ctor_get_uint8(v_e_1988_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1989_);
lean_inc_ref(v_binderType_2000_);
v___x_2003_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1987_, v_binderType_2000_, v_offset_1989_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_);
if (lean_obj_tag(v___x_2003_) == 0)
{
lean_object* v_a_2004_; lean_object* v_a_2005_; lean_object* v_fst_2006_; lean_object* v_snd_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; 
v_a_2004_ = lean_ctor_get(v___x_2003_, 0);
lean_inc(v_a_2004_);
v_a_2005_ = lean_ctor_get(v___x_2003_, 1);
lean_inc(v_a_2005_);
lean_dec_ref_known(v___x_2003_, 2);
v_fst_2006_ = lean_ctor_get(v_a_2004_, 0);
lean_inc(v_fst_2006_);
v_snd_2007_ = lean_ctor_get(v_a_2004_, 1);
lean_inc(v_snd_2007_);
lean_dec(v_a_2004_);
v___x_2008_ = lean_unsigned_to_nat(1u);
v___x_2009_ = lean_nat_add(v_offset_1989_, v___x_2008_);
lean_dec(v_offset_1989_);
lean_inc_ref(v_body_2001_);
v___x_2010_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1987_, v_body_2001_, v___x_2009_, v_snd_2007_, v_a_1991_, v_a_1992_, v_a_2005_);
if (lean_obj_tag(v___x_2010_) == 0)
{
lean_object* v_a_2011_; lean_object* v_a_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2033_; 
v_a_2011_ = lean_ctor_get(v___x_2010_, 0);
v_a_2012_ = lean_ctor_get(v___x_2010_, 1);
v_isSharedCheck_2033_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2033_ == 0)
{
v___x_2014_ = v___x_2010_;
v_isShared_2015_ = v_isSharedCheck_2033_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_a_2012_);
lean_inc(v_a_2011_);
lean_dec(v___x_2010_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2033_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v_fst_2016_; lean_object* v_snd_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2032_; 
v_fst_2016_ = lean_ctor_get(v_a_2011_, 0);
v_snd_2017_ = lean_ctor_get(v_a_2011_, 1);
v_isSharedCheck_2032_ = !lean_is_exclusive(v_a_2011_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_2019_ = v_a_2011_;
v_isShared_2020_ = v_isSharedCheck_2032_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_snd_2017_);
lean_inc(v_fst_2016_);
lean_dec(v_a_2011_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2032_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
uint8_t v___y_2022_; uint8_t v___x_2030_; 
v___x_2030_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_2000_, v_fst_2006_);
if (v___x_2030_ == 0)
{
v___y_2022_ = v___x_2030_;
goto v___jp_2021_;
}
else
{
uint8_t v___x_2031_; 
v___x_2031_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_2001_, v_fst_2016_);
v___y_2022_ = v___x_2031_;
goto v___jp_2021_;
}
v___jp_2021_:
{
if (v___y_2022_ == 0)
{
lean_object* v___x_2023_; 
lean_inc(v_binderName_1999_);
lean_del_object(v___x_2019_);
lean_del_object(v___x_2014_);
lean_dec_ref_known(v_e_1988_, 3);
v___x_2023_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__3(v_binderName_1999_, v_binderInfo_2002_, v_fst_2006_, v_fst_2016_, v_snd_2017_, v_a_1991_, v_a_1992_, v_a_2012_);
return v___x_2023_;
}
else
{
lean_object* v___x_2025_; 
lean_dec(v_fst_2016_);
lean_dec(v_fst_2006_);
if (v_isShared_2020_ == 0)
{
lean_ctor_set(v___x_2019_, 0, v_e_1988_);
v___x_2025_ = v___x_2019_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v_e_1988_);
lean_ctor_set(v_reuseFailAlloc_2029_, 1, v_snd_2017_);
v___x_2025_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
lean_object* v___x_2027_; 
if (v_isShared_2015_ == 0)
{
lean_ctor_set(v___x_2014_, 0, v___x_2025_);
v___x_2027_ = v___x_2014_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v___x_2025_);
lean_ctor_set(v_reuseFailAlloc_2028_, 1, v_a_2012_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_2006_);
lean_dec_ref_known(v_e_1988_, 3);
return v___x_2010_;
}
}
else
{
lean_dec_ref_known(v_e_1988_, 3);
lean_dec(v_offset_1989_);
return v___x_2003_;
}
}
case 7:
{
lean_object* v_binderName_2034_; lean_object* v_binderType_2035_; lean_object* v_body_2036_; uint8_t v_binderInfo_2037_; lean_object* v___x_2038_; 
v_binderName_2034_ = lean_ctor_get(v_e_1988_, 0);
v_binderType_2035_ = lean_ctor_get(v_e_1988_, 1);
v_body_2036_ = lean_ctor_get(v_e_1988_, 2);
v_binderInfo_2037_ = lean_ctor_get_uint8(v_e_1988_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1989_);
lean_inc_ref(v_binderType_2035_);
v___x_2038_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1987_, v_binderType_2035_, v_offset_1989_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_);
if (lean_obj_tag(v___x_2038_) == 0)
{
lean_object* v_a_2039_; lean_object* v_a_2040_; lean_object* v_fst_2041_; lean_object* v_snd_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; 
v_a_2039_ = lean_ctor_get(v___x_2038_, 0);
lean_inc(v_a_2039_);
v_a_2040_ = lean_ctor_get(v___x_2038_, 1);
lean_inc(v_a_2040_);
lean_dec_ref_known(v___x_2038_, 2);
v_fst_2041_ = lean_ctor_get(v_a_2039_, 0);
lean_inc(v_fst_2041_);
v_snd_2042_ = lean_ctor_get(v_a_2039_, 1);
lean_inc(v_snd_2042_);
lean_dec(v_a_2039_);
v___x_2043_ = lean_unsigned_to_nat(1u);
v___x_2044_ = lean_nat_add(v_offset_1989_, v___x_2043_);
lean_dec(v_offset_1989_);
lean_inc_ref(v_body_2036_);
v___x_2045_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1987_, v_body_2036_, v___x_2044_, v_snd_2042_, v_a_1991_, v_a_1992_, v_a_2040_);
if (lean_obj_tag(v___x_2045_) == 0)
{
lean_object* v_a_2046_; lean_object* v_a_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2068_; 
v_a_2046_ = lean_ctor_get(v___x_2045_, 0);
v_a_2047_ = lean_ctor_get(v___x_2045_, 1);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2049_ = v___x_2045_;
v_isShared_2050_ = v_isSharedCheck_2068_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_a_2047_);
lean_inc(v_a_2046_);
lean_dec(v___x_2045_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2068_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v_fst_2051_; lean_object* v_snd_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2067_; 
v_fst_2051_ = lean_ctor_get(v_a_2046_, 0);
v_snd_2052_ = lean_ctor_get(v_a_2046_, 1);
v_isSharedCheck_2067_ = !lean_is_exclusive(v_a_2046_);
if (v_isSharedCheck_2067_ == 0)
{
v___x_2054_ = v_a_2046_;
v_isShared_2055_ = v_isSharedCheck_2067_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_snd_2052_);
lean_inc(v_fst_2051_);
lean_dec(v_a_2046_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2067_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
uint8_t v___y_2057_; uint8_t v___x_2065_; 
v___x_2065_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_2035_, v_fst_2041_);
if (v___x_2065_ == 0)
{
v___y_2057_ = v___x_2065_;
goto v___jp_2056_;
}
else
{
uint8_t v___x_2066_; 
v___x_2066_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_2036_, v_fst_2051_);
v___y_2057_ = v___x_2066_;
goto v___jp_2056_;
}
v___jp_2056_:
{
if (v___y_2057_ == 0)
{
lean_object* v___x_2058_; 
lean_inc(v_binderName_2034_);
lean_del_object(v___x_2054_);
lean_del_object(v___x_2049_);
lean_dec_ref_known(v_e_1988_, 3);
v___x_2058_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__4(v_binderName_2034_, v_binderInfo_2037_, v_fst_2041_, v_fst_2051_, v_snd_2052_, v_a_1991_, v_a_1992_, v_a_2047_);
return v___x_2058_;
}
else
{
lean_object* v___x_2060_; 
lean_dec(v_fst_2051_);
lean_dec(v_fst_2041_);
if (v_isShared_2055_ == 0)
{
lean_ctor_set(v___x_2054_, 0, v_e_1988_);
v___x_2060_ = v___x_2054_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v_e_1988_);
lean_ctor_set(v_reuseFailAlloc_2064_, 1, v_snd_2052_);
v___x_2060_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
lean_object* v___x_2062_; 
if (v_isShared_2050_ == 0)
{
lean_ctor_set(v___x_2049_, 0, v___x_2060_);
v___x_2062_ = v___x_2049_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v___x_2060_);
lean_ctor_set(v_reuseFailAlloc_2063_, 1, v_a_2047_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_2041_);
lean_dec_ref_known(v_e_1988_, 3);
return v___x_2045_;
}
}
else
{
lean_dec_ref_known(v_e_1988_, 3);
lean_dec(v_offset_1989_);
return v___x_2038_;
}
}
case 8:
{
lean_object* v_declName_2069_; lean_object* v_type_2070_; lean_object* v_value_2071_; lean_object* v_body_2072_; uint8_t v_nondep_2073_; lean_object* v___x_2074_; 
v_declName_2069_ = lean_ctor_get(v_e_1988_, 0);
v_type_2070_ = lean_ctor_get(v_e_1988_, 1);
v_value_2071_ = lean_ctor_get(v_e_1988_, 2);
v_body_2072_ = lean_ctor_get(v_e_1988_, 3);
v_nondep_2073_ = lean_ctor_get_uint8(v_e_1988_, sizeof(void*)*4 + 8);
lean_inc(v_offset_1989_);
lean_inc_ref(v_type_2070_);
v___x_2074_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1987_, v_type_2070_, v_offset_1989_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_);
if (lean_obj_tag(v___x_2074_) == 0)
{
lean_object* v_a_2075_; lean_object* v_a_2076_; lean_object* v_fst_2077_; lean_object* v_snd_2078_; lean_object* v___x_2079_; 
v_a_2075_ = lean_ctor_get(v___x_2074_, 0);
lean_inc(v_a_2075_);
v_a_2076_ = lean_ctor_get(v___x_2074_, 1);
lean_inc(v_a_2076_);
lean_dec_ref_known(v___x_2074_, 2);
v_fst_2077_ = lean_ctor_get(v_a_2075_, 0);
lean_inc(v_fst_2077_);
v_snd_2078_ = lean_ctor_get(v_a_2075_, 1);
lean_inc(v_snd_2078_);
lean_dec(v_a_2075_);
lean_inc(v_offset_1989_);
lean_inc_ref(v_value_2071_);
v___x_2079_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1987_, v_value_2071_, v_offset_1989_, v_snd_2078_, v_a_1991_, v_a_1992_, v_a_2076_);
if (lean_obj_tag(v___x_2079_) == 0)
{
lean_object* v_a_2080_; lean_object* v_a_2081_; lean_object* v_fst_2082_; lean_object* v_snd_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; 
v_a_2080_ = lean_ctor_get(v___x_2079_, 0);
lean_inc(v_a_2080_);
v_a_2081_ = lean_ctor_get(v___x_2079_, 1);
lean_inc(v_a_2081_);
lean_dec_ref_known(v___x_2079_, 2);
v_fst_2082_ = lean_ctor_get(v_a_2080_, 0);
lean_inc(v_fst_2082_);
v_snd_2083_ = lean_ctor_get(v_a_2080_, 1);
lean_inc(v_snd_2083_);
lean_dec(v_a_2080_);
v___x_2084_ = lean_unsigned_to_nat(1u);
v___x_2085_ = lean_nat_add(v_offset_1989_, v___x_2084_);
lean_dec(v_offset_1989_);
lean_inc_ref(v_body_2072_);
v___x_2086_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1987_, v_body_2072_, v___x_2085_, v_snd_2083_, v_a_1991_, v_a_1992_, v_a_2081_);
if (lean_obj_tag(v___x_2086_) == 0)
{
lean_object* v_a_2087_; lean_object* v_a_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2111_; 
v_a_2087_ = lean_ctor_get(v___x_2086_, 0);
v_a_2088_ = lean_ctor_get(v___x_2086_, 1);
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2086_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2090_ = v___x_2086_;
v_isShared_2091_ = v_isSharedCheck_2111_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_a_2088_);
lean_inc(v_a_2087_);
lean_dec(v___x_2086_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2111_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v_fst_2092_; lean_object* v_snd_2093_; lean_object* v___x_2095_; uint8_t v_isShared_2096_; uint8_t v_isSharedCheck_2110_; 
v_fst_2092_ = lean_ctor_get(v_a_2087_, 0);
v_snd_2093_ = lean_ctor_get(v_a_2087_, 1);
v_isSharedCheck_2110_ = !lean_is_exclusive(v_a_2087_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2095_ = v_a_2087_;
v_isShared_2096_ = v_isSharedCheck_2110_;
goto v_resetjp_2094_;
}
else
{
lean_inc(v_snd_2093_);
lean_inc(v_fst_2092_);
lean_dec(v_a_2087_);
v___x_2095_ = lean_box(0);
v_isShared_2096_ = v_isSharedCheck_2110_;
goto v_resetjp_2094_;
}
v_resetjp_2094_:
{
uint8_t v___y_2098_; uint8_t v___x_2108_; 
v___x_2108_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_type_2070_, v_fst_2077_);
if (v___x_2108_ == 0)
{
v___y_2098_ = v___x_2108_;
goto v___jp_2097_;
}
else
{
uint8_t v___x_2109_; 
v___x_2109_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_value_2071_, v_fst_2082_);
v___y_2098_ = v___x_2109_;
goto v___jp_2097_;
}
v___jp_2097_:
{
if (v___y_2098_ == 0)
{
lean_object* v___x_2099_; 
lean_inc(v_declName_2069_);
lean_del_object(v___x_2095_);
lean_del_object(v___x_2090_);
lean_dec_ref_known(v_e_1988_, 4);
v___x_2099_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__5(v_declName_2069_, v_fst_2077_, v_fst_2082_, v_fst_2092_, v_nondep_2073_, v_snd_2093_, v_a_1991_, v_a_1992_, v_a_2088_);
return v___x_2099_;
}
else
{
uint8_t v___x_2100_; 
v___x_2100_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_2072_, v_fst_2092_);
if (v___x_2100_ == 0)
{
lean_object* v___x_2101_; 
lean_inc(v_declName_2069_);
lean_del_object(v___x_2095_);
lean_del_object(v___x_2090_);
lean_dec_ref_known(v_e_1988_, 4);
v___x_2101_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__5(v_declName_2069_, v_fst_2077_, v_fst_2082_, v_fst_2092_, v_nondep_2073_, v_snd_2093_, v_a_1991_, v_a_1992_, v_a_2088_);
return v___x_2101_;
}
else
{
lean_object* v___x_2103_; 
lean_dec(v_fst_2092_);
lean_dec(v_fst_2082_);
lean_dec(v_fst_2077_);
if (v_isShared_2096_ == 0)
{
lean_ctor_set(v___x_2095_, 0, v_e_1988_);
v___x_2103_ = v___x_2095_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v_e_1988_);
lean_ctor_set(v_reuseFailAlloc_2107_, 1, v_snd_2093_);
v___x_2103_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
lean_object* v___x_2105_; 
if (v_isShared_2091_ == 0)
{
lean_ctor_set(v___x_2090_, 0, v___x_2103_);
v___x_2105_ = v___x_2090_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v___x_2103_);
lean_ctor_set(v_reuseFailAlloc_2106_, 1, v_a_2088_);
v___x_2105_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
return v___x_2105_;
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
lean_dec(v_fst_2082_);
lean_dec(v_fst_2077_);
lean_dec_ref_known(v_e_1988_, 4);
return v___x_2086_;
}
}
else
{
lean_dec(v_fst_2077_);
lean_dec_ref_known(v_e_1988_, 4);
lean_dec(v_offset_1989_);
return v___x_2079_;
}
}
else
{
lean_dec_ref_known(v_e_1988_, 4);
lean_dec(v_offset_1989_);
return v___x_2074_;
}
}
case 10:
{
lean_object* v_data_2112_; lean_object* v_expr_2113_; lean_object* v___x_2114_; 
v_data_2112_ = lean_ctor_get(v_e_1988_, 0);
v_expr_2113_ = lean_ctor_get(v_e_1988_, 1);
lean_inc_ref(v_expr_2113_);
v___x_2114_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1987_, v_expr_2113_, v_offset_1989_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_);
if (lean_obj_tag(v___x_2114_) == 0)
{
lean_object* v_a_2115_; lean_object* v_a_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2134_; 
v_a_2115_ = lean_ctor_get(v___x_2114_, 0);
v_a_2116_ = lean_ctor_get(v___x_2114_, 1);
v_isSharedCheck_2134_ = !lean_is_exclusive(v___x_2114_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2118_ = v___x_2114_;
v_isShared_2119_ = v_isSharedCheck_2134_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_a_2116_);
lean_inc(v_a_2115_);
lean_dec(v___x_2114_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2134_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v_fst_2120_; lean_object* v_snd_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2133_; 
v_fst_2120_ = lean_ctor_get(v_a_2115_, 0);
v_snd_2121_ = lean_ctor_get(v_a_2115_, 1);
v_isSharedCheck_2133_ = !lean_is_exclusive(v_a_2115_);
if (v_isSharedCheck_2133_ == 0)
{
v___x_2123_ = v_a_2115_;
v_isShared_2124_ = v_isSharedCheck_2133_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_snd_2121_);
lean_inc(v_fst_2120_);
lean_dec(v_a_2115_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2133_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
uint8_t v___x_2125_; 
v___x_2125_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_expr_2113_, v_fst_2120_);
if (v___x_2125_ == 0)
{
lean_object* v___x_2126_; 
lean_inc(v_data_2112_);
lean_del_object(v___x_2123_);
lean_del_object(v___x_2118_);
lean_dec_ref_known(v_e_1988_, 2);
v___x_2126_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__6(v_data_2112_, v_fst_2120_, v_snd_2121_, v_a_1991_, v_a_1992_, v_a_2116_);
return v___x_2126_;
}
else
{
lean_object* v___x_2128_; 
lean_dec(v_fst_2120_);
if (v_isShared_2124_ == 0)
{
lean_ctor_set(v___x_2123_, 0, v_e_1988_);
v___x_2128_ = v___x_2123_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v_e_1988_);
lean_ctor_set(v_reuseFailAlloc_2132_, 1, v_snd_2121_);
v___x_2128_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
lean_object* v___x_2130_; 
if (v_isShared_2119_ == 0)
{
lean_ctor_set(v___x_2118_, 0, v___x_2128_);
v___x_2130_ = v___x_2118_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v___x_2128_);
lean_ctor_set(v_reuseFailAlloc_2131_, 1, v_a_2116_);
v___x_2130_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
return v___x_2130_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_1988_, 2);
return v___x_2114_;
}
}
case 11:
{
lean_object* v_typeName_2135_; lean_object* v_idx_2136_; lean_object* v_struct_2137_; lean_object* v___x_2138_; 
v_typeName_2135_ = lean_ctor_get(v_e_1988_, 0);
v_idx_2136_ = lean_ctor_get(v_e_1988_, 1);
v_struct_2137_ = lean_ctor_get(v_e_1988_, 2);
lean_inc_ref(v_struct_2137_);
v___x_2138_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1987_, v_struct_2137_, v_offset_1989_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_);
if (lean_obj_tag(v___x_2138_) == 0)
{
lean_object* v_a_2139_; lean_object* v_a_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2158_; 
v_a_2139_ = lean_ctor_get(v___x_2138_, 0);
v_a_2140_ = lean_ctor_get(v___x_2138_, 1);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2138_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2142_ = v___x_2138_;
v_isShared_2143_ = v_isSharedCheck_2158_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_a_2140_);
lean_inc(v_a_2139_);
lean_dec(v___x_2138_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2158_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v_fst_2144_; lean_object* v_snd_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2157_; 
v_fst_2144_ = lean_ctor_get(v_a_2139_, 0);
v_snd_2145_ = lean_ctor_get(v_a_2139_, 1);
v_isSharedCheck_2157_ = !lean_is_exclusive(v_a_2139_);
if (v_isSharedCheck_2157_ == 0)
{
v___x_2147_ = v_a_2139_;
v_isShared_2148_ = v_isSharedCheck_2157_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_snd_2145_);
lean_inc(v_fst_2144_);
lean_dec(v_a_2139_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2157_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
uint8_t v___x_2149_; 
v___x_2149_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_2137_, v_fst_2144_);
if (v___x_2149_ == 0)
{
lean_object* v___x_2150_; 
lean_inc(v_idx_2136_);
lean_inc(v_typeName_2135_);
lean_del_object(v___x_2147_);
lean_del_object(v___x_2142_);
lean_dec_ref_known(v_e_1988_, 3);
v___x_2150_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__7(v_typeName_2135_, v_idx_2136_, v_fst_2144_, v_snd_2145_, v_a_1991_, v_a_1992_, v_a_2140_);
return v___x_2150_;
}
else
{
lean_object* v___x_2152_; 
lean_dec(v_fst_2144_);
if (v_isShared_2148_ == 0)
{
lean_ctor_set(v___x_2147_, 0, v_e_1988_);
v___x_2152_ = v___x_2147_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v_e_1988_);
lean_ctor_set(v_reuseFailAlloc_2156_, 1, v_snd_2145_);
v___x_2152_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
lean_object* v___x_2154_; 
if (v_isShared_2143_ == 0)
{
lean_ctor_set(v___x_2142_, 0, v___x_2152_);
v___x_2154_ = v___x_2142_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v___x_2152_);
lean_ctor_set(v_reuseFailAlloc_2155_, 1, v_a_2140_);
v___x_2154_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
return v___x_2154_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_1988_, 3);
return v___x_2138_;
}
}
default: 
{
lean_object* v___x_2159_; lean_object* v___x_2160_; 
lean_dec(v_offset_1989_);
lean_dec_ref(v_e_1988_);
v___x_2159_ = lean_obj_once(&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__1, &l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__1_once, _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__1);
v___x_2160_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8(v___x_2159_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_);
return v___x_2160_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(lean_object* v_subst_2161_, lean_object* v_e_2162_, lean_object* v_offset_2163_, lean_object* v_a_2164_, uint8_t v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_){
_start:
{
lean_object* v___x_2168_; uint8_t v___x_2169_; 
v___x_2168_ = l_Lean_Expr_looseBVarRange(v_e_2162_);
v___x_2169_ = lean_nat_dec_le(v___x_2168_, v_offset_2163_);
lean_dec(v___x_2168_);
if (v___x_2169_ == 0)
{
lean_object* v_key_2170_; lean_object* v___x_2171_; 
lean_inc(v_offset_2163_);
lean_inc_ref(v_e_2162_);
v_key_2170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_2170_, 0, v_e_2162_);
lean_ctor_set(v_key_2170_, 1, v_offset_2163_);
v___x_2171_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3___redArg(v_a_2164_, v_key_2170_);
if (lean_obj_tag(v___x_2171_) == 1)
{
lean_object* v_val_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
lean_dec_ref_known(v_key_2170_, 2);
lean_dec(v_offset_2163_);
lean_dec_ref(v_e_2162_);
v_val_2172_ = lean_ctor_get(v___x_2171_, 0);
lean_inc(v_val_2172_);
lean_dec_ref_known(v___x_2171_, 1);
v___x_2173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2173_, 0, v_val_2172_);
lean_ctor_set(v___x_2173_, 1, v_a_2164_);
v___x_2174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2174_, 0, v___x_2173_);
lean_ctor_set(v___x_2174_, 1, v_a_2167_);
return v___x_2174_;
}
else
{
lean_dec(v___x_2171_);
switch(lean_obj_tag(v_e_2162_))
{
case 0:
{
lean_object* v_deBruijnIndex_2175_; lean_object* v___x_2176_; 
v_deBruijnIndex_2175_ = lean_ctor_get(v_e_2162_, 0);
lean_inc(v_deBruijnIndex_2175_);
v___x_2176_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(v_subst_2161_, v_e_2162_, v_deBruijnIndex_2175_, v_offset_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_);
lean_dec(v_offset_2163_);
lean_dec(v_deBruijnIndex_2175_);
if (lean_obj_tag(v___x_2176_) == 0)
{
lean_object* v_a_2177_; lean_object* v_a_2178_; lean_object* v_fst_2179_; lean_object* v_snd_2180_; lean_object* v___x_2181_; 
v_a_2177_ = lean_ctor_get(v___x_2176_, 0);
lean_inc(v_a_2177_);
v_a_2178_ = lean_ctor_get(v___x_2176_, 1);
lean_inc(v_a_2178_);
lean_dec_ref_known(v___x_2176_, 2);
v_fst_2179_ = lean_ctor_get(v_a_2177_, 0);
lean_inc(v_fst_2179_);
v_snd_2180_ = lean_ctor_get(v_a_2177_, 1);
lean_inc(v_snd_2180_);
lean_dec(v_a_2177_);
v___x_2181_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_2170_, v_fst_2179_, v_snd_2180_, v_a_2178_);
return v___x_2181_;
}
else
{
lean_dec_ref_known(v_key_2170_, 2);
return v___x_2176_;
}
}
case 9:
{
lean_object* v___x_2182_; 
lean_dec(v_offset_2163_);
v___x_2182_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_2170_, v_e_2162_, v_a_2164_, v_a_2167_);
return v___x_2182_;
}
case 2:
{
lean_object* v___x_2183_; 
lean_dec(v_offset_2163_);
v___x_2183_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_2170_, v_e_2162_, v_a_2164_, v_a_2167_);
return v___x_2183_;
}
case 1:
{
lean_object* v___x_2184_; 
lean_dec(v_offset_2163_);
v___x_2184_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_2170_, v_e_2162_, v_a_2164_, v_a_2167_);
return v___x_2184_;
}
case 4:
{
lean_object* v___x_2185_; 
lean_dec(v_offset_2163_);
v___x_2185_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_2170_, v_e_2162_, v_a_2164_, v_a_2167_);
return v___x_2185_;
}
case 3:
{
lean_object* v___x_2186_; 
lean_dec(v_offset_2163_);
v___x_2186_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_2170_, v_e_2162_, v_a_2164_, v_a_2167_);
return v___x_2186_;
}
default: 
{
lean_object* v___x_2187_; 
v___x_2187_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit(v_subst_2161_, v_e_2162_, v_offset_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_);
if (lean_obj_tag(v___x_2187_) == 0)
{
lean_object* v_a_2188_; lean_object* v_a_2189_; lean_object* v_fst_2190_; lean_object* v_snd_2191_; lean_object* v___x_2192_; 
v_a_2188_ = lean_ctor_get(v___x_2187_, 0);
lean_inc(v_a_2188_);
v_a_2189_ = lean_ctor_get(v___x_2187_, 1);
lean_inc(v_a_2189_);
lean_dec_ref_known(v___x_2187_, 2);
v_fst_2190_ = lean_ctor_get(v_a_2188_, 0);
lean_inc(v_fst_2190_);
v_snd_2191_ = lean_ctor_get(v_a_2188_, 1);
lean_inc(v_snd_2191_);
lean_dec(v_a_2188_);
v___x_2192_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_2170_, v_fst_2190_, v_snd_2191_, v_a_2189_);
return v___x_2192_;
}
else
{
lean_dec_ref_known(v_key_2170_, 2);
return v___x_2187_;
}
}
}
}
}
else
{
lean_object* v___x_2193_; lean_object* v___x_2194_; 
lean_dec(v_offset_2163_);
v___x_2193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2193_, 0, v_e_2162_);
lean_ctor_set(v___x_2193_, 1, v_a_2164_);
v___x_2194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2194_, 0, v___x_2193_);
lean_ctor_set(v___x_2194_, 1, v_a_2167_);
return v___x_2194_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault(lean_object* v_subst_2195_, lean_object* v_e_2196_, lean_object* v_offset_2197_, lean_object* v_a_2198_, uint8_t v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_){
_start:
{
if (lean_obj_tag(v_e_2196_) == 5)
{
lean_object* v_fn_2202_; lean_object* v_arg_2203_; lean_object* v_key_2204_; lean_object* v___x_2205_; 
v_fn_2202_ = lean_ctor_get(v_e_2196_, 0);
v_arg_2203_ = lean_ctor_get(v_e_2196_, 1);
lean_inc(v_offset_2197_);
lean_inc_ref(v_e_2196_);
v_key_2204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_2204_, 0, v_e_2196_);
lean_ctor_set(v_key_2204_, 1, v_offset_2197_);
v___x_2205_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3___redArg(v_a_2198_, v_key_2204_);
if (lean_obj_tag(v___x_2205_) == 1)
{
lean_object* v_val_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; 
lean_dec_ref_known(v_key_2204_, 2);
lean_dec_ref_known(v_e_2196_, 2);
lean_dec(v_offset_2197_);
v_val_2206_ = lean_ctor_get(v___x_2205_, 0);
lean_inc(v_val_2206_);
lean_dec_ref_known(v___x_2205_, 1);
v___x_2207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2207_, 0, v_val_2206_);
lean_ctor_set(v___x_2207_, 1, v_a_2198_);
v___x_2208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2207_);
lean_ctor_set(v___x_2208_, 1, v_a_2201_);
return v___x_2208_;
}
else
{
lean_object* v___x_2209_; 
lean_dec(v___x_2205_);
lean_inc(v_offset_2197_);
lean_inc_ref(v_fn_2202_);
v___x_2209_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault(v_subst_2195_, v_fn_2202_, v_offset_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_);
if (lean_obj_tag(v___x_2209_) == 0)
{
lean_object* v_a_2210_; lean_object* v_a_2211_; lean_object* v_fst_2212_; lean_object* v_snd_2213_; lean_object* v___x_2214_; 
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
lean_inc_ref(v_arg_2203_);
v___x_2214_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_2195_, v_arg_2203_, v_offset_2197_, v_snd_2213_, v_a_2199_, v_a_2200_, v_a_2211_);
if (lean_obj_tag(v___x_2214_) == 0)
{
lean_object* v_a_2215_; lean_object* v_a_2216_; lean_object* v_fst_2217_; lean_object* v_snd_2218_; uint8_t v___y_2220_; uint8_t v___x_2228_; 
v_a_2215_ = lean_ctor_get(v___x_2214_, 0);
lean_inc(v_a_2215_);
v_a_2216_ = lean_ctor_get(v___x_2214_, 1);
lean_inc(v_a_2216_);
lean_dec_ref_known(v___x_2214_, 2);
v_fst_2217_ = lean_ctor_get(v_a_2215_, 0);
lean_inc(v_fst_2217_);
v_snd_2218_ = lean_ctor_get(v_a_2215_, 1);
lean_inc(v_snd_2218_);
lean_dec(v_a_2215_);
v___x_2228_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_2202_, v_fst_2212_);
if (v___x_2228_ == 0)
{
v___y_2220_ = v___x_2228_;
goto v___jp_2219_;
}
else
{
uint8_t v___x_2229_; 
v___x_2229_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_2203_, v_fst_2217_);
v___y_2220_ = v___x_2229_;
goto v___jp_2219_;
}
v___jp_2219_:
{
if (v___y_2220_ == 0)
{
lean_object* v___x_2221_; 
lean_dec_ref_known(v_e_2196_, 2);
v___x_2221_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__2(v_fst_2212_, v_fst_2217_, v_snd_2218_, v_a_2199_, v_a_2200_, v_a_2216_);
if (lean_obj_tag(v___x_2221_) == 0)
{
lean_object* v_a_2222_; lean_object* v_a_2223_; lean_object* v_fst_2224_; lean_object* v_snd_2225_; lean_object* v___x_2226_; 
v_a_2222_ = lean_ctor_get(v___x_2221_, 0);
lean_inc(v_a_2222_);
v_a_2223_ = lean_ctor_get(v___x_2221_, 1);
lean_inc(v_a_2223_);
lean_dec_ref_known(v___x_2221_, 2);
v_fst_2224_ = lean_ctor_get(v_a_2222_, 0);
lean_inc(v_fst_2224_);
v_snd_2225_ = lean_ctor_get(v_a_2222_, 1);
lean_inc(v_snd_2225_);
lean_dec(v_a_2222_);
v___x_2226_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_2204_, v_fst_2224_, v_snd_2225_, v_a_2223_);
return v___x_2226_;
}
else
{
lean_dec_ref_known(v_key_2204_, 2);
return v___x_2221_;
}
}
else
{
lean_object* v___x_2227_; 
lean_dec(v_fst_2217_);
lean_dec(v_fst_2212_);
v___x_2227_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_2204_, v_e_2196_, v_snd_2218_, v_a_2216_);
return v___x_2227_;
}
}
}
else
{
lean_dec(v_fst_2212_);
lean_dec_ref_known(v_key_2204_, 2);
lean_dec_ref_known(v_e_2196_, 2);
return v___x_2214_;
}
}
else
{
lean_dec_ref_known(v_key_2204_, 2);
lean_dec_ref_known(v_e_2196_, 2);
lean_dec(v_offset_2197_);
return v___x_2209_;
}
}
}
else
{
lean_object* v___x_2230_; 
v___x_2230_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_2195_, v_e_2196_, v_offset_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_);
return v___x_2230_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault___boxed(lean_object* v_subst_2231_, lean_object* v_e_2232_, lean_object* v_offset_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_){
_start:
{
uint8_t v_a_boxed_2238_; lean_object* v_res_2239_; 
v_a_boxed_2238_ = lean_unbox(v_a_2235_);
v_res_2239_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault(v_subst_2231_, v_e_2232_, v_offset_2233_, v_a_2234_, v_a_boxed_2238_, v_a_2236_, v_a_2237_);
lean_dec_ref(v_a_2236_);
lean_dec_ref(v_subst_2231_);
return v_res_2239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild___boxed(lean_object* v_subst_2240_, lean_object* v_e_2241_, lean_object* v_offset_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_){
_start:
{
uint8_t v_a_boxed_2247_; lean_object* v_res_2248_; 
v_a_boxed_2247_ = lean_unbox(v_a_2244_);
v_res_2248_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_2240_, v_e_2241_, v_offset_2242_, v_a_2243_, v_a_boxed_2247_, v_a_2245_, v_a_2246_);
lean_dec_ref(v_a_2245_);
lean_dec_ref(v_subst_2240_);
return v_res_2248_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___boxed(lean_object* v_subst_2249_, lean_object* v_e_2250_, lean_object* v_f_2251_, lean_object* v_arg_2252_, lean_object* v_offset_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_){
_start:
{
uint8_t v_a_boxed_2258_; lean_object* v_res_2259_; 
v_a_boxed_2258_ = lean_unbox(v_a_2255_);
v_res_2259_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg(v_subst_2249_, v_e_2250_, v_f_2251_, v_arg_2252_, v_offset_2253_, v_a_2254_, v_a_boxed_2258_, v_a_2256_, v_a_2257_);
lean_dec_ref(v_a_2256_);
lean_dec_ref(v_subst_2249_);
return v_res_2259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___boxed(lean_object* v_subst_2260_, lean_object* v_e_2261_, lean_object* v_f_2262_, lean_object* v_argsRev_2263_, lean_object* v_offset_2264_, lean_object* v_modified_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_){
_start:
{
uint8_t v_modified_boxed_2270_; uint8_t v_a_boxed_2271_; lean_object* v_res_2272_; 
v_modified_boxed_2270_ = lean_unbox(v_modified_2265_);
v_a_boxed_2271_ = lean_unbox(v_a_2267_);
v_res_2272_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta(v_subst_2260_, v_e_2261_, v_f_2262_, v_argsRev_2263_, v_offset_2264_, v_modified_boxed_2270_, v_a_2266_, v_a_boxed_2271_, v_a_2268_, v_a_2269_);
lean_dec_ref(v_a_2268_);
lean_dec_ref(v_subst_2260_);
return v_res_2272_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___boxed(lean_object* v_subst_2273_, lean_object* v_e_2274_, lean_object* v_offset_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_){
_start:
{
uint8_t v_a_boxed_2280_; lean_object* v_res_2281_; 
v_a_boxed_2280_ = lean_unbox(v_a_2277_);
v_res_2281_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit(v_subst_2273_, v_e_2274_, v_offset_2275_, v_a_2276_, v_a_boxed_2280_, v_a_2278_, v_a_2279_);
lean_dec_ref(v_a_2278_);
lean_dec_ref(v_subst_2273_);
return v_res_2281_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp(lean_object* v_subst_2282_, lean_object* v_e_2283_, lean_object* v_f_2284_, lean_object* v_arg_2285_, lean_object* v_offset_2286_, lean_object* v_x_2287_, lean_object* v_a_2288_, uint8_t v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_){
_start:
{
lean_object* v___x_2292_; 
v___x_2292_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg(v_subst_2282_, v_e_2283_, v_f_2284_, v_arg_2285_, v_offset_2286_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_);
return v___x_2292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___boxed(lean_object* v_subst_2293_, lean_object* v_e_2294_, lean_object* v_f_2295_, lean_object* v_arg_2296_, lean_object* v_offset_2297_, lean_object* v_x_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_){
_start:
{
uint8_t v_a_boxed_2303_; lean_object* v_res_2304_; 
v_a_boxed_2303_ = lean_unbox(v_a_2300_);
v_res_2304_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp(v_subst_2293_, v_e_2294_, v_f_2295_, v_arg_2296_, v_offset_2297_, v_x_2298_, v_a_2299_, v_a_boxed_2303_, v_a_2301_, v_a_2302_);
lean_dec_ref(v_a_2301_);
lean_dec_ref(v_subst_2293_);
return v_res_2304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27(lean_object* v_e_2305_, lean_object* v_subst_2306_, uint8_t v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_){
_start:
{
uint8_t v___y_2311_; lean_object* v___x_2335_; lean_object* v___x_2336_; uint8_t v___x_2337_; 
v___x_2335_ = lean_array_get_size(v_subst_2306_);
v___x_2336_ = lean_unsigned_to_nat(0u);
v___x_2337_ = lean_nat_dec_eq(v___x_2335_, v___x_2336_);
if (v___x_2337_ == 0)
{
uint8_t v___x_2338_; 
v___x_2338_ = l_Lean_Expr_hasLooseBVars(v_e_2305_);
if (v___x_2338_ == 0)
{
lean_object* v___x_2339_; 
v___x_2339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2339_, 0, v_e_2305_);
lean_ctor_set(v___x_2339_, 1, v_a_2309_);
return v___x_2339_;
}
else
{
v___y_2311_ = v___x_2337_;
goto v___jp_2310_;
}
}
else
{
v___y_2311_ = v___x_2337_;
goto v___jp_2310_;
}
v___jp_2310_:
{
if (v___y_2311_ == 0)
{
lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; 
v___x_2312_ = lean_unsigned_to_nat(0u);
v___x_2313_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__1, &l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__1_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__1);
v___x_2314_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit(v_subst_2306_, v_e_2305_, v___x_2312_, v___x_2313_, v_a_2307_, v_a_2308_, v_a_2309_);
if (lean_obj_tag(v___x_2314_) == 0)
{
lean_object* v_a_2315_; lean_object* v_a_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2324_; 
v_a_2315_ = lean_ctor_get(v___x_2314_, 0);
v_a_2316_ = lean_ctor_get(v___x_2314_, 1);
v_isSharedCheck_2324_ = !lean_is_exclusive(v___x_2314_);
if (v_isSharedCheck_2324_ == 0)
{
v___x_2318_ = v___x_2314_;
v_isShared_2319_ = v_isSharedCheck_2324_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_a_2316_);
lean_inc(v_a_2315_);
lean_dec(v___x_2314_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2324_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
lean_object* v_fst_2320_; lean_object* v___x_2322_; 
v_fst_2320_ = lean_ctor_get(v_a_2315_, 0);
lean_inc(v_fst_2320_);
lean_dec(v_a_2315_);
if (v_isShared_2319_ == 0)
{
lean_ctor_set(v___x_2318_, 0, v_fst_2320_);
v___x_2322_ = v___x_2318_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2323_; 
v_reuseFailAlloc_2323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2323_, 0, v_fst_2320_);
lean_ctor_set(v_reuseFailAlloc_2323_, 1, v_a_2316_);
v___x_2322_ = v_reuseFailAlloc_2323_;
goto v_reusejp_2321_;
}
v_reusejp_2321_:
{
return v___x_2322_;
}
}
}
else
{
lean_object* v_a_2325_; lean_object* v_a_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2333_; 
v_a_2325_ = lean_ctor_get(v___x_2314_, 0);
v_a_2326_ = lean_ctor_get(v___x_2314_, 1);
v_isSharedCheck_2333_ = !lean_is_exclusive(v___x_2314_);
if (v_isSharedCheck_2333_ == 0)
{
v___x_2328_ = v___x_2314_;
v_isShared_2329_ = v_isSharedCheck_2333_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_a_2326_);
lean_inc(v_a_2325_);
lean_dec(v___x_2314_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2333_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v___x_2331_; 
if (v_isShared_2329_ == 0)
{
v___x_2331_ = v___x_2328_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v_a_2325_);
lean_ctor_set(v_reuseFailAlloc_2332_, 1, v_a_2326_);
v___x_2331_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
return v___x_2331_;
}
}
}
}
else
{
lean_object* v___x_2334_; 
v___x_2334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2334_, 0, v_e_2305_);
lean_ctor_set(v___x_2334_, 1, v_a_2309_);
return v___x_2334_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27___boxed(lean_object* v_e_2340_, lean_object* v_subst_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_){
_start:
{
uint8_t v_a_boxed_2345_; lean_object* v_res_2346_; 
v_a_boxed_2345_ = lean_unbox(v_a_2342_);
v_res_2346_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27(v_e_2340_, v_subst_2341_, v_a_boxed_2345_, v_a_2343_, v_a_2344_);
lean_dec_ref(v_a_2343_);
lean_dec_ref(v_subst_2341_);
return v_res_2346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevBetaS(lean_object* v_e_2347_, lean_object* v_subst_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_){
_start:
{
uint8_t v___x_2356_; 
v___x_2356_ = l_Lean_Expr_hasLooseBVars(v_e_2347_);
if (v___x_2356_ == 0)
{
lean_object* v___x_2357_; 
lean_dec_ref(v_subst_2348_);
v___x_2357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2357_, 0, v_e_2347_);
return v___x_2357_;
}
else
{
lean_object* v___x_2358_; lean_object* v___x_2359_; uint8_t v___x_2360_; 
v___x_2358_ = lean_array_get_size(v_subst_2348_);
v___x_2359_ = lean_unsigned_to_nat(0u);
v___x_2360_ = lean_nat_dec_eq(v___x_2358_, v___x_2359_);
if (v___x_2360_ == 0)
{
lean_object* v___x_2361_; lean_object* v___x_2362_; uint8_t v_debug_2363_; lean_object* v_env_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; 
v___x_2361_ = lean_st_ref_get(v_a_2350_);
v___x_2362_ = lean_st_ref_get(v_a_2354_);
v_debug_2363_ = lean_ctor_get_uint8(v___x_2361_, sizeof(void*)*10);
lean_dec(v___x_2361_);
v_env_2364_ = lean_ctor_get(v___x_2362_, 0);
lean_inc_ref(v_env_2364_);
lean_dec(v___x_2362_);
v___x_2365_ = lean_box(v_debug_2363_);
v___x_2366_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27___boxed), 5, 3);
lean_closure_set(v___x_2366_, 0, v_e_2347_);
lean_closure_set(v___x_2366_, 1, v_subst_2348_);
lean_closure_set(v___x_2366_, 2, v___x_2365_);
v___x_2367_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2367_, 0, v_env_2364_);
lean_ctor_set_uint8(v___x_2367_, sizeof(void*)*1, v___x_2360_);
lean_ctor_set_uint8(v___x_2367_, sizeof(void*)*1 + 1, v___x_2360_);
v___x_2368_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___x_2366_, v___x_2367_, v_a_2350_);
if (lean_obj_tag(v___x_2368_) == 0)
{
lean_object* v_a_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2379_; 
v_a_2369_ = lean_ctor_get(v___x_2368_, 0);
v_isSharedCheck_2379_ = !lean_is_exclusive(v___x_2368_);
if (v_isSharedCheck_2379_ == 0)
{
v___x_2371_ = v___x_2368_;
v_isShared_2372_ = v_isSharedCheck_2379_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_a_2369_);
lean_dec(v___x_2368_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2379_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
if (lean_obj_tag(v_a_2369_) == 0)
{
lean_object* v___x_2373_; lean_object* v___x_2374_; 
lean_dec_ref_known(v_a_2369_, 1);
lean_del_object(v___x_2371_);
v___x_2373_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__2, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__2_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__2);
v___x_2374_ = l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(v___x_2373_, v_a_2349_, v_a_2350_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_);
return v___x_2374_;
}
else
{
lean_object* v_a_2375_; lean_object* v___x_2377_; 
v_a_2375_ = lean_ctor_get(v_a_2369_, 0);
lean_inc(v_a_2375_);
lean_dec_ref_known(v_a_2369_, 1);
if (v_isShared_2372_ == 0)
{
lean_ctor_set(v___x_2371_, 0, v_a_2375_);
v___x_2377_ = v___x_2371_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v_a_2375_);
v___x_2377_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
return v___x_2377_;
}
}
}
}
else
{
lean_object* v_a_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2387_; 
v_a_2380_ = lean_ctor_get(v___x_2368_, 0);
v_isSharedCheck_2387_ = !lean_is_exclusive(v___x_2368_);
if (v_isSharedCheck_2387_ == 0)
{
v___x_2382_ = v___x_2368_;
v_isShared_2383_ = v_isSharedCheck_2387_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_a_2380_);
lean_dec(v___x_2368_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2387_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v___x_2385_; 
if (v_isShared_2383_ == 0)
{
v___x_2385_ = v___x_2382_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2386_; 
v_reuseFailAlloc_2386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2386_, 0, v_a_2380_);
v___x_2385_ = v_reuseFailAlloc_2386_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
return v___x_2385_;
}
}
}
}
else
{
lean_object* v___x_2388_; 
lean_dec_ref(v_subst_2348_);
v___x_2388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2388_, 0, v_e_2347_);
return v___x_2388_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevBetaS___boxed(lean_object* v_e_2389_, lean_object* v_subst_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_){
_start:
{
lean_object* v_res_2398_; 
v_res_2398_ = l_Lean_Meta_Sym_instantiateRevBetaS(v_e_2389_, v_subst_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_);
lean_dec(v_a_2396_);
lean_dec_ref(v_a_2395_);
lean_dec(v_a_2394_);
lean_dec_ref(v_a_2393_);
lean_dec(v_a_2392_);
lean_dec_ref(v_a_2391_);
return v_res_2398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_betaRevS(lean_object* v_f_2399_, lean_object* v_revArgs_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_){
_start:
{
lean_object* v___x_2408_; lean_object* v___x_2409_; uint8_t v_debug_2410_; lean_object* v_env_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; uint8_t v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; 
v___x_2408_ = lean_st_ref_get(v_a_2402_);
v___x_2409_ = lean_st_ref_get(v_a_2406_);
v_debug_2410_ = lean_ctor_get_uint8(v___x_2408_, sizeof(void*)*10);
lean_dec(v___x_2408_);
v_env_2411_ = lean_ctor_get(v___x_2409_, 0);
lean_inc_ref(v_env_2411_);
lean_dec(v___x_2409_);
v___x_2412_ = lean_box(v_debug_2410_);
v___x_2413_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27___boxed), 5, 3);
lean_closure_set(v___x_2413_, 0, v_f_2399_);
lean_closure_set(v___x_2413_, 1, v_revArgs_2400_);
lean_closure_set(v___x_2413_, 2, v___x_2412_);
v___x_2414_ = 0;
v___x_2415_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2415_, 0, v_env_2411_);
lean_ctor_set_uint8(v___x_2415_, sizeof(void*)*1, v___x_2414_);
lean_ctor_set_uint8(v___x_2415_, sizeof(void*)*1 + 1, v___x_2414_);
v___x_2416_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___x_2413_, v___x_2415_, v_a_2402_);
if (lean_obj_tag(v___x_2416_) == 0)
{
lean_object* v_a_2417_; lean_object* v___x_2419_; uint8_t v_isShared_2420_; uint8_t v_isSharedCheck_2427_; 
v_a_2417_ = lean_ctor_get(v___x_2416_, 0);
v_isSharedCheck_2427_ = !lean_is_exclusive(v___x_2416_);
if (v_isSharedCheck_2427_ == 0)
{
v___x_2419_ = v___x_2416_;
v_isShared_2420_ = v_isSharedCheck_2427_;
goto v_resetjp_2418_;
}
else
{
lean_inc(v_a_2417_);
lean_dec(v___x_2416_);
v___x_2419_ = lean_box(0);
v_isShared_2420_ = v_isSharedCheck_2427_;
goto v_resetjp_2418_;
}
v_resetjp_2418_:
{
if (lean_obj_tag(v_a_2417_) == 0)
{
lean_object* v___x_2421_; lean_object* v___x_2422_; 
lean_dec_ref_known(v_a_2417_, 1);
lean_del_object(v___x_2419_);
v___x_2421_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__2, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__2_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__2);
v___x_2422_ = l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(v___x_2421_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_);
return v___x_2422_;
}
else
{
lean_object* v_a_2423_; lean_object* v___x_2425_; 
v_a_2423_ = lean_ctor_get(v_a_2417_, 0);
lean_inc(v_a_2423_);
lean_dec_ref_known(v_a_2417_, 1);
if (v_isShared_2420_ == 0)
{
lean_ctor_set(v___x_2419_, 0, v_a_2423_);
v___x_2425_ = v___x_2419_;
goto v_reusejp_2424_;
}
else
{
lean_object* v_reuseFailAlloc_2426_; 
v_reuseFailAlloc_2426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2426_, 0, v_a_2423_);
v___x_2425_ = v_reuseFailAlloc_2426_;
goto v_reusejp_2424_;
}
v_reusejp_2424_:
{
return v___x_2425_;
}
}
}
}
else
{
lean_object* v_a_2428_; lean_object* v___x_2430_; uint8_t v_isShared_2431_; uint8_t v_isSharedCheck_2435_; 
v_a_2428_ = lean_ctor_get(v___x_2416_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v___x_2416_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2430_ = v___x_2416_;
v_isShared_2431_ = v_isSharedCheck_2435_;
goto v_resetjp_2429_;
}
else
{
lean_inc(v_a_2428_);
lean_dec(v___x_2416_);
v___x_2430_ = lean_box(0);
v_isShared_2431_ = v_isSharedCheck_2435_;
goto v_resetjp_2429_;
}
v_resetjp_2429_:
{
lean_object* v___x_2433_; 
if (v_isShared_2431_ == 0)
{
v___x_2433_ = v___x_2430_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v_a_2428_);
v___x_2433_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
return v___x_2433_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_betaRevS___boxed(lean_object* v_f_2436_, lean_object* v_revArgs_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_){
_start:
{
lean_object* v_res_2445_; 
v_res_2445_ = l_Lean_Meta_Sym_betaRevS(v_f_2436_, v_revArgs_2437_, v_a_2438_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_);
lean_dec(v_a_2443_);
lean_dec_ref(v_a_2442_);
lean_dec(v_a_2441_);
lean_dec_ref(v_a_2440_);
lean_dec(v_a_2439_);
lean_dec_ref(v_a_2438_);
return v_res_2445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_betaS(lean_object* v_f_2446_, lean_object* v_args_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_){
_start:
{
lean_object* v___x_2455_; lean_object* v___x_2456_; 
v___x_2455_ = l_Array_reverse___redArg(v_args_2447_);
v___x_2456_ = l_Lean_Meta_Sym_betaRevS(v_f_2446_, v___x_2455_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_);
return v___x_2456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_betaS___boxed(lean_object* v_f_2457_, lean_object* v_args_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_){
_start:
{
lean_object* v_res_2466_; 
v_res_2466_ = l_Lean_Meta_Sym_betaS(v_f_2457_, v_args_2458_, v_a_2459_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_);
lean_dec(v_a_2464_);
lean_dec_ref(v_a_2463_);
lean_dec(v_a_2462_);
lean_dec_ref(v_a_2461_);
lean_dec(v_a_2460_);
lean_dec_ref(v_a_2459_);
return v_res_2466_;
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
