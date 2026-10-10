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
lean_object* l_Std_HashMap_instInhabited___redArg();
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
lean_object* l_EStateM_instMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg();
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___redArg___lam__0, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8___closed__0_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___redArg___lam__1, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___redArg___lam__2, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
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
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1___closed__0;
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
lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0(lean_object* v_idx_5_, uint8_t v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___redArg(v_idx_5_, v___y_8_);
return v___x_9_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_idx_5_ = stack[0].m_obj;
uint8_t v___y_6_ = stack[1].m_num;
lean_object* v___y_7_ = stack[2].m_obj;
lean_object* v___y_8_ = stack[3].m_obj;
lean_object* v_res_10_;
v_res_10_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0(v_idx_5_, v___y_6_, v___y_7_, v___y_8_);
stack->m_obj
 = v_res_10_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___boxed(lean_object* v_idx_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_){
_start:
{
uint8_t v___y_25949__boxed_15_; lean_object* v_res_16_; 
v___y_25949__boxed_15_ = lean_unbox(v___y_12_);
v_res_16_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0(v_idx_11_, v___y_25949__boxed_15_, v___y_13_, v___y_14_);
lean_dec_ref(v___y_13_);
return v_res_16_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__0(void){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = l_Lean_Meta_Sym_instInhabitedSymM___redArg();
return v___x_17_;
}
}
lean_object* l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(lean_object* v_msg_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_){
_start:
{
lean_object* v___x_26_; lean_object* v___x_2922__overap_27_; lean_object* v___x_28_; 
v___x_26_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__0, &l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__0);
v___x_2922__overap_27_ = lean_panic_fn_borrowed(v___x_26_, v_msg_18_);
lean_inc(v___y_24_);
lean_inc_ref(v___y_23_);
lean_inc(v___y_22_);
lean_inc_ref(v___y_21_);
lean_inc(v___y_20_);
lean_inc_ref(v___y_19_);
v___x_28_ = lean_apply_7(v___x_2922__overap_27_, v___y_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, lean_box(0));
return v___x_28_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_18_ = stack[0].m_obj;
lean_object* v___y_19_ = stack[1].m_obj;
lean_object* v___y_20_ = stack[2].m_obj;
lean_object* v___y_21_ = stack[3].m_obj;
lean_object* v___y_22_ = stack[4].m_obj;
lean_object* v___y_23_ = stack[5].m_obj;
lean_object* v___y_24_ = stack[6].m_obj;
lean_object* v_res_29_;
v_res_29_ = l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(v_msg_18_, v___y_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_);
stack->m_obj
 = v_res_29_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___boxed(lean_object* v_msg_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(v_msg_30_, v___y_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_, v___y_36_);
lean_dec(v___y_36_);
lean_dec_ref(v___y_35_);
lean_dec(v___y_34_);
lean_dec_ref(v___y_33_);
lean_dec(v___y_32_);
lean_dec_ref(v___y_31_);
return v_res_38_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__2(lean_object* v_f_39_, lean_object* v_a_40_, lean_object* v___y_41_, uint8_t v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_){
_start:
{
lean_object* v___y_46_; lean_object* v___y_47_; 
if (v___y_42_ == 0)
{
v___y_46_ = v___y_41_;
v___y_47_ = v___y_44_;
goto v___jp_45_;
}
else
{
lean_object* v___x_69_; 
v___x_69_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_f_39_, v___y_42_, v___y_43_, v___y_44_);
if (lean_obj_tag(v___x_69_) == 0)
{
lean_object* v_a_70_; lean_object* v___x_71_; 
v_a_70_ = lean_ctor_get(v___x_69_, 1);
lean_inc(v_a_70_);
lean_dec_ref_known(v___x_69_, 2);
v___x_71_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_a_40_, v___y_42_, v___y_43_, v_a_70_);
if (lean_obj_tag(v___x_71_) == 0)
{
lean_object* v_a_72_; 
v_a_72_ = lean_ctor_get(v___x_71_, 1);
lean_inc(v_a_72_);
lean_dec_ref_known(v___x_71_, 2);
v___y_46_ = v___y_41_;
v___y_47_ = v_a_72_;
goto v___jp_45_;
}
else
{
lean_object* v_a_73_; lean_object* v_a_74_; lean_object* v___x_76_; uint8_t v_isShared_77_; uint8_t v_isSharedCheck_81_; 
lean_dec_ref(v___y_41_);
lean_dec_ref(v_a_40_);
lean_dec_ref(v_f_39_);
v_a_73_ = lean_ctor_get(v___x_71_, 0);
v_a_74_ = lean_ctor_get(v___x_71_, 1);
v_isSharedCheck_81_ = !lean_is_exclusive(v___x_71_);
if (v_isSharedCheck_81_ == 0)
{
v___x_76_ = v___x_71_;
v_isShared_77_ = v_isSharedCheck_81_;
goto v_resetjp_75_;
}
else
{
lean_inc(v_a_74_);
lean_inc(v_a_73_);
lean_dec(v___x_71_);
v___x_76_ = lean_box(0);
v_isShared_77_ = v_isSharedCheck_81_;
goto v_resetjp_75_;
}
v_resetjp_75_:
{
lean_object* v___x_79_; 
if (v_isShared_77_ == 0)
{
v___x_79_ = v___x_76_;
goto v_reusejp_78_;
}
else
{
lean_object* v_reuseFailAlloc_80_; 
v_reuseFailAlloc_80_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_80_, 0, v_a_73_);
lean_ctor_set(v_reuseFailAlloc_80_, 1, v_a_74_);
v___x_79_ = v_reuseFailAlloc_80_;
goto v_reusejp_78_;
}
v_reusejp_78_:
{
return v___x_79_;
}
}
}
}
else
{
lean_object* v_a_82_; lean_object* v_a_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_90_; 
lean_dec_ref(v___y_41_);
lean_dec_ref(v_a_40_);
lean_dec_ref(v_f_39_);
v_a_82_ = lean_ctor_get(v___x_69_, 0);
v_a_83_ = lean_ctor_get(v___x_69_, 1);
v_isSharedCheck_90_ = !lean_is_exclusive(v___x_69_);
if (v_isSharedCheck_90_ == 0)
{
v___x_85_ = v___x_69_;
v_isShared_86_ = v_isSharedCheck_90_;
goto v_resetjp_84_;
}
else
{
lean_inc(v_a_83_);
lean_inc(v_a_82_);
lean_dec(v___x_69_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_90_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v___x_88_; 
if (v_isShared_86_ == 0)
{
v___x_88_ = v___x_85_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v_a_82_);
lean_ctor_set(v_reuseFailAlloc_89_, 1, v_a_83_);
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
v___jp_45_:
{
lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_48_ = l_Lean_Expr_app___override(v_f_39_, v_a_40_);
v___x_49_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_48_, v___y_47_);
if (lean_obj_tag(v___x_49_) == 0)
{
lean_object* v_a_50_; lean_object* v_a_51_; lean_object* v___x_53_; uint8_t v_isShared_54_; uint8_t v_isSharedCheck_59_; 
v_a_50_ = lean_ctor_get(v___x_49_, 0);
v_a_51_ = lean_ctor_get(v___x_49_, 1);
v_isSharedCheck_59_ = !lean_is_exclusive(v___x_49_);
if (v_isSharedCheck_59_ == 0)
{
v___x_53_ = v___x_49_;
v_isShared_54_ = v_isSharedCheck_59_;
goto v_resetjp_52_;
}
else
{
lean_inc(v_a_51_);
lean_inc(v_a_50_);
lean_dec(v___x_49_);
v___x_53_ = lean_box(0);
v_isShared_54_ = v_isSharedCheck_59_;
goto v_resetjp_52_;
}
v_resetjp_52_:
{
lean_object* v___x_55_; lean_object* v___x_57_; 
v___x_55_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_55_, 0, v_a_50_);
lean_ctor_set(v___x_55_, 1, v___y_46_);
if (v_isShared_54_ == 0)
{
lean_ctor_set(v___x_53_, 0, v___x_55_);
v___x_57_ = v___x_53_;
goto v_reusejp_56_;
}
else
{
lean_object* v_reuseFailAlloc_58_; 
v_reuseFailAlloc_58_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_58_, 0, v___x_55_);
lean_ctor_set(v_reuseFailAlloc_58_, 1, v_a_51_);
v___x_57_ = v_reuseFailAlloc_58_;
goto v_reusejp_56_;
}
v_reusejp_56_:
{
return v___x_57_;
}
}
}
else
{
lean_object* v_a_60_; lean_object* v_a_61_; lean_object* v___x_63_; uint8_t v_isShared_64_; uint8_t v_isSharedCheck_68_; 
lean_dec_ref(v___y_46_);
v_a_60_ = lean_ctor_get(v___x_49_, 0);
v_a_61_ = lean_ctor_get(v___x_49_, 1);
v_isSharedCheck_68_ = !lean_is_exclusive(v___x_49_);
if (v_isSharedCheck_68_ == 0)
{
v___x_63_ = v___x_49_;
v_isShared_64_ = v_isSharedCheck_68_;
goto v_resetjp_62_;
}
else
{
lean_inc(v_a_61_);
lean_inc(v_a_60_);
lean_dec(v___x_49_);
v___x_63_ = lean_box(0);
v_isShared_64_ = v_isSharedCheck_68_;
goto v_resetjp_62_;
}
v_resetjp_62_:
{
lean_object* v___x_66_; 
if (v_isShared_64_ == 0)
{
v___x_66_ = v___x_63_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_67_; 
v_reuseFailAlloc_67_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_67_, 0, v_a_60_);
lean_ctor_set(v_reuseFailAlloc_67_, 1, v_a_61_);
v___x_66_ = v_reuseFailAlloc_67_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
return v___x_66_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_39_ = stack[0].m_obj;
lean_object* v_a_40_ = stack[1].m_obj;
lean_object* v___y_41_ = stack[2].m_obj;
uint8_t v___y_42_ = stack[3].m_num;
lean_object* v___y_43_ = stack[4].m_obj;
lean_object* v___y_44_ = stack[5].m_obj;
lean_object* v_res_91_;
v_res_91_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__2(v_f_39_, v_a_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_);
stack->m_obj
 = v_res_91_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__2___boxed(lean_object* v_f_92_, lean_object* v_a_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_){
_start:
{
uint8_t v___y_26013__boxed_98_; lean_object* v_res_99_; 
v___y_26013__boxed_98_ = lean_unbox(v___y_95_);
v_res_99_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__2(v_f_92_, v_a_93_, v___y_94_, v___y_26013__boxed_98_, v___y_96_, v___y_97_);
lean_dec_ref(v___y_96_);
return v_res_99_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__4(lean_object* v_x_100_, uint8_t v_bi_101_, lean_object* v_t_102_, lean_object* v_b_103_, lean_object* v___y_104_, uint8_t v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_){
_start:
{
lean_object* v___y_109_; lean_object* v___y_110_; 
if (v___y_105_ == 0)
{
v___y_109_ = v___y_104_;
v___y_110_ = v___y_107_;
goto v___jp_108_;
}
else
{
lean_object* v___x_132_; 
v___x_132_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_102_, v___y_105_, v___y_106_, v___y_107_);
if (lean_obj_tag(v___x_132_) == 0)
{
lean_object* v_a_133_; lean_object* v___x_134_; 
v_a_133_ = lean_ctor_get(v___x_132_, 1);
lean_inc(v_a_133_);
lean_dec_ref_known(v___x_132_, 2);
v___x_134_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_103_, v___y_105_, v___y_106_, v_a_133_);
if (lean_obj_tag(v___x_134_) == 0)
{
lean_object* v_a_135_; 
v_a_135_ = lean_ctor_get(v___x_134_, 1);
lean_inc(v_a_135_);
lean_dec_ref_known(v___x_134_, 2);
v___y_109_ = v___y_104_;
v___y_110_ = v_a_135_;
goto v___jp_108_;
}
else
{
lean_object* v_a_136_; lean_object* v_a_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_144_; 
lean_dec_ref(v___y_104_);
lean_dec_ref(v_b_103_);
lean_dec_ref(v_t_102_);
lean_dec(v_x_100_);
v_a_136_ = lean_ctor_get(v___x_134_, 0);
v_a_137_ = lean_ctor_get(v___x_134_, 1);
v_isSharedCheck_144_ = !lean_is_exclusive(v___x_134_);
if (v_isSharedCheck_144_ == 0)
{
v___x_139_ = v___x_134_;
v_isShared_140_ = v_isSharedCheck_144_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_a_137_);
lean_inc(v_a_136_);
lean_dec(v___x_134_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_144_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
lean_object* v___x_142_; 
if (v_isShared_140_ == 0)
{
v___x_142_ = v___x_139_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v_a_136_);
lean_ctor_set(v_reuseFailAlloc_143_, 1, v_a_137_);
v___x_142_ = v_reuseFailAlloc_143_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
return v___x_142_;
}
}
}
}
else
{
lean_object* v_a_145_; lean_object* v_a_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_153_; 
lean_dec_ref(v___y_104_);
lean_dec_ref(v_b_103_);
lean_dec_ref(v_t_102_);
lean_dec(v_x_100_);
v_a_145_ = lean_ctor_get(v___x_132_, 0);
v_a_146_ = lean_ctor_get(v___x_132_, 1);
v_isSharedCheck_153_ = !lean_is_exclusive(v___x_132_);
if (v_isSharedCheck_153_ == 0)
{
v___x_148_ = v___x_132_;
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_a_146_);
lean_inc(v_a_145_);
lean_dec(v___x_132_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_151_; 
if (v_isShared_149_ == 0)
{
v___x_151_ = v___x_148_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_a_145_);
lean_ctor_set(v_reuseFailAlloc_152_, 1, v_a_146_);
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
v___jp_108_:
{
lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_111_ = l_Lean_Expr_forallE___override(v_x_100_, v_t_102_, v_b_103_, v_bi_101_);
v___x_112_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_111_, v___y_110_);
if (lean_obj_tag(v___x_112_) == 0)
{
lean_object* v_a_113_; lean_object* v_a_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_122_; 
v_a_113_ = lean_ctor_get(v___x_112_, 0);
v_a_114_ = lean_ctor_get(v___x_112_, 1);
v_isSharedCheck_122_ = !lean_is_exclusive(v___x_112_);
if (v_isSharedCheck_122_ == 0)
{
v___x_116_ = v___x_112_;
v_isShared_117_ = v_isSharedCheck_122_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_a_114_);
lean_inc(v_a_113_);
lean_dec(v___x_112_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_122_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
lean_object* v___x_118_; lean_object* v___x_120_; 
v___x_118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_118_, 0, v_a_113_);
lean_ctor_set(v___x_118_, 1, v___y_109_);
if (v_isShared_117_ == 0)
{
lean_ctor_set(v___x_116_, 0, v___x_118_);
v___x_120_ = v___x_116_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v___x_118_);
lean_ctor_set(v_reuseFailAlloc_121_, 1, v_a_114_);
v___x_120_ = v_reuseFailAlloc_121_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
return v___x_120_;
}
}
}
else
{
lean_object* v_a_123_; lean_object* v_a_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_131_; 
lean_dec_ref(v___y_109_);
v_a_123_ = lean_ctor_get(v___x_112_, 0);
v_a_124_ = lean_ctor_get(v___x_112_, 1);
v_isSharedCheck_131_ = !lean_is_exclusive(v___x_112_);
if (v_isSharedCheck_131_ == 0)
{
v___x_126_ = v___x_112_;
v_isShared_127_ = v_isSharedCheck_131_;
goto v_resetjp_125_;
}
else
{
lean_inc(v_a_124_);
lean_inc(v_a_123_);
lean_dec(v___x_112_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_131_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v___x_129_; 
if (v_isShared_127_ == 0)
{
v___x_129_ = v___x_126_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v_a_123_);
lean_ctor_set(v_reuseFailAlloc_130_, 1, v_a_124_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_100_ = stack[0].m_obj;
uint8_t v_bi_101_ = stack[1].m_num;
lean_object* v_t_102_ = stack[2].m_obj;
lean_object* v_b_103_ = stack[3].m_obj;
lean_object* v___y_104_ = stack[4].m_obj;
uint8_t v___y_105_ = stack[5].m_num;
lean_object* v___y_106_ = stack[6].m_obj;
lean_object* v___y_107_ = stack[7].m_obj;
lean_object* v_res_154_;
v_res_154_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__4(v_x_100_, v_bi_101_, v_t_102_, v_b_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_);
stack->m_obj
 = v_res_154_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__4___boxed(lean_object* v_x_155_, lean_object* v_bi_156_, lean_object* v_t_157_, lean_object* v_b_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_){
_start:
{
uint8_t v_bi_boxed_163_; uint8_t v___y_26173__boxed_164_; lean_object* v_res_165_; 
v_bi_boxed_163_ = lean_unbox(v_bi_156_);
v___y_26173__boxed_164_ = lean_unbox(v___y_160_);
v_res_165_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__4(v_x_155_, v_bi_boxed_163_, v_t_157_, v_b_158_, v___y_159_, v___y_26173__boxed_164_, v___y_161_, v___y_162_);
lean_dec_ref(v___y_161_);
return v_res_165_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__7(lean_object* v_structName_166_, lean_object* v_idx_167_, lean_object* v_struct_168_, lean_object* v___y_169_, uint8_t v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_){
_start:
{
lean_object* v___y_174_; lean_object* v___y_175_; 
if (v___y_170_ == 0)
{
v___y_174_ = v___y_169_;
v___y_175_ = v___y_172_;
goto v___jp_173_;
}
else
{
lean_object* v___x_197_; 
v___x_197_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_struct_168_, v___y_170_, v___y_171_, v___y_172_);
if (lean_obj_tag(v___x_197_) == 0)
{
lean_object* v_a_198_; 
v_a_198_ = lean_ctor_get(v___x_197_, 1);
lean_inc(v_a_198_);
lean_dec_ref_known(v___x_197_, 2);
v___y_174_ = v___y_169_;
v___y_175_ = v_a_198_;
goto v___jp_173_;
}
else
{
lean_object* v_a_199_; lean_object* v_a_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_207_; 
lean_dec_ref(v___y_169_);
lean_dec_ref(v_struct_168_);
lean_dec(v_idx_167_);
lean_dec(v_structName_166_);
v_a_199_ = lean_ctor_get(v___x_197_, 0);
v_a_200_ = lean_ctor_get(v___x_197_, 1);
v_isSharedCheck_207_ = !lean_is_exclusive(v___x_197_);
if (v_isSharedCheck_207_ == 0)
{
v___x_202_ = v___x_197_;
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_a_200_);
lean_inc(v_a_199_);
lean_dec(v___x_197_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_205_; 
if (v_isShared_203_ == 0)
{
v___x_205_ = v___x_202_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v_a_199_);
lean_ctor_set(v_reuseFailAlloc_206_, 1, v_a_200_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
}
}
v___jp_173_:
{
lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_176_ = l_Lean_Expr_proj___override(v_structName_166_, v_idx_167_, v_struct_168_);
v___x_177_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_176_, v___y_175_);
if (lean_obj_tag(v___x_177_) == 0)
{
lean_object* v_a_178_; lean_object* v_a_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_187_; 
v_a_178_ = lean_ctor_get(v___x_177_, 0);
v_a_179_ = lean_ctor_get(v___x_177_, 1);
v_isSharedCheck_187_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_187_ == 0)
{
v___x_181_ = v___x_177_;
v_isShared_182_ = v_isSharedCheck_187_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_a_179_);
lean_inc(v_a_178_);
lean_dec(v___x_177_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_187_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_183_; lean_object* v___x_185_; 
v___x_183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_183_, 0, v_a_178_);
lean_ctor_set(v___x_183_, 1, v___y_174_);
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 0, v___x_183_);
v___x_185_ = v___x_181_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v___x_183_);
lean_ctor_set(v_reuseFailAlloc_186_, 1, v_a_179_);
v___x_185_ = v_reuseFailAlloc_186_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
return v___x_185_;
}
}
}
else
{
lean_object* v_a_188_; lean_object* v_a_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_196_; 
lean_dec_ref(v___y_174_);
v_a_188_ = lean_ctor_get(v___x_177_, 0);
v_a_189_ = lean_ctor_get(v___x_177_, 1);
v_isSharedCheck_196_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_196_ == 0)
{
v___x_191_ = v___x_177_;
v_isShared_192_ = v_isSharedCheck_196_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_a_189_);
lean_inc(v_a_188_);
lean_dec(v___x_177_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_196_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_194_; 
if (v_isShared_192_ == 0)
{
v___x_194_ = v___x_191_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v_a_188_);
lean_ctor_set(v_reuseFailAlloc_195_, 1, v_a_189_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_structName_166_ = stack[0].m_obj;
lean_object* v_idx_167_ = stack[1].m_obj;
lean_object* v_struct_168_ = stack[2].m_obj;
lean_object* v___y_169_ = stack[3].m_obj;
uint8_t v___y_170_ = stack[4].m_num;
lean_object* v___y_171_ = stack[5].m_obj;
lean_object* v___y_172_ = stack[6].m_obj;
lean_object* v_res_208_;
v_res_208_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__7(v_structName_166_, v_idx_167_, v_struct_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_);
stack->m_obj
 = v_res_208_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__7___boxed(lean_object* v_structName_209_, lean_object* v_idx_210_, lean_object* v_struct_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_){
_start:
{
uint8_t v___y_26333__boxed_216_; lean_object* v_res_217_; 
v___y_26333__boxed_216_ = lean_unbox(v___y_213_);
v_res_217_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__7(v_structName_209_, v_idx_210_, v_struct_211_, v___y_212_, v___y_26333__boxed_216_, v___y_214_, v___y_215_);
lean_dec_ref(v___y_214_);
return v_res_217_;
}
}
lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8(lean_object* v_msg_225_, lean_object* v___y_226_, uint8_t v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_){
_start:
{
lean_object* v___f_230_; lean_object* v___f_231_; lean_object* v___f_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___f_242_; lean_object* v___f_243_; lean_object* v___f_244_; lean_object* v___f_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_25477__overap_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v___f_230_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8___closed__0));
v___f_231_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8___closed__1));
v___f_232_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8___closed__2));
v___x_233_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8___closed__3));
v___x_234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_234_, 0, v___x_233_);
lean_ctor_set(v___x_234_, 1, v___f_230_);
v___x_235_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8___closed__4));
v___x_236_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8___closed__5));
v___x_237_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_237_, 0, v___x_234_);
lean_ctor_set(v___x_237_, 1, v___x_235_);
lean_ctor_set(v___x_237_, 2, v___f_231_);
lean_ctor_set(v___x_237_, 3, v___f_232_);
lean_ctor_set(v___x_237_, 4, v___x_236_);
v___x_238_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8___closed__6));
v___x_239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_239_, 0, v___x_237_);
lean_ctor_set(v___x_239_, 1, v___x_238_);
v___x_240_ = l_ReaderT_instMonad___redArg(v___x_239_);
v___x_241_ = l_ReaderT_instMonad___redArg(v___x_240_);
lean_inc_ref_n(v___x_241_, 6);
v___f_242_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_242_, 0, v___x_241_);
v___f_243_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_243_, 0, v___x_241_);
v___f_244_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_244_, 0, v___x_241_);
v___f_245_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_245_, 0, v___x_241_);
v___x_246_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_246_, 0, lean_box(0));
lean_closure_set(v___x_246_, 1, lean_box(0));
lean_closure_set(v___x_246_, 2, v___x_241_);
v___x_247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
lean_ctor_set(v___x_247_, 1, v___f_242_);
v___x_248_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_248_, 0, lean_box(0));
lean_closure_set(v___x_248_, 1, lean_box(0));
lean_closure_set(v___x_248_, 2, v___x_241_);
v___x_249_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_249_, 0, v___x_247_);
lean_ctor_set(v___x_249_, 1, v___x_248_);
lean_ctor_set(v___x_249_, 2, v___f_243_);
lean_ctor_set(v___x_249_, 3, v___f_244_);
lean_ctor_set(v___x_249_, 4, v___f_245_);
v___x_250_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_250_, 0, lean_box(0));
lean_closure_set(v___x_250_, 1, lean_box(0));
lean_closure_set(v___x_250_, 2, v___x_241_);
v___x_251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_251_, 0, v___x_249_);
lean_ctor_set(v___x_251_, 1, v___x_250_);
v___x_252_ = l_Lean_instInhabitedExpr;
v___x_253_ = l_instInhabitedOfMonad___redArg(v___x_251_, v___x_252_);
v___x_25477__overap_254_ = lean_panic_fn_borrowed(v___x_253_, v_msg_225_);
lean_dec(v___x_253_);
v___x_255_ = lean_box(v___y_227_);
lean_inc_ref(v___y_228_);
v___x_256_ = lean_apply_4(v___x_25477__overap_254_, v___y_226_, v___x_255_, v___y_228_, v___y_229_);
return v___x_256_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_225_ = stack[0].m_obj;
lean_object* v___y_226_ = stack[1].m_obj;
uint8_t v___y_227_ = stack[2].m_num;
lean_object* v___y_228_ = stack[3].m_obj;
lean_object* v___y_229_ = stack[4].m_obj;
lean_object* v_res_257_;
v_res_257_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8(v_msg_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_);
stack->m_obj
 = v_res_257_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8___boxed(lean_object* v_msg_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_){
_start:
{
uint8_t v___y_26473__boxed_263_; lean_object* v_res_264_; 
v___y_26473__boxed_263_ = lean_unbox(v___y_260_);
v_res_264_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8(v_msg_258_, v___y_259_, v___y_26473__boxed_263_, v___y_261_, v___y_262_);
lean_dec_ref(v___y_261_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11___redArg(lean_object* v_a_265_, lean_object* v_x_266_){
_start:
{
if (lean_obj_tag(v_x_266_) == 0)
{
lean_object* v___x_267_; 
v___x_267_ = lean_box(0);
return v___x_267_;
}
else
{
lean_object* v_key_268_; lean_object* v_value_269_; lean_object* v_tail_270_; lean_object* v_fst_271_; lean_object* v_snd_272_; lean_object* v_fst_273_; lean_object* v_snd_274_; size_t v___x_275_; size_t v___x_276_; uint8_t v___x_277_; 
v_key_268_ = lean_ctor_get(v_x_266_, 0);
v_value_269_ = lean_ctor_get(v_x_266_, 1);
v_tail_270_ = lean_ctor_get(v_x_266_, 2);
v_fst_271_ = lean_ctor_get(v_key_268_, 0);
v_snd_272_ = lean_ctor_get(v_key_268_, 1);
v_fst_273_ = lean_ctor_get(v_a_265_, 0);
v_snd_274_ = lean_ctor_get(v_a_265_, 1);
v___x_275_ = lean_ptr_addr(v_fst_271_);
v___x_276_ = lean_ptr_addr(v_fst_273_);
v___x_277_ = lean_usize_dec_eq(v___x_275_, v___x_276_);
if (v___x_277_ == 0)
{
v_x_266_ = v_tail_270_;
goto _start;
}
else
{
uint8_t v___x_279_; 
v___x_279_ = lean_nat_dec_eq(v_snd_272_, v_snd_274_);
if (v___x_279_ == 0)
{
v_x_266_ = v_tail_270_;
goto _start;
}
else
{
lean_object* v___x_281_; 
lean_inc(v_value_269_);
v___x_281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_281_, 0, v_value_269_);
return v___x_281_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11___redArg___boxed(lean_object* v_a_282_, lean_object* v_x_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11___redArg(v_a_282_, v_x_283_);
lean_dec(v_x_283_);
lean_dec_ref(v_a_282_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3___redArg(lean_object* v_m_285_, lean_object* v_a_286_){
_start:
{
lean_object* v_buckets_287_; lean_object* v_fst_288_; lean_object* v_snd_289_; lean_object* v___x_290_; size_t v___x_291_; size_t v___x_292_; size_t v___x_293_; uint64_t v___x_294_; uint64_t v___x_295_; uint64_t v___x_296_; uint64_t v___x_297_; uint64_t v___x_298_; uint64_t v_fold_299_; uint64_t v___x_300_; uint64_t v___x_301_; uint64_t v___x_302_; size_t v___x_303_; size_t v___x_304_; size_t v___x_305_; size_t v___x_306_; size_t v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v_buckets_287_ = lean_ctor_get(v_m_285_, 1);
v_fst_288_ = lean_ctor_get(v_a_286_, 0);
v_snd_289_ = lean_ctor_get(v_a_286_, 1);
v___x_290_ = lean_array_get_size(v_buckets_287_);
v___x_291_ = lean_ptr_addr(v_fst_288_);
v___x_292_ = ((size_t)3ULL);
v___x_293_ = lean_usize_shift_right(v___x_291_, v___x_292_);
v___x_294_ = lean_usize_to_uint64(v___x_293_);
v___x_295_ = lean_uint64_of_nat(v_snd_289_);
v___x_296_ = lean_uint64_mix_hash(v___x_294_, v___x_295_);
v___x_297_ = 32ULL;
v___x_298_ = lean_uint64_shift_right(v___x_296_, v___x_297_);
v_fold_299_ = lean_uint64_xor(v___x_296_, v___x_298_);
v___x_300_ = 16ULL;
v___x_301_ = lean_uint64_shift_right(v_fold_299_, v___x_300_);
v___x_302_ = lean_uint64_xor(v_fold_299_, v___x_301_);
v___x_303_ = lean_uint64_to_usize(v___x_302_);
v___x_304_ = lean_usize_of_nat(v___x_290_);
v___x_305_ = ((size_t)1ULL);
v___x_306_ = lean_usize_sub(v___x_304_, v___x_305_);
v___x_307_ = lean_usize_land(v___x_303_, v___x_306_);
v___x_308_ = lean_array_uget_borrowed(v_buckets_287_, v___x_307_);
v___x_309_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11___redArg(v_a_286_, v___x_308_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_m_310_, lean_object* v_a_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3___redArg(v_m_310_, v_a_311_);
lean_dec_ref(v_a_311_);
lean_dec_ref(v_m_310_);
return v_res_312_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__3(lean_object* v_x_313_, uint8_t v_bi_314_, lean_object* v_t_315_, lean_object* v_b_316_, lean_object* v___y_317_, uint8_t v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_){
_start:
{
lean_object* v___y_322_; lean_object* v___y_323_; 
if (v___y_318_ == 0)
{
v___y_322_ = v___y_317_;
v___y_323_ = v___y_320_;
goto v___jp_321_;
}
else
{
lean_object* v___x_345_; 
v___x_345_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_315_, v___y_318_, v___y_319_, v___y_320_);
if (lean_obj_tag(v___x_345_) == 0)
{
lean_object* v_a_346_; lean_object* v___x_347_; 
v_a_346_ = lean_ctor_get(v___x_345_, 1);
lean_inc(v_a_346_);
lean_dec_ref_known(v___x_345_, 2);
v___x_347_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_316_, v___y_318_, v___y_319_, v_a_346_);
if (lean_obj_tag(v___x_347_) == 0)
{
lean_object* v_a_348_; 
v_a_348_ = lean_ctor_get(v___x_347_, 1);
lean_inc(v_a_348_);
lean_dec_ref_known(v___x_347_, 2);
v___y_322_ = v___y_317_;
v___y_323_ = v_a_348_;
goto v___jp_321_;
}
else
{
lean_object* v_a_349_; lean_object* v_a_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_357_; 
lean_dec_ref(v___y_317_);
lean_dec_ref(v_b_316_);
lean_dec_ref(v_t_315_);
lean_dec(v_x_313_);
v_a_349_ = lean_ctor_get(v___x_347_, 0);
v_a_350_ = lean_ctor_get(v___x_347_, 1);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_357_ == 0)
{
v___x_352_ = v___x_347_;
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_a_350_);
lean_inc(v_a_349_);
lean_dec(v___x_347_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_355_; 
if (v_isShared_353_ == 0)
{
v___x_355_ = v___x_352_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_a_349_);
lean_ctor_set(v_reuseFailAlloc_356_, 1, v_a_350_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
}
}
else
{
lean_object* v_a_358_; lean_object* v_a_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_366_; 
lean_dec_ref(v___y_317_);
lean_dec_ref(v_b_316_);
lean_dec_ref(v_t_315_);
lean_dec(v_x_313_);
v_a_358_ = lean_ctor_get(v___x_345_, 0);
v_a_359_ = lean_ctor_get(v___x_345_, 1);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_345_);
if (v_isSharedCheck_366_ == 0)
{
v___x_361_ = v___x_345_;
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_a_359_);
lean_inc(v_a_358_);
lean_dec(v___x_345_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_364_; 
if (v_isShared_362_ == 0)
{
v___x_364_ = v___x_361_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_a_358_);
lean_ctor_set(v_reuseFailAlloc_365_, 1, v_a_359_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
}
v___jp_321_:
{
lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_324_ = l_Lean_Expr_lam___override(v_x_313_, v_t_315_, v_b_316_, v_bi_314_);
v___x_325_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_324_, v___y_323_);
if (lean_obj_tag(v___x_325_) == 0)
{
lean_object* v_a_326_; lean_object* v_a_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_335_; 
v_a_326_ = lean_ctor_get(v___x_325_, 0);
v_a_327_ = lean_ctor_get(v___x_325_, 1);
v_isSharedCheck_335_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_335_ == 0)
{
v___x_329_ = v___x_325_;
v_isShared_330_ = v_isSharedCheck_335_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_a_327_);
lean_inc(v_a_326_);
lean_dec(v___x_325_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_335_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_331_; lean_object* v___x_333_; 
v___x_331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_331_, 0, v_a_326_);
lean_ctor_set(v___x_331_, 1, v___y_322_);
if (v_isShared_330_ == 0)
{
lean_ctor_set(v___x_329_, 0, v___x_331_);
v___x_333_ = v___x_329_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v___x_331_);
lean_ctor_set(v_reuseFailAlloc_334_, 1, v_a_327_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
else
{
lean_object* v_a_336_; lean_object* v_a_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_344_; 
lean_dec_ref(v___y_322_);
v_a_336_ = lean_ctor_get(v___x_325_, 0);
v_a_337_ = lean_ctor_get(v___x_325_, 1);
v_isSharedCheck_344_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_344_ == 0)
{
v___x_339_ = v___x_325_;
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_a_337_);
lean_inc(v_a_336_);
lean_dec(v___x_325_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_342_; 
if (v_isShared_340_ == 0)
{
v___x_342_ = v___x_339_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v_a_336_);
lean_ctor_set(v_reuseFailAlloc_343_, 1, v_a_337_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_313_ = stack[0].m_obj;
uint8_t v_bi_314_ = stack[1].m_num;
lean_object* v_t_315_ = stack[2].m_obj;
lean_object* v_b_316_ = stack[3].m_obj;
lean_object* v___y_317_ = stack[4].m_obj;
uint8_t v___y_318_ = stack[5].m_num;
lean_object* v___y_319_ = stack[6].m_obj;
lean_object* v___y_320_ = stack[7].m_obj;
lean_object* v_res_367_;
v_res_367_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__3(v_x_313_, v_bi_314_, v_t_315_, v_b_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_);
stack->m_obj
 = v_res_367_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__3___boxed(lean_object* v_x_368_, lean_object* v_bi_369_, lean_object* v_t_370_, lean_object* v_b_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_){
_start:
{
uint8_t v_bi_boxed_376_; uint8_t v___y_26701__boxed_377_; lean_object* v_res_378_; 
v_bi_boxed_376_ = lean_unbox(v_bi_369_);
v___y_26701__boxed_377_ = lean_unbox(v___y_373_);
v_res_378_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__3(v_x_368_, v_bi_boxed_376_, v_t_370_, v_b_371_, v___y_372_, v___y_26701__boxed_377_, v___y_374_, v___y_375_);
lean_dec_ref(v___y_374_);
return v_res_378_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__5(lean_object* v_x_379_, lean_object* v_t_380_, lean_object* v_v_381_, lean_object* v_b_382_, uint8_t v_nondep_383_, lean_object* v___y_384_, uint8_t v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
lean_object* v___y_389_; lean_object* v___y_390_; 
if (v___y_385_ == 0)
{
v___y_389_ = v___y_384_;
v___y_390_ = v___y_387_;
goto v___jp_388_;
}
else
{
lean_object* v___x_412_; 
v___x_412_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_380_, v___y_385_, v___y_386_, v___y_387_);
if (lean_obj_tag(v___x_412_) == 0)
{
lean_object* v_a_413_; lean_object* v___x_414_; 
v_a_413_ = lean_ctor_get(v___x_412_, 1);
lean_inc(v_a_413_);
lean_dec_ref_known(v___x_412_, 2);
v___x_414_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_v_381_, v___y_385_, v___y_386_, v_a_413_);
if (lean_obj_tag(v___x_414_) == 0)
{
lean_object* v_a_415_; lean_object* v___x_416_; 
v_a_415_ = lean_ctor_get(v___x_414_, 1);
lean_inc(v_a_415_);
lean_dec_ref_known(v___x_414_, 2);
v___x_416_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_382_, v___y_385_, v___y_386_, v_a_415_);
if (lean_obj_tag(v___x_416_) == 0)
{
lean_object* v_a_417_; 
v_a_417_ = lean_ctor_get(v___x_416_, 1);
lean_inc(v_a_417_);
lean_dec_ref_known(v___x_416_, 2);
v___y_389_ = v___y_384_;
v___y_390_ = v_a_417_;
goto v___jp_388_;
}
else
{
lean_object* v_a_418_; lean_object* v_a_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_426_; 
lean_dec_ref(v___y_384_);
lean_dec_ref(v_b_382_);
lean_dec_ref(v_v_381_);
lean_dec_ref(v_t_380_);
lean_dec(v_x_379_);
v_a_418_ = lean_ctor_get(v___x_416_, 0);
v_a_419_ = lean_ctor_get(v___x_416_, 1);
v_isSharedCheck_426_ = !lean_is_exclusive(v___x_416_);
if (v_isSharedCheck_426_ == 0)
{
v___x_421_ = v___x_416_;
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_a_419_);
lean_inc(v_a_418_);
lean_dec(v___x_416_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_424_; 
if (v_isShared_422_ == 0)
{
v___x_424_ = v___x_421_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_a_418_);
lean_ctor_set(v_reuseFailAlloc_425_, 1, v_a_419_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
}
}
else
{
lean_object* v_a_427_; lean_object* v_a_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_435_; 
lean_dec_ref(v___y_384_);
lean_dec_ref(v_b_382_);
lean_dec_ref(v_v_381_);
lean_dec_ref(v_t_380_);
lean_dec(v_x_379_);
v_a_427_ = lean_ctor_get(v___x_414_, 0);
v_a_428_ = lean_ctor_get(v___x_414_, 1);
v_isSharedCheck_435_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_435_ == 0)
{
v___x_430_ = v___x_414_;
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_a_428_);
lean_inc(v_a_427_);
lean_dec(v___x_414_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_433_; 
if (v_isShared_431_ == 0)
{
v___x_433_ = v___x_430_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_a_427_);
lean_ctor_set(v_reuseFailAlloc_434_, 1, v_a_428_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
}
}
else
{
lean_object* v_a_436_; lean_object* v_a_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_444_; 
lean_dec_ref(v___y_384_);
lean_dec_ref(v_b_382_);
lean_dec_ref(v_v_381_);
lean_dec_ref(v_t_380_);
lean_dec(v_x_379_);
v_a_436_ = lean_ctor_get(v___x_412_, 0);
v_a_437_ = lean_ctor_get(v___x_412_, 1);
v_isSharedCheck_444_ = !lean_is_exclusive(v___x_412_);
if (v_isSharedCheck_444_ == 0)
{
v___x_439_ = v___x_412_;
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_a_437_);
lean_inc(v_a_436_);
lean_dec(v___x_412_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_442_; 
if (v_isShared_440_ == 0)
{
v___x_442_ = v___x_439_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_a_436_);
lean_ctor_set(v_reuseFailAlloc_443_, 1, v_a_437_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
}
v___jp_388_:
{
lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_391_ = l_Lean_Expr_letE___override(v_x_379_, v_t_380_, v_v_381_, v_b_382_, v_nondep_383_);
v___x_392_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_391_, v___y_390_);
if (lean_obj_tag(v___x_392_) == 0)
{
lean_object* v_a_393_; lean_object* v_a_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_402_; 
v_a_393_ = lean_ctor_get(v___x_392_, 0);
v_a_394_ = lean_ctor_get(v___x_392_, 1);
v_isSharedCheck_402_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_402_ == 0)
{
v___x_396_ = v___x_392_;
v_isShared_397_ = v_isSharedCheck_402_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_a_394_);
lean_inc(v_a_393_);
lean_dec(v___x_392_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_402_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_398_; lean_object* v___x_400_; 
v___x_398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_398_, 0, v_a_393_);
lean_ctor_set(v___x_398_, 1, v___y_389_);
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 0, v___x_398_);
v___x_400_ = v___x_396_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v___x_398_);
lean_ctor_set(v_reuseFailAlloc_401_, 1, v_a_394_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
}
}
}
else
{
lean_object* v_a_403_; lean_object* v_a_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_411_; 
lean_dec_ref(v___y_389_);
v_a_403_ = lean_ctor_get(v___x_392_, 0);
v_a_404_ = lean_ctor_get(v___x_392_, 1);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_411_ == 0)
{
v___x_406_ = v___x_392_;
v_isShared_407_ = v_isSharedCheck_411_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_a_404_);
lean_inc(v_a_403_);
lean_dec(v___x_392_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_411_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_409_; 
if (v_isShared_407_ == 0)
{
v___x_409_ = v___x_406_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v_a_403_);
lean_ctor_set(v_reuseFailAlloc_410_, 1, v_a_404_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_379_ = stack[0].m_obj;
lean_object* v_t_380_ = stack[1].m_obj;
lean_object* v_v_381_ = stack[2].m_obj;
lean_object* v_b_382_ = stack[3].m_obj;
uint8_t v_nondep_383_ = stack[4].m_num;
lean_object* v___y_384_ = stack[5].m_obj;
uint8_t v___y_385_ = stack[6].m_num;
lean_object* v___y_386_ = stack[7].m_obj;
lean_object* v___y_387_ = stack[8].m_obj;
lean_object* v_res_445_;
v_res_445_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__5(v_x_379_, v_t_380_, v_v_381_, v_b_382_, v_nondep_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_);
stack->m_obj
 = v_res_445_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__5___boxed(lean_object* v_x_446_, lean_object* v_t_447_, lean_object* v_v_448_, lean_object* v_b_449_, lean_object* v_nondep_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_){
_start:
{
uint8_t v_nondep_boxed_455_; uint8_t v___y_26861__boxed_456_; lean_object* v_res_457_; 
v_nondep_boxed_455_ = lean_unbox(v_nondep_450_);
v___y_26861__boxed_456_ = lean_unbox(v___y_452_);
v_res_457_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__5(v_x_446_, v_t_447_, v_v_448_, v_b_449_, v_nondep_boxed_455_, v___y_451_, v___y_26861__boxed_456_, v___y_453_, v___y_454_);
lean_dec_ref(v___y_453_);
return v_res_457_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__6(lean_object* v_d_458_, lean_object* v_e_459_, lean_object* v___y_460_, uint8_t v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_){
_start:
{
lean_object* v___y_465_; lean_object* v___y_466_; 
if (v___y_461_ == 0)
{
v___y_465_ = v___y_460_;
v___y_466_ = v___y_463_;
goto v___jp_464_;
}
else
{
lean_object* v___x_488_; 
v___x_488_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_e_459_, v___y_461_, v___y_462_, v___y_463_);
if (lean_obj_tag(v___x_488_) == 0)
{
lean_object* v_a_489_; 
v_a_489_ = lean_ctor_get(v___x_488_, 1);
lean_inc(v_a_489_);
lean_dec_ref_known(v___x_488_, 2);
v___y_465_ = v___y_460_;
v___y_466_ = v_a_489_;
goto v___jp_464_;
}
else
{
lean_object* v_a_490_; lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_498_; 
lean_dec_ref(v___y_460_);
lean_dec_ref(v_e_459_);
lean_dec(v_d_458_);
v_a_490_ = lean_ctor_get(v___x_488_, 0);
v_a_491_ = lean_ctor_get(v___x_488_, 1);
v_isSharedCheck_498_ = !lean_is_exclusive(v___x_488_);
if (v_isSharedCheck_498_ == 0)
{
v___x_493_ = v___x_488_;
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_a_491_);
lean_inc(v_a_490_);
lean_dec(v___x_488_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_496_; 
if (v_isShared_494_ == 0)
{
v___x_496_ = v___x_493_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_a_490_);
lean_ctor_set(v_reuseFailAlloc_497_, 1, v_a_491_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
}
v___jp_464_:
{
lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_467_ = l_Lean_Expr_mdata___override(v_d_458_, v_e_459_);
v___x_468_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_467_, v___y_466_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_object* v_a_469_; lean_object* v_a_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_478_; 
v_a_469_ = lean_ctor_get(v___x_468_, 0);
v_a_470_ = lean_ctor_get(v___x_468_, 1);
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_478_ == 0)
{
v___x_472_ = v___x_468_;
v_isShared_473_ = v_isSharedCheck_478_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_a_470_);
lean_inc(v_a_469_);
lean_dec(v___x_468_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_478_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_474_; lean_object* v___x_476_; 
v___x_474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_474_, 0, v_a_469_);
lean_ctor_set(v___x_474_, 1, v___y_465_);
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 0, v___x_474_);
v___x_476_ = v___x_472_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v___x_474_);
lean_ctor_set(v_reuseFailAlloc_477_, 1, v_a_470_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
else
{
lean_object* v_a_479_; lean_object* v_a_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_487_; 
lean_dec_ref(v___y_465_);
v_a_479_ = lean_ctor_get(v___x_468_, 0);
v_a_480_ = lean_ctor_get(v___x_468_, 1);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_487_ == 0)
{
v___x_482_ = v___x_468_;
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_a_480_);
lean_inc(v_a_479_);
lean_dec(v___x_468_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_485_; 
if (v_isShared_483_ == 0)
{
v___x_485_ = v___x_482_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_a_479_);
lean_ctor_set(v_reuseFailAlloc_486_, 1, v_a_480_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_d_458_ = stack[0].m_obj;
lean_object* v_e_459_ = stack[1].m_obj;
lean_object* v___y_460_ = stack[2].m_obj;
uint8_t v___y_461_ = stack[3].m_num;
lean_object* v___y_462_ = stack[4].m_obj;
lean_object* v___y_463_ = stack[5].m_obj;
lean_object* v_res_499_;
v_res_499_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__6(v_d_458_, v_e_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_);
stack->m_obj
 = v_res_499_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__6___boxed(lean_object* v_d_500_, lean_object* v_e_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_){
_start:
{
uint8_t v___y_27055__boxed_506_; lean_object* v_res_507_; 
v___y_27055__boxed_506_ = lean_unbox(v___y_503_);
v_res_507_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__6(v_d_500_, v_e_501_, v___y_502_, v___y_27055__boxed_506_, v___y_504_, v___y_505_);
lean_dec_ref(v___y_504_);
return v_res_507_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__3(void){
_start:
{
lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_511_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__2));
v___x_512_ = lean_unsigned_to_nat(67u);
v___x_513_ = lean_unsigned_to_nat(35u);
v___x_514_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__1));
v___x_515_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__0));
v___x_516_ = l_mkPanicMessageWithDecl(v___x_515_, v___x_514_, v___x_513_, v___x_512_, v___x_511_);
return v___x_516_;
}
}
lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1(lean_object* v_beginIdx_517_, lean_object* v_n_518_, lean_object* v_subst_519_, lean_object* v_e_520_, lean_object* v_offset_521_, lean_object* v_a_522_, uint8_t v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_){
_start:
{
switch(lean_obj_tag(v_e_520_))
{
case 5:
{
lean_object* v_fn_526_; lean_object* v_arg_527_; lean_object* v___x_528_; 
v_fn_526_ = lean_ctor_get(v_e_520_, 0);
v_arg_527_ = lean_ctor_get(v_e_520_, 1);
lean_inc(v_offset_521_);
lean_inc_ref(v_fn_526_);
v___x_528_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(v_beginIdx_517_, v_n_518_, v_subst_519_, v_fn_526_, v_offset_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_);
if (lean_obj_tag(v___x_528_) == 0)
{
lean_object* v_a_529_; lean_object* v_a_530_; lean_object* v_fst_531_; lean_object* v_snd_532_; lean_object* v___x_533_; 
v_a_529_ = lean_ctor_get(v___x_528_, 0);
lean_inc(v_a_529_);
v_a_530_ = lean_ctor_get(v___x_528_, 1);
lean_inc(v_a_530_);
lean_dec_ref_known(v___x_528_, 2);
v_fst_531_ = lean_ctor_get(v_a_529_, 0);
lean_inc(v_fst_531_);
v_snd_532_ = lean_ctor_get(v_a_529_, 1);
lean_inc(v_snd_532_);
lean_dec(v_a_529_);
lean_inc_ref(v_arg_527_);
v___x_533_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(v_beginIdx_517_, v_n_518_, v_subst_519_, v_arg_527_, v_offset_521_, v_snd_532_, v_a_523_, v_a_524_, v_a_530_);
if (lean_obj_tag(v___x_533_) == 0)
{
lean_object* v_a_534_; lean_object* v_a_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_559_; 
v_a_534_ = lean_ctor_get(v___x_533_, 0);
v_a_535_ = lean_ctor_get(v___x_533_, 1);
v_isSharedCheck_559_ = !lean_is_exclusive(v___x_533_);
if (v_isSharedCheck_559_ == 0)
{
v___x_537_ = v___x_533_;
v_isShared_538_ = v_isSharedCheck_559_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_a_535_);
lean_inc(v_a_534_);
lean_dec(v___x_533_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_559_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v_fst_539_; lean_object* v_snd_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_558_; 
v_fst_539_ = lean_ctor_get(v_a_534_, 0);
v_snd_540_ = lean_ctor_get(v_a_534_, 1);
v_isSharedCheck_558_ = !lean_is_exclusive(v_a_534_);
if (v_isSharedCheck_558_ == 0)
{
v___x_542_ = v_a_534_;
v_isShared_543_ = v_isSharedCheck_558_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_snd_540_);
lean_inc(v_fst_539_);
lean_dec(v_a_534_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_558_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
size_t v___x_544_; size_t v___x_545_; uint8_t v___x_546_; 
v___x_544_ = lean_ptr_addr(v_fn_526_);
v___x_545_ = lean_ptr_addr(v_fst_531_);
v___x_546_ = lean_usize_dec_eq(v___x_544_, v___x_545_);
if (v___x_546_ == 0)
{
lean_object* v___x_547_; 
lean_del_object(v___x_542_);
lean_del_object(v___x_537_);
lean_dec_ref_known(v_e_520_, 2);
v___x_547_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__2(v_fst_531_, v_fst_539_, v_snd_540_, v_a_523_, v_a_524_, v_a_535_);
return v___x_547_;
}
else
{
size_t v___x_548_; size_t v___x_549_; uint8_t v___x_550_; 
v___x_548_ = lean_ptr_addr(v_arg_527_);
v___x_549_ = lean_ptr_addr(v_fst_539_);
v___x_550_ = lean_usize_dec_eq(v___x_548_, v___x_549_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; 
lean_del_object(v___x_542_);
lean_del_object(v___x_537_);
lean_dec_ref_known(v_e_520_, 2);
v___x_551_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__2(v_fst_531_, v_fst_539_, v_snd_540_, v_a_523_, v_a_524_, v_a_535_);
return v___x_551_;
}
else
{
lean_object* v___x_553_; 
lean_dec(v_fst_539_);
lean_dec(v_fst_531_);
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 0, v_e_520_);
v___x_553_ = v___x_542_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v_e_520_);
lean_ctor_set(v_reuseFailAlloc_557_, 1, v_snd_540_);
v___x_553_ = v_reuseFailAlloc_557_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
lean_object* v___x_555_; 
if (v_isShared_538_ == 0)
{
lean_ctor_set(v___x_537_, 0, v___x_553_);
v___x_555_ = v___x_537_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v___x_553_);
lean_ctor_set(v_reuseFailAlloc_556_, 1, v_a_535_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_531_);
lean_dec_ref_known(v_e_520_, 2);
return v___x_533_;
}
}
else
{
lean_dec_ref_known(v_e_520_, 2);
lean_dec(v_offset_521_);
return v___x_528_;
}
}
case 6:
{
lean_object* v_binderName_560_; lean_object* v_binderType_561_; lean_object* v_body_562_; uint8_t v_binderInfo_563_; lean_object* v___x_564_; 
v_binderName_560_ = lean_ctor_get(v_e_520_, 0);
v_binderType_561_ = lean_ctor_get(v_e_520_, 1);
v_body_562_ = lean_ctor_get(v_e_520_, 2);
v_binderInfo_563_ = lean_ctor_get_uint8(v_e_520_, sizeof(void*)*3 + 8);
lean_inc(v_offset_521_);
lean_inc_ref(v_binderType_561_);
v___x_564_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(v_beginIdx_517_, v_n_518_, v_subst_519_, v_binderType_561_, v_offset_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_);
if (lean_obj_tag(v___x_564_) == 0)
{
lean_object* v_a_565_; lean_object* v_a_566_; lean_object* v_fst_567_; lean_object* v_snd_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v_a_565_ = lean_ctor_get(v___x_564_, 0);
lean_inc(v_a_565_);
v_a_566_ = lean_ctor_get(v___x_564_, 1);
lean_inc(v_a_566_);
lean_dec_ref_known(v___x_564_, 2);
v_fst_567_ = lean_ctor_get(v_a_565_, 0);
lean_inc(v_fst_567_);
v_snd_568_ = lean_ctor_get(v_a_565_, 1);
lean_inc(v_snd_568_);
lean_dec(v_a_565_);
v___x_569_ = lean_unsigned_to_nat(1u);
v___x_570_ = lean_nat_add(v_offset_521_, v___x_569_);
lean_dec(v_offset_521_);
lean_inc_ref(v_body_562_);
v___x_571_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(v_beginIdx_517_, v_n_518_, v_subst_519_, v_body_562_, v___x_570_, v_snd_568_, v_a_523_, v_a_524_, v_a_566_);
if (lean_obj_tag(v___x_571_) == 0)
{
lean_object* v_a_572_; lean_object* v_a_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_597_; 
v_a_572_ = lean_ctor_get(v___x_571_, 0);
v_a_573_ = lean_ctor_get(v___x_571_, 1);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_597_ == 0)
{
v___x_575_ = v___x_571_;
v_isShared_576_ = v_isSharedCheck_597_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_a_573_);
lean_inc(v_a_572_);
lean_dec(v___x_571_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_597_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v_fst_577_; lean_object* v_snd_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_596_; 
v_fst_577_ = lean_ctor_get(v_a_572_, 0);
v_snd_578_ = lean_ctor_get(v_a_572_, 1);
v_isSharedCheck_596_ = !lean_is_exclusive(v_a_572_);
if (v_isSharedCheck_596_ == 0)
{
v___x_580_ = v_a_572_;
v_isShared_581_ = v_isSharedCheck_596_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_snd_578_);
lean_inc(v_fst_577_);
lean_dec(v_a_572_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_596_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
size_t v___x_582_; size_t v___x_583_; uint8_t v___x_584_; 
v___x_582_ = lean_ptr_addr(v_binderType_561_);
v___x_583_ = lean_ptr_addr(v_fst_567_);
v___x_584_ = lean_usize_dec_eq(v___x_582_, v___x_583_);
if (v___x_584_ == 0)
{
lean_object* v___x_585_; 
lean_inc(v_binderName_560_);
lean_del_object(v___x_580_);
lean_del_object(v___x_575_);
lean_dec_ref_known(v_e_520_, 3);
v___x_585_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__3(v_binderName_560_, v_binderInfo_563_, v_fst_567_, v_fst_577_, v_snd_578_, v_a_523_, v_a_524_, v_a_573_);
return v___x_585_;
}
else
{
size_t v___x_586_; size_t v___x_587_; uint8_t v___x_588_; 
v___x_586_ = lean_ptr_addr(v_body_562_);
v___x_587_ = lean_ptr_addr(v_fst_577_);
v___x_588_ = lean_usize_dec_eq(v___x_586_, v___x_587_);
if (v___x_588_ == 0)
{
lean_object* v___x_589_; 
lean_inc(v_binderName_560_);
lean_del_object(v___x_580_);
lean_del_object(v___x_575_);
lean_dec_ref_known(v_e_520_, 3);
v___x_589_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__3(v_binderName_560_, v_binderInfo_563_, v_fst_567_, v_fst_577_, v_snd_578_, v_a_523_, v_a_524_, v_a_573_);
return v___x_589_;
}
else
{
lean_object* v___x_591_; 
lean_dec(v_fst_577_);
lean_dec(v_fst_567_);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 0, v_e_520_);
v___x_591_ = v___x_580_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_e_520_);
lean_ctor_set(v_reuseFailAlloc_595_, 1, v_snd_578_);
v___x_591_ = v_reuseFailAlloc_595_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
lean_object* v___x_593_; 
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 0, v___x_591_);
v___x_593_ = v___x_575_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_591_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v_a_573_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_567_);
lean_dec_ref_known(v_e_520_, 3);
return v___x_571_;
}
}
else
{
lean_dec_ref_known(v_e_520_, 3);
lean_dec(v_offset_521_);
return v___x_564_;
}
}
case 7:
{
lean_object* v_binderName_598_; lean_object* v_binderType_599_; lean_object* v_body_600_; uint8_t v_binderInfo_601_; lean_object* v___x_602_; 
v_binderName_598_ = lean_ctor_get(v_e_520_, 0);
v_binderType_599_ = lean_ctor_get(v_e_520_, 1);
v_body_600_ = lean_ctor_get(v_e_520_, 2);
v_binderInfo_601_ = lean_ctor_get_uint8(v_e_520_, sizeof(void*)*3 + 8);
lean_inc(v_offset_521_);
lean_inc_ref(v_binderType_599_);
v___x_602_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(v_beginIdx_517_, v_n_518_, v_subst_519_, v_binderType_599_, v_offset_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_);
if (lean_obj_tag(v___x_602_) == 0)
{
lean_object* v_a_603_; lean_object* v_a_604_; lean_object* v_fst_605_; lean_object* v_snd_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v_a_603_ = lean_ctor_get(v___x_602_, 0);
lean_inc(v_a_603_);
v_a_604_ = lean_ctor_get(v___x_602_, 1);
lean_inc(v_a_604_);
lean_dec_ref_known(v___x_602_, 2);
v_fst_605_ = lean_ctor_get(v_a_603_, 0);
lean_inc(v_fst_605_);
v_snd_606_ = lean_ctor_get(v_a_603_, 1);
lean_inc(v_snd_606_);
lean_dec(v_a_603_);
v___x_607_ = lean_unsigned_to_nat(1u);
v___x_608_ = lean_nat_add(v_offset_521_, v___x_607_);
lean_dec(v_offset_521_);
lean_inc_ref(v_body_600_);
v___x_609_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(v_beginIdx_517_, v_n_518_, v_subst_519_, v_body_600_, v___x_608_, v_snd_606_, v_a_523_, v_a_524_, v_a_604_);
if (lean_obj_tag(v___x_609_) == 0)
{
lean_object* v_a_610_; lean_object* v_a_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_635_; 
v_a_610_ = lean_ctor_get(v___x_609_, 0);
v_a_611_ = lean_ctor_get(v___x_609_, 1);
v_isSharedCheck_635_ = !lean_is_exclusive(v___x_609_);
if (v_isSharedCheck_635_ == 0)
{
v___x_613_ = v___x_609_;
v_isShared_614_ = v_isSharedCheck_635_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_a_611_);
lean_inc(v_a_610_);
lean_dec(v___x_609_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_635_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v_fst_615_; lean_object* v_snd_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_634_; 
v_fst_615_ = lean_ctor_get(v_a_610_, 0);
v_snd_616_ = lean_ctor_get(v_a_610_, 1);
v_isSharedCheck_634_ = !lean_is_exclusive(v_a_610_);
if (v_isSharedCheck_634_ == 0)
{
v___x_618_ = v_a_610_;
v_isShared_619_ = v_isSharedCheck_634_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_snd_616_);
lean_inc(v_fst_615_);
lean_dec(v_a_610_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_634_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
size_t v___x_620_; size_t v___x_621_; uint8_t v___x_622_; 
v___x_620_ = lean_ptr_addr(v_binderType_599_);
v___x_621_ = lean_ptr_addr(v_fst_605_);
v___x_622_ = lean_usize_dec_eq(v___x_620_, v___x_621_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; 
lean_inc(v_binderName_598_);
lean_del_object(v___x_618_);
lean_del_object(v___x_613_);
lean_dec_ref_known(v_e_520_, 3);
v___x_623_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__4(v_binderName_598_, v_binderInfo_601_, v_fst_605_, v_fst_615_, v_snd_616_, v_a_523_, v_a_524_, v_a_611_);
return v___x_623_;
}
else
{
size_t v___x_624_; size_t v___x_625_; uint8_t v___x_626_; 
v___x_624_ = lean_ptr_addr(v_body_600_);
v___x_625_ = lean_ptr_addr(v_fst_615_);
v___x_626_ = lean_usize_dec_eq(v___x_624_, v___x_625_);
if (v___x_626_ == 0)
{
lean_object* v___x_627_; 
lean_inc(v_binderName_598_);
lean_del_object(v___x_618_);
lean_del_object(v___x_613_);
lean_dec_ref_known(v_e_520_, 3);
v___x_627_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__4(v_binderName_598_, v_binderInfo_601_, v_fst_605_, v_fst_615_, v_snd_616_, v_a_523_, v_a_524_, v_a_611_);
return v___x_627_;
}
else
{
lean_object* v___x_629_; 
lean_dec(v_fst_615_);
lean_dec(v_fst_605_);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 0, v_e_520_);
v___x_629_ = v___x_618_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_e_520_);
lean_ctor_set(v_reuseFailAlloc_633_, 1, v_snd_616_);
v___x_629_ = v_reuseFailAlloc_633_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
lean_object* v___x_631_; 
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 0, v___x_629_);
v___x_631_ = v___x_613_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v___x_629_);
lean_ctor_set(v_reuseFailAlloc_632_, 1, v_a_611_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_605_);
lean_dec_ref_known(v_e_520_, 3);
return v___x_609_;
}
}
else
{
lean_dec_ref_known(v_e_520_, 3);
lean_dec(v_offset_521_);
return v___x_602_;
}
}
case 8:
{
lean_object* v_declName_636_; lean_object* v_type_637_; lean_object* v_value_638_; lean_object* v_body_639_; uint8_t v_nondep_640_; lean_object* v___x_641_; 
v_declName_636_ = lean_ctor_get(v_e_520_, 0);
v_type_637_ = lean_ctor_get(v_e_520_, 1);
v_value_638_ = lean_ctor_get(v_e_520_, 2);
v_body_639_ = lean_ctor_get(v_e_520_, 3);
v_nondep_640_ = lean_ctor_get_uint8(v_e_520_, sizeof(void*)*4 + 8);
lean_inc(v_offset_521_);
lean_inc_ref(v_type_637_);
v___x_641_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(v_beginIdx_517_, v_n_518_, v_subst_519_, v_type_637_, v_offset_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_);
if (lean_obj_tag(v___x_641_) == 0)
{
lean_object* v_a_642_; lean_object* v_a_643_; lean_object* v_fst_644_; lean_object* v_snd_645_; lean_object* v___x_646_; 
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
lean_inc(v_offset_521_);
lean_inc_ref(v_value_638_);
v___x_646_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(v_beginIdx_517_, v_n_518_, v_subst_519_, v_value_638_, v_offset_521_, v_snd_645_, v_a_523_, v_a_524_, v_a_643_);
if (lean_obj_tag(v___x_646_) == 0)
{
lean_object* v_a_647_; lean_object* v_a_648_; lean_object* v_fst_649_; lean_object* v_snd_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v_a_647_ = lean_ctor_get(v___x_646_, 0);
lean_inc(v_a_647_);
v_a_648_ = lean_ctor_get(v___x_646_, 1);
lean_inc(v_a_648_);
lean_dec_ref_known(v___x_646_, 2);
v_fst_649_ = lean_ctor_get(v_a_647_, 0);
lean_inc(v_fst_649_);
v_snd_650_ = lean_ctor_get(v_a_647_, 1);
lean_inc(v_snd_650_);
lean_dec(v_a_647_);
v___x_651_ = lean_unsigned_to_nat(1u);
v___x_652_ = lean_nat_add(v_offset_521_, v___x_651_);
lean_dec(v_offset_521_);
lean_inc_ref(v_body_639_);
v___x_653_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(v_beginIdx_517_, v_n_518_, v_subst_519_, v_body_639_, v___x_652_, v_snd_650_, v_a_523_, v_a_524_, v_a_648_);
if (lean_obj_tag(v___x_653_) == 0)
{
lean_object* v_a_654_; lean_object* v_a_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_683_; 
v_a_654_ = lean_ctor_get(v___x_653_, 0);
v_a_655_ = lean_ctor_get(v___x_653_, 1);
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_683_ == 0)
{
v___x_657_ = v___x_653_;
v_isShared_658_ = v_isSharedCheck_683_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_a_655_);
lean_inc(v_a_654_);
lean_dec(v___x_653_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_683_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v_fst_659_; lean_object* v_snd_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_682_; 
v_fst_659_ = lean_ctor_get(v_a_654_, 0);
v_snd_660_ = lean_ctor_get(v_a_654_, 1);
v_isSharedCheck_682_ = !lean_is_exclusive(v_a_654_);
if (v_isSharedCheck_682_ == 0)
{
v___x_662_ = v_a_654_;
v_isShared_663_ = v_isSharedCheck_682_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_snd_660_);
lean_inc(v_fst_659_);
lean_dec(v_a_654_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_682_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
size_t v___x_664_; size_t v___x_665_; uint8_t v___x_666_; 
v___x_664_ = lean_ptr_addr(v_type_637_);
v___x_665_ = lean_ptr_addr(v_fst_644_);
v___x_666_ = lean_usize_dec_eq(v___x_664_, v___x_665_);
if (v___x_666_ == 0)
{
lean_object* v___x_667_; 
lean_inc(v_declName_636_);
lean_del_object(v___x_662_);
lean_del_object(v___x_657_);
lean_dec_ref_known(v_e_520_, 4);
v___x_667_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__5(v_declName_636_, v_fst_644_, v_fst_649_, v_fst_659_, v_nondep_640_, v_snd_660_, v_a_523_, v_a_524_, v_a_655_);
return v___x_667_;
}
else
{
size_t v___x_668_; size_t v___x_669_; uint8_t v___x_670_; 
v___x_668_ = lean_ptr_addr(v_value_638_);
v___x_669_ = lean_ptr_addr(v_fst_649_);
v___x_670_ = lean_usize_dec_eq(v___x_668_, v___x_669_);
if (v___x_670_ == 0)
{
lean_object* v___x_671_; 
lean_inc(v_declName_636_);
lean_del_object(v___x_662_);
lean_del_object(v___x_657_);
lean_dec_ref_known(v_e_520_, 4);
v___x_671_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__5(v_declName_636_, v_fst_644_, v_fst_649_, v_fst_659_, v_nondep_640_, v_snd_660_, v_a_523_, v_a_524_, v_a_655_);
return v___x_671_;
}
else
{
size_t v___x_672_; size_t v___x_673_; uint8_t v___x_674_; 
v___x_672_ = lean_ptr_addr(v_body_639_);
v___x_673_ = lean_ptr_addr(v_fst_659_);
v___x_674_ = lean_usize_dec_eq(v___x_672_, v___x_673_);
if (v___x_674_ == 0)
{
lean_object* v___x_675_; 
lean_inc(v_declName_636_);
lean_del_object(v___x_662_);
lean_del_object(v___x_657_);
lean_dec_ref_known(v_e_520_, 4);
v___x_675_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__5(v_declName_636_, v_fst_644_, v_fst_649_, v_fst_659_, v_nondep_640_, v_snd_660_, v_a_523_, v_a_524_, v_a_655_);
return v___x_675_;
}
else
{
lean_object* v___x_677_; 
lean_dec(v_fst_659_);
lean_dec(v_fst_649_);
lean_dec(v_fst_644_);
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 0, v_e_520_);
v___x_677_ = v___x_662_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_e_520_);
lean_ctor_set(v_reuseFailAlloc_681_, 1, v_snd_660_);
v___x_677_ = v_reuseFailAlloc_681_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
lean_object* v___x_679_; 
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 0, v___x_677_);
v___x_679_ = v___x_657_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v___x_677_);
lean_ctor_set(v_reuseFailAlloc_680_, 1, v_a_655_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
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
lean_dec(v_fst_649_);
lean_dec(v_fst_644_);
lean_dec_ref_known(v_e_520_, 4);
return v___x_653_;
}
}
else
{
lean_dec(v_fst_644_);
lean_dec_ref_known(v_e_520_, 4);
lean_dec(v_offset_521_);
return v___x_646_;
}
}
else
{
lean_dec_ref_known(v_e_520_, 4);
lean_dec(v_offset_521_);
return v___x_641_;
}
}
case 10:
{
lean_object* v_data_684_; lean_object* v_expr_685_; lean_object* v___x_686_; 
v_data_684_ = lean_ctor_get(v_e_520_, 0);
v_expr_685_ = lean_ctor_get(v_e_520_, 1);
lean_inc_ref(v_expr_685_);
v___x_686_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(v_beginIdx_517_, v_n_518_, v_subst_519_, v_expr_685_, v_offset_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_);
if (lean_obj_tag(v___x_686_) == 0)
{
lean_object* v_a_687_; lean_object* v_a_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_708_; 
v_a_687_ = lean_ctor_get(v___x_686_, 0);
v_a_688_ = lean_ctor_get(v___x_686_, 1);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_686_);
if (v_isSharedCheck_708_ == 0)
{
v___x_690_ = v___x_686_;
v_isShared_691_ = v_isSharedCheck_708_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_a_688_);
lean_inc(v_a_687_);
lean_dec(v___x_686_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_708_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v_fst_692_; lean_object* v_snd_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_707_; 
v_fst_692_ = lean_ctor_get(v_a_687_, 0);
v_snd_693_ = lean_ctor_get(v_a_687_, 1);
v_isSharedCheck_707_ = !lean_is_exclusive(v_a_687_);
if (v_isSharedCheck_707_ == 0)
{
v___x_695_ = v_a_687_;
v_isShared_696_ = v_isSharedCheck_707_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_snd_693_);
lean_inc(v_fst_692_);
lean_dec(v_a_687_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_707_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
size_t v___x_697_; size_t v___x_698_; uint8_t v___x_699_; 
v___x_697_ = lean_ptr_addr(v_expr_685_);
v___x_698_ = lean_ptr_addr(v_fst_692_);
v___x_699_ = lean_usize_dec_eq(v___x_697_, v___x_698_);
if (v___x_699_ == 0)
{
lean_object* v___x_700_; 
lean_inc(v_data_684_);
lean_del_object(v___x_695_);
lean_del_object(v___x_690_);
lean_dec_ref_known(v_e_520_, 2);
v___x_700_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__6(v_data_684_, v_fst_692_, v_snd_693_, v_a_523_, v_a_524_, v_a_688_);
return v___x_700_;
}
else
{
lean_object* v___x_702_; 
lean_dec(v_fst_692_);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 0, v_e_520_);
v___x_702_ = v___x_695_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_e_520_);
lean_ctor_set(v_reuseFailAlloc_706_, 1, v_snd_693_);
v___x_702_ = v_reuseFailAlloc_706_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
lean_object* v___x_704_; 
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 0, v___x_702_);
v___x_704_ = v___x_690_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_702_);
lean_ctor_set(v_reuseFailAlloc_705_, 1, v_a_688_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_520_, 2);
return v___x_686_;
}
}
case 11:
{
lean_object* v_typeName_709_; lean_object* v_idx_710_; lean_object* v_struct_711_; lean_object* v___x_712_; 
v_typeName_709_ = lean_ctor_get(v_e_520_, 0);
v_idx_710_ = lean_ctor_get(v_e_520_, 1);
v_struct_711_ = lean_ctor_get(v_e_520_, 2);
lean_inc_ref(v_struct_711_);
v___x_712_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(v_beginIdx_517_, v_n_518_, v_subst_519_, v_struct_711_, v_offset_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_);
if (lean_obj_tag(v___x_712_) == 0)
{
lean_object* v_a_713_; lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_734_; 
v_a_713_ = lean_ctor_get(v___x_712_, 0);
v_a_714_ = lean_ctor_get(v___x_712_, 1);
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_734_ == 0)
{
v___x_716_ = v___x_712_;
v_isShared_717_ = v_isSharedCheck_734_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_inc(v_a_713_);
lean_dec(v___x_712_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_734_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v_fst_718_; lean_object* v_snd_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_733_; 
v_fst_718_ = lean_ctor_get(v_a_713_, 0);
v_snd_719_ = lean_ctor_get(v_a_713_, 1);
v_isSharedCheck_733_ = !lean_is_exclusive(v_a_713_);
if (v_isSharedCheck_733_ == 0)
{
v___x_721_ = v_a_713_;
v_isShared_722_ = v_isSharedCheck_733_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_snd_719_);
lean_inc(v_fst_718_);
lean_dec(v_a_713_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_733_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
size_t v___x_723_; size_t v___x_724_; uint8_t v___x_725_; 
v___x_723_ = lean_ptr_addr(v_struct_711_);
v___x_724_ = lean_ptr_addr(v_fst_718_);
v___x_725_ = lean_usize_dec_eq(v___x_723_, v___x_724_);
if (v___x_725_ == 0)
{
lean_object* v___x_726_; 
lean_inc(v_idx_710_);
lean_inc(v_typeName_709_);
lean_del_object(v___x_721_);
lean_del_object(v___x_716_);
lean_dec_ref_known(v_e_520_, 3);
v___x_726_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__7(v_typeName_709_, v_idx_710_, v_fst_718_, v_snd_719_, v_a_523_, v_a_524_, v_a_714_);
return v___x_726_;
}
else
{
lean_object* v___x_728_; 
lean_dec(v_fst_718_);
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 0, v_e_520_);
v___x_728_ = v___x_721_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_e_520_);
lean_ctor_set(v_reuseFailAlloc_732_, 1, v_snd_719_);
v___x_728_ = v_reuseFailAlloc_732_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
lean_object* v___x_730_; 
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 0, v___x_728_);
v___x_730_ = v___x_716_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v___x_728_);
lean_ctor_set(v_reuseFailAlloc_731_, 1, v_a_714_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_520_, 3);
return v___x_712_;
}
}
default: 
{
lean_object* v___x_735_; lean_object* v___x_736_; 
lean_dec(v_offset_521_);
lean_dec_ref(v_e_520_);
v___x_735_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__3);
v___x_736_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8(v___x_735_, v_a_522_, v_a_523_, v_a_524_, v_a_525_);
return v___x_736_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_beginIdx_517_ = stack[0].m_obj;
lean_object* v_n_518_ = stack[1].m_obj;
lean_object* v_subst_519_ = stack[2].m_obj;
lean_object* v_e_520_ = stack[3].m_obj;
lean_object* v_offset_521_ = stack[4].m_obj;
lean_object* v_a_522_ = stack[5].m_obj;
uint8_t v_a_523_ = stack[6].m_num;
lean_object* v_a_524_ = stack[7].m_obj;
lean_object* v_a_525_ = stack[8].m_obj;
lean_object* v_res_737_;
v_res_737_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1(v_beginIdx_517_, v_n_518_, v_subst_519_, v_e_520_, v_offset_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_);
stack->m_obj
 = v_res_737_;
}
lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(lean_object* v_beginIdx_738_, lean_object* v_n_739_, lean_object* v_subst_740_, lean_object* v_e_741_, lean_object* v_offset_742_, lean_object* v_a_743_, uint8_t v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_){
_start:
{
lean_object* v_key_747_; lean_object* v___x_748_; 
lean_inc(v_offset_742_);
lean_inc_ref(v_e_741_);
v_key_747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_747_, 0, v_e_741_);
lean_ctor_set(v_key_747_, 1, v_offset_742_);
v___x_748_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3___redArg(v_a_743_, v_key_747_);
if (lean_obj_tag(v___x_748_) == 1)
{
lean_object* v_val_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
lean_dec_ref_known(v_key_747_, 2);
lean_dec(v_offset_742_);
lean_dec_ref(v_e_741_);
v_val_749_ = lean_ctor_get(v___x_748_, 0);
lean_inc(v_val_749_);
lean_dec_ref_known(v___x_748_, 1);
v___x_750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_750_, 0, v_val_749_);
lean_ctor_set(v___x_750_, 1, v_a_743_);
v___x_751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_751_, 0, v___x_750_);
lean_ctor_set(v___x_751_, 1, v_a_746_);
return v___x_751_;
}
else
{
lean_object* v_s_u2081_752_; 
lean_dec(v___x_748_);
v_s_u2081_752_ = lean_nat_add(v_beginIdx_738_, v_offset_742_);
switch(lean_obj_tag(v_e_741_))
{
case 0:
{
lean_object* v_deBruijnIndex_753_; uint8_t v___x_754_; 
v_deBruijnIndex_753_ = lean_ctor_get(v_e_741_, 0);
v___x_754_ = lean_nat_dec_le(v_s_u2081_752_, v_deBruijnIndex_753_);
lean_dec(v_s_u2081_752_);
if (v___x_754_ == 0)
{
lean_object* v___x_755_; 
lean_dec(v_offset_742_);
v___x_755_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_747_, v_e_741_, v_a_743_, v_a_744_, v_a_745_, v_a_746_);
return v___x_755_;
}
else
{
lean_object* v___x_756_; uint8_t v___x_757_; 
lean_inc(v_deBruijnIndex_753_);
lean_dec_ref_known(v_e_741_, 1);
v___x_756_ = lean_nat_add(v_offset_742_, v_n_739_);
v___x_757_ = lean_nat_dec_lt(v_deBruijnIndex_753_, v___x_756_);
lean_dec(v___x_756_);
if (v___x_757_ == 0)
{
lean_object* v___x_758_; lean_object* v___x_759_; 
lean_dec(v_offset_742_);
v___x_758_ = lean_nat_sub(v_deBruijnIndex_753_, v_n_739_);
lean_dec(v_deBruijnIndex_753_);
v___x_759_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___redArg(v___x_758_, v_a_746_);
if (lean_obj_tag(v___x_759_) == 0)
{
lean_object* v_a_760_; lean_object* v_a_761_; lean_object* v___x_762_; 
v_a_760_ = lean_ctor_get(v___x_759_, 0);
lean_inc(v_a_760_);
v_a_761_ = lean_ctor_get(v___x_759_, 1);
lean_inc(v_a_761_);
lean_dec_ref_known(v___x_759_, 2);
v___x_762_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_747_, v_a_760_, v_a_743_, v_a_744_, v_a_745_, v_a_761_);
return v___x_762_;
}
else
{
lean_object* v_a_763_; lean_object* v_a_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_771_; 
lean_dec_ref_known(v_key_747_, 2);
lean_dec_ref(v_a_743_);
v_a_763_ = lean_ctor_get(v___x_759_, 0);
v_a_764_ = lean_ctor_get(v___x_759_, 1);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_771_ == 0)
{
v___x_766_ = v___x_759_;
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_a_764_);
lean_inc(v_a_763_);
lean_dec(v___x_759_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___x_769_; 
if (v_isShared_767_ == 0)
{
v___x_769_ = v___x_766_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_a_763_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v_a_764_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
}
else
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v_v_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_772_ = lean_nat_sub(v_deBruijnIndex_753_, v_offset_742_);
lean_dec(v_deBruijnIndex_753_);
v___x_773_ = lean_nat_sub(v_n_739_, v___x_772_);
lean_dec(v___x_772_);
v___x_774_ = lean_unsigned_to_nat(1u);
v___x_775_ = lean_nat_sub(v___x_773_, v___x_774_);
lean_dec(v___x_773_);
v_v_776_ = lean_array_fget_borrowed(v_subst_740_, v___x_775_);
lean_dec(v___x_775_);
v___x_777_ = lean_unsigned_to_nat(0u);
lean_inc(v_v_776_);
v___x_778_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(v_v_776_, v___x_777_, v_offset_742_, v_a_744_, v_a_745_, v_a_746_);
lean_dec(v_offset_742_);
if (lean_obj_tag(v___x_778_) == 0)
{
lean_object* v_a_779_; lean_object* v_a_780_; lean_object* v___x_781_; 
v_a_779_ = lean_ctor_get(v___x_778_, 0);
lean_inc(v_a_779_);
v_a_780_ = lean_ctor_get(v___x_778_, 1);
lean_inc(v_a_780_);
lean_dec_ref_known(v___x_778_, 2);
v___x_781_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_747_, v_a_779_, v_a_743_, v_a_744_, v_a_745_, v_a_780_);
return v___x_781_;
}
else
{
lean_object* v_a_782_; lean_object* v_a_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_790_; 
lean_dec_ref_known(v_key_747_, 2);
lean_dec_ref(v_a_743_);
v_a_782_ = lean_ctor_get(v___x_778_, 0);
v_a_783_ = lean_ctor_get(v___x_778_, 1);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_778_);
if (v_isSharedCheck_790_ == 0)
{
v___x_785_ = v___x_778_;
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_a_783_);
lean_inc(v_a_782_);
lean_dec(v___x_778_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_788_; 
if (v_isShared_786_ == 0)
{
v___x_788_ = v___x_785_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_a_782_);
lean_ctor_set(v_reuseFailAlloc_789_, 1, v_a_783_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
}
}
}
case 9:
{
lean_object* v___x_791_; 
lean_dec(v_s_u2081_752_);
lean_dec(v_offset_742_);
v___x_791_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_747_, v_e_741_, v_a_743_, v_a_744_, v_a_745_, v_a_746_);
return v___x_791_;
}
case 2:
{
lean_object* v___x_792_; 
lean_dec(v_s_u2081_752_);
lean_dec(v_offset_742_);
v___x_792_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_747_, v_e_741_, v_a_743_, v_a_744_, v_a_745_, v_a_746_);
return v___x_792_;
}
case 1:
{
lean_object* v___x_793_; 
lean_dec(v_s_u2081_752_);
lean_dec(v_offset_742_);
v___x_793_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_747_, v_e_741_, v_a_743_, v_a_744_, v_a_745_, v_a_746_);
return v___x_793_;
}
case 4:
{
lean_object* v___x_794_; 
lean_dec(v_s_u2081_752_);
lean_dec(v_offset_742_);
v___x_794_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_747_, v_e_741_, v_a_743_, v_a_744_, v_a_745_, v_a_746_);
return v___x_794_;
}
case 3:
{
lean_object* v___x_795_; 
lean_dec(v_s_u2081_752_);
lean_dec(v_offset_742_);
v___x_795_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_747_, v_e_741_, v_a_743_, v_a_744_, v_a_745_, v_a_746_);
return v___x_795_;
}
default: 
{
lean_object* v___x_796_; uint8_t v___x_797_; 
v___x_796_ = l_Lean_Expr_looseBVarRange(v_e_741_);
v___x_797_ = lean_nat_dec_le(v___x_796_, v_s_u2081_752_);
lean_dec(v_s_u2081_752_);
lean_dec(v___x_796_);
if (v___x_797_ == 0)
{
switch(lean_obj_tag(v_e_741_))
{
case 9:
{
lean_object* v___x_798_; 
lean_dec(v_offset_742_);
v___x_798_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_747_, v_e_741_, v_a_743_, v_a_744_, v_a_745_, v_a_746_);
return v___x_798_;
}
case 2:
{
lean_object* v___x_799_; 
lean_dec(v_offset_742_);
v___x_799_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_747_, v_e_741_, v_a_743_, v_a_744_, v_a_745_, v_a_746_);
return v___x_799_;
}
case 0:
{
lean_object* v___x_800_; 
lean_dec(v_offset_742_);
v___x_800_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_747_, v_e_741_, v_a_743_, v_a_744_, v_a_745_, v_a_746_);
return v___x_800_;
}
case 1:
{
lean_object* v___x_801_; 
lean_dec(v_offset_742_);
v___x_801_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_747_, v_e_741_, v_a_743_, v_a_744_, v_a_745_, v_a_746_);
return v___x_801_;
}
case 4:
{
lean_object* v___x_802_; 
lean_dec(v_offset_742_);
v___x_802_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_747_, v_e_741_, v_a_743_, v_a_744_, v_a_745_, v_a_746_);
return v___x_802_;
}
case 3:
{
lean_object* v___x_803_; 
lean_dec(v_offset_742_);
v___x_803_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_747_, v_e_741_, v_a_743_, v_a_744_, v_a_745_, v_a_746_);
return v___x_803_;
}
default: 
{
lean_object* v___x_804_; 
v___x_804_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1(v_beginIdx_738_, v_n_739_, v_subst_740_, v_e_741_, v_offset_742_, v_a_743_, v_a_744_, v_a_745_, v_a_746_);
if (lean_obj_tag(v___x_804_) == 0)
{
lean_object* v_a_805_; lean_object* v_a_806_; lean_object* v_fst_807_; lean_object* v_snd_808_; lean_object* v___x_809_; 
v_a_805_ = lean_ctor_get(v___x_804_, 0);
lean_inc(v_a_805_);
v_a_806_ = lean_ctor_get(v___x_804_, 1);
lean_inc(v_a_806_);
lean_dec_ref_known(v___x_804_, 2);
v_fst_807_ = lean_ctor_get(v_a_805_, 0);
lean_inc(v_fst_807_);
v_snd_808_ = lean_ctor_get(v_a_805_, 1);
lean_inc(v_snd_808_);
lean_dec(v_a_805_);
v___x_809_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_747_, v_fst_807_, v_snd_808_, v_a_744_, v_a_745_, v_a_806_);
return v___x_809_;
}
else
{
lean_dec_ref_known(v_key_747_, 2);
return v___x_804_;
}
}
}
}
else
{
lean_object* v___x_810_; 
lean_dec(v_offset_742_);
v___x_810_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_747_, v_e_741_, v_a_743_, v_a_744_, v_a_745_, v_a_746_);
return v___x_810_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_beginIdx_738_ = stack[0].m_obj;
lean_object* v_n_739_ = stack[1].m_obj;
lean_object* v_subst_740_ = stack[2].m_obj;
lean_object* v_e_741_ = stack[3].m_obj;
lean_object* v_offset_742_ = stack[4].m_obj;
lean_object* v_a_743_ = stack[5].m_obj;
uint8_t v_a_744_ = stack[6].m_num;
lean_object* v_a_745_ = stack[7].m_obj;
lean_object* v_a_746_ = stack[8].m_obj;
lean_object* v_res_811_;
v_res_811_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(v_beginIdx_738_, v_n_739_, v_subst_740_, v_e_741_, v_offset_742_, v_a_743_, v_a_744_, v_a_745_, v_a_746_);
stack->m_obj
 = v_res_811_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1___boxed(lean_object* v_beginIdx_812_, lean_object* v_n_813_, lean_object* v_subst_814_, lean_object* v_e_815_, lean_object* v_offset_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_){
_start:
{
uint8_t v_a_boxed_821_; lean_object* v_res_822_; 
v_a_boxed_821_ = lean_unbox(v_a_818_);
v_res_822_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1(v_beginIdx_812_, v_n_813_, v_subst_814_, v_e_815_, v_offset_816_, v_a_817_, v_a_boxed_821_, v_a_819_, v_a_820_);
lean_dec_ref(v_a_819_);
lean_dec_ref(v_subst_814_);
lean_dec(v_n_813_);
lean_dec(v_beginIdx_812_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___boxed(lean_object* v_beginIdx_823_, lean_object* v_n_824_, lean_object* v_subst_825_, lean_object* v_e_826_, lean_object* v_offset_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_){
_start:
{
uint8_t v_a_boxed_832_; lean_object* v_res_833_; 
v_a_boxed_832_ = lean_unbox(v_a_829_);
v_res_833_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1(v_beginIdx_823_, v_n_824_, v_subst_825_, v_e_826_, v_offset_827_, v_a_828_, v_a_boxed_832_, v_a_830_, v_a_831_);
lean_dec_ref(v_a_830_);
lean_dec_ref(v_subst_825_);
lean_dec(v_n_824_);
lean_dec(v_beginIdx_823_);
return v_res_833_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__0(void){
_start:
{
lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_834_ = lean_box(0);
v___x_835_ = lean_unsigned_to_nat(16u);
v___x_836_ = lean_mk_array(v___x_835_, v___x_834_);
return v___x_836_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__1(void){
_start:
{
lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_837_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__0, &l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__0_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__0);
v___x_838_ = lean_unsigned_to_nat(0u);
v___x_839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_839_, 0, v___x_838_);
lean_ctor_set(v___x_839_, 1, v___x_837_);
return v___x_839_;
}
}
lean_object* l_Lean_Meta_Sym_instantiateRevRangeS___lam__0(lean_object* v_e_840_, lean_object* v_beginIdx_841_, lean_object* v_n_842_, lean_object* v_subst_843_, uint8_t v_debug_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
lean_object* v___x_847_; 
v___x_847_ = lean_unsigned_to_nat(0u);
switch(lean_obj_tag(v_e_840_))
{
case 0:
{
lean_object* v_deBruijnIndex_848_; uint8_t v___x_849_; 
v_deBruijnIndex_848_ = lean_ctor_get(v_e_840_, 0);
v___x_849_ = lean_nat_dec_le(v_beginIdx_841_, v_deBruijnIndex_848_);
if (v___x_849_ == 0)
{
lean_object* v___x_850_; 
v___x_850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_850_, 0, v_e_840_);
lean_ctor_set(v___x_850_, 1, v___y_846_);
return v___x_850_;
}
else
{
uint8_t v___x_851_; 
lean_inc(v_deBruijnIndex_848_);
lean_dec_ref_known(v_e_840_, 1);
v___x_851_ = lean_nat_dec_lt(v_deBruijnIndex_848_, v_n_842_);
if (v___x_851_ == 0)
{
lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_852_ = lean_nat_sub(v_deBruijnIndex_848_, v_n_842_);
lean_dec(v_deBruijnIndex_848_);
v___x_853_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___redArg(v___x_852_, v___y_846_);
return v___x_853_;
}
else
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v_v_857_; lean_object* v___x_858_; 
v___x_854_ = lean_nat_sub(v_n_842_, v_deBruijnIndex_848_);
lean_dec(v_deBruijnIndex_848_);
v___x_855_ = lean_unsigned_to_nat(1u);
v___x_856_ = lean_nat_sub(v___x_854_, v___x_855_);
lean_dec(v___x_854_);
v_v_857_ = lean_array_fget_borrowed(v_subst_843_, v___x_856_);
lean_dec(v___x_856_);
lean_inc(v_v_857_);
v___x_858_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(v_v_857_, v___x_847_, v___x_847_, v_debug_844_, v___y_845_, v___y_846_);
return v___x_858_;
}
}
}
case 9:
{
lean_object* v___x_859_; 
v___x_859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_859_, 0, v_e_840_);
lean_ctor_set(v___x_859_, 1, v___y_846_);
return v___x_859_;
}
case 2:
{
lean_object* v___x_860_; 
v___x_860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_860_, 0, v_e_840_);
lean_ctor_set(v___x_860_, 1, v___y_846_);
return v___x_860_;
}
case 1:
{
lean_object* v___x_861_; 
v___x_861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_861_, 0, v_e_840_);
lean_ctor_set(v___x_861_, 1, v___y_846_);
return v___x_861_;
}
case 4:
{
lean_object* v___x_862_; 
v___x_862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_862_, 0, v_e_840_);
lean_ctor_set(v___x_862_, 1, v___y_846_);
return v___x_862_;
}
case 3:
{
lean_object* v___x_863_; 
v___x_863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_863_, 0, v_e_840_);
lean_ctor_set(v___x_863_, 1, v___y_846_);
return v___x_863_;
}
default: 
{
lean_object* v___x_864_; uint8_t v___x_865_; 
v___x_864_ = l_Lean_Expr_looseBVarRange(v_e_840_);
v___x_865_ = lean_nat_dec_le(v___x_864_, v_beginIdx_841_);
lean_dec(v___x_864_);
if (v___x_865_ == 0)
{
switch(lean_obj_tag(v_e_840_))
{
case 9:
{
lean_object* v___x_866_; 
v___x_866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_866_, 0, v_e_840_);
lean_ctor_set(v___x_866_, 1, v___y_846_);
return v___x_866_;
}
case 2:
{
lean_object* v___x_867_; 
v___x_867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_867_, 0, v_e_840_);
lean_ctor_set(v___x_867_, 1, v___y_846_);
return v___x_867_;
}
case 0:
{
lean_object* v___x_868_; 
v___x_868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_868_, 0, v_e_840_);
lean_ctor_set(v___x_868_, 1, v___y_846_);
return v___x_868_;
}
case 1:
{
lean_object* v___x_869_; 
v___x_869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_869_, 0, v_e_840_);
lean_ctor_set(v___x_869_, 1, v___y_846_);
return v___x_869_;
}
case 4:
{
lean_object* v___x_870_; 
v___x_870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_870_, 0, v_e_840_);
lean_ctor_set(v___x_870_, 1, v___y_846_);
return v___x_870_;
}
case 3:
{
lean_object* v___x_871_; 
v___x_871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_871_, 0, v_e_840_);
lean_ctor_set(v___x_871_, 1, v___y_846_);
return v___x_871_;
}
default: 
{
lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_872_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__1, &l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__1_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__1);
v___x_873_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1(v_beginIdx_841_, v_n_842_, v_subst_843_, v_e_840_, v___x_847_, v___x_872_, v_debug_844_, v___y_845_, v___y_846_);
if (lean_obj_tag(v___x_873_) == 0)
{
lean_object* v_a_874_; lean_object* v_a_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_883_; 
v_a_874_ = lean_ctor_get(v___x_873_, 0);
v_a_875_ = lean_ctor_get(v___x_873_, 1);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_873_);
if (v_isSharedCheck_883_ == 0)
{
v___x_877_ = v___x_873_;
v_isShared_878_ = v_isSharedCheck_883_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_a_875_);
lean_inc(v_a_874_);
lean_dec(v___x_873_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_883_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v_fst_879_; lean_object* v___x_881_; 
v_fst_879_ = lean_ctor_get(v_a_874_, 0);
lean_inc(v_fst_879_);
lean_dec(v_a_874_);
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 0, v_fst_879_);
v___x_881_ = v___x_877_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_fst_879_);
lean_ctor_set(v_reuseFailAlloc_882_, 1, v_a_875_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
else
{
lean_object* v_a_884_; lean_object* v_a_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_892_; 
v_a_884_ = lean_ctor_get(v___x_873_, 0);
v_a_885_ = lean_ctor_get(v___x_873_, 1);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_873_);
if (v_isSharedCheck_892_ == 0)
{
v___x_887_ = v___x_873_;
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_a_885_);
lean_inc(v_a_884_);
lean_dec(v___x_873_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_890_; 
if (v_isShared_888_ == 0)
{
v___x_890_ = v___x_887_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_a_884_);
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
}
}
}
else
{
lean_object* v___x_893_; 
v___x_893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_893_, 0, v_e_840_);
lean_ctor_set(v___x_893_, 1, v___y_846_);
return v___x_893_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_instantiateRevRangeS___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_840_ = stack[0].m_obj;
lean_object* v_beginIdx_841_ = stack[1].m_obj;
lean_object* v_n_842_ = stack[2].m_obj;
lean_object* v_subst_843_ = stack[3].m_obj;
uint8_t v_debug_844_ = stack[4].m_num;
lean_object* v___y_845_ = stack[5].m_obj;
lean_object* v___y_846_ = stack[6].m_obj;
lean_object* v_res_894_;
v_res_894_ = l_Lean_Meta_Sym_instantiateRevRangeS___lam__0(v_e_840_, v_beginIdx_841_, v_n_842_, v_subst_843_, v_debug_844_, v___y_845_, v___y_846_);
stack->m_obj
 = v_res_894_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___boxed(lean_object* v_e_895_, lean_object* v_beginIdx_896_, lean_object* v_n_897_, lean_object* v_subst_898_, lean_object* v_debug_899_, lean_object* v___y_900_, lean_object* v___y_901_){
_start:
{
uint8_t v_debug_boxed_902_; lean_object* v_res_903_; 
v_debug_boxed_902_ = lean_unbox(v_debug_899_);
v_res_903_ = l_Lean_Meta_Sym_instantiateRevRangeS___lam__0(v_e_895_, v_beginIdx_896_, v_n_897_, v_subst_898_, v_debug_boxed_902_, v___y_900_, v___y_901_);
lean_dec_ref(v___y_900_);
lean_dec_ref(v_subst_898_);
lean_dec(v_n_897_);
lean_dec(v_beginIdx_896_);
return v_res_903_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__2(void){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_906_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__2));
v___x_907_ = lean_unsigned_to_nat(16u);
v___x_908_ = lean_unsigned_to_nat(62u);
v___x_909_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__1));
v___x_910_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__0));
v___x_911_ = l_mkPanicMessageWithDecl(v___x_910_, v___x_909_, v___x_908_, v___x_907_, v___x_906_);
return v___x_911_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__5(void){
_start:
{
lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_914_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__2));
v___x_915_ = lean_unsigned_to_nat(34u);
v___x_916_ = lean_unsigned_to_nat(20u);
v___x_917_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__4));
v___x_918_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__3));
v___x_919_ = l_mkPanicMessageWithDecl(v___x_918_, v___x_917_, v___x_916_, v___x_915_, v___x_914_);
return v___x_919_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__6(void){
_start:
{
lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
v___x_920_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__2));
v___x_921_ = lean_unsigned_to_nat(32u);
v___x_922_ = lean_unsigned_to_nat(19u);
v___x_923_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__4));
v___x_924_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__3));
v___x_925_ = l_mkPanicMessageWithDecl(v___x_924_, v___x_923_, v___x_922_, v___x_921_, v___x_920_);
return v___x_925_;
}
}
lean_object* l_Lean_Meta_Sym_instantiateRevRangeS(lean_object* v_e_926_, lean_object* v_beginIdx_927_, lean_object* v_endIdx_928_, lean_object* v_subst_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_){
_start:
{
uint8_t v___x_937_; 
v___x_937_ = lean_nat_dec_lt(v_endIdx_928_, v_beginIdx_927_);
if (v___x_937_ == 0)
{
lean_object* v___x_938_; uint8_t v___x_939_; 
v___x_938_ = lean_array_get_size(v_subst_929_);
v___x_939_ = lean_nat_dec_lt(v___x_938_, v_endIdx_928_);
if (v___x_939_ == 0)
{
lean_object* v_n_940_; lean_object* v___x_941_; uint8_t v_debug_942_; lean_object* v___x_943_; lean_object* v___f_944_; lean_object* v___x_945_; lean_object* v_env_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v_n_940_ = lean_nat_sub(v_endIdx_928_, v_beginIdx_927_);
v___x_941_ = lean_st_ref_get(v_a_931_);
v_debug_942_ = lean_ctor_get_uint8(v___x_941_, sizeof(void*)*12);
lean_dec(v___x_941_);
v___x_943_ = lean_box(v_debug_942_);
v___f_944_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___boxed), 7, 5);
lean_closure_set(v___f_944_, 0, v_e_926_);
lean_closure_set(v___f_944_, 1, v_beginIdx_927_);
lean_closure_set(v___f_944_, 2, v_n_940_);
lean_closure_set(v___f_944_, 3, v_subst_929_);
lean_closure_set(v___f_944_, 4, v___x_943_);
v___x_945_ = lean_st_ref_get(v_a_935_);
v_env_946_ = lean_ctor_get(v___x_945_, 0);
lean_inc_ref(v_env_946_);
lean_dec(v___x_945_);
v___x_947_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_947_, 0, v_env_946_);
lean_ctor_set_uint8(v___x_947_, sizeof(void*)*1, v___x_939_);
lean_ctor_set_uint8(v___x_947_, sizeof(void*)*1 + 1, v___x_939_);
v___x_948_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___f_944_, v___x_947_, v_a_931_);
if (lean_obj_tag(v___x_948_) == 0)
{
lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_959_; 
v_a_949_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_959_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_959_ == 0)
{
v___x_951_ = v___x_948_;
v_isShared_952_ = v_isSharedCheck_959_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_dec(v___x_948_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_959_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
if (lean_obj_tag(v_a_949_) == 0)
{
lean_object* v___x_953_; lean_object* v___x_954_; 
lean_dec_ref_known(v_a_949_, 1);
lean_del_object(v___x_951_);
v___x_953_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__2, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__2_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__2);
v___x_954_ = l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(v___x_953_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_);
return v___x_954_;
}
else
{
lean_object* v_a_955_; lean_object* v___x_957_; 
v_a_955_ = lean_ctor_get(v_a_949_, 0);
lean_inc(v_a_955_);
lean_dec_ref_known(v_a_949_, 1);
if (v_isShared_952_ == 0)
{
lean_ctor_set(v___x_951_, 0, v_a_955_);
v___x_957_ = v___x_951_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_a_955_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
}
}
else
{
lean_object* v_a_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_967_; 
v_a_960_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_967_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_967_ == 0)
{
v___x_962_ = v___x_948_;
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_a_960_);
lean_dec(v___x_948_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___x_965_; 
if (v_isShared_963_ == 0)
{
v___x_965_ = v___x_962_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_a_960_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
}
}
else
{
lean_object* v___x_968_; lean_object* v___x_969_; 
lean_dec_ref(v_subst_929_);
lean_dec(v_beginIdx_927_);
lean_dec_ref(v_e_926_);
v___x_968_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__5, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__5_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__5);
v___x_969_ = l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(v___x_968_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_);
return v___x_969_;
}
}
else
{
lean_object* v___x_970_; lean_object* v___x_971_; 
lean_dec_ref(v_subst_929_);
lean_dec(v_beginIdx_927_);
lean_dec_ref(v_e_926_);
v___x_970_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__6, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__6_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__6);
v___x_971_ = l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(v___x_970_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_);
return v___x_971_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_instantiateRevRangeS_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_926_ = stack[0].m_obj;
lean_object* v_beginIdx_927_ = stack[1].m_obj;
lean_object* v_endIdx_928_ = stack[2].m_obj;
lean_object* v_subst_929_ = stack[3].m_obj;
lean_object* v_a_930_ = stack[4].m_obj;
lean_object* v_a_931_ = stack[5].m_obj;
lean_object* v_a_932_ = stack[6].m_obj;
lean_object* v_a_933_ = stack[7].m_obj;
lean_object* v_a_934_ = stack[8].m_obj;
lean_object* v_a_935_ = stack[9].m_obj;
lean_object* v_res_972_;
v_res_972_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_e_926_, v_beginIdx_927_, v_endIdx_928_, v_subst_929_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_);
stack->m_obj
 = v_res_972_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevRangeS___boxed(lean_object* v_e_973_, lean_object* v_beginIdx_974_, lean_object* v_endIdx_975_, lean_object* v_subst_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_e_973_, v_beginIdx_974_, v_endIdx_975_, v_subst_976_, v_a_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_);
lean_dec(v_a_982_);
lean_dec_ref(v_a_981_);
lean_dec(v_a_980_);
lean_dec_ref(v_a_979_);
lean_dec(v_a_978_);
lean_dec_ref(v_a_977_);
lean_dec(v_endIdx_975_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_985_, lean_object* v_m_986_, lean_object* v_a_987_){
_start:
{
lean_object* v___x_988_; 
v___x_988_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3___redArg(v_m_986_, v_a_987_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_989_, lean_object* v_m_990_, lean_object* v_a_991_){
_start:
{
lean_object* v_res_992_; 
v_res_992_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3(v_00_u03b2_989_, v_m_990_, v_a_991_);
lean_dec_ref(v_a_991_);
lean_dec_ref(v_m_990_);
return v_res_992_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11(lean_object* v_00_u03b2_993_, lean_object* v_a_994_, lean_object* v_x_995_){
_start:
{
lean_object* v___x_996_; 
v___x_996_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11___redArg(v_a_994_, v_x_995_);
return v___x_996_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11___boxed(lean_object* v_00_u03b2_997_, lean_object* v_a_998_, lean_object* v_x_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3_spec__11(v_00_u03b2_997_, v_a_998_, v_x_999_);
lean_dec(v_x_999_);
lean_dec_ref(v_a_998_);
return v_res_1000_;
}
}
lean_object* l_Lean_Meta_Sym_instantiateRevS(lean_object* v_e_1001_, lean_object* v_subst_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1010_ = lean_unsigned_to_nat(0u);
v___x_1011_ = lean_array_get_size(v_subst_1002_);
v___x_1012_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_e_1001_, v___x_1010_, v___x_1011_, v_subst_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_);
return v___x_1012_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_instantiateRevS_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1001_ = stack[0].m_obj;
lean_object* v_subst_1002_ = stack[1].m_obj;
lean_object* v_a_1003_ = stack[2].m_obj;
lean_object* v_a_1004_ = stack[3].m_obj;
lean_object* v_a_1005_ = stack[4].m_obj;
lean_object* v_a_1006_ = stack[5].m_obj;
lean_object* v_a_1007_ = stack[6].m_obj;
lean_object* v_a_1008_ = stack[7].m_obj;
lean_object* v_res_1013_;
v_res_1013_ = l_Lean_Meta_Sym_instantiateRevS(v_e_1001_, v_subst_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_);
stack->m_obj
 = v_res_1013_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevS___boxed(lean_object* v_e_1014_, lean_object* v_subst_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l_Lean_Meta_Sym_instantiateRevS(v_e_1014_, v_subst_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_);
lean_dec(v_a_1021_);
lean_dec_ref(v_a_1020_);
lean_dec(v_a_1019_);
lean_dec_ref(v_a_1018_);
lean_dec(v_a_1017_);
lean_dec_ref(v_a_1016_);
return v_res_1023_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1024_; 
v___x_1024_ = l_Std_HashMap_instInhabited___redArg();
return v___x_1024_;
}
}
lean_object* l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1(lean_object* v_msg_1025_, uint8_t v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v___x_1029_; lean_object* v___f_1030_; lean_object* v___f_1031_; lean_object* v___f_1032_; lean_object* v___x_2857__overap_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1029_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1___closed__0);
v___f_1030_ = lean_alloc_closure((void*)(l_EStateM_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1030_, 0, v___x_1029_);
v___f_1031_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1031_, 0, v___f_1030_);
v___f_1032_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1032_, 0, v___f_1031_);
v___x_2857__overap_1033_ = lean_panic_fn_borrowed(v___f_1032_, v_msg_1025_);
lean_dec_ref(v___f_1032_);
v___x_1034_ = lean_box(v___y_1026_);
lean_inc_ref(v___y_1027_);
v___x_1035_ = lean_apply_3(v___x_2857__overap_1033_, v___x_1034_, v___y_1027_, v___y_1028_);
return v___x_1035_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1025_ = stack[0].m_obj;
uint8_t v___y_1026_ = stack[1].m_num;
lean_object* v___y_1027_ = stack[2].m_obj;
lean_object* v___y_1028_ = stack[3].m_obj;
lean_object* v_res_1036_;
v_res_1036_ = l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1(v_msg_1025_, v___y_1026_, v___y_1027_, v___y_1028_);
stack->m_obj
 = v_res_1036_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1___boxed(lean_object* v_msg_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_){
_start:
{
uint8_t v___y_3381__boxed_1041_; lean_object* v_res_1042_; 
v___y_3381__boxed_1041_ = lean_unbox(v___y_1038_);
v_res_1042_ = l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1(v_msg_1037_, v___y_3381__boxed_1041_, v___y_1039_, v___y_1040_);
lean_dec_ref(v___y_1039_);
return v_res_1042_;
}
}
lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0(lean_object* v_n_1043_, lean_object* v_beginIdx_1044_, lean_object* v_subst_1045_, lean_object* v_e_1046_, lean_object* v_offset_1047_, lean_object* v_a_1048_, uint8_t v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_){
_start:
{
switch(lean_obj_tag(v_e_1046_))
{
case 5:
{
lean_object* v_fn_1052_; lean_object* v_arg_1053_; lean_object* v___x_1054_; 
v_fn_1052_ = lean_ctor_get(v_e_1046_, 0);
v_arg_1053_ = lean_ctor_get(v_e_1046_, 1);
lean_inc(v_offset_1047_);
lean_inc_ref(v_fn_1052_);
v___x_1054_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1043_, v_beginIdx_1044_, v_subst_1045_, v_fn_1052_, v_offset_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_);
if (lean_obj_tag(v___x_1054_) == 0)
{
lean_object* v_a_1055_; lean_object* v_a_1056_; lean_object* v_fst_1057_; lean_object* v_snd_1058_; lean_object* v___x_1059_; 
v_a_1055_ = lean_ctor_get(v___x_1054_, 0);
lean_inc(v_a_1055_);
v_a_1056_ = lean_ctor_get(v___x_1054_, 1);
lean_inc(v_a_1056_);
lean_dec_ref_known(v___x_1054_, 2);
v_fst_1057_ = lean_ctor_get(v_a_1055_, 0);
lean_inc(v_fst_1057_);
v_snd_1058_ = lean_ctor_get(v_a_1055_, 1);
lean_inc(v_snd_1058_);
lean_dec(v_a_1055_);
lean_inc_ref(v_arg_1053_);
v___x_1059_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1043_, v_beginIdx_1044_, v_subst_1045_, v_arg_1053_, v_offset_1047_, v_snd_1058_, v_a_1049_, v_a_1050_, v_a_1056_);
if (lean_obj_tag(v___x_1059_) == 0)
{
lean_object* v_a_1060_; lean_object* v_a_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1085_; 
v_a_1060_ = lean_ctor_get(v___x_1059_, 0);
v_a_1061_ = lean_ctor_get(v___x_1059_, 1);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1059_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1063_ = v___x_1059_;
v_isShared_1064_ = v_isSharedCheck_1085_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_a_1061_);
lean_inc(v_a_1060_);
lean_dec(v___x_1059_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1085_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v_fst_1065_; lean_object* v_snd_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1084_; 
v_fst_1065_ = lean_ctor_get(v_a_1060_, 0);
v_snd_1066_ = lean_ctor_get(v_a_1060_, 1);
v_isSharedCheck_1084_ = !lean_is_exclusive(v_a_1060_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1068_ = v_a_1060_;
v_isShared_1069_ = v_isSharedCheck_1084_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_snd_1066_);
lean_inc(v_fst_1065_);
lean_dec(v_a_1060_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1084_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
size_t v___x_1070_; size_t v___x_1071_; uint8_t v___x_1072_; 
v___x_1070_ = lean_ptr_addr(v_fn_1052_);
v___x_1071_ = lean_ptr_addr(v_fst_1057_);
v___x_1072_ = lean_usize_dec_eq(v___x_1070_, v___x_1071_);
if (v___x_1072_ == 0)
{
lean_object* v___x_1073_; 
lean_del_object(v___x_1068_);
lean_del_object(v___x_1063_);
lean_dec_ref_known(v_e_1046_, 2);
v___x_1073_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__2(v_fst_1057_, v_fst_1065_, v_snd_1066_, v_a_1049_, v_a_1050_, v_a_1061_);
return v___x_1073_;
}
else
{
size_t v___x_1074_; size_t v___x_1075_; uint8_t v___x_1076_; 
v___x_1074_ = lean_ptr_addr(v_arg_1053_);
v___x_1075_ = lean_ptr_addr(v_fst_1065_);
v___x_1076_ = lean_usize_dec_eq(v___x_1074_, v___x_1075_);
if (v___x_1076_ == 0)
{
lean_object* v___x_1077_; 
lean_del_object(v___x_1068_);
lean_del_object(v___x_1063_);
lean_dec_ref_known(v_e_1046_, 2);
v___x_1077_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__2(v_fst_1057_, v_fst_1065_, v_snd_1066_, v_a_1049_, v_a_1050_, v_a_1061_);
return v___x_1077_;
}
else
{
lean_object* v___x_1079_; 
lean_dec(v_fst_1065_);
lean_dec(v_fst_1057_);
if (v_isShared_1069_ == 0)
{
lean_ctor_set(v___x_1068_, 0, v_e_1046_);
v___x_1079_ = v___x_1068_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_e_1046_);
lean_ctor_set(v_reuseFailAlloc_1083_, 1, v_snd_1066_);
v___x_1079_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
lean_object* v___x_1081_; 
if (v_isShared_1064_ == 0)
{
lean_ctor_set(v___x_1063_, 0, v___x_1079_);
v___x_1081_ = v___x_1063_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v___x_1079_);
lean_ctor_set(v_reuseFailAlloc_1082_, 1, v_a_1061_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1057_);
lean_dec_ref_known(v_e_1046_, 2);
return v___x_1059_;
}
}
else
{
lean_dec_ref_known(v_e_1046_, 2);
lean_dec(v_offset_1047_);
return v___x_1054_;
}
}
case 6:
{
lean_object* v_binderName_1086_; lean_object* v_binderType_1087_; lean_object* v_body_1088_; uint8_t v_binderInfo_1089_; lean_object* v___x_1090_; 
v_binderName_1086_ = lean_ctor_get(v_e_1046_, 0);
v_binderType_1087_ = lean_ctor_get(v_e_1046_, 1);
v_body_1088_ = lean_ctor_get(v_e_1046_, 2);
v_binderInfo_1089_ = lean_ctor_get_uint8(v_e_1046_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1047_);
lean_inc_ref(v_binderType_1087_);
v___x_1090_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1043_, v_beginIdx_1044_, v_subst_1045_, v_binderType_1087_, v_offset_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_);
if (lean_obj_tag(v___x_1090_) == 0)
{
lean_object* v_a_1091_; lean_object* v_a_1092_; lean_object* v_fst_1093_; lean_object* v_snd_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
v_a_1091_ = lean_ctor_get(v___x_1090_, 0);
lean_inc(v_a_1091_);
v_a_1092_ = lean_ctor_get(v___x_1090_, 1);
lean_inc(v_a_1092_);
lean_dec_ref_known(v___x_1090_, 2);
v_fst_1093_ = lean_ctor_get(v_a_1091_, 0);
lean_inc(v_fst_1093_);
v_snd_1094_ = lean_ctor_get(v_a_1091_, 1);
lean_inc(v_snd_1094_);
lean_dec(v_a_1091_);
v___x_1095_ = lean_unsigned_to_nat(1u);
v___x_1096_ = lean_nat_add(v_offset_1047_, v___x_1095_);
lean_dec(v_offset_1047_);
lean_inc_ref(v_body_1088_);
v___x_1097_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1043_, v_beginIdx_1044_, v_subst_1045_, v_body_1088_, v___x_1096_, v_snd_1094_, v_a_1049_, v_a_1050_, v_a_1092_);
if (lean_obj_tag(v___x_1097_) == 0)
{
lean_object* v_a_1098_; lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1123_; 
v_a_1098_ = lean_ctor_get(v___x_1097_, 0);
v_a_1099_ = lean_ctor_get(v___x_1097_, 1);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1101_ = v___x_1097_;
v_isShared_1102_ = v_isSharedCheck_1123_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_inc(v_a_1098_);
lean_dec(v___x_1097_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1123_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v_fst_1103_; lean_object* v_snd_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1122_; 
v_fst_1103_ = lean_ctor_get(v_a_1098_, 0);
v_snd_1104_ = lean_ctor_get(v_a_1098_, 1);
v_isSharedCheck_1122_ = !lean_is_exclusive(v_a_1098_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1106_ = v_a_1098_;
v_isShared_1107_ = v_isSharedCheck_1122_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_snd_1104_);
lean_inc(v_fst_1103_);
lean_dec(v_a_1098_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1122_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
size_t v___x_1108_; size_t v___x_1109_; uint8_t v___x_1110_; 
v___x_1108_ = lean_ptr_addr(v_binderType_1087_);
v___x_1109_ = lean_ptr_addr(v_fst_1093_);
v___x_1110_ = lean_usize_dec_eq(v___x_1108_, v___x_1109_);
if (v___x_1110_ == 0)
{
lean_object* v___x_1111_; 
lean_inc(v_binderName_1086_);
lean_del_object(v___x_1106_);
lean_del_object(v___x_1101_);
lean_dec_ref_known(v_e_1046_, 3);
v___x_1111_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__3(v_binderName_1086_, v_binderInfo_1089_, v_fst_1093_, v_fst_1103_, v_snd_1104_, v_a_1049_, v_a_1050_, v_a_1099_);
return v___x_1111_;
}
else
{
size_t v___x_1112_; size_t v___x_1113_; uint8_t v___x_1114_; 
v___x_1112_ = lean_ptr_addr(v_body_1088_);
v___x_1113_ = lean_ptr_addr(v_fst_1103_);
v___x_1114_ = lean_usize_dec_eq(v___x_1112_, v___x_1113_);
if (v___x_1114_ == 0)
{
lean_object* v___x_1115_; 
lean_inc(v_binderName_1086_);
lean_del_object(v___x_1106_);
lean_del_object(v___x_1101_);
lean_dec_ref_known(v_e_1046_, 3);
v___x_1115_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__3(v_binderName_1086_, v_binderInfo_1089_, v_fst_1093_, v_fst_1103_, v_snd_1104_, v_a_1049_, v_a_1050_, v_a_1099_);
return v___x_1115_;
}
else
{
lean_object* v___x_1117_; 
lean_dec(v_fst_1103_);
lean_dec(v_fst_1093_);
if (v_isShared_1107_ == 0)
{
lean_ctor_set(v___x_1106_, 0, v_e_1046_);
v___x_1117_ = v___x_1106_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_e_1046_);
lean_ctor_set(v_reuseFailAlloc_1121_, 1, v_snd_1104_);
v___x_1117_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
lean_object* v___x_1119_; 
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 0, v___x_1117_);
v___x_1119_ = v___x_1101_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v___x_1117_);
lean_ctor_set(v_reuseFailAlloc_1120_, 1, v_a_1099_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1093_);
lean_dec_ref_known(v_e_1046_, 3);
return v___x_1097_;
}
}
else
{
lean_dec_ref_known(v_e_1046_, 3);
lean_dec(v_offset_1047_);
return v___x_1090_;
}
}
case 7:
{
lean_object* v_binderName_1124_; lean_object* v_binderType_1125_; lean_object* v_body_1126_; uint8_t v_binderInfo_1127_; lean_object* v___x_1128_; 
v_binderName_1124_ = lean_ctor_get(v_e_1046_, 0);
v_binderType_1125_ = lean_ctor_get(v_e_1046_, 1);
v_body_1126_ = lean_ctor_get(v_e_1046_, 2);
v_binderInfo_1127_ = lean_ctor_get_uint8(v_e_1046_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1047_);
lean_inc_ref(v_binderType_1125_);
v___x_1128_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1043_, v_beginIdx_1044_, v_subst_1045_, v_binderType_1125_, v_offset_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_);
if (lean_obj_tag(v___x_1128_) == 0)
{
lean_object* v_a_1129_; lean_object* v_a_1130_; lean_object* v_fst_1131_; lean_object* v_snd_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
v_a_1129_ = lean_ctor_get(v___x_1128_, 0);
lean_inc(v_a_1129_);
v_a_1130_ = lean_ctor_get(v___x_1128_, 1);
lean_inc(v_a_1130_);
lean_dec_ref_known(v___x_1128_, 2);
v_fst_1131_ = lean_ctor_get(v_a_1129_, 0);
lean_inc(v_fst_1131_);
v_snd_1132_ = lean_ctor_get(v_a_1129_, 1);
lean_inc(v_snd_1132_);
lean_dec(v_a_1129_);
v___x_1133_ = lean_unsigned_to_nat(1u);
v___x_1134_ = lean_nat_add(v_offset_1047_, v___x_1133_);
lean_dec(v_offset_1047_);
lean_inc_ref(v_body_1126_);
v___x_1135_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1043_, v_beginIdx_1044_, v_subst_1045_, v_body_1126_, v___x_1134_, v_snd_1132_, v_a_1049_, v_a_1050_, v_a_1130_);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v_a_1136_; lean_object* v_a_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1161_; 
v_a_1136_ = lean_ctor_get(v___x_1135_, 0);
v_a_1137_ = lean_ctor_get(v___x_1135_, 1);
v_isSharedCheck_1161_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1139_ = v___x_1135_;
v_isShared_1140_ = v_isSharedCheck_1161_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_a_1137_);
lean_inc(v_a_1136_);
lean_dec(v___x_1135_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1161_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v_fst_1141_; lean_object* v_snd_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1160_; 
v_fst_1141_ = lean_ctor_get(v_a_1136_, 0);
v_snd_1142_ = lean_ctor_get(v_a_1136_, 1);
v_isSharedCheck_1160_ = !lean_is_exclusive(v_a_1136_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1144_ = v_a_1136_;
v_isShared_1145_ = v_isSharedCheck_1160_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_snd_1142_);
lean_inc(v_fst_1141_);
lean_dec(v_a_1136_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1160_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
size_t v___x_1146_; size_t v___x_1147_; uint8_t v___x_1148_; 
v___x_1146_ = lean_ptr_addr(v_binderType_1125_);
v___x_1147_ = lean_ptr_addr(v_fst_1131_);
v___x_1148_ = lean_usize_dec_eq(v___x_1146_, v___x_1147_);
if (v___x_1148_ == 0)
{
lean_object* v___x_1149_; 
lean_inc(v_binderName_1124_);
lean_del_object(v___x_1144_);
lean_del_object(v___x_1139_);
lean_dec_ref_known(v_e_1046_, 3);
v___x_1149_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__4(v_binderName_1124_, v_binderInfo_1127_, v_fst_1131_, v_fst_1141_, v_snd_1142_, v_a_1049_, v_a_1050_, v_a_1137_);
return v___x_1149_;
}
else
{
size_t v___x_1150_; size_t v___x_1151_; uint8_t v___x_1152_; 
v___x_1150_ = lean_ptr_addr(v_body_1126_);
v___x_1151_ = lean_ptr_addr(v_fst_1141_);
v___x_1152_ = lean_usize_dec_eq(v___x_1150_, v___x_1151_);
if (v___x_1152_ == 0)
{
lean_object* v___x_1153_; 
lean_inc(v_binderName_1124_);
lean_del_object(v___x_1144_);
lean_del_object(v___x_1139_);
lean_dec_ref_known(v_e_1046_, 3);
v___x_1153_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__4(v_binderName_1124_, v_binderInfo_1127_, v_fst_1131_, v_fst_1141_, v_snd_1142_, v_a_1049_, v_a_1050_, v_a_1137_);
return v___x_1153_;
}
else
{
lean_object* v___x_1155_; 
lean_dec(v_fst_1141_);
lean_dec(v_fst_1131_);
if (v_isShared_1145_ == 0)
{
lean_ctor_set(v___x_1144_, 0, v_e_1046_);
v___x_1155_ = v___x_1144_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_e_1046_);
lean_ctor_set(v_reuseFailAlloc_1159_, 1, v_snd_1142_);
v___x_1155_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
lean_object* v___x_1157_; 
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 0, v___x_1155_);
v___x_1157_ = v___x_1139_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v___x_1155_);
lean_ctor_set(v_reuseFailAlloc_1158_, 1, v_a_1137_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1131_);
lean_dec_ref_known(v_e_1046_, 3);
return v___x_1135_;
}
}
else
{
lean_dec_ref_known(v_e_1046_, 3);
lean_dec(v_offset_1047_);
return v___x_1128_;
}
}
case 8:
{
lean_object* v_declName_1162_; lean_object* v_type_1163_; lean_object* v_value_1164_; lean_object* v_body_1165_; uint8_t v_nondep_1166_; lean_object* v___x_1167_; 
v_declName_1162_ = lean_ctor_get(v_e_1046_, 0);
v_type_1163_ = lean_ctor_get(v_e_1046_, 1);
v_value_1164_ = lean_ctor_get(v_e_1046_, 2);
v_body_1165_ = lean_ctor_get(v_e_1046_, 3);
v_nondep_1166_ = lean_ctor_get_uint8(v_e_1046_, sizeof(void*)*4 + 8);
lean_inc(v_offset_1047_);
lean_inc_ref(v_type_1163_);
v___x_1167_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1043_, v_beginIdx_1044_, v_subst_1045_, v_type_1163_, v_offset_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_);
if (lean_obj_tag(v___x_1167_) == 0)
{
lean_object* v_a_1168_; lean_object* v_a_1169_; lean_object* v_fst_1170_; lean_object* v_snd_1171_; lean_object* v___x_1172_; 
v_a_1168_ = lean_ctor_get(v___x_1167_, 0);
lean_inc(v_a_1168_);
v_a_1169_ = lean_ctor_get(v___x_1167_, 1);
lean_inc(v_a_1169_);
lean_dec_ref_known(v___x_1167_, 2);
v_fst_1170_ = lean_ctor_get(v_a_1168_, 0);
lean_inc(v_fst_1170_);
v_snd_1171_ = lean_ctor_get(v_a_1168_, 1);
lean_inc(v_snd_1171_);
lean_dec(v_a_1168_);
lean_inc(v_offset_1047_);
lean_inc_ref(v_value_1164_);
v___x_1172_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1043_, v_beginIdx_1044_, v_subst_1045_, v_value_1164_, v_offset_1047_, v_snd_1171_, v_a_1049_, v_a_1050_, v_a_1169_);
if (lean_obj_tag(v___x_1172_) == 0)
{
lean_object* v_a_1173_; lean_object* v_a_1174_; lean_object* v_fst_1175_; lean_object* v_snd_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; 
v_a_1173_ = lean_ctor_get(v___x_1172_, 0);
lean_inc(v_a_1173_);
v_a_1174_ = lean_ctor_get(v___x_1172_, 1);
lean_inc(v_a_1174_);
lean_dec_ref_known(v___x_1172_, 2);
v_fst_1175_ = lean_ctor_get(v_a_1173_, 0);
lean_inc(v_fst_1175_);
v_snd_1176_ = lean_ctor_get(v_a_1173_, 1);
lean_inc(v_snd_1176_);
lean_dec(v_a_1173_);
v___x_1177_ = lean_unsigned_to_nat(1u);
v___x_1178_ = lean_nat_add(v_offset_1047_, v___x_1177_);
lean_dec(v_offset_1047_);
lean_inc_ref(v_body_1165_);
v___x_1179_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1043_, v_beginIdx_1044_, v_subst_1045_, v_body_1165_, v___x_1178_, v_snd_1176_, v_a_1049_, v_a_1050_, v_a_1174_);
if (lean_obj_tag(v___x_1179_) == 0)
{
lean_object* v_a_1180_; lean_object* v_a_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1209_; 
v_a_1180_ = lean_ctor_get(v___x_1179_, 0);
v_a_1181_ = lean_ctor_get(v___x_1179_, 1);
v_isSharedCheck_1209_ = !lean_is_exclusive(v___x_1179_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1183_ = v___x_1179_;
v_isShared_1184_ = v_isSharedCheck_1209_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_a_1181_);
lean_inc(v_a_1180_);
lean_dec(v___x_1179_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1209_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v_fst_1185_; lean_object* v_snd_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1208_; 
v_fst_1185_ = lean_ctor_get(v_a_1180_, 0);
v_snd_1186_ = lean_ctor_get(v_a_1180_, 1);
v_isSharedCheck_1208_ = !lean_is_exclusive(v_a_1180_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1188_ = v_a_1180_;
v_isShared_1189_ = v_isSharedCheck_1208_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_snd_1186_);
lean_inc(v_fst_1185_);
lean_dec(v_a_1180_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1208_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
size_t v___x_1190_; size_t v___x_1191_; uint8_t v___x_1192_; 
v___x_1190_ = lean_ptr_addr(v_type_1163_);
v___x_1191_ = lean_ptr_addr(v_fst_1170_);
v___x_1192_ = lean_usize_dec_eq(v___x_1190_, v___x_1191_);
if (v___x_1192_ == 0)
{
lean_object* v___x_1193_; 
lean_inc(v_declName_1162_);
lean_del_object(v___x_1188_);
lean_del_object(v___x_1183_);
lean_dec_ref_known(v_e_1046_, 4);
v___x_1193_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__5(v_declName_1162_, v_fst_1170_, v_fst_1175_, v_fst_1185_, v_nondep_1166_, v_snd_1186_, v_a_1049_, v_a_1050_, v_a_1181_);
return v___x_1193_;
}
else
{
size_t v___x_1194_; size_t v___x_1195_; uint8_t v___x_1196_; 
v___x_1194_ = lean_ptr_addr(v_value_1164_);
v___x_1195_ = lean_ptr_addr(v_fst_1175_);
v___x_1196_ = lean_usize_dec_eq(v___x_1194_, v___x_1195_);
if (v___x_1196_ == 0)
{
lean_object* v___x_1197_; 
lean_inc(v_declName_1162_);
lean_del_object(v___x_1188_);
lean_del_object(v___x_1183_);
lean_dec_ref_known(v_e_1046_, 4);
v___x_1197_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__5(v_declName_1162_, v_fst_1170_, v_fst_1175_, v_fst_1185_, v_nondep_1166_, v_snd_1186_, v_a_1049_, v_a_1050_, v_a_1181_);
return v___x_1197_;
}
else
{
size_t v___x_1198_; size_t v___x_1199_; uint8_t v___x_1200_; 
v___x_1198_ = lean_ptr_addr(v_body_1165_);
v___x_1199_ = lean_ptr_addr(v_fst_1185_);
v___x_1200_ = lean_usize_dec_eq(v___x_1198_, v___x_1199_);
if (v___x_1200_ == 0)
{
lean_object* v___x_1201_; 
lean_inc(v_declName_1162_);
lean_del_object(v___x_1188_);
lean_del_object(v___x_1183_);
lean_dec_ref_known(v_e_1046_, 4);
v___x_1201_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__5(v_declName_1162_, v_fst_1170_, v_fst_1175_, v_fst_1185_, v_nondep_1166_, v_snd_1186_, v_a_1049_, v_a_1050_, v_a_1181_);
return v___x_1201_;
}
else
{
lean_object* v___x_1203_; 
lean_dec(v_fst_1185_);
lean_dec(v_fst_1175_);
lean_dec(v_fst_1170_);
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 0, v_e_1046_);
v___x_1203_ = v___x_1188_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_e_1046_);
lean_ctor_set(v_reuseFailAlloc_1207_, 1, v_snd_1186_);
v___x_1203_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
lean_object* v___x_1205_; 
if (v_isShared_1184_ == 0)
{
lean_ctor_set(v___x_1183_, 0, v___x_1203_);
v___x_1205_ = v___x_1183_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v___x_1203_);
lean_ctor_set(v_reuseFailAlloc_1206_, 1, v_a_1181_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
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
lean_dec(v_fst_1175_);
lean_dec(v_fst_1170_);
lean_dec_ref_known(v_e_1046_, 4);
return v___x_1179_;
}
}
else
{
lean_dec(v_fst_1170_);
lean_dec_ref_known(v_e_1046_, 4);
lean_dec(v_offset_1047_);
return v___x_1172_;
}
}
else
{
lean_dec_ref_known(v_e_1046_, 4);
lean_dec(v_offset_1047_);
return v___x_1167_;
}
}
case 10:
{
lean_object* v_data_1210_; lean_object* v_expr_1211_; lean_object* v___x_1212_; 
v_data_1210_ = lean_ctor_get(v_e_1046_, 0);
v_expr_1211_ = lean_ctor_get(v_e_1046_, 1);
lean_inc_ref(v_expr_1211_);
v___x_1212_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1043_, v_beginIdx_1044_, v_subst_1045_, v_expr_1211_, v_offset_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_);
if (lean_obj_tag(v___x_1212_) == 0)
{
lean_object* v_a_1213_; lean_object* v_a_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1234_; 
v_a_1213_ = lean_ctor_get(v___x_1212_, 0);
v_a_1214_ = lean_ctor_get(v___x_1212_, 1);
v_isSharedCheck_1234_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1216_ = v___x_1212_;
v_isShared_1217_ = v_isSharedCheck_1234_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_a_1214_);
lean_inc(v_a_1213_);
lean_dec(v___x_1212_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1234_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v_fst_1218_; lean_object* v_snd_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1233_; 
v_fst_1218_ = lean_ctor_get(v_a_1213_, 0);
v_snd_1219_ = lean_ctor_get(v_a_1213_, 1);
v_isSharedCheck_1233_ = !lean_is_exclusive(v_a_1213_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1221_ = v_a_1213_;
v_isShared_1222_ = v_isSharedCheck_1233_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_snd_1219_);
lean_inc(v_fst_1218_);
lean_dec(v_a_1213_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1233_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
size_t v___x_1223_; size_t v___x_1224_; uint8_t v___x_1225_; 
v___x_1223_ = lean_ptr_addr(v_expr_1211_);
v___x_1224_ = lean_ptr_addr(v_fst_1218_);
v___x_1225_ = lean_usize_dec_eq(v___x_1223_, v___x_1224_);
if (v___x_1225_ == 0)
{
lean_object* v___x_1226_; 
lean_inc(v_data_1210_);
lean_del_object(v___x_1221_);
lean_del_object(v___x_1216_);
lean_dec_ref_known(v_e_1046_, 2);
v___x_1226_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__6(v_data_1210_, v_fst_1218_, v_snd_1219_, v_a_1049_, v_a_1050_, v_a_1214_);
return v___x_1226_;
}
else
{
lean_object* v___x_1228_; 
lean_dec(v_fst_1218_);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 0, v_e_1046_);
v___x_1228_ = v___x_1221_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_e_1046_);
lean_ctor_set(v_reuseFailAlloc_1232_, 1, v_snd_1219_);
v___x_1228_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
lean_object* v___x_1230_; 
if (v_isShared_1217_ == 0)
{
lean_ctor_set(v___x_1216_, 0, v___x_1228_);
v___x_1230_ = v___x_1216_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v___x_1228_);
lean_ctor_set(v_reuseFailAlloc_1231_, 1, v_a_1214_);
v___x_1230_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
return v___x_1230_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_1046_, 2);
return v___x_1212_;
}
}
case 11:
{
lean_object* v_typeName_1235_; lean_object* v_idx_1236_; lean_object* v_struct_1237_; lean_object* v___x_1238_; 
v_typeName_1235_ = lean_ctor_get(v_e_1046_, 0);
v_idx_1236_ = lean_ctor_get(v_e_1046_, 1);
v_struct_1237_ = lean_ctor_get(v_e_1046_, 2);
lean_inc_ref(v_struct_1237_);
v___x_1238_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1043_, v_beginIdx_1044_, v_subst_1045_, v_struct_1237_, v_offset_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_);
if (lean_obj_tag(v___x_1238_) == 0)
{
lean_object* v_a_1239_; lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1260_; 
v_a_1239_ = lean_ctor_get(v___x_1238_, 0);
v_a_1240_ = lean_ctor_get(v___x_1238_, 1);
v_isSharedCheck_1260_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1242_ = v___x_1238_;
v_isShared_1243_ = v_isSharedCheck_1260_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_inc(v_a_1239_);
lean_dec(v___x_1238_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1260_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v_fst_1244_; lean_object* v_snd_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1259_; 
v_fst_1244_ = lean_ctor_get(v_a_1239_, 0);
v_snd_1245_ = lean_ctor_get(v_a_1239_, 1);
v_isSharedCheck_1259_ = !lean_is_exclusive(v_a_1239_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1247_ = v_a_1239_;
v_isShared_1248_ = v_isSharedCheck_1259_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_snd_1245_);
lean_inc(v_fst_1244_);
lean_dec(v_a_1239_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1259_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
size_t v___x_1249_; size_t v___x_1250_; uint8_t v___x_1251_; 
v___x_1249_ = lean_ptr_addr(v_struct_1237_);
v___x_1250_ = lean_ptr_addr(v_fst_1244_);
v___x_1251_ = lean_usize_dec_eq(v___x_1249_, v___x_1250_);
if (v___x_1251_ == 0)
{
lean_object* v___x_1252_; 
lean_inc(v_idx_1236_);
lean_inc(v_typeName_1235_);
lean_del_object(v___x_1247_);
lean_del_object(v___x_1242_);
lean_dec_ref_known(v_e_1046_, 3);
v___x_1252_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__7(v_typeName_1235_, v_idx_1236_, v_fst_1244_, v_snd_1245_, v_a_1049_, v_a_1050_, v_a_1240_);
return v___x_1252_;
}
else
{
lean_object* v___x_1254_; 
lean_dec(v_fst_1244_);
if (v_isShared_1248_ == 0)
{
lean_ctor_set(v___x_1247_, 0, v_e_1046_);
v___x_1254_ = v___x_1247_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_e_1046_);
lean_ctor_set(v_reuseFailAlloc_1258_, 1, v_snd_1245_);
v___x_1254_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
lean_object* v___x_1256_; 
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 0, v___x_1254_);
v___x_1256_ = v___x_1242_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v___x_1254_);
lean_ctor_set(v_reuseFailAlloc_1257_, 1, v_a_1240_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_1046_, 3);
return v___x_1238_;
}
}
default: 
{
lean_object* v___x_1261_; lean_object* v___x_1262_; 
lean_dec(v_offset_1047_);
lean_dec_ref(v_e_1046_);
v___x_1261_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__3);
v___x_1262_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8(v___x_1261_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_);
return v___x_1262_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_1043_ = stack[0].m_obj;
lean_object* v_beginIdx_1044_ = stack[1].m_obj;
lean_object* v_subst_1045_ = stack[2].m_obj;
lean_object* v_e_1046_ = stack[3].m_obj;
lean_object* v_offset_1047_ = stack[4].m_obj;
lean_object* v_a_1048_ = stack[5].m_obj;
uint8_t v_a_1049_ = stack[6].m_num;
lean_object* v_a_1050_ = stack[7].m_obj;
lean_object* v_a_1051_ = stack[8].m_obj;
lean_object* v_res_1263_;
v_res_1263_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0(v_n_1043_, v_beginIdx_1044_, v_subst_1045_, v_e_1046_, v_offset_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_);
stack->m_obj
 = v_res_1263_;
}
lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(lean_object* v_n_1264_, lean_object* v_beginIdx_1265_, lean_object* v_subst_1266_, lean_object* v_e_1267_, lean_object* v_offset_1268_, lean_object* v_a_1269_, uint8_t v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_){
_start:
{
lean_object* v_key_1273_; lean_object* v___x_1274_; 
lean_inc(v_offset_1268_);
lean_inc_ref(v_e_1267_);
v_key_1273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1273_, 0, v_e_1267_);
lean_ctor_set(v_key_1273_, 1, v_offset_1268_);
v___x_1274_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3___redArg(v_a_1269_, v_key_1273_);
if (lean_obj_tag(v___x_1274_) == 1)
{
lean_object* v_val_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; 
lean_dec_ref_known(v_key_1273_, 2);
lean_dec(v_offset_1268_);
lean_dec_ref(v_e_1267_);
v_val_1275_ = lean_ctor_get(v___x_1274_, 0);
lean_inc(v_val_1275_);
lean_dec_ref_known(v___x_1274_, 1);
v___x_1276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1276_, 0, v_val_1275_);
lean_ctor_set(v___x_1276_, 1, v_a_1269_);
v___x_1277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1277_, 0, v___x_1276_);
lean_ctor_set(v___x_1277_, 1, v_a_1272_);
return v___x_1277_;
}
else
{
lean_dec(v___x_1274_);
switch(lean_obj_tag(v_e_1267_))
{
case 0:
{
lean_object* v_deBruijnIndex_1278_; uint8_t v___x_1279_; 
v_deBruijnIndex_1278_ = lean_ctor_get(v_e_1267_, 0);
v___x_1279_ = lean_nat_dec_le(v_offset_1268_, v_deBruijnIndex_1278_);
if (v___x_1279_ == 0)
{
lean_object* v___x_1280_; 
lean_dec(v_offset_1268_);
v___x_1280_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1273_, v_e_1267_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
return v___x_1280_;
}
else
{
lean_object* v___x_1281_; uint8_t v___x_1282_; 
lean_inc(v_deBruijnIndex_1278_);
lean_dec_ref_known(v_e_1267_, 1);
v___x_1281_ = lean_nat_add(v_offset_1268_, v_n_1264_);
v___x_1282_ = lean_nat_dec_lt(v_deBruijnIndex_1278_, v___x_1281_);
lean_dec(v___x_1281_);
if (v___x_1282_ == 0)
{
lean_object* v___x_1283_; lean_object* v___x_1284_; 
lean_dec(v_offset_1268_);
v___x_1283_ = lean_nat_sub(v_deBruijnIndex_1278_, v_n_1264_);
lean_dec(v_deBruijnIndex_1278_);
v___x_1284_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___redArg(v___x_1283_, v_a_1272_);
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_object* v_a_1285_; lean_object* v_a_1286_; lean_object* v___x_1287_; 
v_a_1285_ = lean_ctor_get(v___x_1284_, 0);
lean_inc(v_a_1285_);
v_a_1286_ = lean_ctor_get(v___x_1284_, 1);
lean_inc(v_a_1286_);
lean_dec_ref_known(v___x_1284_, 2);
v___x_1287_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1273_, v_a_1285_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1286_);
return v___x_1287_;
}
else
{
lean_object* v_a_1288_; lean_object* v_a_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1296_; 
lean_dec_ref_known(v_key_1273_, 2);
lean_dec_ref(v_a_1269_);
v_a_1288_ = lean_ctor_get(v___x_1284_, 0);
v_a_1289_ = lean_ctor_get(v___x_1284_, 1);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1291_ = v___x_1284_;
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_a_1289_);
lean_inc(v_a_1288_);
lean_dec(v___x_1284_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v___x_1294_; 
if (v_isShared_1292_ == 0)
{
v___x_1294_ = v___x_1291_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_a_1288_);
lean_ctor_set(v_reuseFailAlloc_1295_, 1, v_a_1289_);
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
else
{
lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v_v_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1297_ = lean_nat_add(v_beginIdx_1265_, v_deBruijnIndex_1278_);
lean_dec(v_deBruijnIndex_1278_);
v___x_1298_ = lean_nat_sub(v___x_1297_, v_offset_1268_);
lean_dec(v___x_1297_);
v_v_1299_ = lean_array_fget_borrowed(v_subst_1266_, v___x_1298_);
lean_dec(v___x_1298_);
v___x_1300_ = lean_unsigned_to_nat(0u);
lean_inc(v_v_1299_);
v___x_1301_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(v_v_1299_, v___x_1300_, v_offset_1268_, v_a_1270_, v_a_1271_, v_a_1272_);
lean_dec(v_offset_1268_);
if (lean_obj_tag(v___x_1301_) == 0)
{
lean_object* v_a_1302_; lean_object* v_a_1303_; lean_object* v___x_1304_; 
v_a_1302_ = lean_ctor_get(v___x_1301_, 0);
lean_inc(v_a_1302_);
v_a_1303_ = lean_ctor_get(v___x_1301_, 1);
lean_inc(v_a_1303_);
lean_dec_ref_known(v___x_1301_, 2);
v___x_1304_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1273_, v_a_1302_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1303_);
return v___x_1304_;
}
else
{
lean_object* v_a_1305_; lean_object* v_a_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1313_; 
lean_dec_ref_known(v_key_1273_, 2);
lean_dec_ref(v_a_1269_);
v_a_1305_ = lean_ctor_get(v___x_1301_, 0);
v_a_1306_ = lean_ctor_get(v___x_1301_, 1);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1308_ = v___x_1301_;
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_a_1306_);
lean_inc(v_a_1305_);
lean_dec(v___x_1301_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v___x_1311_; 
if (v_isShared_1309_ == 0)
{
v___x_1311_ = v___x_1308_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v_a_1305_);
lean_ctor_set(v_reuseFailAlloc_1312_, 1, v_a_1306_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
}
}
}
}
case 9:
{
lean_object* v___x_1314_; 
lean_dec(v_offset_1268_);
v___x_1314_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1273_, v_e_1267_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
return v___x_1314_;
}
case 2:
{
lean_object* v___x_1315_; 
lean_dec(v_offset_1268_);
v___x_1315_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1273_, v_e_1267_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
return v___x_1315_;
}
case 1:
{
lean_object* v___x_1316_; 
lean_dec(v_offset_1268_);
v___x_1316_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1273_, v_e_1267_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
return v___x_1316_;
}
case 4:
{
lean_object* v___x_1317_; 
lean_dec(v_offset_1268_);
v___x_1317_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1273_, v_e_1267_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
return v___x_1317_;
}
case 3:
{
lean_object* v___x_1318_; 
lean_dec(v_offset_1268_);
v___x_1318_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1273_, v_e_1267_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
return v___x_1318_;
}
default: 
{
lean_object* v___x_1319_; uint8_t v___x_1320_; 
v___x_1319_ = l_Lean_Expr_looseBVarRange(v_e_1267_);
v___x_1320_ = lean_nat_dec_le(v___x_1319_, v_offset_1268_);
lean_dec(v___x_1319_);
if (v___x_1320_ == 0)
{
switch(lean_obj_tag(v_e_1267_))
{
case 9:
{
lean_object* v___x_1321_; 
lean_dec(v_offset_1268_);
v___x_1321_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1273_, v_e_1267_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
return v___x_1321_;
}
case 2:
{
lean_object* v___x_1322_; 
lean_dec(v_offset_1268_);
v___x_1322_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1273_, v_e_1267_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
return v___x_1322_;
}
case 0:
{
lean_object* v___x_1323_; 
lean_dec(v_offset_1268_);
v___x_1323_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1273_, v_e_1267_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
return v___x_1323_;
}
case 1:
{
lean_object* v___x_1324_; 
lean_dec(v_offset_1268_);
v___x_1324_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1273_, v_e_1267_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
return v___x_1324_;
}
case 4:
{
lean_object* v___x_1325_; 
lean_dec(v_offset_1268_);
v___x_1325_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1273_, v_e_1267_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
return v___x_1325_;
}
case 3:
{
lean_object* v___x_1326_; 
lean_dec(v_offset_1268_);
v___x_1326_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1273_, v_e_1267_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
return v___x_1326_;
}
default: 
{
lean_object* v___x_1327_; 
v___x_1327_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0(v_n_1264_, v_beginIdx_1265_, v_subst_1266_, v_e_1267_, v_offset_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
if (lean_obj_tag(v___x_1327_) == 0)
{
lean_object* v_a_1328_; lean_object* v_a_1329_; lean_object* v_fst_1330_; lean_object* v_snd_1331_; lean_object* v___x_1332_; 
v_a_1328_ = lean_ctor_get(v___x_1327_, 0);
lean_inc(v_a_1328_);
v_a_1329_ = lean_ctor_get(v___x_1327_, 1);
lean_inc(v_a_1329_);
lean_dec_ref_known(v___x_1327_, 2);
v_fst_1330_ = lean_ctor_get(v_a_1328_, 0);
lean_inc(v_fst_1330_);
v_snd_1331_ = lean_ctor_get(v_a_1328_, 1);
lean_inc(v_snd_1331_);
lean_dec(v_a_1328_);
v___x_1332_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1273_, v_fst_1330_, v_snd_1331_, v_a_1270_, v_a_1271_, v_a_1329_);
return v___x_1332_;
}
else
{
lean_dec_ref_known(v_key_1273_, 2);
return v___x_1327_;
}
}
}
}
else
{
lean_object* v___x_1333_; 
lean_dec(v_offset_1268_);
v___x_1333_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1273_, v_e_1267_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
return v___x_1333_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_1264_ = stack[0].m_obj;
lean_object* v_beginIdx_1265_ = stack[1].m_obj;
lean_object* v_subst_1266_ = stack[2].m_obj;
lean_object* v_e_1267_ = stack[3].m_obj;
lean_object* v_offset_1268_ = stack[4].m_obj;
lean_object* v_a_1269_ = stack[5].m_obj;
uint8_t v_a_1270_ = stack[6].m_num;
lean_object* v_a_1271_ = stack[7].m_obj;
lean_object* v_a_1272_ = stack[8].m_obj;
lean_object* v_res_1334_;
v_res_1334_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1264_, v_beginIdx_1265_, v_subst_1266_, v_e_1267_, v_offset_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
stack->m_obj
 = v_res_1334_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0___boxed(lean_object* v_n_1335_, lean_object* v_beginIdx_1336_, lean_object* v_subst_1337_, lean_object* v_e_1338_, lean_object* v_offset_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_){
_start:
{
uint8_t v_a_boxed_1344_; lean_object* v_res_1345_; 
v_a_boxed_1344_ = lean_unbox(v_a_1341_);
v_res_1345_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1335_, v_beginIdx_1336_, v_subst_1337_, v_e_1338_, v_offset_1339_, v_a_1340_, v_a_boxed_1344_, v_a_1342_, v_a_1343_);
lean_dec_ref(v_a_1342_);
lean_dec_ref(v_subst_1337_);
lean_dec(v_beginIdx_1336_);
lean_dec(v_n_1335_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0___boxed(lean_object* v_n_1346_, lean_object* v_beginIdx_1347_, lean_object* v_subst_1348_, lean_object* v_e_1349_, lean_object* v_offset_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_){
_start:
{
uint8_t v_a_boxed_1355_; lean_object* v_res_1356_; 
v_a_boxed_1355_ = lean_unbox(v_a_1352_);
v_res_1356_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0(v_n_1346_, v_beginIdx_1347_, v_subst_1348_, v_e_1349_, v_offset_1350_, v_a_1351_, v_a_boxed_1355_, v_a_1353_, v_a_1354_);
lean_dec_ref(v_a_1353_);
lean_dec_ref(v_subst_1348_);
lean_dec(v_beginIdx_1347_);
lean_dec(v_n_1346_);
return v_res_1356_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__1(void){
_start:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1358_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__2));
v___x_1359_ = lean_unsigned_to_nat(34u);
v___x_1360_ = lean_unsigned_to_nat(57u);
v___x_1361_ = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__0));
v___x_1362_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__3));
v___x_1363_ = l_mkPanicMessageWithDecl(v___x_1362_, v___x_1361_, v___x_1360_, v___x_1359_, v___x_1358_);
return v___x_1363_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__2(void){
_start:
{
lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1364_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__2));
v___x_1365_ = lean_unsigned_to_nat(32u);
v___x_1366_ = lean_unsigned_to_nat(56u);
v___x_1367_ = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__0));
v___x_1368_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__3));
v___x_1369_ = l_mkPanicMessageWithDecl(v___x_1368_, v___x_1367_, v___x_1366_, v___x_1365_, v___x_1364_);
return v___x_1369_;
}
}
lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27(lean_object* v_e_1370_, lean_object* v_beginIdx_1371_, lean_object* v_endIdx_1372_, lean_object* v_subst_1373_, uint8_t v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_){
_start:
{
uint8_t v___x_1377_; 
v___x_1377_ = lean_nat_dec_lt(v_endIdx_1372_, v_beginIdx_1371_);
if (v___x_1377_ == 0)
{
lean_object* v___x_1378_; uint8_t v___x_1379_; 
v___x_1378_ = lean_array_get_size(v_subst_1373_);
v___x_1379_ = lean_nat_dec_lt(v___x_1378_, v_endIdx_1372_);
if (v___x_1379_ == 0)
{
lean_object* v_n_1380_; lean_object* v___x_1381_; 
v_n_1380_ = lean_nat_sub(v_endIdx_1372_, v_beginIdx_1371_);
v___x_1381_ = lean_unsigned_to_nat(0u);
switch(lean_obj_tag(v_e_1370_))
{
case 0:
{
lean_object* v_deBruijnIndex_1382_; uint8_t v___x_1383_; 
v_deBruijnIndex_1382_ = lean_ctor_get(v_e_1370_, 0);
v___x_1383_ = lean_nat_dec_le(v___x_1381_, v_deBruijnIndex_1382_);
if (v___x_1383_ == 0)
{
lean_object* v___x_1384_; 
lean_dec(v_n_1380_);
v___x_1384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1384_, 0, v_e_1370_);
lean_ctor_set(v___x_1384_, 1, v_a_1376_);
return v___x_1384_;
}
else
{
uint8_t v___x_1385_; 
lean_inc(v_deBruijnIndex_1382_);
lean_dec_ref_known(v_e_1370_, 1);
v___x_1385_ = lean_nat_dec_lt(v_deBruijnIndex_1382_, v_n_1380_);
if (v___x_1385_ == 0)
{
lean_object* v___x_1386_; lean_object* v___x_1387_; 
v___x_1386_ = lean_nat_sub(v_deBruijnIndex_1382_, v_n_1380_);
lean_dec(v_n_1380_);
lean_dec(v_deBruijnIndex_1382_);
v___x_1387_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___redArg(v___x_1386_, v_a_1376_);
return v___x_1387_;
}
else
{
lean_object* v___x_1388_; lean_object* v_v_1389_; lean_object* v___x_1390_; 
lean_dec(v_n_1380_);
v___x_1388_ = lean_nat_add(v_beginIdx_1371_, v_deBruijnIndex_1382_);
lean_dec(v_deBruijnIndex_1382_);
v_v_1389_ = lean_array_fget_borrowed(v_subst_1373_, v___x_1388_);
lean_dec(v___x_1388_);
lean_inc(v_v_1389_);
v___x_1390_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(v_v_1389_, v___x_1381_, v___x_1381_, v_a_1374_, v_a_1375_, v_a_1376_);
return v___x_1390_;
}
}
}
case 9:
{
lean_object* v___x_1391_; 
lean_dec(v_n_1380_);
v___x_1391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1391_, 0, v_e_1370_);
lean_ctor_set(v___x_1391_, 1, v_a_1376_);
return v___x_1391_;
}
case 2:
{
lean_object* v___x_1392_; 
lean_dec(v_n_1380_);
v___x_1392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1392_, 0, v_e_1370_);
lean_ctor_set(v___x_1392_, 1, v_a_1376_);
return v___x_1392_;
}
case 1:
{
lean_object* v___x_1393_; 
lean_dec(v_n_1380_);
v___x_1393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1393_, 0, v_e_1370_);
lean_ctor_set(v___x_1393_, 1, v_a_1376_);
return v___x_1393_;
}
case 4:
{
lean_object* v___x_1394_; 
lean_dec(v_n_1380_);
v___x_1394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1394_, 0, v_e_1370_);
lean_ctor_set(v___x_1394_, 1, v_a_1376_);
return v___x_1394_;
}
case 3:
{
lean_object* v___x_1395_; 
lean_dec(v_n_1380_);
v___x_1395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1395_, 0, v_e_1370_);
lean_ctor_set(v___x_1395_, 1, v_a_1376_);
return v___x_1395_;
}
default: 
{
lean_object* v___x_1396_; uint8_t v___x_1397_; 
v___x_1396_ = l_Lean_Expr_looseBVarRange(v_e_1370_);
v___x_1397_ = lean_nat_dec_le(v___x_1396_, v___x_1381_);
lean_dec(v___x_1396_);
if (v___x_1397_ == 0)
{
switch(lean_obj_tag(v_e_1370_))
{
case 9:
{
lean_object* v___x_1398_; 
lean_dec(v_n_1380_);
v___x_1398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1398_, 0, v_e_1370_);
lean_ctor_set(v___x_1398_, 1, v_a_1376_);
return v___x_1398_;
}
case 2:
{
lean_object* v___x_1399_; 
lean_dec(v_n_1380_);
v___x_1399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1399_, 0, v_e_1370_);
lean_ctor_set(v___x_1399_, 1, v_a_1376_);
return v___x_1399_;
}
case 0:
{
lean_object* v___x_1400_; 
lean_dec(v_n_1380_);
v___x_1400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1400_, 0, v_e_1370_);
lean_ctor_set(v___x_1400_, 1, v_a_1376_);
return v___x_1400_;
}
case 1:
{
lean_object* v___x_1401_; 
lean_dec(v_n_1380_);
v___x_1401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1401_, 0, v_e_1370_);
lean_ctor_set(v___x_1401_, 1, v_a_1376_);
return v___x_1401_;
}
case 4:
{
lean_object* v___x_1402_; 
lean_dec(v_n_1380_);
v___x_1402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1402_, 0, v_e_1370_);
lean_ctor_set(v___x_1402_, 1, v_a_1376_);
return v___x_1402_;
}
case 3:
{
lean_object* v___x_1403_; 
lean_dec(v_n_1380_);
v___x_1403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1403_, 0, v_e_1370_);
lean_ctor_set(v___x_1403_, 1, v_a_1376_);
return v___x_1403_;
}
default: 
{
lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1404_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__1, &l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__1_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__1);
v___x_1405_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0(v_n_1380_, v_beginIdx_1371_, v_subst_1373_, v_e_1370_, v___x_1381_, v___x_1404_, v_a_1374_, v_a_1375_, v_a_1376_);
lean_dec(v_n_1380_);
if (lean_obj_tag(v___x_1405_) == 0)
{
lean_object* v_a_1406_; lean_object* v_a_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1415_; 
v_a_1406_ = lean_ctor_get(v___x_1405_, 0);
v_a_1407_ = lean_ctor_get(v___x_1405_, 1);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1409_ = v___x_1405_;
v_isShared_1410_ = v_isSharedCheck_1415_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_a_1407_);
lean_inc(v_a_1406_);
lean_dec(v___x_1405_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1415_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v_fst_1411_; lean_object* v___x_1413_; 
v_fst_1411_ = lean_ctor_get(v_a_1406_, 0);
lean_inc(v_fst_1411_);
lean_dec(v_a_1406_);
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 0, v_fst_1411_);
v___x_1413_ = v___x_1409_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_fst_1411_);
lean_ctor_set(v_reuseFailAlloc_1414_, 1, v_a_1407_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
}
else
{
lean_object* v_a_1416_; lean_object* v_a_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1424_; 
v_a_1416_ = lean_ctor_get(v___x_1405_, 0);
v_a_1417_ = lean_ctor_get(v___x_1405_, 1);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1419_ = v___x_1405_;
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_a_1417_);
lean_inc(v_a_1416_);
lean_dec(v___x_1405_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v___x_1422_; 
if (v_isShared_1420_ == 0)
{
v___x_1422_ = v___x_1419_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_a_1416_);
lean_ctor_set(v_reuseFailAlloc_1423_, 1, v_a_1417_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
}
}
}
}
}
}
else
{
lean_object* v___x_1425_; 
lean_dec(v_n_1380_);
v___x_1425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1425_, 0, v_e_1370_);
lean_ctor_set(v___x_1425_, 1, v_a_1376_);
return v___x_1425_;
}
}
}
}
else
{
lean_object* v___x_1426_; lean_object* v___x_1427_; 
lean_dec_ref(v_e_1370_);
v___x_1426_ = lean_obj_once(&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__1, &l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__1_once, _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__1);
v___x_1427_ = l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1(v___x_1426_, v_a_1374_, v_a_1375_, v_a_1376_);
return v___x_1427_;
}
}
else
{
lean_object* v___x_1428_; lean_object* v___x_1429_; 
lean_dec_ref(v_e_1370_);
v___x_1428_ = lean_obj_once(&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__2, &l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__2_once, _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__2);
v___x_1429_ = l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1(v___x_1428_, v_a_1374_, v_a_1375_, v_a_1376_);
return v___x_1429_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1370_ = stack[0].m_obj;
lean_object* v_beginIdx_1371_ = stack[1].m_obj;
lean_object* v_endIdx_1372_ = stack[2].m_obj;
lean_object* v_subst_1373_ = stack[3].m_obj;
uint8_t v_a_1374_ = stack[4].m_num;
lean_object* v_a_1375_ = stack[5].m_obj;
lean_object* v_a_1376_ = stack[6].m_obj;
lean_object* v_res_1430_;
v_res_1430_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27(v_e_1370_, v_beginIdx_1371_, v_endIdx_1372_, v_subst_1373_, v_a_1374_, v_a_1375_, v_a_1376_);
stack->m_obj
 = v_res_1430_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___boxed(lean_object* v_e_1431_, lean_object* v_beginIdx_1432_, lean_object* v_endIdx_1433_, lean_object* v_subst_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_){
_start:
{
uint8_t v_a_boxed_1438_; lean_object* v_res_1439_; 
v_a_boxed_1438_ = lean_unbox(v_a_1435_);
v_res_1439_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27(v_e_1431_, v_beginIdx_1432_, v_endIdx_1433_, v_subst_1434_, v_a_boxed_1438_, v_a_1436_, v_a_1437_);
lean_dec_ref(v_a_1436_);
lean_dec_ref(v_subst_1434_);
lean_dec(v_endIdx_1433_);
lean_dec(v_beginIdx_1432_);
return v_res_1439_;
}
}
lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27(lean_object* v_e_1440_, lean_object* v_subst_1441_, uint8_t v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_){
_start:
{
lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1445_ = lean_unsigned_to_nat(0u);
v___x_1446_ = lean_array_get_size(v_subst_1441_);
v___x_1447_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27(v_e_1440_, v___x_1445_, v___x_1446_, v_subst_1441_, v_a_1442_, v_a_1443_, v_a_1444_);
return v___x_1447_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1440_ = stack[0].m_obj;
lean_object* v_subst_1441_ = stack[1].m_obj;
uint8_t v_a_1442_ = stack[2].m_num;
lean_object* v_a_1443_ = stack[3].m_obj;
lean_object* v_a_1444_ = stack[4].m_obj;
lean_object* v_res_1448_;
v_res_1448_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27(v_e_1440_, v_subst_1441_, v_a_1442_, v_a_1443_, v_a_1444_);
stack->m_obj
 = v_res_1448_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27___boxed(lean_object* v_e_1449_, lean_object* v_subst_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_){
_start:
{
uint8_t v_a_boxed_1454_; lean_object* v_res_1455_; 
v_a_boxed_1454_ = lean_unbox(v_a_1451_);
v_res_1455_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27(v_e_1449_, v_subst_1450_, v_a_boxed_1454_, v_a_1452_, v_a_1453_);
lean_dec_ref(v_a_1452_);
lean_dec_ref(v_subst_1450_);
return v_res_1455_;
}
}
lean_object* l_Lean_Meta_Sym_instantiateS(lean_object* v_e_1456_, lean_object* v_subst_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_){
_start:
{
lean_object* v___x_1465_; uint8_t v_debug_1466_; lean_object* v___x_1467_; lean_object* v_env_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; uint8_t v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1465_ = lean_st_ref_get(v_a_1459_);
v_debug_1466_ = lean_ctor_get_uint8(v___x_1465_, sizeof(void*)*12);
lean_dec(v___x_1465_);
v___x_1467_ = lean_st_ref_get(v_a_1463_);
v_env_1468_ = lean_ctor_get(v___x_1467_, 0);
lean_inc_ref(v_env_1468_);
lean_dec(v___x_1467_);
v___x_1469_ = lean_box(v_debug_1466_);
v___x_1470_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27___boxed), 5, 3);
lean_closure_set(v___x_1470_, 0, v_e_1456_);
lean_closure_set(v___x_1470_, 1, v_subst_1457_);
lean_closure_set(v___x_1470_, 2, v___x_1469_);
v___x_1471_ = 0;
v___x_1472_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_1472_, 0, v_env_1468_);
lean_ctor_set_uint8(v___x_1472_, sizeof(void*)*1, v___x_1471_);
lean_ctor_set_uint8(v___x_1472_, sizeof(void*)*1 + 1, v___x_1471_);
v___x_1473_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___x_1470_, v___x_1472_, v_a_1459_);
if (lean_obj_tag(v___x_1473_) == 0)
{
lean_object* v_a_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1484_; 
v_a_1474_ = lean_ctor_get(v___x_1473_, 0);
v_isSharedCheck_1484_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1484_ == 0)
{
v___x_1476_ = v___x_1473_;
v_isShared_1477_ = v_isSharedCheck_1484_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_a_1474_);
lean_dec(v___x_1473_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1484_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
if (lean_obj_tag(v_a_1474_) == 0)
{
lean_object* v___x_1478_; lean_object* v___x_1479_; 
lean_dec_ref_known(v_a_1474_, 1);
lean_del_object(v___x_1476_);
v___x_1478_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__2, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__2_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__2);
v___x_1479_ = l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(v___x_1478_, v_a_1458_, v_a_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_);
return v___x_1479_;
}
else
{
lean_object* v_a_1480_; lean_object* v___x_1482_; 
v_a_1480_ = lean_ctor_get(v_a_1474_, 0);
lean_inc(v_a_1480_);
lean_dec_ref_known(v_a_1474_, 1);
if (v_isShared_1477_ == 0)
{
lean_ctor_set(v___x_1476_, 0, v_a_1480_);
v___x_1482_ = v___x_1476_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v_a_1480_);
v___x_1482_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
return v___x_1482_;
}
}
}
}
else
{
lean_object* v_a_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1492_; 
v_a_1485_ = lean_ctor_get(v___x_1473_, 0);
v_isSharedCheck_1492_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1487_ = v___x_1473_;
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_a_1485_);
lean_dec(v___x_1473_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1490_; 
if (v_isShared_1488_ == 0)
{
v___x_1490_ = v___x_1487_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_a_1485_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_instantiateS_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1456_ = stack[0].m_obj;
lean_object* v_subst_1457_ = stack[1].m_obj;
lean_object* v_a_1458_ = stack[2].m_obj;
lean_object* v_a_1459_ = stack[3].m_obj;
lean_object* v_a_1460_ = stack[4].m_obj;
lean_object* v_a_1461_ = stack[5].m_obj;
lean_object* v_a_1462_ = stack[6].m_obj;
lean_object* v_a_1463_ = stack[7].m_obj;
lean_object* v_res_1493_;
v_res_1493_ = l_Lean_Meta_Sym_instantiateS(v_e_1456_, v_subst_1457_, v_a_1458_, v_a_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_);
stack->m_obj
 = v_res_1493_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateS___boxed(lean_object* v_e_1494_, lean_object* v_subst_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_){
_start:
{
lean_object* v_res_1503_; 
v_res_1503_ = l_Lean_Meta_Sym_instantiateS(v_e_1494_, v_subst_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_);
lean_dec(v_a_1501_);
lean_dec_ref(v_a_1500_);
lean_dec(v_a_1499_);
lean_dec_ref(v_a_1498_);
lean_dec(v_a_1497_);
lean_dec_ref(v_a_1496_);
return v_res_1503_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0_spec__0(lean_object* v_f_1504_, lean_object* v_a_1505_, uint8_t v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
lean_object* v___y_1510_; 
if (v___y_1506_ == 0)
{
v___y_1510_ = v___y_1508_;
goto v___jp_1509_;
}
else
{
lean_object* v___x_1513_; 
v___x_1513_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_f_1504_, v___y_1506_, v___y_1507_, v___y_1508_);
if (lean_obj_tag(v___x_1513_) == 0)
{
lean_object* v_a_1514_; lean_object* v___x_1515_; 
v_a_1514_ = lean_ctor_get(v___x_1513_, 1);
lean_inc(v_a_1514_);
lean_dec_ref_known(v___x_1513_, 2);
v___x_1515_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_a_1505_, v___y_1506_, v___y_1507_, v_a_1514_);
if (lean_obj_tag(v___x_1515_) == 0)
{
lean_object* v_a_1516_; 
v_a_1516_ = lean_ctor_get(v___x_1515_, 1);
lean_inc(v_a_1516_);
lean_dec_ref_known(v___x_1515_, 2);
v___y_1510_ = v_a_1516_;
goto v___jp_1509_;
}
else
{
lean_object* v_a_1517_; lean_object* v_a_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1525_; 
lean_dec_ref(v_a_1505_);
lean_dec_ref(v_f_1504_);
v_a_1517_ = lean_ctor_get(v___x_1515_, 0);
v_a_1518_ = lean_ctor_get(v___x_1515_, 1);
v_isSharedCheck_1525_ = !lean_is_exclusive(v___x_1515_);
if (v_isSharedCheck_1525_ == 0)
{
v___x_1520_ = v___x_1515_;
v_isShared_1521_ = v_isSharedCheck_1525_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_a_1518_);
lean_inc(v_a_1517_);
lean_dec(v___x_1515_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1525_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v___x_1523_; 
if (v_isShared_1521_ == 0)
{
v___x_1523_ = v___x_1520_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v_a_1517_);
lean_ctor_set(v_reuseFailAlloc_1524_, 1, v_a_1518_);
v___x_1523_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
return v___x_1523_;
}
}
}
}
else
{
lean_object* v_a_1526_; lean_object* v_a_1527_; lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1534_; 
lean_dec_ref(v_a_1505_);
lean_dec_ref(v_f_1504_);
v_a_1526_ = lean_ctor_get(v___x_1513_, 0);
v_a_1527_ = lean_ctor_get(v___x_1513_, 1);
v_isSharedCheck_1534_ = !lean_is_exclusive(v___x_1513_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1529_ = v___x_1513_;
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
else
{
lean_inc(v_a_1527_);
lean_inc(v_a_1526_);
lean_dec(v___x_1513_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
lean_object* v___x_1532_; 
if (v_isShared_1530_ == 0)
{
v___x_1532_ = v___x_1529_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_a_1526_);
lean_ctor_set(v_reuseFailAlloc_1533_, 1, v_a_1527_);
v___x_1532_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
return v___x_1532_;
}
}
}
}
v___jp_1509_:
{
lean_object* v___x_1511_; lean_object* v___x_1512_; 
v___x_1511_ = l_Lean_Expr_app___override(v_f_1504_, v_a_1505_);
v___x_1512_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1511_, v___y_1510_);
return v___x_1512_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1504_ = stack[0].m_obj;
lean_object* v_a_1505_ = stack[1].m_obj;
uint8_t v___y_1506_ = stack[2].m_num;
lean_object* v___y_1507_ = stack[3].m_obj;
lean_object* v___y_1508_ = stack[4].m_obj;
lean_object* v_res_1535_;
v_res_1535_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0_spec__0(v_f_1504_, v_a_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
stack->m_obj
 = v_res_1535_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0_spec__0___boxed(lean_object* v_f_1536_, lean_object* v_a_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_){
_start:
{
uint8_t v___y_1315__boxed_1541_; lean_object* v_res_1542_; 
v___y_1315__boxed_1541_ = lean_unbox(v___y_1538_);
v_res_1542_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0_spec__0(v_f_1536_, v_a_1537_, v___y_1315__boxed_1541_, v___y_1539_, v___y_1540_);
lean_dec_ref(v___y_1539_);
return v_res_1542_;
}
}
lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0(lean_object* v_revArgs_1543_, lean_object* v_start_1544_, lean_object* v_b_1545_, lean_object* v_i_1546_, uint8_t v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_){
_start:
{
uint8_t v___x_1550_; 
v___x_1550_ = lean_nat_dec_le(v_i_1546_, v_start_1544_);
if (v___x_1550_ == 0)
{
lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v_i_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1551_ = l_Lean_instInhabitedExpr;
v___x_1552_ = lean_unsigned_to_nat(1u);
v_i_1553_ = lean_nat_sub(v_i_1546_, v___x_1552_);
lean_dec(v_i_1546_);
v___x_1554_ = lean_array_get_borrowed(v___x_1551_, v_revArgs_1543_, v_i_1553_);
lean_inc(v___x_1554_);
v___x_1555_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0_spec__0(v_b_1545_, v___x_1554_, v___y_1547_, v___y_1548_, v___y_1549_);
if (lean_obj_tag(v___x_1555_) == 0)
{
lean_object* v_a_1556_; lean_object* v_a_1557_; 
v_a_1556_ = lean_ctor_get(v___x_1555_, 0);
lean_inc(v_a_1556_);
v_a_1557_ = lean_ctor_get(v___x_1555_, 1);
lean_inc(v_a_1557_);
lean_dec_ref_known(v___x_1555_, 2);
v_b_1545_ = v_a_1556_;
v_i_1546_ = v_i_1553_;
v___y_1549_ = v_a_1557_;
goto _start;
}
else
{
lean_dec(v_i_1553_);
return v___x_1555_;
}
}
else
{
lean_object* v___x_1559_; 
lean_dec(v_i_1546_);
v___x_1559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1559_, 0, v_b_1545_);
lean_ctor_set(v___x_1559_, 1, v___y_1549_);
return v___x_1559_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_revArgs_1543_ = stack[0].m_obj;
lean_object* v_start_1544_ = stack[1].m_obj;
lean_object* v_b_1545_ = stack[2].m_obj;
lean_object* v_i_1546_ = stack[3].m_obj;
uint8_t v___y_1547_ = stack[4].m_num;
lean_object* v___y_1548_ = stack[5].m_obj;
lean_object* v___y_1549_ = stack[6].m_obj;
lean_object* v_res_1560_;
v_res_1560_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0(v_revArgs_1543_, v_start_1544_, v_b_1545_, v_i_1546_, v___y_1547_, v___y_1548_, v___y_1549_);
stack->m_obj
 = v_res_1560_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0___boxed(lean_object* v_revArgs_1561_, lean_object* v_start_1562_, lean_object* v_b_1563_, lean_object* v_i_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_){
_start:
{
uint8_t v___y_1410__boxed_1568_; lean_object* v_res_1569_; 
v___y_1410__boxed_1568_ = lean_unbox(v___y_1565_);
v_res_1569_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0(v_revArgs_1561_, v_start_1562_, v_b_1563_, v_i_1564_, v___y_1410__boxed_1568_, v___y_1566_, v___y_1567_);
lean_dec_ref(v___y_1566_);
lean_dec(v_start_1562_);
lean_dec_ref(v_revArgs_1561_);
return v_res_1569_;
}
}
lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go(lean_object* v_revArgs_1570_, lean_object* v_sz_1571_, lean_object* v_e_1572_, lean_object* v_i_1573_, uint8_t v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_){
_start:
{
switch(lean_obj_tag(v_e_1572_))
{
case 6:
{
lean_object* v_body_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; uint8_t v___x_1580_; 
v_body_1577_ = lean_ctor_get(v_e_1572_, 2);
lean_inc_ref(v_body_1577_);
lean_dec_ref_known(v_e_1572_, 3);
v___x_1578_ = lean_unsigned_to_nat(1u);
v___x_1579_ = lean_nat_add(v_i_1573_, v___x_1578_);
lean_dec(v_i_1573_);
v___x_1580_ = lean_nat_dec_lt(v___x_1579_, v_sz_1571_);
if (v___x_1580_ == 0)
{
lean_object* v___x_1581_; 
lean_dec(v___x_1579_);
v___x_1581_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27(v_body_1577_, v_revArgs_1570_, v_a_1574_, v_a_1575_, v_a_1576_);
return v___x_1581_;
}
else
{
v_e_1572_ = v_body_1577_;
v_i_1573_ = v___x_1579_;
goto _start;
}
}
case 10:
{
lean_object* v_expr_1583_; 
v_expr_1583_ = lean_ctor_get(v_e_1572_, 1);
lean_inc_ref(v_expr_1583_);
lean_dec_ref_known(v_e_1572_, 2);
v_e_1572_ = v_expr_1583_;
goto _start;
}
default: 
{
lean_object* v_n_1585_; lean_object* v___x_1586_; 
v_n_1585_ = lean_nat_sub(v_sz_1571_, v_i_1573_);
lean_dec(v_i_1573_);
v___x_1586_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27(v_e_1572_, v_n_1585_, v_sz_1571_, v_revArgs_1570_, v_a_1574_, v_a_1575_, v_a_1576_);
if (lean_obj_tag(v___x_1586_) == 0)
{
lean_object* v_a_1587_; lean_object* v_a_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
v_a_1587_ = lean_ctor_get(v___x_1586_, 0);
lean_inc(v_a_1587_);
v_a_1588_ = lean_ctor_get(v___x_1586_, 1);
lean_inc(v_a_1588_);
lean_dec_ref_known(v___x_1586_, 2);
v___x_1589_ = lean_unsigned_to_nat(0u);
v___x_1590_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0(v_revArgs_1570_, v___x_1589_, v_a_1587_, v_n_1585_, v_a_1574_, v_a_1575_, v_a_1588_);
return v___x_1590_;
}
else
{
lean_dec(v_n_1585_);
return v___x_1586_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_revArgs_1570_ = stack[0].m_obj;
lean_object* v_sz_1571_ = stack[1].m_obj;
lean_object* v_e_1572_ = stack[2].m_obj;
lean_object* v_i_1573_ = stack[3].m_obj;
uint8_t v_a_1574_ = stack[4].m_num;
lean_object* v_a_1575_ = stack[5].m_obj;
lean_object* v_a_1576_ = stack[6].m_obj;
lean_object* v_res_1591_;
v_res_1591_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go(v_revArgs_1570_, v_sz_1571_, v_e_1572_, v_i_1573_, v_a_1574_, v_a_1575_, v_a_1576_);
stack->m_obj
 = v_res_1591_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go___boxed(lean_object* v_revArgs_1592_, lean_object* v_sz_1593_, lean_object* v_e_1594_, lean_object* v_i_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_){
_start:
{
uint8_t v_a_boxed_1599_; lean_object* v_res_1600_; 
v_a_boxed_1599_ = lean_unbox(v_a_1596_);
v_res_1600_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go(v_revArgs_1592_, v_sz_1593_, v_e_1594_, v_i_1595_, v_a_boxed_1599_, v_a_1597_, v_a_1598_);
lean_dec_ref(v_a_1597_);
lean_dec(v_sz_1593_);
lean_dec_ref(v_revArgs_1592_);
return v_res_1600_;
}
}
lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27(lean_object* v_f_1601_, lean_object* v_revArgs_1602_, uint8_t v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_){
_start:
{
lean_object* v_sz_1606_; lean_object* v___x_1607_; uint8_t v___x_1608_; 
v_sz_1606_ = lean_array_get_size(v_revArgs_1602_);
v___x_1607_ = lean_unsigned_to_nat(0u);
v___x_1608_ = lean_nat_dec_eq(v_sz_1606_, v___x_1607_);
if (v___x_1608_ == 0)
{
lean_object* v___x_1609_; 
v___x_1609_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go(v_revArgs_1602_, v_sz_1606_, v_f_1601_, v___x_1607_, v_a_1603_, v_a_1604_, v_a_1605_);
return v___x_1609_;
}
else
{
lean_object* v___x_1610_; 
v___x_1610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1610_, 0, v_f_1601_);
lean_ctor_set(v___x_1610_, 1, v_a_1605_);
return v___x_1610_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1601_ = stack[0].m_obj;
lean_object* v_revArgs_1602_ = stack[1].m_obj;
uint8_t v_a_1603_ = stack[2].m_num;
lean_object* v_a_1604_ = stack[3].m_obj;
lean_object* v_a_1605_ = stack[4].m_obj;
lean_object* v_res_1611_;
v_res_1611_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27(v_f_1601_, v_revArgs_1602_, v_a_1603_, v_a_1604_, v_a_1605_);
stack->m_obj
 = v_res_1611_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27___boxed(lean_object* v_f_1612_, lean_object* v_revArgs_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_){
_start:
{
uint8_t v_a_boxed_1617_; lean_object* v_res_1618_; 
v_a_boxed_1617_ = lean_unbox(v_a_1614_);
v_res_1618_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27(v_f_1612_, v_revArgs_1613_, v_a_boxed_1617_, v_a_1615_, v_a_1616_);
lean_dec_ref(v_a_1615_);
lean_dec_ref(v_revArgs_1613_);
return v_res_1618_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_1619_, lean_object* v_x_1620_){
_start:
{
if (lean_obj_tag(v_x_1620_) == 0)
{
return v_x_1619_;
}
else
{
lean_object* v_key_1621_; lean_object* v_value_1622_; lean_object* v_tail_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1653_; 
v_key_1621_ = lean_ctor_get(v_x_1620_, 0);
v_value_1622_ = lean_ctor_get(v_x_1620_, 1);
v_tail_1623_ = lean_ctor_get(v_x_1620_, 2);
v_isSharedCheck_1653_ = !lean_is_exclusive(v_x_1620_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1625_ = v_x_1620_;
v_isShared_1626_ = v_isSharedCheck_1653_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_tail_1623_);
lean_inc(v_value_1622_);
lean_inc(v_key_1621_);
lean_dec(v_x_1620_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1653_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v_fst_1627_; lean_object* v_snd_1628_; lean_object* v___x_1629_; size_t v___x_1630_; size_t v___x_1631_; size_t v___x_1632_; uint64_t v___x_1633_; uint64_t v___x_1634_; uint64_t v___x_1635_; uint64_t v___x_1636_; uint64_t v___x_1637_; uint64_t v_fold_1638_; uint64_t v___x_1639_; uint64_t v___x_1640_; uint64_t v___x_1641_; size_t v___x_1642_; size_t v___x_1643_; size_t v___x_1644_; size_t v___x_1645_; size_t v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1649_; 
v_fst_1627_ = lean_ctor_get(v_key_1621_, 0);
v_snd_1628_ = lean_ctor_get(v_key_1621_, 1);
v___x_1629_ = lean_array_get_size(v_x_1619_);
v___x_1630_ = lean_ptr_addr(v_fst_1627_);
v___x_1631_ = ((size_t)3ULL);
v___x_1632_ = lean_usize_shift_right(v___x_1630_, v___x_1631_);
v___x_1633_ = lean_usize_to_uint64(v___x_1632_);
v___x_1634_ = lean_uint64_of_nat(v_snd_1628_);
v___x_1635_ = lean_uint64_mix_hash(v___x_1633_, v___x_1634_);
v___x_1636_ = 32ULL;
v___x_1637_ = lean_uint64_shift_right(v___x_1635_, v___x_1636_);
v_fold_1638_ = lean_uint64_xor(v___x_1635_, v___x_1637_);
v___x_1639_ = 16ULL;
v___x_1640_ = lean_uint64_shift_right(v_fold_1638_, v___x_1639_);
v___x_1641_ = lean_uint64_xor(v_fold_1638_, v___x_1640_);
v___x_1642_ = lean_uint64_to_usize(v___x_1641_);
v___x_1643_ = lean_usize_of_nat(v___x_1629_);
v___x_1644_ = ((size_t)1ULL);
v___x_1645_ = lean_usize_sub(v___x_1643_, v___x_1644_);
v___x_1646_ = lean_usize_land(v___x_1642_, v___x_1645_);
v___x_1647_ = lean_array_uget_borrowed(v_x_1619_, v___x_1646_);
lean_inc(v___x_1647_);
if (v_isShared_1626_ == 0)
{
lean_ctor_set(v___x_1625_, 2, v___x_1647_);
v___x_1649_ = v___x_1625_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v_key_1621_);
lean_ctor_set(v_reuseFailAlloc_1652_, 1, v_value_1622_);
lean_ctor_set(v_reuseFailAlloc_1652_, 2, v___x_1647_);
v___x_1649_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
lean_object* v___x_1650_; 
v___x_1650_ = lean_array_uset(v_x_1619_, v___x_1646_, v___x_1649_);
v_x_1619_ = v___x_1650_;
v_x_1620_ = v_tail_1623_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2___redArg(lean_object* v_i_1654_, lean_object* v_source_1655_, lean_object* v_target_1656_){
_start:
{
lean_object* v___x_1657_; uint8_t v___x_1658_; 
v___x_1657_ = lean_array_get_size(v_source_1655_);
v___x_1658_ = lean_nat_dec_lt(v_i_1654_, v___x_1657_);
if (v___x_1658_ == 0)
{
lean_dec_ref(v_source_1655_);
lean_dec(v_i_1654_);
return v_target_1656_;
}
else
{
lean_object* v_es_1659_; lean_object* v___x_1660_; lean_object* v_source_1661_; lean_object* v_target_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; 
v_es_1659_ = lean_array_fget(v_source_1655_, v_i_1654_);
v___x_1660_ = lean_box(0);
v_source_1661_ = lean_array_fset(v_source_1655_, v_i_1654_, v___x_1660_);
v_target_1662_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3___redArg(v_target_1656_, v_es_1659_);
v___x_1663_ = lean_unsigned_to_nat(1u);
v___x_1664_ = lean_nat_add(v_i_1654_, v___x_1663_);
lean_dec(v_i_1654_);
v_i_1654_ = v___x_1664_;
v_source_1655_ = v_source_1661_;
v_target_1656_ = v_target_1662_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1___redArg(lean_object* v_data_1666_){
_start:
{
lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v_nbuckets_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; 
v___x_1667_ = lean_array_get_size(v_data_1666_);
v___x_1668_ = lean_unsigned_to_nat(2u);
v_nbuckets_1669_ = lean_nat_mul(v___x_1667_, v___x_1668_);
v___x_1670_ = lean_unsigned_to_nat(0u);
v___x_1671_ = lean_box(0);
v___x_1672_ = lean_mk_array(v_nbuckets_1669_, v___x_1671_);
v___x_1673_ = lean_array_propagate_mark(v_data_1666_, v___x_1672_);
v___x_1674_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2___redArg(v___x_1670_, v_data_1666_, v___x_1673_);
return v___x_1674_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(lean_object* v_a_1675_, lean_object* v_b_1676_, lean_object* v_x_1677_){
_start:
{
if (lean_obj_tag(v_x_1677_) == 0)
{
lean_dec(v_b_1676_);
lean_dec_ref(v_a_1675_);
return v_x_1677_;
}
else
{
lean_object* v_key_1678_; lean_object* v_value_1679_; lean_object* v_tail_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1698_; 
v_key_1678_ = lean_ctor_get(v_x_1677_, 0);
v_value_1679_ = lean_ctor_get(v_x_1677_, 1);
v_tail_1680_ = lean_ctor_get(v_x_1677_, 2);
v_isSharedCheck_1698_ = !lean_is_exclusive(v_x_1677_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1682_ = v_x_1677_;
v_isShared_1683_ = v_isSharedCheck_1698_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_tail_1680_);
lean_inc(v_value_1679_);
lean_inc(v_key_1678_);
lean_dec(v_x_1677_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1698_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v_fst_1689_; lean_object* v_snd_1690_; lean_object* v_fst_1691_; lean_object* v_snd_1692_; size_t v___x_1693_; size_t v___x_1694_; uint8_t v___x_1695_; 
v_fst_1689_ = lean_ctor_get(v_key_1678_, 0);
v_snd_1690_ = lean_ctor_get(v_key_1678_, 1);
v_fst_1691_ = lean_ctor_get(v_a_1675_, 0);
v_snd_1692_ = lean_ctor_get(v_a_1675_, 1);
v___x_1693_ = lean_ptr_addr(v_fst_1689_);
v___x_1694_ = lean_ptr_addr(v_fst_1691_);
v___x_1695_ = lean_usize_dec_eq(v___x_1693_, v___x_1694_);
if (v___x_1695_ == 0)
{
goto v___jp_1684_;
}
else
{
uint8_t v___x_1696_; 
v___x_1696_ = lean_nat_dec_eq(v_snd_1690_, v_snd_1692_);
if (v___x_1696_ == 0)
{
goto v___jp_1684_;
}
else
{
lean_object* v___x_1697_; 
lean_del_object(v___x_1682_);
lean_dec(v_value_1679_);
lean_dec(v_key_1678_);
v___x_1697_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1697_, 0, v_a_1675_);
lean_ctor_set(v___x_1697_, 1, v_b_1676_);
lean_ctor_set(v___x_1697_, 2, v_tail_1680_);
return v___x_1697_;
}
}
v___jp_1684_:
{
lean_object* v___x_1685_; lean_object* v___x_1687_; 
v___x_1685_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(v_a_1675_, v_b_1676_, v_tail_1680_);
if (v_isShared_1683_ == 0)
{
lean_ctor_set(v___x_1682_, 2, v___x_1685_);
v___x_1687_ = v___x_1682_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_key_1678_);
lean_ctor_set(v_reuseFailAlloc_1688_, 1, v_value_1679_);
lean_ctor_set(v_reuseFailAlloc_1688_, 2, v___x_1685_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
}
}
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(lean_object* v_a_1699_, lean_object* v_x_1700_){
_start:
{
if (lean_obj_tag(v_x_1700_) == 0)
{
uint8_t v___x_1701_; 
v___x_1701_ = 0;
return v___x_1701_;
}
else
{
lean_object* v_key_1702_; lean_object* v_tail_1703_; lean_object* v_fst_1704_; lean_object* v_snd_1705_; lean_object* v_fst_1706_; lean_object* v_snd_1707_; size_t v___x_1708_; size_t v___x_1709_; uint8_t v___x_1710_; 
v_key_1702_ = lean_ctor_get(v_x_1700_, 0);
v_tail_1703_ = lean_ctor_get(v_x_1700_, 2);
v_fst_1704_ = lean_ctor_get(v_key_1702_, 0);
v_snd_1705_ = lean_ctor_get(v_key_1702_, 1);
v_fst_1706_ = lean_ctor_get(v_a_1699_, 0);
v_snd_1707_ = lean_ctor_get(v_a_1699_, 1);
v___x_1708_ = lean_ptr_addr(v_fst_1704_);
v___x_1709_ = lean_ptr_addr(v_fst_1706_);
v___x_1710_ = lean_usize_dec_eq(v___x_1708_, v___x_1709_);
if (v___x_1710_ == 0)
{
v_x_1700_ = v_tail_1703_;
goto _start;
}
else
{
uint8_t v___x_1712_; 
v___x_1712_ = lean_nat_dec_eq(v_snd_1705_, v_snd_1707_);
if (v___x_1712_ == 0)
{
v_x_1700_ = v_tail_1703_;
goto _start;
}
else
{
return v___x_1712_;
}
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1699_ = stack[0].m_obj;
lean_object* v_x_1700_ = stack[1].m_obj;
uint8_t v_res_1714_;
v_res_1714_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_a_1699_, v_x_1700_);
stack->m_num = v_res_1714_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg___boxed(lean_object* v_a_1715_, lean_object* v_x_1716_){
_start:
{
uint8_t v_res_1717_; lean_object* v_r_1718_; 
v_res_1717_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_a_1715_, v_x_1716_);
lean_dec(v_x_1716_);
lean_dec_ref(v_a_1715_);
v_r_1718_ = lean_box(v_res_1717_);
return v_r_1718_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0___redArg(lean_object* v_m_1719_, lean_object* v_a_1720_, lean_object* v_b_1721_){
_start:
{
lean_object* v_size_1722_; lean_object* v_buckets_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1773_; 
v_size_1722_ = lean_ctor_get(v_m_1719_, 0);
v_buckets_1723_ = lean_ctor_get(v_m_1719_, 1);
v_isSharedCheck_1773_ = !lean_is_exclusive(v_m_1719_);
if (v_isSharedCheck_1773_ == 0)
{
v___x_1725_ = v_m_1719_;
v_isShared_1726_ = v_isSharedCheck_1773_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_buckets_1723_);
lean_inc(v_size_1722_);
lean_dec(v_m_1719_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1773_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v_fst_1727_; lean_object* v_snd_1728_; lean_object* v___x_1729_; size_t v___x_1730_; size_t v___x_1731_; size_t v___x_1732_; uint64_t v___x_1733_; uint64_t v___x_1734_; uint64_t v___x_1735_; uint64_t v___x_1736_; uint64_t v___x_1737_; uint64_t v_fold_1738_; uint64_t v___x_1739_; uint64_t v___x_1740_; uint64_t v___x_1741_; size_t v___x_1742_; size_t v___x_1743_; size_t v___x_1744_; size_t v___x_1745_; size_t v___x_1746_; lean_object* v_bkt_1747_; uint8_t v___x_1748_; 
v_fst_1727_ = lean_ctor_get(v_a_1720_, 0);
v_snd_1728_ = lean_ctor_get(v_a_1720_, 1);
v___x_1729_ = lean_array_get_size(v_buckets_1723_);
v___x_1730_ = lean_ptr_addr(v_fst_1727_);
v___x_1731_ = ((size_t)3ULL);
v___x_1732_ = lean_usize_shift_right(v___x_1730_, v___x_1731_);
v___x_1733_ = lean_usize_to_uint64(v___x_1732_);
v___x_1734_ = lean_uint64_of_nat(v_snd_1728_);
v___x_1735_ = lean_uint64_mix_hash(v___x_1733_, v___x_1734_);
v___x_1736_ = 32ULL;
v___x_1737_ = lean_uint64_shift_right(v___x_1735_, v___x_1736_);
v_fold_1738_ = lean_uint64_xor(v___x_1735_, v___x_1737_);
v___x_1739_ = 16ULL;
v___x_1740_ = lean_uint64_shift_right(v_fold_1738_, v___x_1739_);
v___x_1741_ = lean_uint64_xor(v_fold_1738_, v___x_1740_);
v___x_1742_ = lean_uint64_to_usize(v___x_1741_);
v___x_1743_ = lean_usize_of_nat(v___x_1729_);
v___x_1744_ = ((size_t)1ULL);
v___x_1745_ = lean_usize_sub(v___x_1743_, v___x_1744_);
v___x_1746_ = lean_usize_land(v___x_1742_, v___x_1745_);
v_bkt_1747_ = lean_array_uget_borrowed(v_buckets_1723_, v___x_1746_);
v___x_1748_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_a_1720_, v_bkt_1747_);
if (v___x_1748_ == 0)
{
lean_object* v___x_1749_; lean_object* v_size_x27_1750_; lean_object* v___x_1751_; lean_object* v_buckets_x27_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; uint8_t v___x_1758_; 
v___x_1749_ = lean_unsigned_to_nat(1u);
v_size_x27_1750_ = lean_nat_add(v_size_1722_, v___x_1749_);
lean_dec(v_size_1722_);
lean_inc(v_bkt_1747_);
v___x_1751_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1751_, 0, v_a_1720_);
lean_ctor_set(v___x_1751_, 1, v_b_1721_);
lean_ctor_set(v___x_1751_, 2, v_bkt_1747_);
v_buckets_x27_1752_ = lean_array_uset(v_buckets_1723_, v___x_1746_, v___x_1751_);
v___x_1753_ = lean_unsigned_to_nat(4u);
v___x_1754_ = lean_nat_mul(v_size_x27_1750_, v___x_1753_);
v___x_1755_ = lean_unsigned_to_nat(3u);
v___x_1756_ = lean_nat_div(v___x_1754_, v___x_1755_);
lean_dec(v___x_1754_);
v___x_1757_ = lean_array_get_size(v_buckets_x27_1752_);
v___x_1758_ = lean_nat_dec_le(v___x_1756_, v___x_1757_);
lean_dec(v___x_1756_);
if (v___x_1758_ == 0)
{
lean_object* v_val_1759_; lean_object* v___x_1761_; 
v_val_1759_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1___redArg(v_buckets_x27_1752_);
if (v_isShared_1726_ == 0)
{
lean_ctor_set(v___x_1725_, 1, v_val_1759_);
lean_ctor_set(v___x_1725_, 0, v_size_x27_1750_);
v___x_1761_ = v___x_1725_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v_size_x27_1750_);
lean_ctor_set(v_reuseFailAlloc_1762_, 1, v_val_1759_);
v___x_1761_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
return v___x_1761_;
}
}
else
{
lean_object* v___x_1764_; 
if (v_isShared_1726_ == 0)
{
lean_ctor_set(v___x_1725_, 1, v_buckets_x27_1752_);
lean_ctor_set(v___x_1725_, 0, v_size_x27_1750_);
v___x_1764_ = v___x_1725_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_size_x27_1750_);
lean_ctor_set(v_reuseFailAlloc_1765_, 1, v_buckets_x27_1752_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
}
else
{
lean_object* v___x_1766_; lean_object* v_buckets_x27_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1771_; 
lean_inc(v_bkt_1747_);
v___x_1766_ = lean_box(0);
v_buckets_x27_1767_ = lean_array_uset(v_buckets_1723_, v___x_1746_, v___x_1766_);
v___x_1768_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(v_a_1720_, v_b_1721_, v_bkt_1747_);
v___x_1769_ = lean_array_uset(v_buckets_x27_1767_, v___x_1746_, v___x_1768_);
if (v_isShared_1726_ == 0)
{
lean_ctor_set(v___x_1725_, 1, v___x_1769_);
v___x_1771_ = v___x_1725_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v_size_1722_);
lean_ctor_set(v_reuseFailAlloc_1772_, 1, v___x_1769_);
v___x_1771_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
return v___x_1771_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(lean_object* v_key_1774_, lean_object* v_r_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_){
_start:
{
lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; 
lean_inc_ref(v_r_1775_);
v___x_1778_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1776_, v_key_1774_, v_r_1775_);
v___x_1779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1779_, 0, v_r_1775_);
lean_ctor_set(v___x_1779_, 1, v___x_1778_);
v___x_1780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1780_, 0, v___x_1779_);
lean_ctor_set(v___x_1780_, 1, v_a_1777_);
return v___x_1780_;
}
}
lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save(lean_object* v_key_1781_, lean_object* v_r_1782_, lean_object* v_a_1783_, uint8_t v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_){
_start:
{
lean_object* v___x_1787_; 
v___x_1787_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_1781_, v_r_1782_, v_a_1783_, v_a_1786_);
return v___x_1787_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_0interp(lean_interpreter_value* stack)
{
lean_object* v_key_1781_ = stack[0].m_obj;
lean_object* v_r_1782_ = stack[1].m_obj;
lean_object* v_a_1783_ = stack[2].m_obj;
uint8_t v_a_1784_ = stack[3].m_num;
lean_object* v_a_1785_ = stack[4].m_obj;
lean_object* v_a_1786_ = stack[5].m_obj;
lean_object* v_res_1788_;
v_res_1788_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save(v_key_1781_, v_r_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_);
stack->m_obj
 = v_res_1788_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___boxed(lean_object* v_key_1789_, lean_object* v_r_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_){
_start:
{
uint8_t v_a_boxed_1795_; lean_object* v_res_1796_; 
v_a_boxed_1795_ = lean_unbox(v_a_1792_);
v_res_1796_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save(v_key_1789_, v_r_1790_, v_a_1791_, v_a_boxed_1795_, v_a_1793_, v_a_1794_);
lean_dec_ref(v_a_1793_);
return v_res_1796_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0(lean_object* v_00_u03b2_1797_, lean_object* v_m_1798_, lean_object* v_a_1799_, lean_object* v_b_1800_){
_start:
{
lean_object* v___x_1801_; 
v___x_1801_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0___redArg(v_m_1798_, v_a_1799_, v_b_1800_);
return v___x_1801_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0(lean_object* v_00_u03b2_1802_, lean_object* v_a_1803_, lean_object* v_x_1804_){
_start:
{
uint8_t v___x_1805_; 
v___x_1805_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_a_1803_, v_x_1804_);
return v___x_1805_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1803_ = stack[1].m_obj;
lean_object* v_x_1804_ = stack[2].m_obj;
uint8_t v_res_1806_;
v_res_1806_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0(lean_box(0), v_a_1803_, v_x_1804_);
stack->m_num = v_res_1806_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1807_, lean_object* v_a_1808_, lean_object* v_x_1809_){
_start:
{
uint8_t v_res_1810_; lean_object* v_r_1811_; 
v_res_1810_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0(v_00_u03b2_1807_, v_a_1808_, v_x_1809_);
lean_dec(v_x_1809_);
lean_dec_ref(v_a_1808_);
v_r_1811_ = lean_box(v_res_1810_);
return v_r_1811_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1(lean_object* v_00_u03b2_1812_, lean_object* v_data_1813_){
_start:
{
lean_object* v___x_1814_; 
v___x_1814_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1___redArg(v_data_1813_);
return v___x_1814_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2(lean_object* v_00_u03b2_1815_, lean_object* v_a_1816_, lean_object* v_b_1817_, lean_object* v_x_1818_){
_start:
{
lean_object* v___x_1819_; 
v___x_1819_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(v_a_1816_, v_b_1817_, v_x_1818_);
return v___x_1819_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1820_, lean_object* v_i_1821_, lean_object* v_source_1822_, lean_object* v_target_1823_){
_start:
{
lean_object* v___x_1824_; 
v___x_1824_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2___redArg(v_i_1821_, v_source_1822_, v_target_1823_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1825_, lean_object* v_x_1826_, lean_object* v_x_1827_){
_start:
{
lean_object* v___x_1828_; 
v___x_1828_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1826_, v_x_1827_);
return v___x_1828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0___redArg(lean_object* v_idx_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_){
_start:
{
lean_object* v___x_1832_; lean_object* v___x_1833_; 
v___x_1832_ = l_Lean_Expr_bvar___override(v_idx_1829_);
v___x_1833_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1832_, v___y_1831_);
if (lean_obj_tag(v___x_1833_) == 0)
{
lean_object* v_a_1834_; lean_object* v_a_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1843_; 
v_a_1834_ = lean_ctor_get(v___x_1833_, 0);
v_a_1835_ = lean_ctor_get(v___x_1833_, 1);
v_isSharedCheck_1843_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1837_ = v___x_1833_;
v_isShared_1838_ = v_isSharedCheck_1843_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_a_1835_);
lean_inc(v_a_1834_);
lean_dec(v___x_1833_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1843_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
lean_object* v___x_1839_; lean_object* v___x_1841_; 
v___x_1839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1839_, 0, v_a_1834_);
lean_ctor_set(v___x_1839_, 1, v___y_1830_);
if (v_isShared_1838_ == 0)
{
lean_ctor_set(v___x_1837_, 0, v___x_1839_);
v___x_1841_ = v___x_1837_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v___x_1839_);
lean_ctor_set(v_reuseFailAlloc_1842_, 1, v_a_1835_);
v___x_1841_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
return v___x_1841_;
}
}
}
else
{
lean_object* v_a_1844_; lean_object* v_a_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1852_; 
lean_dec_ref(v___y_1830_);
v_a_1844_ = lean_ctor_get(v___x_1833_, 0);
v_a_1845_ = lean_ctor_get(v___x_1833_, 1);
v_isSharedCheck_1852_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1847_ = v___x_1833_;
v_isShared_1848_ = v_isSharedCheck_1852_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_a_1845_);
lean_inc(v_a_1844_);
lean_dec(v___x_1833_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1852_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
lean_object* v___x_1850_; 
if (v_isShared_1848_ == 0)
{
v___x_1850_ = v___x_1847_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v_a_1844_);
lean_ctor_set(v_reuseFailAlloc_1851_, 1, v_a_1845_);
v___x_1850_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
return v___x_1850_;
}
}
}
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0(lean_object* v_idx_1853_, lean_object* v___y_1854_, uint8_t v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_){
_start:
{
lean_object* v___x_1858_; 
v___x_1858_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0___redArg(v_idx_1853_, v___y_1854_, v___y_1857_);
return v___x_1858_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_idx_1853_ = stack[0].m_obj;
lean_object* v___y_1854_ = stack[1].m_obj;
uint8_t v___y_1855_ = stack[2].m_num;
lean_object* v___y_1856_ = stack[3].m_obj;
lean_object* v___y_1857_ = stack[4].m_obj;
lean_object* v_res_1859_;
v_res_1859_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0(v_idx_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_);
stack->m_obj
 = v_res_1859_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0___boxed(lean_object* v_idx_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_){
_start:
{
uint8_t v___y_1135__boxed_1865_; lean_object* v_res_1866_; 
v___y_1135__boxed_1865_ = lean_unbox(v___y_1862_);
v_res_1866_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0(v_idx_1860_, v___y_1861_, v___y_1135__boxed_1865_, v___y_1863_, v___y_1864_);
lean_dec_ref(v___y_1863_);
return v_res_1866_;
}
}
lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(lean_object* v_subst_1867_, lean_object* v_e_1868_, lean_object* v_bidx_1869_, lean_object* v_offset_1870_, lean_object* v_a_1871_, uint8_t v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_){
_start:
{
uint8_t v___x_1875_; 
v___x_1875_ = lean_nat_dec_le(v_offset_1870_, v_bidx_1869_);
if (v___x_1875_ == 0)
{
lean_object* v___x_1876_; lean_object* v___x_1877_; 
v___x_1876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1876_, 0, v_e_1868_);
lean_ctor_set(v___x_1876_, 1, v_a_1871_);
v___x_1877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1876_);
lean_ctor_set(v___x_1877_, 1, v_a_1874_);
return v___x_1877_;
}
else
{
lean_object* v_n_1878_; lean_object* v___x_1879_; uint8_t v___x_1880_; 
lean_dec_ref(v_e_1868_);
v_n_1878_ = lean_array_get_size(v_subst_1867_);
v___x_1879_ = lean_nat_add(v_offset_1870_, v_n_1878_);
v___x_1880_ = lean_nat_dec_lt(v_bidx_1869_, v___x_1879_);
lean_dec(v___x_1879_);
if (v___x_1880_ == 0)
{
lean_object* v___x_1881_; lean_object* v___x_1882_; 
v___x_1881_ = lean_nat_sub(v_bidx_1869_, v_n_1878_);
v___x_1882_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0___redArg(v___x_1881_, v_a_1871_, v_a_1874_);
return v___x_1882_;
}
else
{
lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v_v_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; 
v___x_1883_ = lean_nat_sub(v_bidx_1869_, v_offset_1870_);
v___x_1884_ = lean_nat_sub(v_n_1878_, v___x_1883_);
lean_dec(v___x_1883_);
v___x_1885_ = lean_unsigned_to_nat(1u);
v___x_1886_ = lean_nat_sub(v___x_1884_, v___x_1885_);
lean_dec(v___x_1884_);
v_v_1887_ = lean_array_fget_borrowed(v_subst_1867_, v___x_1886_);
lean_dec(v___x_1886_);
v___x_1888_ = lean_unsigned_to_nat(0u);
lean_inc(v_v_1887_);
v___x_1889_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(v_v_1887_, v___x_1888_, v_offset_1870_, v_a_1872_, v_a_1873_, v_a_1874_);
if (lean_obj_tag(v___x_1889_) == 0)
{
lean_object* v_a_1890_; lean_object* v_a_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1899_; 
v_a_1890_ = lean_ctor_get(v___x_1889_, 0);
v_a_1891_ = lean_ctor_get(v___x_1889_, 1);
v_isSharedCheck_1899_ = !lean_is_exclusive(v___x_1889_);
if (v_isSharedCheck_1899_ == 0)
{
v___x_1893_ = v___x_1889_;
v_isShared_1894_ = v_isSharedCheck_1899_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_a_1891_);
lean_inc(v_a_1890_);
lean_dec(v___x_1889_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1899_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1895_; lean_object* v___x_1897_; 
v___x_1895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1895_, 0, v_a_1890_);
lean_ctor_set(v___x_1895_, 1, v_a_1871_);
if (v_isShared_1894_ == 0)
{
lean_ctor_set(v___x_1893_, 0, v___x_1895_);
v___x_1897_ = v___x_1893_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v___x_1895_);
lean_ctor_set(v_reuseFailAlloc_1898_, 1, v_a_1891_);
v___x_1897_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
return v___x_1897_;
}
}
}
else
{
lean_object* v_a_1900_; lean_object* v_a_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1908_; 
lean_dec_ref(v_a_1871_);
v_a_1900_ = lean_ctor_get(v___x_1889_, 0);
v_a_1901_ = lean_ctor_get(v___x_1889_, 1);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___x_1889_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1903_ = v___x_1889_;
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_a_1901_);
lean_inc(v_a_1900_);
lean_dec(v___x_1889_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1906_; 
if (v_isShared_1904_ == 0)
{
v___x_1906_ = v___x_1903_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_a_1900_);
lean_ctor_set(v_reuseFailAlloc_1907_, 1, v_a_1901_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
return v___x_1906_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_subst_1867_ = stack[0].m_obj;
lean_object* v_e_1868_ = stack[1].m_obj;
lean_object* v_bidx_1869_ = stack[2].m_obj;
lean_object* v_offset_1870_ = stack[3].m_obj;
lean_object* v_a_1871_ = stack[4].m_obj;
uint8_t v_a_1872_ = stack[5].m_num;
lean_object* v_a_1873_ = stack[6].m_obj;
lean_object* v_a_1874_ = stack[7].m_obj;
lean_object* v_res_1909_;
v_res_1909_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(v_subst_1867_, v_e_1868_, v_bidx_1869_, v_offset_1870_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_);
stack->m_obj
 = v_res_1909_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar___boxed(lean_object* v_subst_1910_, lean_object* v_e_1911_, lean_object* v_bidx_1912_, lean_object* v_offset_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_){
_start:
{
uint8_t v_a_boxed_1918_; lean_object* v_res_1919_; 
v_a_boxed_1918_ = lean_unbox(v_a_1915_);
v_res_1919_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(v_subst_1910_, v_e_1911_, v_bidx_1912_, v_offset_1913_, v_a_1914_, v_a_boxed_1918_, v_a_1916_, v_a_1917_);
lean_dec_ref(v_a_1916_);
lean_dec(v_offset_1913_);
lean_dec(v_bidx_1912_);
lean_dec_ref(v_subst_1910_);
return v_res_1919_;
}
}
lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault(lean_object* v_subst_1920_, lean_object* v_e_1921_, lean_object* v_offset_1922_, lean_object* v_a_1923_, uint8_t v_a_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_){
_start:
{
if (lean_obj_tag(v_e_1921_) == 5)
{
lean_object* v_fn_1927_; lean_object* v_arg_1928_; lean_object* v_key_1929_; lean_object* v___y_1931_; lean_object* v___x_1937_; 
v_fn_1927_ = lean_ctor_get(v_e_1921_, 0);
v_arg_1928_ = lean_ctor_get(v_e_1921_, 1);
lean_inc(v_offset_1922_);
lean_inc_ref(v_e_1921_);
v_key_1929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1929_, 0, v_e_1921_);
lean_ctor_set(v_key_1929_, 1, v_offset_1922_);
v___x_1937_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3___redArg(v_a_1923_, v_key_1929_);
if (lean_obj_tag(v___x_1937_) == 1)
{
lean_object* v_val_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; 
lean_dec_ref_known(v_key_1929_, 2);
lean_dec_ref_known(v_e_1921_, 2);
lean_dec(v_offset_1922_);
v_val_1938_ = lean_ctor_get(v___x_1937_, 0);
lean_inc(v_val_1938_);
lean_dec_ref_known(v___x_1937_, 1);
v___x_1939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1939_, 0, v_val_1938_);
lean_ctor_set(v___x_1939_, 1, v_a_1923_);
v___x_1940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1940_, 0, v___x_1939_);
lean_ctor_set(v___x_1940_, 1, v_a_1926_);
return v___x_1940_;
}
else
{
lean_object* v___x_1941_; 
lean_dec(v___x_1937_);
lean_inc(v_offset_1922_);
lean_inc_ref(v_fn_1927_);
v___x_1941_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault(v_subst_1920_, v_fn_1927_, v_offset_1922_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_);
if (lean_obj_tag(v___x_1941_) == 0)
{
lean_object* v_a_1942_; lean_object* v_a_1943_; lean_object* v_fst_1944_; lean_object* v_snd_1945_; lean_object* v___x_1946_; 
v_a_1942_ = lean_ctor_get(v___x_1941_, 0);
lean_inc(v_a_1942_);
v_a_1943_ = lean_ctor_get(v___x_1941_, 1);
lean_inc(v_a_1943_);
lean_dec_ref_known(v___x_1941_, 2);
v_fst_1944_ = lean_ctor_get(v_a_1942_, 0);
lean_inc(v_fst_1944_);
v_snd_1945_ = lean_ctor_get(v_a_1942_, 1);
lean_inc(v_snd_1945_);
lean_dec(v_a_1942_);
lean_inc_ref(v_arg_1928_);
v___x_1946_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1920_, v_arg_1928_, v_offset_1922_, v_snd_1945_, v_a_1924_, v_a_1925_, v_a_1943_);
if (lean_obj_tag(v___x_1946_) == 0)
{
lean_object* v_a_1947_; lean_object* v_a_1948_; lean_object* v_fst_1949_; lean_object* v_snd_1950_; size_t v___x_1951_; size_t v___x_1952_; uint8_t v___x_1953_; 
v_a_1947_ = lean_ctor_get(v___x_1946_, 0);
lean_inc(v_a_1947_);
v_a_1948_ = lean_ctor_get(v___x_1946_, 1);
lean_inc(v_a_1948_);
lean_dec_ref_known(v___x_1946_, 2);
v_fst_1949_ = lean_ctor_get(v_a_1947_, 0);
lean_inc(v_fst_1949_);
v_snd_1950_ = lean_ctor_get(v_a_1947_, 1);
lean_inc(v_snd_1950_);
lean_dec(v_a_1947_);
v___x_1951_ = lean_ptr_addr(v_fn_1927_);
v___x_1952_ = lean_ptr_addr(v_fst_1944_);
v___x_1953_ = lean_usize_dec_eq(v___x_1951_, v___x_1952_);
if (v___x_1953_ == 0)
{
lean_object* v___x_1954_; 
lean_dec_ref_known(v_e_1921_, 2);
v___x_1954_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__2(v_fst_1944_, v_fst_1949_, v_snd_1950_, v_a_1924_, v_a_1925_, v_a_1948_);
v___y_1931_ = v___x_1954_;
goto v___jp_1930_;
}
else
{
size_t v___x_1955_; size_t v___x_1956_; uint8_t v___x_1957_; 
v___x_1955_ = lean_ptr_addr(v_arg_1928_);
v___x_1956_ = lean_ptr_addr(v_fst_1949_);
v___x_1957_ = lean_usize_dec_eq(v___x_1955_, v___x_1956_);
if (v___x_1957_ == 0)
{
lean_object* v___x_1958_; 
lean_dec_ref_known(v_e_1921_, 2);
v___x_1958_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__2(v_fst_1944_, v_fst_1949_, v_snd_1950_, v_a_1924_, v_a_1925_, v_a_1948_);
v___y_1931_ = v___x_1958_;
goto v___jp_1930_;
}
else
{
lean_object* v___x_1959_; 
lean_dec(v_fst_1949_);
lean_dec(v_fst_1944_);
v___x_1959_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_1929_, v_e_1921_, v_snd_1950_, v_a_1948_);
return v___x_1959_;
}
}
}
else
{
lean_dec(v_fst_1944_);
lean_dec_ref_known(v_key_1929_, 2);
lean_dec_ref_known(v_e_1921_, 2);
return v___x_1946_;
}
}
else
{
lean_dec_ref_known(v_key_1929_, 2);
lean_dec_ref_known(v_e_1921_, 2);
lean_dec(v_offset_1922_);
return v___x_1941_;
}
}
v___jp_1930_:
{
if (lean_obj_tag(v___y_1931_) == 0)
{
lean_object* v_a_1932_; lean_object* v_a_1933_; lean_object* v_fst_1934_; lean_object* v_snd_1935_; lean_object* v___x_1936_; 
v_a_1932_ = lean_ctor_get(v___y_1931_, 0);
lean_inc(v_a_1932_);
v_a_1933_ = lean_ctor_get(v___y_1931_, 1);
lean_inc(v_a_1933_);
lean_dec_ref_known(v___y_1931_, 2);
v_fst_1934_ = lean_ctor_get(v_a_1932_, 0);
lean_inc(v_fst_1934_);
v_snd_1935_ = lean_ctor_get(v_a_1932_, 1);
lean_inc(v_snd_1935_);
lean_dec(v_a_1932_);
v___x_1936_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_1929_, v_fst_1934_, v_snd_1935_, v_a_1933_);
return v___x_1936_;
}
else
{
lean_dec_ref_known(v_key_1929_, 2);
return v___y_1931_;
}
}
}
else
{
lean_object* v___x_1960_; 
v___x_1960_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1920_, v_e_1921_, v_offset_1922_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_);
return v___x_1960_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault_0interp(lean_interpreter_value* stack)
{
lean_object* v_subst_1920_ = stack[0].m_obj;
lean_object* v_e_1921_ = stack[1].m_obj;
lean_object* v_offset_1922_ = stack[2].m_obj;
lean_object* v_a_1923_ = stack[3].m_obj;
uint8_t v_a_1924_ = stack[4].m_num;
lean_object* v_a_1925_ = stack[5].m_obj;
lean_object* v_a_1926_ = stack[6].m_obj;
lean_object* v_res_1961_;
v_res_1961_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault(v_subst_1920_, v_e_1921_, v_offset_1922_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_);
stack->m_obj
 = v_res_1961_;
}
static lean_object* _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__2(void){
_start:
{
lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; 
v___x_1964_ = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__1));
v___x_1965_ = lean_unsigned_to_nat(25u);
v___x_1966_ = lean_unsigned_to_nat(148u);
v___x_1967_ = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__0));
v___x_1968_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__0));
v___x_1969_ = l_mkPanicMessageWithDecl(v___x_1968_, v___x_1967_, v___x_1966_, v___x_1965_, v___x_1964_);
return v___x_1969_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__1(void){
_start:
{
lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; 
v___x_1971_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__2));
v___x_1972_ = lean_unsigned_to_nat(11u);
v___x_1973_ = lean_unsigned_to_nat(165u);
v___x_1974_ = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__0));
v___x_1975_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__3));
v___x_1976_ = l_mkPanicMessageWithDecl(v___x_1975_, v___x_1974_, v___x_1973_, v___x_1972_, v___x_1971_);
return v___x_1976_;
}
}
lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta(lean_object* v_subst_1977_, lean_object* v_e_1978_, lean_object* v_f_1979_, lean_object* v_argsRev_1980_, lean_object* v_offset_1981_, uint8_t v_modified_1982_, lean_object* v_a_1983_, uint8_t v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_){
_start:
{
switch(lean_obj_tag(v_f_1979_))
{
case 5:
{
lean_object* v_fn_1987_; lean_object* v_arg_1988_; lean_object* v___x_1989_; 
v_fn_1987_ = lean_ctor_get(v_f_1979_, 0);
lean_inc_ref(v_fn_1987_);
v_arg_1988_ = lean_ctor_get(v_f_1979_, 1);
lean_inc_ref_n(v_arg_1988_, 2);
lean_dec_ref_known(v_f_1979_, 2);
lean_inc(v_offset_1981_);
v___x_1989_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1977_, v_arg_1988_, v_offset_1981_, v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_);
if (lean_obj_tag(v___x_1989_) == 0)
{
lean_object* v_a_1990_; lean_object* v_a_1991_; lean_object* v_fst_1992_; lean_object* v_snd_1993_; lean_object* v___x_1994_; 
v_a_1990_ = lean_ctor_get(v___x_1989_, 0);
lean_inc(v_a_1990_);
v_a_1991_ = lean_ctor_get(v___x_1989_, 1);
lean_inc(v_a_1991_);
lean_dec_ref_known(v___x_1989_, 2);
v_fst_1992_ = lean_ctor_get(v_a_1990_, 0);
lean_inc_n(v_fst_1992_, 2);
v_snd_1993_ = lean_ctor_get(v_a_1990_, 1);
lean_inc(v_snd_1993_);
lean_dec(v_a_1990_);
v___x_1994_ = lean_array_push(v_argsRev_1980_, v_fst_1992_);
if (v_modified_1982_ == 0)
{
size_t v___x_1995_; size_t v___x_1996_; uint8_t v___x_1997_; 
v___x_1995_ = lean_ptr_addr(v_arg_1988_);
lean_dec_ref(v_arg_1988_);
v___x_1996_ = lean_ptr_addr(v_fst_1992_);
lean_dec(v_fst_1992_);
v___x_1997_ = lean_usize_dec_eq(v___x_1995_, v___x_1996_);
if (v___x_1997_ == 0)
{
uint8_t v___x_1998_; 
v___x_1998_ = 1;
v_f_1979_ = v_fn_1987_;
v_argsRev_1980_ = v___x_1994_;
v_modified_1982_ = v___x_1998_;
v_a_1983_ = v_snd_1993_;
v_a_1986_ = v_a_1991_;
goto _start;
}
else
{
v_f_1979_ = v_fn_1987_;
v_argsRev_1980_ = v___x_1994_;
v_a_1983_ = v_snd_1993_;
v_a_1986_ = v_a_1991_;
goto _start;
}
}
else
{
lean_dec(v_fst_1992_);
lean_dec_ref(v_arg_1988_);
v_f_1979_ = v_fn_1987_;
v_argsRev_1980_ = v___x_1994_;
v_a_1983_ = v_snd_1993_;
v_a_1986_ = v_a_1991_;
goto _start;
}
}
else
{
lean_dec_ref(v_arg_1988_);
lean_dec_ref(v_fn_1987_);
lean_dec(v_offset_1981_);
lean_dec_ref(v_argsRev_1980_);
lean_dec_ref(v_e_1978_);
return v___x_1989_;
}
}
case 0:
{
lean_object* v_deBruijnIndex_2002_; lean_object* v___x_2003_; 
v_deBruijnIndex_2002_ = lean_ctor_get(v_f_1979_, 0);
lean_inc_ref(v_f_1979_);
v___x_2003_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(v_subst_1977_, v_f_1979_, v_deBruijnIndex_2002_, v_offset_1981_, v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_);
lean_dec(v_offset_1981_);
if (lean_obj_tag(v___x_2003_) == 0)
{
lean_object* v_a_2004_; lean_object* v_a_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2045_; 
v_a_2004_ = lean_ctor_get(v___x_2003_, 0);
v_a_2005_ = lean_ctor_get(v___x_2003_, 1);
v_isSharedCheck_2045_ = !lean_is_exclusive(v___x_2003_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_2007_ = v___x_2003_;
v_isShared_2008_ = v_isSharedCheck_2045_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_a_2005_);
lean_inc(v_a_2004_);
lean_dec(v___x_2003_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2045_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v_fst_2009_; lean_object* v_snd_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2044_; 
v_fst_2009_ = lean_ctor_get(v_a_2004_, 0);
v_snd_2010_ = lean_ctor_get(v_a_2004_, 1);
v_isSharedCheck_2044_ = !lean_is_exclusive(v_a_2004_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_2012_ = v_a_2004_;
v_isShared_2013_ = v_isSharedCheck_2044_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_snd_2010_);
lean_inc(v_fst_2009_);
lean_dec(v_a_2004_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2044_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
if (v_modified_1982_ == 0)
{
size_t v___x_2037_; size_t v___x_2038_; uint8_t v___x_2039_; 
v___x_2037_ = lean_ptr_addr(v_f_1979_);
lean_dec_ref_known(v_f_1979_, 1);
v___x_2038_ = lean_ptr_addr(v_fst_2009_);
v___x_2039_ = lean_usize_dec_eq(v___x_2037_, v___x_2038_);
if (v___x_2039_ == 0)
{
lean_del_object(v___x_2007_);
lean_dec_ref(v_e_1978_);
goto v___jp_2014_;
}
else
{
lean_object* v___x_2040_; lean_object* v___x_2042_; 
lean_del_object(v___x_2012_);
lean_dec(v_fst_2009_);
lean_dec_ref(v_argsRev_1980_);
v___x_2040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2040_, 0, v_e_1978_);
lean_ctor_set(v___x_2040_, 1, v_snd_2010_);
if (v_isShared_2008_ == 0)
{
lean_ctor_set(v___x_2007_, 0, v___x_2040_);
v___x_2042_ = v___x_2007_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v___x_2040_);
lean_ctor_set(v_reuseFailAlloc_2043_, 1, v_a_2005_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
}
else
{
lean_del_object(v___x_2007_);
lean_dec_ref_known(v_f_1979_, 1);
lean_dec_ref(v_e_1978_);
goto v___jp_2014_;
}
v___jp_2014_:
{
lean_object* v___x_2015_; 
v___x_2015_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27(v_fst_2009_, v_argsRev_1980_, v_a_1984_, v_a_1985_, v_a_2005_);
lean_dec_ref(v_argsRev_1980_);
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_object* v_a_2016_; lean_object* v_a_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2027_; 
v_a_2016_ = lean_ctor_get(v___x_2015_, 0);
v_a_2017_ = lean_ctor_get(v___x_2015_, 1);
v_isSharedCheck_2027_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_2019_ = v___x_2015_;
v_isShared_2020_ = v_isSharedCheck_2027_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_a_2017_);
lean_inc(v_a_2016_);
lean_dec(v___x_2015_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2027_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v___x_2022_; 
if (v_isShared_2013_ == 0)
{
lean_ctor_set(v___x_2012_, 0, v_a_2016_);
v___x_2022_ = v___x_2012_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v_a_2016_);
lean_ctor_set(v_reuseFailAlloc_2026_, 1, v_snd_2010_);
v___x_2022_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
lean_object* v___x_2024_; 
if (v_isShared_2020_ == 0)
{
lean_ctor_set(v___x_2019_, 0, v___x_2022_);
v___x_2024_ = v___x_2019_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v___x_2022_);
lean_ctor_set(v_reuseFailAlloc_2025_, 1, v_a_2017_);
v___x_2024_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
return v___x_2024_;
}
}
}
}
else
{
lean_object* v_a_2028_; lean_object* v_a_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2036_; 
lean_del_object(v___x_2012_);
lean_dec(v_snd_2010_);
v_a_2028_ = lean_ctor_get(v___x_2015_, 0);
v_a_2029_ = lean_ctor_get(v___x_2015_, 1);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2031_ = v___x_2015_;
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_a_2029_);
lean_inc(v_a_2028_);
lean_dec(v___x_2015_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2034_; 
if (v_isShared_2032_ == 0)
{
v___x_2034_ = v___x_2031_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_a_2028_);
lean_ctor_set(v_reuseFailAlloc_2035_, 1, v_a_2029_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_f_1979_, 1);
lean_dec_ref(v_argsRev_1980_);
lean_dec_ref(v_e_1978_);
return v___x_2003_;
}
}
default: 
{
lean_object* v___x_2046_; lean_object* v___x_2047_; 
lean_dec(v_offset_1981_);
lean_dec_ref(v_argsRev_1980_);
lean_dec_ref(v_f_1979_);
lean_dec_ref(v_e_1978_);
v___x_2046_ = lean_obj_once(&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__1, &l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__1_once, _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__1);
v___x_2047_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8(v___x_2046_, v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_);
return v___x_2047_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta_0interp(lean_interpreter_value* stack)
{
lean_object* v_subst_1977_ = stack[0].m_obj;
lean_object* v_e_1978_ = stack[1].m_obj;
lean_object* v_f_1979_ = stack[2].m_obj;
lean_object* v_argsRev_1980_ = stack[3].m_obj;
lean_object* v_offset_1981_ = stack[4].m_obj;
uint8_t v_modified_1982_ = stack[5].m_num;
lean_object* v_a_1983_ = stack[6].m_obj;
uint8_t v_a_1984_ = stack[7].m_num;
lean_object* v_a_1985_ = stack[8].m_obj;
lean_object* v_a_1986_ = stack[9].m_obj;
lean_object* v_res_2048_;
v_res_2048_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta(v_subst_1977_, v_e_1978_, v_f_1979_, v_argsRev_1980_, v_offset_1981_, v_modified_1982_, v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_);
stack->m_obj
 = v_res_2048_;
}
lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg(lean_object* v_subst_2049_, lean_object* v_e_2050_, lean_object* v_f_2051_, lean_object* v_arg_2052_, lean_object* v_offset_2053_, lean_object* v_a_2054_, uint8_t v_a_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_){
_start:
{
lean_object* v___x_2058_; 
lean_inc(v_offset_2053_);
lean_inc_ref(v_arg_2052_);
v___x_2058_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_2049_, v_arg_2052_, v_offset_2053_, v_a_2054_, v_a_2055_, v_a_2056_, v_a_2057_);
if (lean_obj_tag(v___x_2058_) == 0)
{
lean_object* v_a_2059_; lean_object* v_a_2060_; lean_object* v_fst_2061_; lean_object* v_snd_2062_; lean_object* v___x_2063_; uint8_t v___x_2064_; 
v_a_2059_ = lean_ctor_get(v___x_2058_, 0);
lean_inc(v_a_2059_);
v_a_2060_ = lean_ctor_get(v___x_2058_, 1);
lean_inc(v_a_2060_);
lean_dec_ref_known(v___x_2058_, 2);
v_fst_2061_ = lean_ctor_get(v_a_2059_, 0);
lean_inc(v_fst_2061_);
v_snd_2062_ = lean_ctor_get(v_a_2059_, 1);
lean_inc(v_snd_2062_);
lean_dec(v_a_2059_);
v___x_2063_ = l_Lean_Expr_getAppFn(v_f_2051_);
v___x_2064_ = l_Lean_Expr_isBVar(v___x_2063_);
lean_dec_ref(v___x_2063_);
if (v___x_2064_ == 0)
{
lean_object* v___x_2065_; 
lean_dec_ref(v_arg_2052_);
v___x_2065_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault(v_subst_2049_, v_f_2051_, v_offset_2053_, v_snd_2062_, v_a_2055_, v_a_2056_, v_a_2060_);
if (lean_obj_tag(v___x_2065_) == 0)
{
lean_object* v_a_2066_; 
v_a_2066_ = lean_ctor_get(v___x_2065_, 0);
lean_inc(v_a_2066_);
if (lean_obj_tag(v_e_2050_) == 5)
{
lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2093_; 
v_a_2067_ = lean_ctor_get(v___x_2065_, 1);
v_isSharedCheck_2093_ = !lean_is_exclusive(v___x_2065_);
if (v_isSharedCheck_2093_ == 0)
{
lean_object* v_unused_2094_; 
v_unused_2094_ = lean_ctor_get(v___x_2065_, 0);
lean_dec(v_unused_2094_);
v___x_2069_ = v___x_2065_;
v_isShared_2070_ = v_isSharedCheck_2093_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___x_2065_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2093_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v_fst_2071_; lean_object* v_snd_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2092_; 
v_fst_2071_ = lean_ctor_get(v_a_2066_, 0);
v_snd_2072_ = lean_ctor_get(v_a_2066_, 1);
v_isSharedCheck_2092_ = !lean_is_exclusive(v_a_2066_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2074_ = v_a_2066_;
v_isShared_2075_ = v_isSharedCheck_2092_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_snd_2072_);
lean_inc(v_fst_2071_);
lean_dec(v_a_2066_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2092_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v_fn_2076_; lean_object* v_arg_2077_; size_t v___x_2078_; size_t v___x_2079_; uint8_t v___x_2080_; 
v_fn_2076_ = lean_ctor_get(v_e_2050_, 0);
v_arg_2077_ = lean_ctor_get(v_e_2050_, 1);
v___x_2078_ = lean_ptr_addr(v_fn_2076_);
v___x_2079_ = lean_ptr_addr(v_fst_2071_);
v___x_2080_ = lean_usize_dec_eq(v___x_2078_, v___x_2079_);
if (v___x_2080_ == 0)
{
lean_object* v___x_2081_; 
lean_del_object(v___x_2074_);
lean_del_object(v___x_2069_);
lean_dec_ref_known(v_e_2050_, 2);
v___x_2081_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__2(v_fst_2071_, v_fst_2061_, v_snd_2072_, v_a_2055_, v_a_2056_, v_a_2067_);
return v___x_2081_;
}
else
{
size_t v___x_2082_; size_t v___x_2083_; uint8_t v___x_2084_; 
v___x_2082_ = lean_ptr_addr(v_arg_2077_);
v___x_2083_ = lean_ptr_addr(v_fst_2061_);
v___x_2084_ = lean_usize_dec_eq(v___x_2082_, v___x_2083_);
if (v___x_2084_ == 0)
{
lean_object* v___x_2085_; 
lean_del_object(v___x_2074_);
lean_del_object(v___x_2069_);
lean_dec_ref_known(v_e_2050_, 2);
v___x_2085_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__2(v_fst_2071_, v_fst_2061_, v_snd_2072_, v_a_2055_, v_a_2056_, v_a_2067_);
return v___x_2085_;
}
else
{
lean_object* v___x_2087_; 
lean_dec(v_fst_2071_);
lean_dec(v_fst_2061_);
if (v_isShared_2075_ == 0)
{
lean_ctor_set(v___x_2074_, 0, v_e_2050_);
v___x_2087_ = v___x_2074_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_e_2050_);
lean_ctor_set(v_reuseFailAlloc_2091_, 1, v_snd_2072_);
v___x_2087_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
lean_object* v___x_2089_; 
if (v_isShared_2070_ == 0)
{
lean_ctor_set(v___x_2069_, 0, v___x_2087_);
v___x_2089_ = v___x_2069_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v___x_2087_);
lean_ctor_set(v_reuseFailAlloc_2090_, 1, v_a_2067_);
v___x_2089_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
return v___x_2089_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2095_; lean_object* v_snd_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; 
lean_dec(v_fst_2061_);
lean_dec_ref(v_e_2050_);
v_a_2095_ = lean_ctor_get(v___x_2065_, 1);
lean_inc(v_a_2095_);
lean_dec_ref_known(v___x_2065_, 2);
v_snd_2096_ = lean_ctor_get(v_a_2066_, 1);
lean_inc(v_snd_2096_);
lean_dec(v_a_2066_);
v___x_2097_ = lean_obj_once(&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__2, &l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__2_once, _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__2);
v___x_2098_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8(v___x_2097_, v_snd_2096_, v_a_2055_, v_a_2056_, v_a_2095_);
return v___x_2098_;
}
}
else
{
lean_dec(v_fst_2061_);
lean_dec_ref(v_e_2050_);
return v___x_2065_;
}
}
else
{
lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; size_t v___x_2102_; size_t v___x_2103_; uint8_t v___x_2104_; 
v___x_2099_ = lean_unsigned_to_nat(1u);
v___x_2100_ = lean_mk_empty_array_with_capacity(v___x_2099_);
lean_inc(v_fst_2061_);
v___x_2101_ = lean_array_push(v___x_2100_, v_fst_2061_);
v___x_2102_ = lean_ptr_addr(v_arg_2052_);
lean_dec_ref(v_arg_2052_);
v___x_2103_ = lean_ptr_addr(v_fst_2061_);
lean_dec(v_fst_2061_);
v___x_2104_ = lean_usize_dec_eq(v___x_2102_, v___x_2103_);
if (v___x_2104_ == 0)
{
lean_object* v___x_2105_; 
v___x_2105_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta(v_subst_2049_, v_e_2050_, v_f_2051_, v___x_2101_, v_offset_2053_, v___x_2064_, v_snd_2062_, v_a_2055_, v_a_2056_, v_a_2060_);
return v___x_2105_;
}
else
{
uint8_t v___x_2106_; lean_object* v___x_2107_; 
v___x_2106_ = 0;
v___x_2107_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta(v_subst_2049_, v_e_2050_, v_f_2051_, v___x_2101_, v_offset_2053_, v___x_2106_, v_snd_2062_, v_a_2055_, v_a_2056_, v_a_2060_);
return v___x_2107_;
}
}
}
else
{
lean_dec(v_offset_2053_);
lean_dec_ref(v_arg_2052_);
lean_dec_ref(v_f_2051_);
lean_dec_ref(v_e_2050_);
return v___x_2058_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_subst_2049_ = stack[0].m_obj;
lean_object* v_e_2050_ = stack[1].m_obj;
lean_object* v_f_2051_ = stack[2].m_obj;
lean_object* v_arg_2052_ = stack[3].m_obj;
lean_object* v_offset_2053_ = stack[4].m_obj;
lean_object* v_a_2054_ = stack[5].m_obj;
uint8_t v_a_2055_ = stack[6].m_num;
lean_object* v_a_2056_ = stack[7].m_obj;
lean_object* v_a_2057_ = stack[8].m_obj;
lean_object* v_res_2108_;
v_res_2108_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg(v_subst_2049_, v_e_2050_, v_f_2051_, v_arg_2052_, v_offset_2053_, v_a_2054_, v_a_2055_, v_a_2056_, v_a_2057_);
stack->m_obj
 = v_res_2108_;
}
static lean_object* _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__1(void){
_start:
{
lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; 
v___x_2110_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___closed__2));
v___x_2111_ = lean_unsigned_to_nat(59u);
v___x_2112_ = lean_unsigned_to_nat(176u);
v___x_2113_ = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__0));
v___x_2114_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__3));
v___x_2115_ = l_mkPanicMessageWithDecl(v___x_2114_, v___x_2113_, v___x_2112_, v___x_2111_, v___x_2110_);
return v___x_2115_;
}
}
lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit(lean_object* v_subst_2116_, lean_object* v_e_2117_, lean_object* v_offset_2118_, lean_object* v_a_2119_, uint8_t v_a_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_){
_start:
{
switch(lean_obj_tag(v_e_2117_))
{
case 0:
{
lean_object* v_deBruijnIndex_2123_; lean_object* v___x_2124_; 
v_deBruijnIndex_2123_ = lean_ctor_get(v_e_2117_, 0);
lean_inc(v_deBruijnIndex_2123_);
v___x_2124_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(v_subst_2116_, v_e_2117_, v_deBruijnIndex_2123_, v_offset_2118_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_);
lean_dec(v_offset_2118_);
lean_dec(v_deBruijnIndex_2123_);
return v___x_2124_;
}
case 5:
{
lean_object* v_fn_2125_; lean_object* v_arg_2126_; lean_object* v___x_2127_; 
v_fn_2125_ = lean_ctor_get(v_e_2117_, 0);
lean_inc_ref(v_fn_2125_);
v_arg_2126_ = lean_ctor_get(v_e_2117_, 1);
lean_inc_ref(v_arg_2126_);
v___x_2127_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg(v_subst_2116_, v_e_2117_, v_fn_2125_, v_arg_2126_, v_offset_2118_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_);
return v___x_2127_;
}
case 6:
{
lean_object* v_binderName_2128_; lean_object* v_binderType_2129_; lean_object* v_body_2130_; uint8_t v_binderInfo_2131_; lean_object* v___x_2132_; 
v_binderName_2128_ = lean_ctor_get(v_e_2117_, 0);
v_binderType_2129_ = lean_ctor_get(v_e_2117_, 1);
v_body_2130_ = lean_ctor_get(v_e_2117_, 2);
v_binderInfo_2131_ = lean_ctor_get_uint8(v_e_2117_, sizeof(void*)*3 + 8);
lean_inc(v_offset_2118_);
lean_inc_ref(v_binderType_2129_);
v___x_2132_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_2116_, v_binderType_2129_, v_offset_2118_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v_a_2133_; lean_object* v_a_2134_; lean_object* v_fst_2135_; lean_object* v_snd_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; 
v_a_2133_ = lean_ctor_get(v___x_2132_, 0);
lean_inc(v_a_2133_);
v_a_2134_ = lean_ctor_get(v___x_2132_, 1);
lean_inc(v_a_2134_);
lean_dec_ref_known(v___x_2132_, 2);
v_fst_2135_ = lean_ctor_get(v_a_2133_, 0);
lean_inc(v_fst_2135_);
v_snd_2136_ = lean_ctor_get(v_a_2133_, 1);
lean_inc(v_snd_2136_);
lean_dec(v_a_2133_);
v___x_2137_ = lean_unsigned_to_nat(1u);
v___x_2138_ = lean_nat_add(v_offset_2118_, v___x_2137_);
lean_dec(v_offset_2118_);
lean_inc_ref(v_body_2130_);
v___x_2139_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_2116_, v_body_2130_, v___x_2138_, v_snd_2136_, v_a_2120_, v_a_2121_, v_a_2134_);
if (lean_obj_tag(v___x_2139_) == 0)
{
lean_object* v_a_2140_; lean_object* v_a_2141_; lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2165_; 
v_a_2140_ = lean_ctor_get(v___x_2139_, 0);
v_a_2141_ = lean_ctor_get(v___x_2139_, 1);
v_isSharedCheck_2165_ = !lean_is_exclusive(v___x_2139_);
if (v_isSharedCheck_2165_ == 0)
{
v___x_2143_ = v___x_2139_;
v_isShared_2144_ = v_isSharedCheck_2165_;
goto v_resetjp_2142_;
}
else
{
lean_inc(v_a_2141_);
lean_inc(v_a_2140_);
lean_dec(v___x_2139_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2165_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
lean_object* v_fst_2145_; lean_object* v_snd_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2164_; 
v_fst_2145_ = lean_ctor_get(v_a_2140_, 0);
v_snd_2146_ = lean_ctor_get(v_a_2140_, 1);
v_isSharedCheck_2164_ = !lean_is_exclusive(v_a_2140_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2148_ = v_a_2140_;
v_isShared_2149_ = v_isSharedCheck_2164_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_snd_2146_);
lean_inc(v_fst_2145_);
lean_dec(v_a_2140_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2164_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
size_t v___x_2150_; size_t v___x_2151_; uint8_t v___x_2152_; 
v___x_2150_ = lean_ptr_addr(v_binderType_2129_);
v___x_2151_ = lean_ptr_addr(v_fst_2135_);
v___x_2152_ = lean_usize_dec_eq(v___x_2150_, v___x_2151_);
if (v___x_2152_ == 0)
{
lean_object* v___x_2153_; 
lean_inc(v_binderName_2128_);
lean_del_object(v___x_2148_);
lean_del_object(v___x_2143_);
lean_dec_ref_known(v_e_2117_, 3);
v___x_2153_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__3(v_binderName_2128_, v_binderInfo_2131_, v_fst_2135_, v_fst_2145_, v_snd_2146_, v_a_2120_, v_a_2121_, v_a_2141_);
return v___x_2153_;
}
else
{
size_t v___x_2154_; size_t v___x_2155_; uint8_t v___x_2156_; 
v___x_2154_ = lean_ptr_addr(v_body_2130_);
v___x_2155_ = lean_ptr_addr(v_fst_2145_);
v___x_2156_ = lean_usize_dec_eq(v___x_2154_, v___x_2155_);
if (v___x_2156_ == 0)
{
lean_object* v___x_2157_; 
lean_inc(v_binderName_2128_);
lean_del_object(v___x_2148_);
lean_del_object(v___x_2143_);
lean_dec_ref_known(v_e_2117_, 3);
v___x_2157_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__3(v_binderName_2128_, v_binderInfo_2131_, v_fst_2135_, v_fst_2145_, v_snd_2146_, v_a_2120_, v_a_2121_, v_a_2141_);
return v___x_2157_;
}
else
{
lean_object* v___x_2159_; 
lean_dec(v_fst_2145_);
lean_dec(v_fst_2135_);
if (v_isShared_2149_ == 0)
{
lean_ctor_set(v___x_2148_, 0, v_e_2117_);
v___x_2159_ = v___x_2148_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v_e_2117_);
lean_ctor_set(v_reuseFailAlloc_2163_, 1, v_snd_2146_);
v___x_2159_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
lean_object* v___x_2161_; 
if (v_isShared_2144_ == 0)
{
lean_ctor_set(v___x_2143_, 0, v___x_2159_);
v___x_2161_ = v___x_2143_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v___x_2159_);
lean_ctor_set(v_reuseFailAlloc_2162_, 1, v_a_2141_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_2135_);
lean_dec_ref_known(v_e_2117_, 3);
return v___x_2139_;
}
}
else
{
lean_dec_ref_known(v_e_2117_, 3);
lean_dec(v_offset_2118_);
return v___x_2132_;
}
}
case 7:
{
lean_object* v_binderName_2166_; lean_object* v_binderType_2167_; lean_object* v_body_2168_; uint8_t v_binderInfo_2169_; lean_object* v___x_2170_; 
v_binderName_2166_ = lean_ctor_get(v_e_2117_, 0);
v_binderType_2167_ = lean_ctor_get(v_e_2117_, 1);
v_body_2168_ = lean_ctor_get(v_e_2117_, 2);
v_binderInfo_2169_ = lean_ctor_get_uint8(v_e_2117_, sizeof(void*)*3 + 8);
lean_inc(v_offset_2118_);
lean_inc_ref(v_binderType_2167_);
v___x_2170_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_2116_, v_binderType_2167_, v_offset_2118_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_);
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
v___x_2176_ = lean_nat_add(v_offset_2118_, v___x_2175_);
lean_dec(v_offset_2118_);
lean_inc_ref(v_body_2168_);
v___x_2177_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_2116_, v_body_2168_, v___x_2176_, v_snd_2174_, v_a_2120_, v_a_2121_, v_a_2172_);
if (lean_obj_tag(v___x_2177_) == 0)
{
lean_object* v_a_2178_; lean_object* v_a_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2203_; 
v_a_2178_ = lean_ctor_get(v___x_2177_, 0);
v_a_2179_ = lean_ctor_get(v___x_2177_, 1);
v_isSharedCheck_2203_ = !lean_is_exclusive(v___x_2177_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_2181_ = v___x_2177_;
v_isShared_2182_ = v_isSharedCheck_2203_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_a_2179_);
lean_inc(v_a_2178_);
lean_dec(v___x_2177_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2203_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v_fst_2183_; lean_object* v_snd_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2202_; 
v_fst_2183_ = lean_ctor_get(v_a_2178_, 0);
v_snd_2184_ = lean_ctor_get(v_a_2178_, 1);
v_isSharedCheck_2202_ = !lean_is_exclusive(v_a_2178_);
if (v_isSharedCheck_2202_ == 0)
{
v___x_2186_ = v_a_2178_;
v_isShared_2187_ = v_isSharedCheck_2202_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_snd_2184_);
lean_inc(v_fst_2183_);
lean_dec(v_a_2178_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2202_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
size_t v___x_2188_; size_t v___x_2189_; uint8_t v___x_2190_; 
v___x_2188_ = lean_ptr_addr(v_binderType_2167_);
v___x_2189_ = lean_ptr_addr(v_fst_2173_);
v___x_2190_ = lean_usize_dec_eq(v___x_2188_, v___x_2189_);
if (v___x_2190_ == 0)
{
lean_object* v___x_2191_; 
lean_inc(v_binderName_2166_);
lean_del_object(v___x_2186_);
lean_del_object(v___x_2181_);
lean_dec_ref_known(v_e_2117_, 3);
v___x_2191_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__4(v_binderName_2166_, v_binderInfo_2169_, v_fst_2173_, v_fst_2183_, v_snd_2184_, v_a_2120_, v_a_2121_, v_a_2179_);
return v___x_2191_;
}
else
{
size_t v___x_2192_; size_t v___x_2193_; uint8_t v___x_2194_; 
v___x_2192_ = lean_ptr_addr(v_body_2168_);
v___x_2193_ = lean_ptr_addr(v_fst_2183_);
v___x_2194_ = lean_usize_dec_eq(v___x_2192_, v___x_2193_);
if (v___x_2194_ == 0)
{
lean_object* v___x_2195_; 
lean_inc(v_binderName_2166_);
lean_del_object(v___x_2186_);
lean_del_object(v___x_2181_);
lean_dec_ref_known(v_e_2117_, 3);
v___x_2195_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__4(v_binderName_2166_, v_binderInfo_2169_, v_fst_2173_, v_fst_2183_, v_snd_2184_, v_a_2120_, v_a_2121_, v_a_2179_);
return v___x_2195_;
}
else
{
lean_object* v___x_2197_; 
lean_dec(v_fst_2183_);
lean_dec(v_fst_2173_);
if (v_isShared_2187_ == 0)
{
lean_ctor_set(v___x_2186_, 0, v_e_2117_);
v___x_2197_ = v___x_2186_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v_e_2117_);
lean_ctor_set(v_reuseFailAlloc_2201_, 1, v_snd_2184_);
v___x_2197_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
lean_object* v___x_2199_; 
if (v_isShared_2182_ == 0)
{
lean_ctor_set(v___x_2181_, 0, v___x_2197_);
v___x_2199_ = v___x_2181_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v___x_2197_);
lean_ctor_set(v_reuseFailAlloc_2200_, 1, v_a_2179_);
v___x_2199_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
return v___x_2199_;
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
lean_dec_ref_known(v_e_2117_, 3);
return v___x_2177_;
}
}
else
{
lean_dec_ref_known(v_e_2117_, 3);
lean_dec(v_offset_2118_);
return v___x_2170_;
}
}
case 8:
{
lean_object* v_declName_2204_; lean_object* v_type_2205_; lean_object* v_value_2206_; lean_object* v_body_2207_; uint8_t v_nondep_2208_; lean_object* v___x_2209_; 
v_declName_2204_ = lean_ctor_get(v_e_2117_, 0);
v_type_2205_ = lean_ctor_get(v_e_2117_, 1);
v_value_2206_ = lean_ctor_get(v_e_2117_, 2);
v_body_2207_ = lean_ctor_get(v_e_2117_, 3);
v_nondep_2208_ = lean_ctor_get_uint8(v_e_2117_, sizeof(void*)*4 + 8);
lean_inc(v_offset_2118_);
lean_inc_ref(v_type_2205_);
v___x_2209_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_2116_, v_type_2205_, v_offset_2118_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_);
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
lean_inc(v_offset_2118_);
lean_inc_ref(v_value_2206_);
v___x_2214_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_2116_, v_value_2206_, v_offset_2118_, v_snd_2213_, v_a_2120_, v_a_2121_, v_a_2211_);
if (lean_obj_tag(v___x_2214_) == 0)
{
lean_object* v_a_2215_; lean_object* v_a_2216_; lean_object* v_fst_2217_; lean_object* v_snd_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; 
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
v___x_2219_ = lean_unsigned_to_nat(1u);
v___x_2220_ = lean_nat_add(v_offset_2118_, v___x_2219_);
lean_dec(v_offset_2118_);
lean_inc_ref(v_body_2207_);
v___x_2221_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_2116_, v_body_2207_, v___x_2220_, v_snd_2218_, v_a_2120_, v_a_2121_, v_a_2216_);
if (lean_obj_tag(v___x_2221_) == 0)
{
lean_object* v_a_2222_; lean_object* v_a_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2251_; 
v_a_2222_ = lean_ctor_get(v___x_2221_, 0);
v_a_2223_ = lean_ctor_get(v___x_2221_, 1);
v_isSharedCheck_2251_ = !lean_is_exclusive(v___x_2221_);
if (v_isSharedCheck_2251_ == 0)
{
v___x_2225_ = v___x_2221_;
v_isShared_2226_ = v_isSharedCheck_2251_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_a_2223_);
lean_inc(v_a_2222_);
lean_dec(v___x_2221_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2251_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v_fst_2227_; lean_object* v_snd_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2250_; 
v_fst_2227_ = lean_ctor_get(v_a_2222_, 0);
v_snd_2228_ = lean_ctor_get(v_a_2222_, 1);
v_isSharedCheck_2250_ = !lean_is_exclusive(v_a_2222_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2230_ = v_a_2222_;
v_isShared_2231_ = v_isSharedCheck_2250_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_snd_2228_);
lean_inc(v_fst_2227_);
lean_dec(v_a_2222_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2250_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
size_t v___x_2232_; size_t v___x_2233_; uint8_t v___x_2234_; 
v___x_2232_ = lean_ptr_addr(v_type_2205_);
v___x_2233_ = lean_ptr_addr(v_fst_2212_);
v___x_2234_ = lean_usize_dec_eq(v___x_2232_, v___x_2233_);
if (v___x_2234_ == 0)
{
lean_object* v___x_2235_; 
lean_inc(v_declName_2204_);
lean_del_object(v___x_2230_);
lean_del_object(v___x_2225_);
lean_dec_ref_known(v_e_2117_, 4);
v___x_2235_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__5(v_declName_2204_, v_fst_2212_, v_fst_2217_, v_fst_2227_, v_nondep_2208_, v_snd_2228_, v_a_2120_, v_a_2121_, v_a_2223_);
return v___x_2235_;
}
else
{
size_t v___x_2236_; size_t v___x_2237_; uint8_t v___x_2238_; 
v___x_2236_ = lean_ptr_addr(v_value_2206_);
v___x_2237_ = lean_ptr_addr(v_fst_2217_);
v___x_2238_ = lean_usize_dec_eq(v___x_2236_, v___x_2237_);
if (v___x_2238_ == 0)
{
lean_object* v___x_2239_; 
lean_inc(v_declName_2204_);
lean_del_object(v___x_2230_);
lean_del_object(v___x_2225_);
lean_dec_ref_known(v_e_2117_, 4);
v___x_2239_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__5(v_declName_2204_, v_fst_2212_, v_fst_2217_, v_fst_2227_, v_nondep_2208_, v_snd_2228_, v_a_2120_, v_a_2121_, v_a_2223_);
return v___x_2239_;
}
else
{
size_t v___x_2240_; size_t v___x_2241_; uint8_t v___x_2242_; 
v___x_2240_ = lean_ptr_addr(v_body_2207_);
v___x_2241_ = lean_ptr_addr(v_fst_2227_);
v___x_2242_ = lean_usize_dec_eq(v___x_2240_, v___x_2241_);
if (v___x_2242_ == 0)
{
lean_object* v___x_2243_; 
lean_inc(v_declName_2204_);
lean_del_object(v___x_2230_);
lean_del_object(v___x_2225_);
lean_dec_ref_known(v_e_2117_, 4);
v___x_2243_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__5(v_declName_2204_, v_fst_2212_, v_fst_2217_, v_fst_2227_, v_nondep_2208_, v_snd_2228_, v_a_2120_, v_a_2121_, v_a_2223_);
return v___x_2243_;
}
else
{
lean_object* v___x_2245_; 
lean_dec(v_fst_2227_);
lean_dec(v_fst_2217_);
lean_dec(v_fst_2212_);
if (v_isShared_2231_ == 0)
{
lean_ctor_set(v___x_2230_, 0, v_e_2117_);
v___x_2245_ = v___x_2230_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v_e_2117_);
lean_ctor_set(v_reuseFailAlloc_2249_, 1, v_snd_2228_);
v___x_2245_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
lean_object* v___x_2247_; 
if (v_isShared_2226_ == 0)
{
lean_ctor_set(v___x_2225_, 0, v___x_2245_);
v___x_2247_ = v___x_2225_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v___x_2245_);
lean_ctor_set(v_reuseFailAlloc_2248_, 1, v_a_2223_);
v___x_2247_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
return v___x_2247_;
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
lean_dec(v_fst_2217_);
lean_dec(v_fst_2212_);
lean_dec_ref_known(v_e_2117_, 4);
return v___x_2221_;
}
}
else
{
lean_dec(v_fst_2212_);
lean_dec_ref_known(v_e_2117_, 4);
lean_dec(v_offset_2118_);
return v___x_2214_;
}
}
else
{
lean_dec_ref_known(v_e_2117_, 4);
lean_dec(v_offset_2118_);
return v___x_2209_;
}
}
case 10:
{
lean_object* v_data_2252_; lean_object* v_expr_2253_; lean_object* v___x_2254_; 
v_data_2252_ = lean_ctor_get(v_e_2117_, 0);
v_expr_2253_ = lean_ctor_get(v_e_2117_, 1);
lean_inc_ref(v_expr_2253_);
v___x_2254_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_2116_, v_expr_2253_, v_offset_2118_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_);
if (lean_obj_tag(v___x_2254_) == 0)
{
lean_object* v_a_2255_; lean_object* v_a_2256_; lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2276_; 
v_a_2255_ = lean_ctor_get(v___x_2254_, 0);
v_a_2256_ = lean_ctor_get(v___x_2254_, 1);
v_isSharedCheck_2276_ = !lean_is_exclusive(v___x_2254_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2258_ = v___x_2254_;
v_isShared_2259_ = v_isSharedCheck_2276_;
goto v_resetjp_2257_;
}
else
{
lean_inc(v_a_2256_);
lean_inc(v_a_2255_);
lean_dec(v___x_2254_);
v___x_2258_ = lean_box(0);
v_isShared_2259_ = v_isSharedCheck_2276_;
goto v_resetjp_2257_;
}
v_resetjp_2257_:
{
lean_object* v_fst_2260_; lean_object* v_snd_2261_; lean_object* v___x_2263_; uint8_t v_isShared_2264_; uint8_t v_isSharedCheck_2275_; 
v_fst_2260_ = lean_ctor_get(v_a_2255_, 0);
v_snd_2261_ = lean_ctor_get(v_a_2255_, 1);
v_isSharedCheck_2275_ = !lean_is_exclusive(v_a_2255_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2263_ = v_a_2255_;
v_isShared_2264_ = v_isSharedCheck_2275_;
goto v_resetjp_2262_;
}
else
{
lean_inc(v_snd_2261_);
lean_inc(v_fst_2260_);
lean_dec(v_a_2255_);
v___x_2263_ = lean_box(0);
v_isShared_2264_ = v_isSharedCheck_2275_;
goto v_resetjp_2262_;
}
v_resetjp_2262_:
{
size_t v___x_2265_; size_t v___x_2266_; uint8_t v___x_2267_; 
v___x_2265_ = lean_ptr_addr(v_expr_2253_);
v___x_2266_ = lean_ptr_addr(v_fst_2260_);
v___x_2267_ = lean_usize_dec_eq(v___x_2265_, v___x_2266_);
if (v___x_2267_ == 0)
{
lean_object* v___x_2268_; 
lean_inc(v_data_2252_);
lean_del_object(v___x_2263_);
lean_del_object(v___x_2258_);
lean_dec_ref_known(v_e_2117_, 2);
v___x_2268_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__6(v_data_2252_, v_fst_2260_, v_snd_2261_, v_a_2120_, v_a_2121_, v_a_2256_);
return v___x_2268_;
}
else
{
lean_object* v___x_2270_; 
lean_dec(v_fst_2260_);
if (v_isShared_2264_ == 0)
{
lean_ctor_set(v___x_2263_, 0, v_e_2117_);
v___x_2270_ = v___x_2263_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_e_2117_);
lean_ctor_set(v_reuseFailAlloc_2274_, 1, v_snd_2261_);
v___x_2270_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
lean_object* v___x_2272_; 
if (v_isShared_2259_ == 0)
{
lean_ctor_set(v___x_2258_, 0, v___x_2270_);
v___x_2272_ = v___x_2258_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v___x_2270_);
lean_ctor_set(v_reuseFailAlloc_2273_, 1, v_a_2256_);
v___x_2272_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
return v___x_2272_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2117_, 2);
return v___x_2254_;
}
}
case 11:
{
lean_object* v_typeName_2277_; lean_object* v_idx_2278_; lean_object* v_struct_2279_; lean_object* v___x_2280_; 
v_typeName_2277_ = lean_ctor_get(v_e_2117_, 0);
v_idx_2278_ = lean_ctor_get(v_e_2117_, 1);
v_struct_2279_ = lean_ctor_get(v_e_2117_, 2);
lean_inc_ref(v_struct_2279_);
v___x_2280_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_2116_, v_struct_2279_, v_offset_2118_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_);
if (lean_obj_tag(v___x_2280_) == 0)
{
lean_object* v_a_2281_; lean_object* v_a_2282_; lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2302_; 
v_a_2281_ = lean_ctor_get(v___x_2280_, 0);
v_a_2282_ = lean_ctor_get(v___x_2280_, 1);
v_isSharedCheck_2302_ = !lean_is_exclusive(v___x_2280_);
if (v_isSharedCheck_2302_ == 0)
{
v___x_2284_ = v___x_2280_;
v_isShared_2285_ = v_isSharedCheck_2302_;
goto v_resetjp_2283_;
}
else
{
lean_inc(v_a_2282_);
lean_inc(v_a_2281_);
lean_dec(v___x_2280_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2302_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v_fst_2286_; lean_object* v_snd_2287_; lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2301_; 
v_fst_2286_ = lean_ctor_get(v_a_2281_, 0);
v_snd_2287_ = lean_ctor_get(v_a_2281_, 1);
v_isSharedCheck_2301_ = !lean_is_exclusive(v_a_2281_);
if (v_isSharedCheck_2301_ == 0)
{
v___x_2289_ = v_a_2281_;
v_isShared_2290_ = v_isSharedCheck_2301_;
goto v_resetjp_2288_;
}
else
{
lean_inc(v_snd_2287_);
lean_inc(v_fst_2286_);
lean_dec(v_a_2281_);
v___x_2289_ = lean_box(0);
v_isShared_2290_ = v_isSharedCheck_2301_;
goto v_resetjp_2288_;
}
v_resetjp_2288_:
{
size_t v___x_2291_; size_t v___x_2292_; uint8_t v___x_2293_; 
v___x_2291_ = lean_ptr_addr(v_struct_2279_);
v___x_2292_ = lean_ptr_addr(v_fst_2286_);
v___x_2293_ = lean_usize_dec_eq(v___x_2291_, v___x_2292_);
if (v___x_2293_ == 0)
{
lean_object* v___x_2294_; 
lean_inc(v_idx_2278_);
lean_inc(v_typeName_2277_);
lean_del_object(v___x_2289_);
lean_del_object(v___x_2284_);
lean_dec_ref_known(v_e_2117_, 3);
v___x_2294_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__7(v_typeName_2277_, v_idx_2278_, v_fst_2286_, v_snd_2287_, v_a_2120_, v_a_2121_, v_a_2282_);
return v___x_2294_;
}
else
{
lean_object* v___x_2296_; 
lean_dec(v_fst_2286_);
if (v_isShared_2290_ == 0)
{
lean_ctor_set(v___x_2289_, 0, v_e_2117_);
v___x_2296_ = v___x_2289_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v_e_2117_);
lean_ctor_set(v_reuseFailAlloc_2300_, 1, v_snd_2287_);
v___x_2296_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
lean_object* v___x_2298_; 
if (v_isShared_2285_ == 0)
{
lean_ctor_set(v___x_2284_, 0, v___x_2296_);
v___x_2298_ = v___x_2284_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v___x_2296_);
lean_ctor_set(v_reuseFailAlloc_2299_, 1, v_a_2282_);
v___x_2298_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
return v___x_2298_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2117_, 3);
return v___x_2280_;
}
}
default: 
{
lean_object* v___x_2303_; lean_object* v___x_2304_; 
lean_dec(v_offset_2118_);
lean_dec_ref(v_e_2117_);
v___x_2303_ = lean_obj_once(&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__1, &l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__1_once, _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__1);
v___x_2304_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__8(v___x_2303_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_);
return v___x_2304_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit_0interp(lean_interpreter_value* stack)
{
lean_object* v_subst_2116_ = stack[0].m_obj;
lean_object* v_e_2117_ = stack[1].m_obj;
lean_object* v_offset_2118_ = stack[2].m_obj;
lean_object* v_a_2119_ = stack[3].m_obj;
uint8_t v_a_2120_ = stack[4].m_num;
lean_object* v_a_2121_ = stack[5].m_obj;
lean_object* v_a_2122_ = stack[6].m_obj;
lean_object* v_res_2305_;
v_res_2305_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit(v_subst_2116_, v_e_2117_, v_offset_2118_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_);
stack->m_obj
 = v_res_2305_;
}
lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(lean_object* v_subst_2306_, lean_object* v_e_2307_, lean_object* v_offset_2308_, lean_object* v_a_2309_, uint8_t v_a_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_){
_start:
{
lean_object* v___x_2313_; uint8_t v___x_2314_; 
v___x_2313_ = l_Lean_Expr_looseBVarRange(v_e_2307_);
v___x_2314_ = lean_nat_dec_le(v___x_2313_, v_offset_2308_);
lean_dec(v___x_2313_);
if (v___x_2314_ == 0)
{
lean_object* v_key_2315_; lean_object* v___x_2316_; 
lean_inc(v_offset_2308_);
lean_inc_ref(v_e_2307_);
v_key_2315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_2315_, 0, v_e_2307_);
lean_ctor_set(v_key_2315_, 1, v_offset_2308_);
v___x_2316_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1_spec__1_spec__3___redArg(v_a_2309_, v_key_2315_);
if (lean_obj_tag(v___x_2316_) == 1)
{
lean_object* v_val_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; 
lean_dec_ref_known(v_key_2315_, 2);
lean_dec(v_offset_2308_);
lean_dec_ref(v_e_2307_);
v_val_2317_ = lean_ctor_get(v___x_2316_, 0);
lean_inc(v_val_2317_);
lean_dec_ref_known(v___x_2316_, 1);
v___x_2318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2318_, 0, v_val_2317_);
lean_ctor_set(v___x_2318_, 1, v_a_2309_);
v___x_2319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2319_, 0, v___x_2318_);
lean_ctor_set(v___x_2319_, 1, v_a_2312_);
return v___x_2319_;
}
else
{
lean_dec(v___x_2316_);
switch(lean_obj_tag(v_e_2307_))
{
case 0:
{
lean_object* v_deBruijnIndex_2320_; lean_object* v___x_2321_; 
v_deBruijnIndex_2320_ = lean_ctor_get(v_e_2307_, 0);
lean_inc(v_deBruijnIndex_2320_);
v___x_2321_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(v_subst_2306_, v_e_2307_, v_deBruijnIndex_2320_, v_offset_2308_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_);
lean_dec(v_offset_2308_);
lean_dec(v_deBruijnIndex_2320_);
if (lean_obj_tag(v___x_2321_) == 0)
{
lean_object* v_a_2322_; lean_object* v_a_2323_; lean_object* v_fst_2324_; lean_object* v_snd_2325_; lean_object* v___x_2326_; 
v_a_2322_ = lean_ctor_get(v___x_2321_, 0);
lean_inc(v_a_2322_);
v_a_2323_ = lean_ctor_get(v___x_2321_, 1);
lean_inc(v_a_2323_);
lean_dec_ref_known(v___x_2321_, 2);
v_fst_2324_ = lean_ctor_get(v_a_2322_, 0);
lean_inc(v_fst_2324_);
v_snd_2325_ = lean_ctor_get(v_a_2322_, 1);
lean_inc(v_snd_2325_);
lean_dec(v_a_2322_);
v___x_2326_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_2315_, v_fst_2324_, v_snd_2325_, v_a_2323_);
return v___x_2326_;
}
else
{
lean_dec_ref_known(v_key_2315_, 2);
return v___x_2321_;
}
}
case 9:
{
lean_object* v___x_2327_; 
lean_dec(v_offset_2308_);
v___x_2327_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_2315_, v_e_2307_, v_a_2309_, v_a_2312_);
return v___x_2327_;
}
case 2:
{
lean_object* v___x_2328_; 
lean_dec(v_offset_2308_);
v___x_2328_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_2315_, v_e_2307_, v_a_2309_, v_a_2312_);
return v___x_2328_;
}
case 1:
{
lean_object* v___x_2329_; 
lean_dec(v_offset_2308_);
v___x_2329_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_2315_, v_e_2307_, v_a_2309_, v_a_2312_);
return v___x_2329_;
}
case 4:
{
lean_object* v___x_2330_; 
lean_dec(v_offset_2308_);
v___x_2330_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_2315_, v_e_2307_, v_a_2309_, v_a_2312_);
return v___x_2330_;
}
case 3:
{
lean_object* v___x_2331_; 
lean_dec(v_offset_2308_);
v___x_2331_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_2315_, v_e_2307_, v_a_2309_, v_a_2312_);
return v___x_2331_;
}
default: 
{
lean_object* v___x_2332_; 
v___x_2332_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit(v_subst_2306_, v_e_2307_, v_offset_2308_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_);
if (lean_obj_tag(v___x_2332_) == 0)
{
lean_object* v_a_2333_; lean_object* v_a_2334_; lean_object* v_fst_2335_; lean_object* v_snd_2336_; lean_object* v___x_2337_; 
v_a_2333_ = lean_ctor_get(v___x_2332_, 0);
lean_inc(v_a_2333_);
v_a_2334_ = lean_ctor_get(v___x_2332_, 1);
lean_inc(v_a_2334_);
lean_dec_ref_known(v___x_2332_, 2);
v_fst_2335_ = lean_ctor_get(v_a_2333_, 0);
lean_inc(v_fst_2335_);
v_snd_2336_ = lean_ctor_get(v_a_2333_, 1);
lean_inc(v_snd_2336_);
lean_dec(v_a_2333_);
v___x_2337_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_2315_, v_fst_2335_, v_snd_2336_, v_a_2334_);
return v___x_2337_;
}
else
{
lean_dec_ref_known(v_key_2315_, 2);
return v___x_2332_;
}
}
}
}
}
else
{
lean_object* v___x_2338_; lean_object* v___x_2339_; 
lean_dec(v_offset_2308_);
v___x_2338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2338_, 0, v_e_2307_);
lean_ctor_set(v___x_2338_, 1, v_a_2309_);
v___x_2339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2339_, 0, v___x_2338_);
lean_ctor_set(v___x_2339_, 1, v_a_2312_);
return v___x_2339_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild_0interp(lean_interpreter_value* stack)
{
lean_object* v_subst_2306_ = stack[0].m_obj;
lean_object* v_e_2307_ = stack[1].m_obj;
lean_object* v_offset_2308_ = stack[2].m_obj;
lean_object* v_a_2309_ = stack[3].m_obj;
uint8_t v_a_2310_ = stack[4].m_num;
lean_object* v_a_2311_ = stack[5].m_obj;
lean_object* v_a_2312_ = stack[6].m_obj;
lean_object* v_res_2340_;
v_res_2340_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_2306_, v_e_2307_, v_offset_2308_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_);
stack->m_obj
 = v_res_2340_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild___boxed(lean_object* v_subst_2341_, lean_object* v_e_2342_, lean_object* v_offset_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_){
_start:
{
uint8_t v_a_boxed_2348_; lean_object* v_res_2349_; 
v_a_boxed_2348_ = lean_unbox(v_a_2345_);
v_res_2349_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_2341_, v_e_2342_, v_offset_2343_, v_a_2344_, v_a_boxed_2348_, v_a_2346_, v_a_2347_);
lean_dec_ref(v_a_2346_);
lean_dec_ref(v_subst_2341_);
return v_res_2349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault___boxed(lean_object* v_subst_2350_, lean_object* v_e_2351_, lean_object* v_offset_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_){
_start:
{
uint8_t v_a_boxed_2357_; lean_object* v_res_2358_; 
v_a_boxed_2357_ = lean_unbox(v_a_2354_);
v_res_2358_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault(v_subst_2350_, v_e_2351_, v_offset_2352_, v_a_2353_, v_a_boxed_2357_, v_a_2355_, v_a_2356_);
lean_dec_ref(v_a_2355_);
lean_dec_ref(v_subst_2350_);
return v_res_2358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___boxed(lean_object* v_subst_2359_, lean_object* v_e_2360_, lean_object* v_f_2361_, lean_object* v_arg_2362_, lean_object* v_offset_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_){
_start:
{
uint8_t v_a_boxed_2368_; lean_object* v_res_2369_; 
v_a_boxed_2368_ = lean_unbox(v_a_2365_);
v_res_2369_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg(v_subst_2359_, v_e_2360_, v_f_2361_, v_arg_2362_, v_offset_2363_, v_a_2364_, v_a_boxed_2368_, v_a_2366_, v_a_2367_);
lean_dec_ref(v_a_2366_);
lean_dec_ref(v_subst_2359_);
return v_res_2369_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___boxed(lean_object* v_subst_2370_, lean_object* v_e_2371_, lean_object* v_f_2372_, lean_object* v_argsRev_2373_, lean_object* v_offset_2374_, lean_object* v_modified_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_){
_start:
{
uint8_t v_modified_boxed_2380_; uint8_t v_a_boxed_2381_; lean_object* v_res_2382_; 
v_modified_boxed_2380_ = lean_unbox(v_modified_2375_);
v_a_boxed_2381_ = lean_unbox(v_a_2377_);
v_res_2382_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta(v_subst_2370_, v_e_2371_, v_f_2372_, v_argsRev_2373_, v_offset_2374_, v_modified_boxed_2380_, v_a_2376_, v_a_boxed_2381_, v_a_2378_, v_a_2379_);
lean_dec_ref(v_a_2378_);
lean_dec_ref(v_subst_2370_);
return v_res_2382_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___boxed(lean_object* v_subst_2383_, lean_object* v_e_2384_, lean_object* v_offset_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_){
_start:
{
uint8_t v_a_boxed_2390_; lean_object* v_res_2391_; 
v_a_boxed_2390_ = lean_unbox(v_a_2387_);
v_res_2391_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit(v_subst_2383_, v_e_2384_, v_offset_2385_, v_a_2386_, v_a_boxed_2390_, v_a_2388_, v_a_2389_);
lean_dec_ref(v_a_2388_);
lean_dec_ref(v_subst_2383_);
return v_res_2391_;
}
}
lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp(lean_object* v_subst_2392_, lean_object* v_e_2393_, lean_object* v_f_2394_, lean_object* v_arg_2395_, lean_object* v_offset_2396_, lean_object* v_x_2397_, lean_object* v_a_2398_, uint8_t v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_){
_start:
{
lean_object* v___x_2402_; 
v___x_2402_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg(v_subst_2392_, v_e_2393_, v_f_2394_, v_arg_2395_, v_offset_2396_, v_a_2398_, v_a_2399_, v_a_2400_, v_a_2401_);
return v___x_2402_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp_0interp(lean_interpreter_value* stack)
{
lean_object* v_subst_2392_ = stack[0].m_obj;
lean_object* v_e_2393_ = stack[1].m_obj;
lean_object* v_f_2394_ = stack[2].m_obj;
lean_object* v_arg_2395_ = stack[3].m_obj;
lean_object* v_offset_2396_ = stack[4].m_obj;
lean_object* v_a_2398_ = stack[6].m_obj;
uint8_t v_a_2399_ = stack[7].m_num;
lean_object* v_a_2400_ = stack[8].m_obj;
lean_object* v_a_2401_ = stack[9].m_obj;
lean_object* v_res_2403_;
v_res_2403_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp(v_subst_2392_, v_e_2393_, v_f_2394_, v_arg_2395_, v_offset_2396_, lean_box(0), v_a_2398_, v_a_2399_, v_a_2400_, v_a_2401_);
stack->m_obj
 = v_res_2403_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___boxed(lean_object* v_subst_2404_, lean_object* v_e_2405_, lean_object* v_f_2406_, lean_object* v_arg_2407_, lean_object* v_offset_2408_, lean_object* v_x_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_){
_start:
{
uint8_t v_a_boxed_2414_; lean_object* v_res_2415_; 
v_a_boxed_2414_ = lean_unbox(v_a_2411_);
v_res_2415_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp(v_subst_2404_, v_e_2405_, v_f_2406_, v_arg_2407_, v_offset_2408_, v_x_2409_, v_a_2410_, v_a_boxed_2414_, v_a_2412_, v_a_2413_);
lean_dec_ref(v_a_2412_);
lean_dec_ref(v_subst_2404_);
return v_res_2415_;
}
}
lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27(lean_object* v_e_2416_, lean_object* v_subst_2417_, uint8_t v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_){
_start:
{
lean_object* v___x_2421_; lean_object* v___x_2422_; uint8_t v___x_2423_; 
v___x_2421_ = lean_array_get_size(v_subst_2417_);
v___x_2422_ = lean_unsigned_to_nat(0u);
v___x_2423_ = lean_nat_dec_eq(v___x_2421_, v___x_2422_);
if (v___x_2423_ == 0)
{
uint8_t v___x_2424_; 
v___x_2424_ = l_Lean_Expr_hasLooseBVars(v_e_2416_);
if (v___x_2424_ == 0)
{
lean_object* v___x_2425_; 
v___x_2425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2425_, 0, v_e_2416_);
lean_ctor_set(v___x_2425_, 1, v_a_2420_);
return v___x_2425_;
}
else
{
lean_object* v___x_2426_; lean_object* v___x_2427_; 
v___x_2426_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__1, &l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__1_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___lam__0___closed__1);
v___x_2427_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit(v_subst_2417_, v_e_2416_, v___x_2422_, v___x_2426_, v_a_2418_, v_a_2419_, v_a_2420_);
if (lean_obj_tag(v___x_2427_) == 0)
{
lean_object* v_a_2428_; lean_object* v_a_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2437_; 
v_a_2428_ = lean_ctor_get(v___x_2427_, 0);
v_a_2429_ = lean_ctor_get(v___x_2427_, 1);
v_isSharedCheck_2437_ = !lean_is_exclusive(v___x_2427_);
if (v_isSharedCheck_2437_ == 0)
{
v___x_2431_ = v___x_2427_;
v_isShared_2432_ = v_isSharedCheck_2437_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_a_2429_);
lean_inc(v_a_2428_);
lean_dec(v___x_2427_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2437_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
lean_object* v_fst_2433_; lean_object* v___x_2435_; 
v_fst_2433_ = lean_ctor_get(v_a_2428_, 0);
lean_inc(v_fst_2433_);
lean_dec(v_a_2428_);
if (v_isShared_2432_ == 0)
{
lean_ctor_set(v___x_2431_, 0, v_fst_2433_);
v___x_2435_ = v___x_2431_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v_fst_2433_);
lean_ctor_set(v_reuseFailAlloc_2436_, 1, v_a_2429_);
v___x_2435_ = v_reuseFailAlloc_2436_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
return v___x_2435_;
}
}
}
else
{
lean_object* v_a_2438_; lean_object* v_a_2439_; lean_object* v___x_2441_; uint8_t v_isShared_2442_; uint8_t v_isSharedCheck_2446_; 
v_a_2438_ = lean_ctor_get(v___x_2427_, 0);
v_a_2439_ = lean_ctor_get(v___x_2427_, 1);
v_isSharedCheck_2446_ = !lean_is_exclusive(v___x_2427_);
if (v_isSharedCheck_2446_ == 0)
{
v___x_2441_ = v___x_2427_;
v_isShared_2442_ = v_isSharedCheck_2446_;
goto v_resetjp_2440_;
}
else
{
lean_inc(v_a_2439_);
lean_inc(v_a_2438_);
lean_dec(v___x_2427_);
v___x_2441_ = lean_box(0);
v_isShared_2442_ = v_isSharedCheck_2446_;
goto v_resetjp_2440_;
}
v_resetjp_2440_:
{
lean_object* v___x_2444_; 
if (v_isShared_2442_ == 0)
{
v___x_2444_ = v___x_2441_;
goto v_reusejp_2443_;
}
else
{
lean_object* v_reuseFailAlloc_2445_; 
v_reuseFailAlloc_2445_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2445_, 0, v_a_2438_);
lean_ctor_set(v_reuseFailAlloc_2445_, 1, v_a_2439_);
v___x_2444_ = v_reuseFailAlloc_2445_;
goto v_reusejp_2443_;
}
v_reusejp_2443_:
{
return v___x_2444_;
}
}
}
}
}
else
{
lean_object* v___x_2447_; 
v___x_2447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2447_, 0, v_e_2416_);
lean_ctor_set(v___x_2447_, 1, v_a_2420_);
return v___x_2447_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2416_ = stack[0].m_obj;
lean_object* v_subst_2417_ = stack[1].m_obj;
uint8_t v_a_2418_ = stack[2].m_num;
lean_object* v_a_2419_ = stack[3].m_obj;
lean_object* v_a_2420_ = stack[4].m_obj;
lean_object* v_res_2448_;
v_res_2448_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27(v_e_2416_, v_subst_2417_, v_a_2418_, v_a_2419_, v_a_2420_);
stack->m_obj
 = v_res_2448_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27___boxed(lean_object* v_e_2449_, lean_object* v_subst_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_){
_start:
{
uint8_t v_a_boxed_2454_; lean_object* v_res_2455_; 
v_a_boxed_2454_ = lean_unbox(v_a_2451_);
v_res_2455_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27(v_e_2449_, v_subst_2450_, v_a_boxed_2454_, v_a_2452_, v_a_2453_);
lean_dec_ref(v_a_2452_);
lean_dec_ref(v_subst_2450_);
return v_res_2455_;
}
}
lean_object* l_Lean_Meta_Sym_instantiateRevBetaS(lean_object* v_e_2456_, lean_object* v_subst_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_){
_start:
{
uint8_t v___x_2465_; 
v___x_2465_ = l_Lean_Expr_hasLooseBVars(v_e_2456_);
if (v___x_2465_ == 0)
{
lean_object* v___x_2466_; 
lean_dec_ref(v_subst_2457_);
v___x_2466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2466_, 0, v_e_2456_);
return v___x_2466_;
}
else
{
lean_object* v___x_2467_; lean_object* v___x_2468_; uint8_t v___x_2469_; 
v___x_2467_ = lean_array_get_size(v_subst_2457_);
v___x_2468_ = lean_unsigned_to_nat(0u);
v___x_2469_ = lean_nat_dec_eq(v___x_2467_, v___x_2468_);
if (v___x_2469_ == 0)
{
lean_object* v___x_2470_; uint8_t v_debug_2471_; lean_object* v___x_2472_; lean_object* v_env_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; 
v___x_2470_ = lean_st_ref_get(v_a_2459_);
v_debug_2471_ = lean_ctor_get_uint8(v___x_2470_, sizeof(void*)*12);
lean_dec(v___x_2470_);
v___x_2472_ = lean_st_ref_get(v_a_2463_);
v_env_2473_ = lean_ctor_get(v___x_2472_, 0);
lean_inc_ref(v_env_2473_);
lean_dec(v___x_2472_);
v___x_2474_ = lean_box(v_debug_2471_);
v___x_2475_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27___boxed), 5, 3);
lean_closure_set(v___x_2475_, 0, v_e_2456_);
lean_closure_set(v___x_2475_, 1, v_subst_2457_);
lean_closure_set(v___x_2475_, 2, v___x_2474_);
v___x_2476_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2476_, 0, v_env_2473_);
lean_ctor_set_uint8(v___x_2476_, sizeof(void*)*1, v___x_2469_);
lean_ctor_set_uint8(v___x_2476_, sizeof(void*)*1 + 1, v___x_2469_);
v___x_2477_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___x_2475_, v___x_2476_, v_a_2459_);
if (lean_obj_tag(v___x_2477_) == 0)
{
lean_object* v_a_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2488_; 
v_a_2478_ = lean_ctor_get(v___x_2477_, 0);
v_isSharedCheck_2488_ = !lean_is_exclusive(v___x_2477_);
if (v_isSharedCheck_2488_ == 0)
{
v___x_2480_ = v___x_2477_;
v_isShared_2481_ = v_isSharedCheck_2488_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_a_2478_);
lean_dec(v___x_2477_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2488_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
if (lean_obj_tag(v_a_2478_) == 0)
{
lean_object* v___x_2482_; lean_object* v___x_2483_; 
lean_dec_ref_known(v_a_2478_, 1);
lean_del_object(v___x_2480_);
v___x_2482_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__2, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__2_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__2);
v___x_2483_ = l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(v___x_2482_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_);
return v___x_2483_;
}
else
{
lean_object* v_a_2484_; lean_object* v___x_2486_; 
v_a_2484_ = lean_ctor_get(v_a_2478_, 0);
lean_inc(v_a_2484_);
lean_dec_ref_known(v_a_2478_, 1);
if (v_isShared_2481_ == 0)
{
lean_ctor_set(v___x_2480_, 0, v_a_2484_);
v___x_2486_ = v___x_2480_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v_a_2484_);
v___x_2486_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
return v___x_2486_;
}
}
}
}
else
{
lean_object* v_a_2489_; lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2496_; 
v_a_2489_ = lean_ctor_get(v___x_2477_, 0);
v_isSharedCheck_2496_ = !lean_is_exclusive(v___x_2477_);
if (v_isSharedCheck_2496_ == 0)
{
v___x_2491_ = v___x_2477_;
v_isShared_2492_ = v_isSharedCheck_2496_;
goto v_resetjp_2490_;
}
else
{
lean_inc(v_a_2489_);
lean_dec(v___x_2477_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2496_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
lean_object* v___x_2494_; 
if (v_isShared_2492_ == 0)
{
v___x_2494_ = v___x_2491_;
goto v_reusejp_2493_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v_a_2489_);
v___x_2494_ = v_reuseFailAlloc_2495_;
goto v_reusejp_2493_;
}
v_reusejp_2493_:
{
return v___x_2494_;
}
}
}
}
else
{
lean_object* v___x_2497_; 
lean_dec_ref(v_subst_2457_);
v___x_2497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2497_, 0, v_e_2456_);
return v___x_2497_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_instantiateRevBetaS_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2456_ = stack[0].m_obj;
lean_object* v_subst_2457_ = stack[1].m_obj;
lean_object* v_a_2458_ = stack[2].m_obj;
lean_object* v_a_2459_ = stack[3].m_obj;
lean_object* v_a_2460_ = stack[4].m_obj;
lean_object* v_a_2461_ = stack[5].m_obj;
lean_object* v_a_2462_ = stack[6].m_obj;
lean_object* v_a_2463_ = stack[7].m_obj;
lean_object* v_res_2498_;
v_res_2498_ = l_Lean_Meta_Sym_instantiateRevBetaS(v_e_2456_, v_subst_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_);
stack->m_obj
 = v_res_2498_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevBetaS___boxed(lean_object* v_e_2499_, lean_object* v_subst_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_){
_start:
{
lean_object* v_res_2508_; 
v_res_2508_ = l_Lean_Meta_Sym_instantiateRevBetaS(v_e_2499_, v_subst_2500_, v_a_2501_, v_a_2502_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_);
lean_dec(v_a_2506_);
lean_dec_ref(v_a_2505_);
lean_dec(v_a_2504_);
lean_dec_ref(v_a_2503_);
lean_dec(v_a_2502_);
lean_dec_ref(v_a_2501_);
return v_res_2508_;
}
}
lean_object* l_Lean_Meta_Sym_betaRevS(lean_object* v_f_2509_, lean_object* v_revArgs_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_){
_start:
{
lean_object* v___x_2518_; uint8_t v_debug_2519_; lean_object* v___x_2520_; lean_object* v_env_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; uint8_t v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; 
v___x_2518_ = lean_st_ref_get(v_a_2512_);
v_debug_2519_ = lean_ctor_get_uint8(v___x_2518_, sizeof(void*)*12);
lean_dec(v___x_2518_);
v___x_2520_ = lean_st_ref_get(v_a_2516_);
v_env_2521_ = lean_ctor_get(v___x_2520_, 0);
lean_inc_ref(v_env_2521_);
lean_dec(v___x_2520_);
v___x_2522_ = lean_box(v_debug_2519_);
v___x_2523_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27___boxed), 5, 3);
lean_closure_set(v___x_2523_, 0, v_f_2509_);
lean_closure_set(v___x_2523_, 1, v_revArgs_2510_);
lean_closure_set(v___x_2523_, 2, v___x_2522_);
v___x_2524_ = 0;
v___x_2525_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2525_, 0, v_env_2521_);
lean_ctor_set_uint8(v___x_2525_, sizeof(void*)*1, v___x_2524_);
lean_ctor_set_uint8(v___x_2525_, sizeof(void*)*1 + 1, v___x_2524_);
v___x_2526_ = l_Lean_Meta_Sym_runShareCommonM___redArg(v___x_2523_, v___x_2525_, v_a_2512_);
if (lean_obj_tag(v___x_2526_) == 0)
{
lean_object* v_a_2527_; lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2537_; 
v_a_2527_ = lean_ctor_get(v___x_2526_, 0);
v_isSharedCheck_2537_ = !lean_is_exclusive(v___x_2526_);
if (v_isSharedCheck_2537_ == 0)
{
v___x_2529_ = v___x_2526_;
v_isShared_2530_ = v_isSharedCheck_2537_;
goto v_resetjp_2528_;
}
else
{
lean_inc(v_a_2527_);
lean_dec(v___x_2526_);
v___x_2529_ = lean_box(0);
v_isShared_2530_ = v_isSharedCheck_2537_;
goto v_resetjp_2528_;
}
v_resetjp_2528_:
{
if (lean_obj_tag(v_a_2527_) == 0)
{
lean_object* v___x_2531_; lean_object* v___x_2532_; 
lean_dec_ref_known(v_a_2527_, 1);
lean_del_object(v___x_2529_);
v___x_2531_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__2, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__2_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__2);
v___x_2532_ = l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(v___x_2531_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_);
return v___x_2532_;
}
else
{
lean_object* v_a_2533_; lean_object* v___x_2535_; 
v_a_2533_ = lean_ctor_get(v_a_2527_, 0);
lean_inc(v_a_2533_);
lean_dec_ref_known(v_a_2527_, 1);
if (v_isShared_2530_ == 0)
{
lean_ctor_set(v___x_2529_, 0, v_a_2533_);
v___x_2535_ = v___x_2529_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v_a_2533_);
v___x_2535_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
return v___x_2535_;
}
}
}
}
else
{
lean_object* v_a_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2545_; 
v_a_2538_ = lean_ctor_get(v___x_2526_, 0);
v_isSharedCheck_2545_ = !lean_is_exclusive(v___x_2526_);
if (v_isSharedCheck_2545_ == 0)
{
v___x_2540_ = v___x_2526_;
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_a_2538_);
lean_dec(v___x_2526_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v___x_2543_; 
if (v_isShared_2541_ == 0)
{
v___x_2543_ = v___x_2540_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v_a_2538_);
v___x_2543_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
return v___x_2543_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_betaRevS_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2509_ = stack[0].m_obj;
lean_object* v_revArgs_2510_ = stack[1].m_obj;
lean_object* v_a_2511_ = stack[2].m_obj;
lean_object* v_a_2512_ = stack[3].m_obj;
lean_object* v_a_2513_ = stack[4].m_obj;
lean_object* v_a_2514_ = stack[5].m_obj;
lean_object* v_a_2515_ = stack[6].m_obj;
lean_object* v_a_2516_ = stack[7].m_obj;
lean_object* v_res_2546_;
v_res_2546_ = l_Lean_Meta_Sym_betaRevS(v_f_2509_, v_revArgs_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_);
stack->m_obj
 = v_res_2546_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_betaRevS___boxed(lean_object* v_f_2547_, lean_object* v_revArgs_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_){
_start:
{
lean_object* v_res_2556_; 
v_res_2556_ = l_Lean_Meta_Sym_betaRevS(v_f_2547_, v_revArgs_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_);
lean_dec(v_a_2554_);
lean_dec_ref(v_a_2553_);
lean_dec(v_a_2552_);
lean_dec_ref(v_a_2551_);
lean_dec(v_a_2550_);
lean_dec_ref(v_a_2549_);
return v_res_2556_;
}
}
lean_object* l_Lean_Meta_Sym_betaS(lean_object* v_f_2557_, lean_object* v_args_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_){
_start:
{
lean_object* v___x_2566_; lean_object* v___x_2567_; 
v___x_2566_ = l_Array_reverse___redArg(v_args_2558_);
v___x_2567_ = l_Lean_Meta_Sym_betaRevS(v_f_2557_, v___x_2566_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_, v_a_2564_);
return v___x_2567_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_betaS_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2557_ = stack[0].m_obj;
lean_object* v_args_2558_ = stack[1].m_obj;
lean_object* v_a_2559_ = stack[2].m_obj;
lean_object* v_a_2560_ = stack[3].m_obj;
lean_object* v_a_2561_ = stack[4].m_obj;
lean_object* v_a_2562_ = stack[5].m_obj;
lean_object* v_a_2563_ = stack[6].m_obj;
lean_object* v_a_2564_ = stack[7].m_obj;
lean_object* v_res_2568_;
v_res_2568_ = l_Lean_Meta_Sym_betaS(v_f_2557_, v_args_2558_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_, v_a_2564_);
stack->m_obj
 = v_res_2568_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_betaS___boxed(lean_object* v_f_2569_, lean_object* v_args_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_){
_start:
{
lean_object* v_res_2578_; 
v_res_2578_ = l_Lean_Meta_Sym_betaS(v_f_2569_, v_args_2570_, v_a_2571_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_, v_a_2576_);
lean_dec(v_a_2576_);
lean_dec_ref(v_a_2575_);
lean_dec(v_a_2574_);
lean_dec_ref(v_a_2573_);
lean_dec(v_a_2572_);
lean_dec_ref(v_a_2571_);
return v_res_2578_;
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
