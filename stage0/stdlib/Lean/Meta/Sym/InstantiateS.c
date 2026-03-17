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
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Builder_share1___redArg(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_liftLooseBVarsS_x27(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
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
lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Builder_assertShared(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_Lean_Expr_isBVar(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__0;
static const lean_closure_object l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__1 = (const lean_object*)&l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__2 = (const lean_object*)&l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__3 = (const lean_object*)&l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__4 = (const lean_object*)&l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__0_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__2_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__3 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__3_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__4 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__4_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__5 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__5_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__6 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__6_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__7(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4_spec__12___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "_private.Lean.Meta.Sym.ReplaceS.0.Lean.Meta.Sym.visit"};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Meta.Sym.ReplaceS"};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Sym_instantiateRevRangeS___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instantiateRevRangeS___closed__0;
static lean_once_cell_t l_Lean_Meta_Sym_instantiateRevRangeS___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instantiateRevRangeS___closed__1;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4_spec__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 70, .m_data = "_private.Lean.Meta.Sym.InstantiateS.0.Lean.Meta.Sym.instantiateRangeS'"};
static const lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateS___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateS___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS_loop_spec__0(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS_loop_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS_loop(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_go(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "application expected"};
static const lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Expr.updateAppS!"};
static const lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Meta.Sym.AlphaShareBuilder"};
static const lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__3;
static const lean_string_object l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 86, .m_capacity = 86, .m_length = 85, .m_data = "_private.Lean.Meta.Sym.InstantiateS.0.Lean.Meta.Sym.instantiateRevBetaS'.visitAppBeta"};
static const lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "_private.Lean.Meta.Sym.InstantiateS.0.Lean.Meta.Sym.instantiateRevBetaS'.visit"};
static const lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevBetaS___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevBetaS___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevBetaS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevBetaS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___closed__0);
v___x_3_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0(lean_object* v_00_u03b2_4_){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___closed__1);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___redArg(lean_object* v_idx_6_, lean_object* v___y_7_){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_8_ = l_Lean_Expr_bvar___override(v_idx_6_);
v___x_9_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_8_, v___y_7_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1(lean_object* v_idx_10_, uint8_t v___y_11_, lean_object* v___y_12_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___redArg(v_idx_10_, v___y_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___boxed(lean_object* v_idx_14_, lean_object* v___y_15_, lean_object* v___y_16_){
_start:
{
uint8_t v___y_23000__boxed_17_; lean_object* v_res_18_; 
v___y_23000__boxed_17_ = lean_unbox(v___y_15_);
v_res_18_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1(v_idx_14_, v___y_23000__boxed_17_, v___y_16_);
return v_res_18_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__0(void){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3(lean_object* v_msg_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v_toApplicative_34_; lean_object* v___x_36_; uint8_t v_isShared_37_; uint8_t v_isSharedCheck_97_; 
v___x_32_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__0, &l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__0);
v___x_33_ = l_ReaderT_instMonad___redArg(v___x_32_);
v_toApplicative_34_ = lean_ctor_get(v___x_33_, 0);
v_isSharedCheck_97_ = !lean_is_exclusive(v___x_33_);
if (v_isSharedCheck_97_ == 0)
{
lean_object* v_unused_98_; 
v_unused_98_ = lean_ctor_get(v___x_33_, 1);
lean_dec(v_unused_98_);
v___x_36_ = v___x_33_;
v_isShared_37_ = v_isSharedCheck_97_;
goto v_resetjp_35_;
}
else
{
lean_inc(v_toApplicative_34_);
lean_dec(v___x_33_);
v___x_36_ = lean_box(0);
v_isShared_37_ = v_isSharedCheck_97_;
goto v_resetjp_35_;
}
v_resetjp_35_:
{
lean_object* v_toFunctor_38_; lean_object* v_toSeq_39_; lean_object* v_toSeqLeft_40_; lean_object* v_toSeqRight_41_; lean_object* v___x_43_; uint8_t v_isShared_44_; uint8_t v_isSharedCheck_95_; 
v_toFunctor_38_ = lean_ctor_get(v_toApplicative_34_, 0);
v_toSeq_39_ = lean_ctor_get(v_toApplicative_34_, 2);
v_toSeqLeft_40_ = lean_ctor_get(v_toApplicative_34_, 3);
v_toSeqRight_41_ = lean_ctor_get(v_toApplicative_34_, 4);
v_isSharedCheck_95_ = !lean_is_exclusive(v_toApplicative_34_);
if (v_isSharedCheck_95_ == 0)
{
lean_object* v_unused_96_; 
v_unused_96_ = lean_ctor_get(v_toApplicative_34_, 1);
lean_dec(v_unused_96_);
v___x_43_ = v_toApplicative_34_;
v_isShared_44_ = v_isSharedCheck_95_;
goto v_resetjp_42_;
}
else
{
lean_inc(v_toSeqRight_41_);
lean_inc(v_toSeqLeft_40_);
lean_inc(v_toSeq_39_);
lean_inc(v_toFunctor_38_);
lean_dec(v_toApplicative_34_);
v___x_43_ = lean_box(0);
v_isShared_44_ = v_isSharedCheck_95_;
goto v_resetjp_42_;
}
v_resetjp_42_:
{
lean_object* v___f_45_; lean_object* v___f_46_; lean_object* v___f_47_; lean_object* v___f_48_; lean_object* v___x_49_; lean_object* v___f_50_; lean_object* v___f_51_; lean_object* v___f_52_; lean_object* v___x_54_; 
v___f_45_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__1));
v___f_46_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__2));
lean_inc_ref(v_toFunctor_38_);
v___f_47_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_47_, 0, v_toFunctor_38_);
v___f_48_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_48_, 0, v_toFunctor_38_);
v___x_49_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_49_, 0, v___f_47_);
lean_ctor_set(v___x_49_, 1, v___f_48_);
v___f_50_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_50_, 0, v_toSeqRight_41_);
v___f_51_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_51_, 0, v_toSeqLeft_40_);
v___f_52_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_52_, 0, v_toSeq_39_);
if (v_isShared_44_ == 0)
{
lean_ctor_set(v___x_43_, 4, v___f_50_);
lean_ctor_set(v___x_43_, 3, v___f_51_);
lean_ctor_set(v___x_43_, 2, v___f_52_);
lean_ctor_set(v___x_43_, 1, v___f_45_);
lean_ctor_set(v___x_43_, 0, v___x_49_);
v___x_54_ = v___x_43_;
goto v_reusejp_53_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v___x_49_);
lean_ctor_set(v_reuseFailAlloc_94_, 1, v___f_45_);
lean_ctor_set(v_reuseFailAlloc_94_, 2, v___f_52_);
lean_ctor_set(v_reuseFailAlloc_94_, 3, v___f_51_);
lean_ctor_set(v_reuseFailAlloc_94_, 4, v___f_50_);
v___x_54_ = v_reuseFailAlloc_94_;
goto v_reusejp_53_;
}
v_reusejp_53_:
{
lean_object* v___x_56_; 
if (v_isShared_37_ == 0)
{
lean_ctor_set(v___x_36_, 1, v___f_46_);
lean_ctor_set(v___x_36_, 0, v___x_54_);
v___x_56_ = v___x_36_;
goto v_reusejp_55_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v___x_54_);
lean_ctor_set(v_reuseFailAlloc_93_, 1, v___f_46_);
v___x_56_ = v_reuseFailAlloc_93_;
goto v_reusejp_55_;
}
v_reusejp_55_:
{
lean_object* v___x_57_; lean_object* v_toApplicative_58_; lean_object* v___x_60_; uint8_t v_isShared_61_; uint8_t v_isSharedCheck_91_; 
v___x_57_ = l_ReaderT_instMonad___redArg(v___x_56_);
v_toApplicative_58_ = lean_ctor_get(v___x_57_, 0);
v_isSharedCheck_91_ = !lean_is_exclusive(v___x_57_);
if (v_isSharedCheck_91_ == 0)
{
lean_object* v_unused_92_; 
v_unused_92_ = lean_ctor_get(v___x_57_, 1);
lean_dec(v_unused_92_);
v___x_60_ = v___x_57_;
v_isShared_61_ = v_isSharedCheck_91_;
goto v_resetjp_59_;
}
else
{
lean_inc(v_toApplicative_58_);
lean_dec(v___x_57_);
v___x_60_ = lean_box(0);
v_isShared_61_ = v_isSharedCheck_91_;
goto v_resetjp_59_;
}
v_resetjp_59_:
{
lean_object* v_toFunctor_62_; lean_object* v_toSeq_63_; lean_object* v_toSeqLeft_64_; lean_object* v_toSeqRight_65_; lean_object* v___x_67_; uint8_t v_isShared_68_; uint8_t v_isSharedCheck_89_; 
v_toFunctor_62_ = lean_ctor_get(v_toApplicative_58_, 0);
v_toSeq_63_ = lean_ctor_get(v_toApplicative_58_, 2);
v_toSeqLeft_64_ = lean_ctor_get(v_toApplicative_58_, 3);
v_toSeqRight_65_ = lean_ctor_get(v_toApplicative_58_, 4);
v_isSharedCheck_89_ = !lean_is_exclusive(v_toApplicative_58_);
if (v_isSharedCheck_89_ == 0)
{
lean_object* v_unused_90_; 
v_unused_90_ = lean_ctor_get(v_toApplicative_58_, 1);
lean_dec(v_unused_90_);
v___x_67_ = v_toApplicative_58_;
v_isShared_68_ = v_isSharedCheck_89_;
goto v_resetjp_66_;
}
else
{
lean_inc(v_toSeqRight_65_);
lean_inc(v_toSeqLeft_64_);
lean_inc(v_toSeq_63_);
lean_inc(v_toFunctor_62_);
lean_dec(v_toApplicative_58_);
v___x_67_ = lean_box(0);
v_isShared_68_ = v_isSharedCheck_89_;
goto v_resetjp_66_;
}
v_resetjp_66_:
{
lean_object* v___f_69_; lean_object* v___f_70_; lean_object* v___f_71_; lean_object* v___f_72_; lean_object* v___x_73_; lean_object* v___f_74_; lean_object* v___f_75_; lean_object* v___f_76_; lean_object* v___x_78_; 
v___f_69_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__3));
v___f_70_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__4));
lean_inc_ref(v_toFunctor_62_);
v___f_71_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_71_, 0, v_toFunctor_62_);
v___f_72_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_72_, 0, v_toFunctor_62_);
v___x_73_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_73_, 0, v___f_71_);
lean_ctor_set(v___x_73_, 1, v___f_72_);
v___f_74_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_74_, 0, v_toSeqRight_65_);
v___f_75_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_75_, 0, v_toSeqLeft_64_);
v___f_76_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_76_, 0, v_toSeq_63_);
if (v_isShared_68_ == 0)
{
lean_ctor_set(v___x_67_, 4, v___f_74_);
lean_ctor_set(v___x_67_, 3, v___f_75_);
lean_ctor_set(v___x_67_, 2, v___f_76_);
lean_ctor_set(v___x_67_, 1, v___f_69_);
lean_ctor_set(v___x_67_, 0, v___x_73_);
v___x_78_ = v___x_67_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v___x_73_);
lean_ctor_set(v_reuseFailAlloc_88_, 1, v___f_69_);
lean_ctor_set(v_reuseFailAlloc_88_, 2, v___f_76_);
lean_ctor_set(v_reuseFailAlloc_88_, 3, v___f_75_);
lean_ctor_set(v_reuseFailAlloc_88_, 4, v___f_74_);
v___x_78_ = v_reuseFailAlloc_88_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
lean_object* v___x_80_; 
if (v_isShared_61_ == 0)
{
lean_ctor_set(v___x_60_, 1, v___f_70_);
lean_ctor_set(v___x_60_, 0, v___x_78_);
v___x_80_ = v___x_60_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v___x_78_);
lean_ctor_set(v_reuseFailAlloc_87_, 1, v___f_70_);
v___x_80_ = v_reuseFailAlloc_87_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___f_84_; lean_object* v___x_3213__overap_85_; lean_object* v___x_86_; 
v___x_81_ = l_ReaderT_instMonad___redArg(v___x_80_);
v___x_82_ = l_Lean_instInhabitedExpr;
v___x_83_ = l_instInhabitedOfMonad___redArg(v___x_81_, v___x_82_);
v___f_84_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_84_, 0, v___x_83_);
v___x_3213__overap_85_ = lean_panic_fn(v___f_84_, v_msg_24_);
v___x_86_ = lean_apply_7(v___x_3213__overap_85_, v___y_25_, v___y_26_, v___y_27_, v___y_28_, v___y_29_, v___y_30_, lean_box(0));
return v___x_86_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___boxed(lean_object* v_msg_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3(v_msg_99_, v___y_100_, v___y_101_, v___y_102_, v___y_103_, v___y_104_, v___y_105_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__5(lean_object* v_x_108_, uint8_t v_bi_109_, lean_object* v_t_110_, lean_object* v_b_111_, lean_object* v___y_112_, uint8_t v___y_113_, lean_object* v___y_114_){
_start:
{
lean_object* v___y_116_; lean_object* v___y_117_; 
if (v___y_113_ == 0)
{
v___y_116_ = v___y_112_;
v___y_117_ = v___y_114_;
goto v___jp_115_;
}
else
{
lean_object* v___x_130_; lean_object* v_snd_131_; lean_object* v___x_132_; lean_object* v_snd_133_; 
lean_inc_ref(v_t_110_);
v___x_130_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_110_, v___y_113_, v___y_114_);
v_snd_131_ = lean_ctor_get(v___x_130_, 1);
lean_inc(v_snd_131_);
lean_dec_ref(v___x_130_);
lean_inc_ref(v_b_111_);
v___x_132_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_111_, v___y_113_, v_snd_131_);
v_snd_133_ = lean_ctor_get(v___x_132_, 1);
lean_inc(v_snd_133_);
lean_dec_ref(v___x_132_);
v___y_116_ = v___y_112_;
v___y_117_ = v_snd_133_;
goto v___jp_115_;
}
v___jp_115_:
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v_fst_120_; lean_object* v_snd_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_129_; 
v___x_118_ = l_Lean_Expr_forallE___override(v_x_108_, v_t_110_, v_b_111_, v_bi_109_);
v___x_119_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_118_, v___y_117_);
v_fst_120_ = lean_ctor_get(v___x_119_, 0);
v_snd_121_ = lean_ctor_get(v___x_119_, 1);
v_isSharedCheck_129_ = !lean_is_exclusive(v___x_119_);
if (v_isSharedCheck_129_ == 0)
{
v___x_123_ = v___x_119_;
v_isShared_124_ = v_isSharedCheck_129_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_snd_121_);
lean_inc(v_fst_120_);
lean_dec(v___x_119_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_129_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_126_; 
if (v_isShared_124_ == 0)
{
lean_ctor_set(v___x_123_, 1, v___y_116_);
v___x_126_ = v___x_123_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v_fst_120_);
lean_ctor_set(v_reuseFailAlloc_128_, 1, v___y_116_);
v___x_126_ = v_reuseFailAlloc_128_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
lean_object* v___x_127_; 
v___x_127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_127_, 0, v___x_126_);
lean_ctor_set(v___x_127_, 1, v_snd_121_);
return v___x_127_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__5___boxed(lean_object* v_x_134_, lean_object* v_bi_135_, lean_object* v_t_136_, lean_object* v_b_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_){
_start:
{
uint8_t v_bi_boxed_141_; uint8_t v___y_23157__boxed_142_; lean_object* v_res_143_; 
v_bi_boxed_141_ = lean_unbox(v_bi_135_);
v___y_23157__boxed_142_ = lean_unbox(v___y_139_);
v_res_143_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__5(v_x_134_, v_bi_boxed_141_, v_t_136_, v_b_137_, v___y_138_, v___y_23157__boxed_142_, v___y_140_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9(lean_object* v_msg_151_, lean_object* v___y_152_, uint8_t v___y_153_, lean_object* v___y_154_){
_start:
{
lean_object* v___f_155_; lean_object* v___f_156_; lean_object* v___f_157_; lean_object* v___f_158_; lean_object* v___f_159_; lean_object* v___f_160_; lean_object* v___f_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___f_165_; lean_object* v___f_166_; lean_object* v___f_167_; lean_object* v___f_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___f_176_; lean_object* v___f_177_; lean_object* v___f_178_; lean_object* v___f_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_22641__overap_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v___f_155_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__0));
v___f_156_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__1));
v___f_157_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__2));
v___f_158_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__3));
v___f_159_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__4));
v___f_160_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__5));
v___f_161_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__6));
v___x_162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_162_, 0, v___f_155_);
lean_ctor_set(v___x_162_, 1, v___f_156_);
v___x_163_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
lean_ctor_set(v___x_163_, 1, v___f_157_);
lean_ctor_set(v___x_163_, 2, v___f_158_);
lean_ctor_set(v___x_163_, 3, v___f_159_);
lean_ctor_set(v___x_163_, 4, v___f_160_);
v___x_164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
lean_ctor_set(v___x_164_, 1, v___f_161_);
lean_inc_ref(v___x_164_);
v___f_165_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_165_, 0, v___x_164_);
lean_inc_ref(v___x_164_);
v___f_166_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_166_, 0, v___x_164_);
lean_inc_ref(v___x_164_);
v___f_167_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_167_, 0, v___x_164_);
lean_inc_ref(v___x_164_);
v___f_168_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_168_, 0, v___x_164_);
lean_inc_ref(v___x_164_);
v___x_169_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_169_, 0, lean_box(0));
lean_closure_set(v___x_169_, 1, lean_box(0));
lean_closure_set(v___x_169_, 2, v___x_164_);
v___x_170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
lean_ctor_set(v___x_170_, 1, v___f_165_);
lean_inc_ref(v___x_164_);
v___x_171_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_171_, 0, lean_box(0));
lean_closure_set(v___x_171_, 1, lean_box(0));
lean_closure_set(v___x_171_, 2, v___x_164_);
v___x_172_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_172_, 0, v___x_170_);
lean_ctor_set(v___x_172_, 1, v___x_171_);
lean_ctor_set(v___x_172_, 2, v___f_166_);
lean_ctor_set(v___x_172_, 3, v___f_167_);
lean_ctor_set(v___x_172_, 4, v___f_168_);
v___x_173_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_173_, 0, lean_box(0));
lean_closure_set(v___x_173_, 1, lean_box(0));
lean_closure_set(v___x_173_, 2, v___x_164_);
v___x_174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_174_, 0, v___x_172_);
lean_ctor_set(v___x_174_, 1, v___x_173_);
v___x_175_ = l_ReaderT_instMonad___redArg(v___x_174_);
lean_inc_ref(v___x_175_);
v___f_176_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_176_, 0, v___x_175_);
lean_inc_ref(v___x_175_);
v___f_177_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_177_, 0, v___x_175_);
lean_inc_ref(v___x_175_);
v___f_178_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_178_, 0, v___x_175_);
lean_inc_ref(v___x_175_);
v___f_179_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_179_, 0, v___x_175_);
lean_inc_ref(v___x_175_);
v___x_180_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_180_, 0, lean_box(0));
lean_closure_set(v___x_180_, 1, lean_box(0));
lean_closure_set(v___x_180_, 2, v___x_175_);
v___x_181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_181_, 0, v___x_180_);
lean_ctor_set(v___x_181_, 1, v___f_176_);
lean_inc_ref(v___x_175_);
v___x_182_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_182_, 0, lean_box(0));
lean_closure_set(v___x_182_, 1, lean_box(0));
lean_closure_set(v___x_182_, 2, v___x_175_);
v___x_183_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_183_, 0, v___x_181_);
lean_ctor_set(v___x_183_, 1, v___x_182_);
lean_ctor_set(v___x_183_, 2, v___f_177_);
lean_ctor_set(v___x_183_, 3, v___f_178_);
lean_ctor_set(v___x_183_, 4, v___f_179_);
v___x_184_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_184_, 0, lean_box(0));
lean_closure_set(v___x_184_, 1, lean_box(0));
lean_closure_set(v___x_184_, 2, v___x_175_);
v___x_185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_185_, 0, v___x_183_);
lean_ctor_set(v___x_185_, 1, v___x_184_);
v___x_186_ = l_Lean_instInhabitedExpr;
v___x_187_ = l_instInhabitedOfMonad___redArg(v___x_185_, v___x_186_);
v___x_22641__overap_188_ = lean_panic_fn(v___x_187_, v_msg_151_);
v___x_189_ = lean_box(v___y_153_);
v___x_190_ = lean_apply_3(v___x_22641__overap_188_, v___y_152_, v___x_189_, v___y_154_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___boxed(lean_object* v_msg_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_){
_start:
{
uint8_t v___y_23220__boxed_195_; lean_object* v_res_196_; 
v___y_23220__boxed_195_ = lean_unbox(v___y_193_);
v_res_196_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9(v_msg_191_, v___y_192_, v___y_23220__boxed_195_, v___y_194_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__8(lean_object* v_structName_197_, lean_object* v_idx_198_, lean_object* v_struct_199_, lean_object* v___y_200_, uint8_t v___y_201_, lean_object* v___y_202_){
_start:
{
lean_object* v___y_204_; lean_object* v___y_205_; 
if (v___y_201_ == 0)
{
v___y_204_ = v___y_200_;
v___y_205_ = v___y_202_;
goto v___jp_203_;
}
else
{
lean_object* v___x_218_; lean_object* v_snd_219_; 
lean_inc_ref(v_struct_199_);
v___x_218_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_struct_199_, v___y_201_, v___y_202_);
v_snd_219_ = lean_ctor_get(v___x_218_, 1);
lean_inc(v_snd_219_);
lean_dec_ref(v___x_218_);
v___y_204_ = v___y_200_;
v___y_205_ = v_snd_219_;
goto v___jp_203_;
}
v___jp_203_:
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v_fst_208_; lean_object* v_snd_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_217_; 
v___x_206_ = l_Lean_Expr_proj___override(v_structName_197_, v_idx_198_, v_struct_199_);
v___x_207_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_206_, v___y_205_);
v_fst_208_ = lean_ctor_get(v___x_207_, 0);
v_snd_209_ = lean_ctor_get(v___x_207_, 1);
v_isSharedCheck_217_ = !lean_is_exclusive(v___x_207_);
if (v_isSharedCheck_217_ == 0)
{
v___x_211_ = v___x_207_;
v_isShared_212_ = v_isSharedCheck_217_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_snd_209_);
lean_inc(v_fst_208_);
lean_dec(v___x_207_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_217_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v___x_214_; 
if (v_isShared_212_ == 0)
{
lean_ctor_set(v___x_211_, 1, v___y_204_);
v___x_214_ = v___x_211_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v_fst_208_);
lean_ctor_set(v_reuseFailAlloc_216_, 1, v___y_204_);
v___x_214_ = v_reuseFailAlloc_216_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
lean_object* v___x_215_; 
v___x_215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_215_, 0, v___x_214_);
lean_ctor_set(v___x_215_, 1, v_snd_209_);
return v___x_215_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__8___boxed(lean_object* v_structName_220_, lean_object* v_idx_221_, lean_object* v_struct_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_){
_start:
{
uint8_t v___y_23306__boxed_226_; lean_object* v_res_227_; 
v___y_23306__boxed_226_ = lean_unbox(v___y_224_);
v_res_227_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__8(v_structName_220_, v_idx_221_, v_struct_222_, v___y_223_, v___y_23306__boxed_226_, v___y_225_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__4(lean_object* v_x_228_, uint8_t v_bi_229_, lean_object* v_t_230_, lean_object* v_b_231_, lean_object* v___y_232_, uint8_t v___y_233_, lean_object* v___y_234_){
_start:
{
lean_object* v___y_236_; lean_object* v___y_237_; 
if (v___y_233_ == 0)
{
v___y_236_ = v___y_232_;
v___y_237_ = v___y_234_;
goto v___jp_235_;
}
else
{
lean_object* v___x_250_; lean_object* v_snd_251_; lean_object* v___x_252_; lean_object* v_snd_253_; 
lean_inc_ref(v_t_230_);
v___x_250_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_230_, v___y_233_, v___y_234_);
v_snd_251_ = lean_ctor_get(v___x_250_, 1);
lean_inc(v_snd_251_);
lean_dec_ref(v___x_250_);
lean_inc_ref(v_b_231_);
v___x_252_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_231_, v___y_233_, v_snd_251_);
v_snd_253_ = lean_ctor_get(v___x_252_, 1);
lean_inc(v_snd_253_);
lean_dec_ref(v___x_252_);
v___y_236_ = v___y_232_;
v___y_237_ = v_snd_253_;
goto v___jp_235_;
}
v___jp_235_:
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v_fst_240_; lean_object* v_snd_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_249_; 
v___x_238_ = l_Lean_Expr_lam___override(v_x_228_, v_t_230_, v_b_231_, v_bi_229_);
v___x_239_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_238_, v___y_237_);
v_fst_240_ = lean_ctor_get(v___x_239_, 0);
v_snd_241_ = lean_ctor_get(v___x_239_, 1);
v_isSharedCheck_249_ = !lean_is_exclusive(v___x_239_);
if (v_isSharedCheck_249_ == 0)
{
v___x_243_ = v___x_239_;
v_isShared_244_ = v_isSharedCheck_249_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_snd_241_);
lean_inc(v_fst_240_);
lean_dec(v___x_239_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_249_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v___x_246_; 
if (v_isShared_244_ == 0)
{
lean_ctor_set(v___x_243_, 1, v___y_236_);
v___x_246_ = v___x_243_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v_fst_240_);
lean_ctor_set(v_reuseFailAlloc_248_, 1, v___y_236_);
v___x_246_ = v_reuseFailAlloc_248_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
lean_object* v___x_247_; 
v___x_247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
lean_ctor_set(v___x_247_, 1, v_snd_241_);
return v___x_247_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__4___boxed(lean_object* v_x_254_, lean_object* v_bi_255_, lean_object* v_t_256_, lean_object* v_b_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
uint8_t v_bi_boxed_261_; uint8_t v___y_23350__boxed_262_; lean_object* v_res_263_; 
v_bi_boxed_261_ = lean_unbox(v_bi_255_);
v___y_23350__boxed_262_ = lean_unbox(v___y_259_);
v_res_263_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__4(v_x_254_, v_bi_boxed_261_, v_t_256_, v_b_257_, v___y_258_, v___y_23350__boxed_262_, v___y_260_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__7(lean_object* v_d_264_, lean_object* v_e_265_, lean_object* v___y_266_, uint8_t v___y_267_, lean_object* v___y_268_){
_start:
{
lean_object* v___y_270_; lean_object* v___y_271_; 
if (v___y_267_ == 0)
{
v___y_270_ = v___y_266_;
v___y_271_ = v___y_268_;
goto v___jp_269_;
}
else
{
lean_object* v___x_284_; lean_object* v_snd_285_; 
lean_inc_ref(v_e_265_);
v___x_284_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_e_265_, v___y_267_, v___y_268_);
v_snd_285_ = lean_ctor_get(v___x_284_, 1);
lean_inc(v_snd_285_);
lean_dec_ref(v___x_284_);
v___y_270_ = v___y_266_;
v___y_271_ = v_snd_285_;
goto v___jp_269_;
}
v___jp_269_:
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v_fst_274_; lean_object* v_snd_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_283_; 
v___x_272_ = l_Lean_Expr_mdata___override(v_d_264_, v_e_265_);
v___x_273_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_272_, v___y_271_);
v_fst_274_ = lean_ctor_get(v___x_273_, 0);
v_snd_275_ = lean_ctor_get(v___x_273_, 1);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_283_ == 0)
{
v___x_277_ = v___x_273_;
v_isShared_278_ = v_isSharedCheck_283_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_snd_275_);
lean_inc(v_fst_274_);
lean_dec(v___x_273_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_283_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v___x_280_; 
if (v_isShared_278_ == 0)
{
lean_ctor_set(v___x_277_, 1, v___y_270_);
v___x_280_ = v___x_277_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_fst_274_);
lean_ctor_set(v_reuseFailAlloc_282_, 1, v___y_270_);
v___x_280_ = v_reuseFailAlloc_282_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
lean_object* v___x_281_; 
v___x_281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_281_, 0, v___x_280_);
lean_ctor_set(v___x_281_, 1, v_snd_275_);
return v___x_281_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__7___boxed(lean_object* v_d_286_, lean_object* v_e_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_){
_start:
{
uint8_t v___y_23399__boxed_291_; lean_object* v_res_292_; 
v___y_23399__boxed_291_ = lean_unbox(v___y_289_);
v_res_292_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__7(v_d_286_, v_e_287_, v___y_288_, v___y_23399__boxed_291_, v___y_290_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4_spec__12___redArg(lean_object* v_a_293_, lean_object* v_x_294_){
_start:
{
if (lean_obj_tag(v_x_294_) == 0)
{
lean_object* v___x_295_; 
v___x_295_ = lean_box(0);
return v___x_295_;
}
else
{
lean_object* v_key_296_; lean_object* v_value_297_; lean_object* v_tail_298_; uint8_t v___y_300_; lean_object* v_fst_303_; lean_object* v_snd_304_; lean_object* v_fst_305_; lean_object* v_snd_306_; uint8_t v___x_307_; 
v_key_296_ = lean_ctor_get(v_x_294_, 0);
v_value_297_ = lean_ctor_get(v_x_294_, 1);
v_tail_298_ = lean_ctor_get(v_x_294_, 2);
v_fst_303_ = lean_ctor_get(v_key_296_, 0);
v_snd_304_ = lean_ctor_get(v_key_296_, 1);
v_fst_305_ = lean_ctor_get(v_a_293_, 0);
v_snd_306_ = lean_ctor_get(v_a_293_, 1);
v___x_307_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_303_, v_fst_305_);
if (v___x_307_ == 0)
{
v___y_300_ = v___x_307_;
goto v___jp_299_;
}
else
{
uint8_t v___x_308_; 
v___x_308_ = lean_nat_dec_eq(v_snd_304_, v_snd_306_);
v___y_300_ = v___x_308_;
goto v___jp_299_;
}
v___jp_299_:
{
if (v___y_300_ == 0)
{
v_x_294_ = v_tail_298_;
goto _start;
}
else
{
lean_object* v___x_302_; 
lean_inc(v_value_297_);
v___x_302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_302_, 0, v_value_297_);
return v___x_302_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4_spec__12___redArg___boxed(lean_object* v_a_309_, lean_object* v_x_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4_spec__12___redArg(v_a_309_, v_x_310_);
lean_dec(v_x_310_);
lean_dec_ref(v_a_309_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___redArg(lean_object* v_m_312_, lean_object* v_a_313_){
_start:
{
lean_object* v_buckets_314_; lean_object* v_fst_315_; lean_object* v_snd_316_; lean_object* v___x_317_; uint64_t v___x_318_; uint64_t v___x_319_; uint64_t v___x_320_; uint64_t v___x_321_; uint64_t v___x_322_; uint64_t v_fold_323_; uint64_t v___x_324_; uint64_t v___x_325_; uint64_t v___x_326_; size_t v___x_327_; size_t v___x_328_; size_t v___x_329_; size_t v___x_330_; size_t v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v_buckets_314_ = lean_ctor_get(v_m_312_, 1);
v_fst_315_ = lean_ctor_get(v_a_313_, 0);
v_snd_316_ = lean_ctor_get(v_a_313_, 1);
v___x_317_ = lean_array_get_size(v_buckets_314_);
v___x_318_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_315_);
v___x_319_ = lean_uint64_of_nat(v_snd_316_);
v___x_320_ = lean_uint64_mix_hash(v___x_318_, v___x_319_);
v___x_321_ = 32ULL;
v___x_322_ = lean_uint64_shift_right(v___x_320_, v___x_321_);
v_fold_323_ = lean_uint64_xor(v___x_320_, v___x_322_);
v___x_324_ = 16ULL;
v___x_325_ = lean_uint64_shift_right(v_fold_323_, v___x_324_);
v___x_326_ = lean_uint64_xor(v_fold_323_, v___x_325_);
v___x_327_ = lean_uint64_to_usize(v___x_326_);
v___x_328_ = lean_usize_of_nat(v___x_317_);
v___x_329_ = ((size_t)1ULL);
v___x_330_ = lean_usize_sub(v___x_328_, v___x_329_);
v___x_331_ = lean_usize_land(v___x_327_, v___x_330_);
v___x_332_ = lean_array_uget_borrowed(v_buckets_314_, v___x_331_);
v___x_333_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4_spec__12___redArg(v_a_313_, v___x_332_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___redArg___boxed(lean_object* v_m_334_, lean_object* v_a_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___redArg(v_m_334_, v_a_335_);
lean_dec_ref(v_a_335_);
lean_dec_ref(v_m_334_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__3(lean_object* v_f_337_, lean_object* v_a_338_, lean_object* v___y_339_, uint8_t v___y_340_, lean_object* v___y_341_){
_start:
{
lean_object* v___y_343_; lean_object* v___y_344_; 
if (v___y_340_ == 0)
{
v___y_343_ = v___y_339_;
v___y_344_ = v___y_341_;
goto v___jp_342_;
}
else
{
lean_object* v___x_357_; lean_object* v_snd_358_; lean_object* v___x_359_; lean_object* v_snd_360_; 
lean_inc_ref(v_f_337_);
v___x_357_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_f_337_, v___y_340_, v___y_341_);
v_snd_358_ = lean_ctor_get(v___x_357_, 1);
lean_inc(v_snd_358_);
lean_dec_ref(v___x_357_);
lean_inc_ref(v_a_338_);
v___x_359_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_a_338_, v___y_340_, v_snd_358_);
v_snd_360_ = lean_ctor_get(v___x_359_, 1);
lean_inc(v_snd_360_);
lean_dec_ref(v___x_359_);
v___y_343_ = v___y_339_;
v___y_344_ = v_snd_360_;
goto v___jp_342_;
}
v___jp_342_:
{
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v_fst_347_; lean_object* v_snd_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_356_; 
v___x_345_ = l_Lean_Expr_app___override(v_f_337_, v_a_338_);
v___x_346_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_345_, v___y_344_);
v_fst_347_ = lean_ctor_get(v___x_346_, 0);
v_snd_348_ = lean_ctor_get(v___x_346_, 1);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_356_ == 0)
{
v___x_350_ = v___x_346_;
v_isShared_351_ = v_isSharedCheck_356_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_snd_348_);
lean_inc(v_fst_347_);
lean_dec(v___x_346_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_356_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_353_; 
if (v_isShared_351_ == 0)
{
lean_ctor_set(v___x_350_, 1, v___y_343_);
v___x_353_ = v___x_350_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_fst_347_);
lean_ctor_set(v_reuseFailAlloc_355_, 1, v___y_343_);
v___x_353_ = v_reuseFailAlloc_355_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
lean_object* v___x_354_; 
v___x_354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_354_, 0, v___x_353_);
lean_ctor_set(v___x_354_, 1, v_snd_348_);
return v___x_354_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__3___boxed(lean_object* v_f_361_, lean_object* v_a_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_){
_start:
{
uint8_t v___y_23512__boxed_366_; lean_object* v_res_367_; 
v___y_23512__boxed_366_ = lean_unbox(v___y_364_);
v_res_367_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__3(v_f_361_, v_a_362_, v___y_363_, v___y_23512__boxed_366_, v___y_365_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6(lean_object* v_x_368_, lean_object* v_t_369_, lean_object* v_v_370_, lean_object* v_b_371_, uint8_t v_nondep_372_, lean_object* v___y_373_, uint8_t v___y_374_, lean_object* v___y_375_){
_start:
{
lean_object* v___y_377_; lean_object* v___y_378_; 
if (v___y_374_ == 0)
{
v___y_377_ = v___y_373_;
v___y_378_ = v___y_375_;
goto v___jp_376_;
}
else
{
lean_object* v___x_391_; lean_object* v_snd_392_; lean_object* v___x_393_; lean_object* v_snd_394_; lean_object* v___x_395_; lean_object* v_snd_396_; 
lean_inc_ref(v_t_369_);
v___x_391_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_369_, v___y_374_, v___y_375_);
v_snd_392_ = lean_ctor_get(v___x_391_, 1);
lean_inc(v_snd_392_);
lean_dec_ref(v___x_391_);
lean_inc_ref(v_v_370_);
v___x_393_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_v_370_, v___y_374_, v_snd_392_);
v_snd_394_ = lean_ctor_get(v___x_393_, 1);
lean_inc(v_snd_394_);
lean_dec_ref(v___x_393_);
lean_inc_ref(v_b_371_);
v___x_395_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_371_, v___y_374_, v_snd_394_);
v_snd_396_ = lean_ctor_get(v___x_395_, 1);
lean_inc(v_snd_396_);
lean_dec_ref(v___x_395_);
v___y_377_ = v___y_373_;
v___y_378_ = v_snd_396_;
goto v___jp_376_;
}
v___jp_376_:
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v_fst_381_; lean_object* v_snd_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_390_; 
v___x_379_ = l_Lean_Expr_letE___override(v_x_368_, v_t_369_, v_v_370_, v_b_371_, v_nondep_372_);
v___x_380_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_379_, v___y_378_);
v_fst_381_ = lean_ctor_get(v___x_380_, 0);
v_snd_382_ = lean_ctor_get(v___x_380_, 1);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_390_ == 0)
{
v___x_384_ = v___x_380_;
v_isShared_385_ = v_isSharedCheck_390_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_snd_382_);
lean_inc(v_fst_381_);
lean_dec(v___x_380_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_390_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_387_; 
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 1, v___y_377_);
v___x_387_ = v___x_384_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_fst_381_);
lean_ctor_set(v_reuseFailAlloc_389_, 1, v___y_377_);
v___x_387_ = v_reuseFailAlloc_389_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
lean_object* v___x_388_; 
v___x_388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_388_, 0, v___x_387_);
lean_ctor_set(v___x_388_, 1, v_snd_382_);
return v___x_388_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6___boxed(lean_object* v_x_397_, lean_object* v_t_398_, lean_object* v_v_399_, lean_object* v_b_400_, lean_object* v_nondep_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_){
_start:
{
uint8_t v_nondep_boxed_405_; uint8_t v___y_23561__boxed_406_; lean_object* v_res_407_; 
v_nondep_boxed_405_ = lean_unbox(v_nondep_401_);
v___y_23561__boxed_406_ = lean_unbox(v___y_403_);
v_res_407_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6(v_x_397_, v_t_398_, v_v_399_, v_b_400_, v_nondep_boxed_405_, v___y_402_, v___y_23561__boxed_406_, v___y_404_);
return v_res_407_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__3(void){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_411_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__2));
v___x_412_ = lean_unsigned_to_nat(67u);
v___x_413_ = lean_unsigned_to_nat(35u);
v___x_414_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__1));
v___x_415_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__0));
v___x_416_ = l_mkPanicMessageWithDecl(v___x_415_, v___x_414_, v___x_413_, v___x_412_, v___x_411_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(lean_object* v_beginIdx_417_, lean_object* v_n_418_, lean_object* v_subst_419_, lean_object* v_e_420_, lean_object* v_offset_421_, lean_object* v_a_422_, uint8_t v_a_423_, lean_object* v_a_424_){
_start:
{
switch(lean_obj_tag(v_e_420_))
{
case 5:
{
lean_object* v_fn_425_; lean_object* v_arg_426_; lean_object* v___x_427_; lean_object* v_fst_428_; lean_object* v_snd_429_; lean_object* v_fst_430_; lean_object* v_snd_431_; lean_object* v___x_432_; lean_object* v_fst_433_; lean_object* v_snd_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_455_; 
v_fn_425_ = lean_ctor_get(v_e_420_, 0);
v_arg_426_ = lean_ctor_get(v_e_420_, 1);
lean_inc(v_offset_421_);
lean_inc_ref(v_fn_425_);
v___x_427_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(v_beginIdx_417_, v_n_418_, v_subst_419_, v_fn_425_, v_offset_421_, v_a_422_, v_a_423_, v_a_424_);
v_fst_428_ = lean_ctor_get(v___x_427_, 0);
lean_inc(v_fst_428_);
v_snd_429_ = lean_ctor_get(v___x_427_, 1);
lean_inc(v_snd_429_);
lean_dec_ref(v___x_427_);
v_fst_430_ = lean_ctor_get(v_fst_428_, 0);
lean_inc(v_fst_430_);
v_snd_431_ = lean_ctor_get(v_fst_428_, 1);
lean_inc(v_snd_431_);
lean_dec(v_fst_428_);
lean_inc_ref(v_arg_426_);
v___x_432_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(v_beginIdx_417_, v_n_418_, v_subst_419_, v_arg_426_, v_offset_421_, v_snd_431_, v_a_423_, v_snd_429_);
v_fst_433_ = lean_ctor_get(v___x_432_, 0);
v_snd_434_ = lean_ctor_get(v___x_432_, 1);
v_isSharedCheck_455_ = !lean_is_exclusive(v___x_432_);
if (v_isSharedCheck_455_ == 0)
{
v___x_436_ = v___x_432_;
v_isShared_437_ = v_isSharedCheck_455_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_snd_434_);
lean_inc(v_fst_433_);
lean_dec(v___x_432_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_455_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v_fst_438_; lean_object* v_snd_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_454_; 
v_fst_438_ = lean_ctor_get(v_fst_433_, 0);
v_snd_439_ = lean_ctor_get(v_fst_433_, 1);
v_isSharedCheck_454_ = !lean_is_exclusive(v_fst_433_);
if (v_isSharedCheck_454_ == 0)
{
v___x_441_ = v_fst_433_;
v_isShared_442_ = v_isSharedCheck_454_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_snd_439_);
lean_inc(v_fst_438_);
lean_dec(v_fst_433_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_454_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
uint8_t v___y_444_; uint8_t v___x_452_; 
v___x_452_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_425_, v_fst_430_);
if (v___x_452_ == 0)
{
v___y_444_ = v___x_452_;
goto v___jp_443_;
}
else
{
uint8_t v___x_453_; 
v___x_453_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_426_, v_fst_438_);
v___y_444_ = v___x_453_;
goto v___jp_443_;
}
v___jp_443_:
{
if (v___y_444_ == 0)
{
lean_object* v___x_445_; 
lean_del_object(v___x_441_);
lean_del_object(v___x_436_);
lean_dec_ref(v_e_420_);
v___x_445_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__3(v_fst_430_, v_fst_438_, v_snd_439_, v_a_423_, v_snd_434_);
return v___x_445_;
}
else
{
lean_object* v___x_447_; 
lean_dec(v_fst_438_);
lean_dec(v_fst_430_);
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 0, v_e_420_);
v___x_447_ = v___x_441_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v_e_420_);
lean_ctor_set(v_reuseFailAlloc_451_, 1, v_snd_439_);
v___x_447_ = v_reuseFailAlloc_451_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
lean_object* v___x_449_; 
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 0, v___x_447_);
v___x_449_ = v___x_436_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v___x_447_);
lean_ctor_set(v_reuseFailAlloc_450_, 1, v_snd_434_);
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
case 6:
{
lean_object* v_binderName_456_; lean_object* v_binderType_457_; lean_object* v_body_458_; uint8_t v_binderInfo_459_; lean_object* v___x_460_; lean_object* v_fst_461_; lean_object* v_snd_462_; lean_object* v_fst_463_; lean_object* v_snd_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v_fst_468_; lean_object* v_snd_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_490_; 
v_binderName_456_ = lean_ctor_get(v_e_420_, 0);
v_binderType_457_ = lean_ctor_get(v_e_420_, 1);
v_body_458_ = lean_ctor_get(v_e_420_, 2);
v_binderInfo_459_ = lean_ctor_get_uint8(v_e_420_, sizeof(void*)*3 + 8);
lean_inc(v_offset_421_);
lean_inc_ref(v_binderType_457_);
v___x_460_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(v_beginIdx_417_, v_n_418_, v_subst_419_, v_binderType_457_, v_offset_421_, v_a_422_, v_a_423_, v_a_424_);
v_fst_461_ = lean_ctor_get(v___x_460_, 0);
lean_inc(v_fst_461_);
v_snd_462_ = lean_ctor_get(v___x_460_, 1);
lean_inc(v_snd_462_);
lean_dec_ref(v___x_460_);
v_fst_463_ = lean_ctor_get(v_fst_461_, 0);
lean_inc(v_fst_463_);
v_snd_464_ = lean_ctor_get(v_fst_461_, 1);
lean_inc(v_snd_464_);
lean_dec(v_fst_461_);
v___x_465_ = lean_unsigned_to_nat(1u);
v___x_466_ = lean_nat_add(v_offset_421_, v___x_465_);
lean_dec(v_offset_421_);
lean_inc_ref(v_body_458_);
v___x_467_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(v_beginIdx_417_, v_n_418_, v_subst_419_, v_body_458_, v___x_466_, v_snd_464_, v_a_423_, v_snd_462_);
v_fst_468_ = lean_ctor_get(v___x_467_, 0);
v_snd_469_ = lean_ctor_get(v___x_467_, 1);
v_isSharedCheck_490_ = !lean_is_exclusive(v___x_467_);
if (v_isSharedCheck_490_ == 0)
{
v___x_471_ = v___x_467_;
v_isShared_472_ = v_isSharedCheck_490_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_snd_469_);
lean_inc(v_fst_468_);
lean_dec(v___x_467_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_490_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v_fst_473_; lean_object* v_snd_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_489_; 
v_fst_473_ = lean_ctor_get(v_fst_468_, 0);
v_snd_474_ = lean_ctor_get(v_fst_468_, 1);
v_isSharedCheck_489_ = !lean_is_exclusive(v_fst_468_);
if (v_isSharedCheck_489_ == 0)
{
v___x_476_ = v_fst_468_;
v_isShared_477_ = v_isSharedCheck_489_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_snd_474_);
lean_inc(v_fst_473_);
lean_dec(v_fst_468_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_489_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
uint8_t v___y_479_; uint8_t v___x_487_; 
v___x_487_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_457_, v_fst_463_);
if (v___x_487_ == 0)
{
v___y_479_ = v___x_487_;
goto v___jp_478_;
}
else
{
uint8_t v___x_488_; 
v___x_488_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_458_, v_fst_473_);
v___y_479_ = v___x_488_;
goto v___jp_478_;
}
v___jp_478_:
{
if (v___y_479_ == 0)
{
lean_object* v___x_480_; 
lean_inc(v_binderName_456_);
lean_del_object(v___x_476_);
lean_del_object(v___x_471_);
lean_dec_ref(v_e_420_);
v___x_480_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__4(v_binderName_456_, v_binderInfo_459_, v_fst_463_, v_fst_473_, v_snd_474_, v_a_423_, v_snd_469_);
return v___x_480_;
}
else
{
lean_object* v___x_482_; 
lean_dec(v_fst_473_);
lean_dec(v_fst_463_);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 0, v_e_420_);
v___x_482_ = v___x_476_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_e_420_);
lean_ctor_set(v_reuseFailAlloc_486_, 1, v_snd_474_);
v___x_482_ = v_reuseFailAlloc_486_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
lean_object* v___x_484_; 
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 0, v___x_482_);
v___x_484_ = v___x_471_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v___x_482_);
lean_ctor_set(v_reuseFailAlloc_485_, 1, v_snd_469_);
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
}
}
}
case 7:
{
lean_object* v_binderName_491_; lean_object* v_binderType_492_; lean_object* v_body_493_; uint8_t v_binderInfo_494_; lean_object* v___x_495_; lean_object* v_fst_496_; lean_object* v_snd_497_; lean_object* v_fst_498_; lean_object* v_snd_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v_fst_503_; lean_object* v_snd_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_525_; 
v_binderName_491_ = lean_ctor_get(v_e_420_, 0);
v_binderType_492_ = lean_ctor_get(v_e_420_, 1);
v_body_493_ = lean_ctor_get(v_e_420_, 2);
v_binderInfo_494_ = lean_ctor_get_uint8(v_e_420_, sizeof(void*)*3 + 8);
lean_inc(v_offset_421_);
lean_inc_ref(v_binderType_492_);
v___x_495_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(v_beginIdx_417_, v_n_418_, v_subst_419_, v_binderType_492_, v_offset_421_, v_a_422_, v_a_423_, v_a_424_);
v_fst_496_ = lean_ctor_get(v___x_495_, 0);
lean_inc(v_fst_496_);
v_snd_497_ = lean_ctor_get(v___x_495_, 1);
lean_inc(v_snd_497_);
lean_dec_ref(v___x_495_);
v_fst_498_ = lean_ctor_get(v_fst_496_, 0);
lean_inc(v_fst_498_);
v_snd_499_ = lean_ctor_get(v_fst_496_, 1);
lean_inc(v_snd_499_);
lean_dec(v_fst_496_);
v___x_500_ = lean_unsigned_to_nat(1u);
v___x_501_ = lean_nat_add(v_offset_421_, v___x_500_);
lean_dec(v_offset_421_);
lean_inc_ref(v_body_493_);
v___x_502_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(v_beginIdx_417_, v_n_418_, v_subst_419_, v_body_493_, v___x_501_, v_snd_499_, v_a_423_, v_snd_497_);
v_fst_503_ = lean_ctor_get(v___x_502_, 0);
v_snd_504_ = lean_ctor_get(v___x_502_, 1);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_525_ == 0)
{
v___x_506_ = v___x_502_;
v_isShared_507_ = v_isSharedCheck_525_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_snd_504_);
lean_inc(v_fst_503_);
lean_dec(v___x_502_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_525_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v_fst_508_; lean_object* v_snd_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_524_; 
v_fst_508_ = lean_ctor_get(v_fst_503_, 0);
v_snd_509_ = lean_ctor_get(v_fst_503_, 1);
v_isSharedCheck_524_ = !lean_is_exclusive(v_fst_503_);
if (v_isSharedCheck_524_ == 0)
{
v___x_511_ = v_fst_503_;
v_isShared_512_ = v_isSharedCheck_524_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_snd_509_);
lean_inc(v_fst_508_);
lean_dec(v_fst_503_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_524_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
uint8_t v___y_514_; uint8_t v___x_522_; 
v___x_522_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_492_, v_fst_498_);
if (v___x_522_ == 0)
{
v___y_514_ = v___x_522_;
goto v___jp_513_;
}
else
{
uint8_t v___x_523_; 
v___x_523_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_493_, v_fst_508_);
v___y_514_ = v___x_523_;
goto v___jp_513_;
}
v___jp_513_:
{
if (v___y_514_ == 0)
{
lean_object* v___x_515_; 
lean_inc(v_binderName_491_);
lean_del_object(v___x_511_);
lean_del_object(v___x_506_);
lean_dec_ref(v_e_420_);
v___x_515_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__5(v_binderName_491_, v_binderInfo_494_, v_fst_498_, v_fst_508_, v_snd_509_, v_a_423_, v_snd_504_);
return v___x_515_;
}
else
{
lean_object* v___x_517_; 
lean_dec(v_fst_508_);
lean_dec(v_fst_498_);
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 0, v_e_420_);
v___x_517_ = v___x_511_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v_e_420_);
lean_ctor_set(v_reuseFailAlloc_521_, 1, v_snd_509_);
v___x_517_ = v_reuseFailAlloc_521_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
lean_object* v___x_519_; 
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 0, v___x_517_);
v___x_519_ = v___x_506_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v___x_517_);
lean_ctor_set(v_reuseFailAlloc_520_, 1, v_snd_504_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
}
}
}
}
}
case 8:
{
lean_object* v_declName_526_; lean_object* v_type_527_; lean_object* v_value_528_; lean_object* v_body_529_; uint8_t v_nondep_530_; lean_object* v___x_531_; lean_object* v_fst_532_; lean_object* v_snd_533_; lean_object* v_fst_534_; lean_object* v_snd_535_; lean_object* v___x_536_; lean_object* v_fst_537_; lean_object* v_snd_538_; lean_object* v_fst_539_; lean_object* v_snd_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v_fst_544_; lean_object* v_snd_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_568_; 
v_declName_526_ = lean_ctor_get(v_e_420_, 0);
v_type_527_ = lean_ctor_get(v_e_420_, 1);
v_value_528_ = lean_ctor_get(v_e_420_, 2);
v_body_529_ = lean_ctor_get(v_e_420_, 3);
v_nondep_530_ = lean_ctor_get_uint8(v_e_420_, sizeof(void*)*4 + 8);
lean_inc(v_offset_421_);
lean_inc_ref(v_type_527_);
v___x_531_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(v_beginIdx_417_, v_n_418_, v_subst_419_, v_type_527_, v_offset_421_, v_a_422_, v_a_423_, v_a_424_);
v_fst_532_ = lean_ctor_get(v___x_531_, 0);
lean_inc(v_fst_532_);
v_snd_533_ = lean_ctor_get(v___x_531_, 1);
lean_inc(v_snd_533_);
lean_dec_ref(v___x_531_);
v_fst_534_ = lean_ctor_get(v_fst_532_, 0);
lean_inc(v_fst_534_);
v_snd_535_ = lean_ctor_get(v_fst_532_, 1);
lean_inc(v_snd_535_);
lean_dec(v_fst_532_);
lean_inc(v_offset_421_);
lean_inc_ref(v_value_528_);
v___x_536_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(v_beginIdx_417_, v_n_418_, v_subst_419_, v_value_528_, v_offset_421_, v_snd_535_, v_a_423_, v_snd_533_);
v_fst_537_ = lean_ctor_get(v___x_536_, 0);
lean_inc(v_fst_537_);
v_snd_538_ = lean_ctor_get(v___x_536_, 1);
lean_inc(v_snd_538_);
lean_dec_ref(v___x_536_);
v_fst_539_ = lean_ctor_get(v_fst_537_, 0);
lean_inc(v_fst_539_);
v_snd_540_ = lean_ctor_get(v_fst_537_, 1);
lean_inc(v_snd_540_);
lean_dec(v_fst_537_);
v___x_541_ = lean_unsigned_to_nat(1u);
v___x_542_ = lean_nat_add(v_offset_421_, v___x_541_);
lean_dec(v_offset_421_);
lean_inc_ref(v_body_529_);
v___x_543_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(v_beginIdx_417_, v_n_418_, v_subst_419_, v_body_529_, v___x_542_, v_snd_540_, v_a_423_, v_snd_538_);
v_fst_544_ = lean_ctor_get(v___x_543_, 0);
v_snd_545_ = lean_ctor_get(v___x_543_, 1);
v_isSharedCheck_568_ = !lean_is_exclusive(v___x_543_);
if (v_isSharedCheck_568_ == 0)
{
v___x_547_ = v___x_543_;
v_isShared_548_ = v_isSharedCheck_568_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_snd_545_);
lean_inc(v_fst_544_);
lean_dec(v___x_543_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_568_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v_fst_549_; lean_object* v_snd_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_567_; 
v_fst_549_ = lean_ctor_get(v_fst_544_, 0);
v_snd_550_ = lean_ctor_get(v_fst_544_, 1);
v_isSharedCheck_567_ = !lean_is_exclusive(v_fst_544_);
if (v_isSharedCheck_567_ == 0)
{
v___x_552_ = v_fst_544_;
v_isShared_553_ = v_isSharedCheck_567_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_snd_550_);
lean_inc(v_fst_549_);
lean_dec(v_fst_544_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_567_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
uint8_t v___y_555_; uint8_t v___x_565_; 
v___x_565_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_type_527_, v_fst_534_);
if (v___x_565_ == 0)
{
v___y_555_ = v___x_565_;
goto v___jp_554_;
}
else
{
uint8_t v___x_566_; 
v___x_566_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_value_528_, v_fst_539_);
v___y_555_ = v___x_566_;
goto v___jp_554_;
}
v___jp_554_:
{
if (v___y_555_ == 0)
{
lean_object* v___x_556_; 
lean_inc(v_declName_526_);
lean_del_object(v___x_552_);
lean_del_object(v___x_547_);
lean_dec_ref(v_e_420_);
v___x_556_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6(v_declName_526_, v_fst_534_, v_fst_539_, v_fst_549_, v_nondep_530_, v_snd_550_, v_a_423_, v_snd_545_);
return v___x_556_;
}
else
{
uint8_t v___x_557_; 
v___x_557_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_529_, v_fst_549_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; 
lean_inc(v_declName_526_);
lean_del_object(v___x_552_);
lean_del_object(v___x_547_);
lean_dec_ref(v_e_420_);
v___x_558_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6(v_declName_526_, v_fst_534_, v_fst_539_, v_fst_549_, v_nondep_530_, v_snd_550_, v_a_423_, v_snd_545_);
return v___x_558_;
}
else
{
lean_object* v___x_560_; 
lean_dec(v_fst_549_);
lean_dec(v_fst_539_);
lean_dec(v_fst_534_);
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 0, v_e_420_);
v___x_560_ = v___x_552_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v_e_420_);
lean_ctor_set(v_reuseFailAlloc_564_, 1, v_snd_550_);
v___x_560_ = v_reuseFailAlloc_564_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
lean_object* v___x_562_; 
if (v_isShared_548_ == 0)
{
lean_ctor_set(v___x_547_, 0, v___x_560_);
v___x_562_ = v___x_547_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v___x_560_);
lean_ctor_set(v_reuseFailAlloc_563_, 1, v_snd_545_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
}
}
}
}
}
}
case 10:
{
lean_object* v_data_569_; lean_object* v_expr_570_; lean_object* v___x_571_; lean_object* v_fst_572_; lean_object* v_snd_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_591_; 
v_data_569_ = lean_ctor_get(v_e_420_, 0);
v_expr_570_ = lean_ctor_get(v_e_420_, 1);
lean_inc_ref(v_expr_570_);
v___x_571_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(v_beginIdx_417_, v_n_418_, v_subst_419_, v_expr_570_, v_offset_421_, v_a_422_, v_a_423_, v_a_424_);
v_fst_572_ = lean_ctor_get(v___x_571_, 0);
v_snd_573_ = lean_ctor_get(v___x_571_, 1);
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_591_ == 0)
{
v___x_575_ = v___x_571_;
v_isShared_576_ = v_isSharedCheck_591_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_snd_573_);
lean_inc(v_fst_572_);
lean_dec(v___x_571_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_591_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v_fst_577_; lean_object* v_snd_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_590_; 
v_fst_577_ = lean_ctor_get(v_fst_572_, 0);
v_snd_578_ = lean_ctor_get(v_fst_572_, 1);
v_isSharedCheck_590_ = !lean_is_exclusive(v_fst_572_);
if (v_isSharedCheck_590_ == 0)
{
v___x_580_ = v_fst_572_;
v_isShared_581_ = v_isSharedCheck_590_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_snd_578_);
lean_inc(v_fst_577_);
lean_dec(v_fst_572_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_590_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
uint8_t v___x_582_; 
v___x_582_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_expr_570_, v_fst_577_);
if (v___x_582_ == 0)
{
lean_object* v___x_583_; 
lean_inc(v_data_569_);
lean_del_object(v___x_580_);
lean_del_object(v___x_575_);
lean_dec_ref(v_e_420_);
v___x_583_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__7(v_data_569_, v_fst_577_, v_snd_578_, v_a_423_, v_snd_573_);
return v___x_583_;
}
else
{
lean_object* v___x_585_; 
lean_dec(v_fst_577_);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 0, v_e_420_);
v___x_585_ = v___x_580_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_e_420_);
lean_ctor_set(v_reuseFailAlloc_589_, 1, v_snd_578_);
v___x_585_ = v_reuseFailAlloc_589_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
lean_object* v___x_587_; 
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 0, v___x_585_);
v___x_587_ = v___x_575_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v___x_585_);
lean_ctor_set(v_reuseFailAlloc_588_, 1, v_snd_573_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
}
}
}
}
case 11:
{
lean_object* v_typeName_592_; lean_object* v_idx_593_; lean_object* v_struct_594_; lean_object* v___x_595_; lean_object* v_fst_596_; lean_object* v_snd_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_615_; 
v_typeName_592_ = lean_ctor_get(v_e_420_, 0);
v_idx_593_ = lean_ctor_get(v_e_420_, 1);
v_struct_594_ = lean_ctor_get(v_e_420_, 2);
lean_inc_ref(v_struct_594_);
v___x_595_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(v_beginIdx_417_, v_n_418_, v_subst_419_, v_struct_594_, v_offset_421_, v_a_422_, v_a_423_, v_a_424_);
v_fst_596_ = lean_ctor_get(v___x_595_, 0);
v_snd_597_ = lean_ctor_get(v___x_595_, 1);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_615_ == 0)
{
v___x_599_ = v___x_595_;
v_isShared_600_ = v_isSharedCheck_615_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_snd_597_);
lean_inc(v_fst_596_);
lean_dec(v___x_595_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_615_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v_fst_601_; lean_object* v_snd_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_614_; 
v_fst_601_ = lean_ctor_get(v_fst_596_, 0);
v_snd_602_ = lean_ctor_get(v_fst_596_, 1);
v_isSharedCheck_614_ = !lean_is_exclusive(v_fst_596_);
if (v_isSharedCheck_614_ == 0)
{
v___x_604_ = v_fst_596_;
v_isShared_605_ = v_isSharedCheck_614_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_snd_602_);
lean_inc(v_fst_601_);
lean_dec(v_fst_596_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_614_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
uint8_t v___x_606_; 
v___x_606_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_594_, v_fst_601_);
if (v___x_606_ == 0)
{
lean_object* v___x_607_; 
lean_inc(v_idx_593_);
lean_inc(v_typeName_592_);
lean_del_object(v___x_604_);
lean_del_object(v___x_599_);
lean_dec_ref(v_e_420_);
v___x_607_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__8(v_typeName_592_, v_idx_593_, v_fst_601_, v_snd_602_, v_a_423_, v_snd_597_);
return v___x_607_;
}
else
{
lean_object* v___x_609_; 
lean_dec(v_fst_601_);
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 0, v_e_420_);
v___x_609_ = v___x_604_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_e_420_);
lean_ctor_set(v_reuseFailAlloc_613_, 1, v_snd_602_);
v___x_609_ = v_reuseFailAlloc_613_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
lean_object* v___x_611_; 
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 0, v___x_609_);
v___x_611_ = v___x_599_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v___x_609_);
lean_ctor_set(v_reuseFailAlloc_612_, 1, v_snd_597_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_616_; lean_object* v___x_617_; 
lean_dec(v_offset_421_);
lean_dec_ref(v_e_420_);
v___x_616_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__3);
v___x_617_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9(v___x_616_, v_a_422_, v_a_423_, v_a_424_);
return v___x_617_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(lean_object* v_beginIdx_618_, lean_object* v_n_619_, lean_object* v_subst_620_, lean_object* v_e_621_, lean_object* v_offset_622_, lean_object* v_a_623_, uint8_t v_a_624_, lean_object* v_a_625_){
_start:
{
lean_object* v_key_626_; lean_object* v___x_627_; 
lean_inc(v_offset_622_);
lean_inc_ref(v_e_621_);
v_key_626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_626_, 0, v_e_621_);
lean_ctor_set(v_key_626_, 1, v_offset_622_);
v___x_627_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___redArg(v_a_623_, v_key_626_);
if (lean_obj_tag(v___x_627_) == 1)
{
lean_object* v_val_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
lean_dec_ref(v_key_626_);
lean_dec(v_offset_622_);
lean_dec_ref(v_e_621_);
v_val_628_ = lean_ctor_get(v___x_627_, 0);
lean_inc(v_val_628_);
lean_dec_ref(v___x_627_);
v___x_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_629_, 0, v_val_628_);
lean_ctor_set(v___x_629_, 1, v_a_623_);
v___x_630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
lean_ctor_set(v___x_630_, 1, v_a_625_);
return v___x_630_;
}
else
{
lean_object* v_s_u2081_631_; 
lean_dec(v___x_627_);
v_s_u2081_631_ = lean_nat_add(v_beginIdx_618_, v_offset_622_);
switch(lean_obj_tag(v_e_621_))
{
case 0:
{
lean_object* v_deBruijnIndex_632_; uint8_t v___x_633_; 
v_deBruijnIndex_632_ = lean_ctor_get(v_e_621_, 0);
v___x_633_ = lean_nat_dec_le(v_s_u2081_631_, v_deBruijnIndex_632_);
lean_dec(v_s_u2081_631_);
if (v___x_633_ == 0)
{
lean_object* v___x_634_; 
lean_dec(v_offset_622_);
v___x_634_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_626_, v_e_621_, v_a_623_, v_a_624_, v_a_625_);
return v___x_634_;
}
else
{
lean_object* v___x_635_; uint8_t v___x_636_; 
lean_inc(v_deBruijnIndex_632_);
lean_dec_ref(v_e_621_);
v___x_635_ = lean_nat_add(v_offset_622_, v_n_619_);
v___x_636_ = lean_nat_dec_lt(v_deBruijnIndex_632_, v___x_635_);
lean_dec(v___x_635_);
if (v___x_636_ == 0)
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v_fst_639_; lean_object* v_snd_640_; lean_object* v___x_641_; 
lean_dec(v_offset_622_);
v___x_637_ = lean_nat_sub(v_deBruijnIndex_632_, v_n_619_);
lean_dec(v_deBruijnIndex_632_);
v___x_638_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___redArg(v___x_637_, v_a_625_);
v_fst_639_ = lean_ctor_get(v___x_638_, 0);
lean_inc(v_fst_639_);
v_snd_640_ = lean_ctor_get(v___x_638_, 1);
lean_inc(v_snd_640_);
lean_dec_ref(v___x_638_);
v___x_641_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_626_, v_fst_639_, v_a_623_, v_a_624_, v_snd_640_);
return v___x_641_;
}
else
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v_v_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v_fst_649_; lean_object* v_snd_650_; lean_object* v___x_651_; 
v___x_642_ = lean_nat_sub(v_deBruijnIndex_632_, v_offset_622_);
lean_dec(v_deBruijnIndex_632_);
v___x_643_ = lean_nat_sub(v_n_619_, v___x_642_);
lean_dec(v___x_642_);
v___x_644_ = lean_unsigned_to_nat(1u);
v___x_645_ = lean_nat_sub(v___x_643_, v___x_644_);
lean_dec(v___x_643_);
v_v_646_ = lean_array_fget_borrowed(v_subst_620_, v___x_645_);
lean_dec(v___x_645_);
v___x_647_ = lean_unsigned_to_nat(0u);
lean_inc(v_v_646_);
v___x_648_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(v_v_646_, v___x_647_, v_offset_622_, v_a_624_, v_a_625_);
lean_dec(v_offset_622_);
v_fst_649_ = lean_ctor_get(v___x_648_, 0);
lean_inc(v_fst_649_);
v_snd_650_ = lean_ctor_get(v___x_648_, 1);
lean_inc(v_snd_650_);
lean_dec_ref(v___x_648_);
v___x_651_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_626_, v_fst_649_, v_a_623_, v_a_624_, v_snd_650_);
return v___x_651_;
}
}
}
case 9:
{
lean_object* v___x_652_; 
lean_dec(v_s_u2081_631_);
lean_dec(v_offset_622_);
v___x_652_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_626_, v_e_621_, v_a_623_, v_a_624_, v_a_625_);
return v___x_652_;
}
case 2:
{
lean_object* v___x_653_; 
lean_dec(v_s_u2081_631_);
lean_dec(v_offset_622_);
v___x_653_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_626_, v_e_621_, v_a_623_, v_a_624_, v_a_625_);
return v___x_653_;
}
case 1:
{
lean_object* v___x_654_; 
lean_dec(v_s_u2081_631_);
lean_dec(v_offset_622_);
v___x_654_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_626_, v_e_621_, v_a_623_, v_a_624_, v_a_625_);
return v___x_654_;
}
case 4:
{
lean_object* v___x_655_; 
lean_dec(v_s_u2081_631_);
lean_dec(v_offset_622_);
v___x_655_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_626_, v_e_621_, v_a_623_, v_a_624_, v_a_625_);
return v___x_655_;
}
case 3:
{
lean_object* v___x_656_; 
lean_dec(v_s_u2081_631_);
lean_dec(v_offset_622_);
v___x_656_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_626_, v_e_621_, v_a_623_, v_a_624_, v_a_625_);
return v___x_656_;
}
default: 
{
lean_object* v___x_657_; uint8_t v___x_658_; 
v___x_657_ = l_Lean_Expr_looseBVarRange(v_e_621_);
v___x_658_ = lean_nat_dec_le(v___x_657_, v_s_u2081_631_);
lean_dec(v_s_u2081_631_);
lean_dec(v___x_657_);
if (v___x_658_ == 0)
{
switch(lean_obj_tag(v_e_621_))
{
case 9:
{
lean_object* v___x_659_; 
lean_dec(v_offset_622_);
v___x_659_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_626_, v_e_621_, v_a_623_, v_a_624_, v_a_625_);
return v___x_659_;
}
case 2:
{
lean_object* v___x_660_; 
lean_dec(v_offset_622_);
v___x_660_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_626_, v_e_621_, v_a_623_, v_a_624_, v_a_625_);
return v___x_660_;
}
case 0:
{
lean_object* v___x_661_; 
lean_dec(v_offset_622_);
v___x_661_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_626_, v_e_621_, v_a_623_, v_a_624_, v_a_625_);
return v___x_661_;
}
case 1:
{
lean_object* v___x_662_; 
lean_dec(v_offset_622_);
v___x_662_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_626_, v_e_621_, v_a_623_, v_a_624_, v_a_625_);
return v___x_662_;
}
case 4:
{
lean_object* v___x_663_; 
lean_dec(v_offset_622_);
v___x_663_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_626_, v_e_621_, v_a_623_, v_a_624_, v_a_625_);
return v___x_663_;
}
case 3:
{
lean_object* v___x_664_; 
lean_dec(v_offset_622_);
v___x_664_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_626_, v_e_621_, v_a_623_, v_a_624_, v_a_625_);
return v___x_664_;
}
default: 
{
lean_object* v___x_665_; lean_object* v_fst_666_; lean_object* v_snd_667_; lean_object* v_fst_668_; lean_object* v_snd_669_; lean_object* v___x_670_; 
v___x_665_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(v_beginIdx_618_, v_n_619_, v_subst_620_, v_e_621_, v_offset_622_, v_a_623_, v_a_624_, v_a_625_);
v_fst_666_ = lean_ctor_get(v___x_665_, 0);
lean_inc(v_fst_666_);
v_snd_667_ = lean_ctor_get(v___x_665_, 1);
lean_inc(v_snd_667_);
lean_dec_ref(v___x_665_);
v_fst_668_ = lean_ctor_get(v_fst_666_, 0);
lean_inc(v_fst_668_);
v_snd_669_ = lean_ctor_get(v_fst_666_, 1);
lean_inc(v_snd_669_);
lean_dec(v_fst_666_);
v___x_670_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_626_, v_fst_668_, v_snd_669_, v_a_624_, v_snd_667_);
return v___x_670_;
}
}
}
else
{
lean_object* v___x_671_; 
lean_dec(v_offset_622_);
v___x_671_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_626_, v_e_621_, v_a_623_, v_a_624_, v_a_625_);
return v___x_671_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2___boxed(lean_object* v_beginIdx_672_, lean_object* v_n_673_, lean_object* v_subst_674_, lean_object* v_e_675_, lean_object* v_offset_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_){
_start:
{
uint8_t v_a_23624__boxed_680_; lean_object* v_res_681_; 
v_a_23624__boxed_680_ = lean_unbox(v_a_678_);
v_res_681_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(v_beginIdx_672_, v_n_673_, v_subst_674_, v_e_675_, v_offset_676_, v_a_677_, v_a_23624__boxed_680_, v_a_679_);
lean_dec_ref(v_subst_674_);
lean_dec(v_n_673_);
lean_dec(v_beginIdx_672_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___boxed(lean_object* v_beginIdx_682_, lean_object* v_n_683_, lean_object* v_subst_684_, lean_object* v_e_685_, lean_object* v_offset_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_){
_start:
{
uint8_t v_a_23692__boxed_690_; lean_object* v_res_691_; 
v_a_23692__boxed_690_ = lean_unbox(v_a_688_);
v_res_691_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(v_beginIdx_682_, v_n_683_, v_subst_684_, v_e_685_, v_offset_686_, v_a_687_, v_a_23692__boxed_690_, v_a_689_);
lean_dec_ref(v_subst_684_);
lean_dec(v_n_683_);
lean_dec(v_beginIdx_682_);
return v_res_691_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__0(void){
_start:
{
lean_object* v___x_692_; 
v___x_692_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0(lean_box(0));
return v___x_692_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__1(void){
_start:
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_693_ = lean_box(0);
v___x_694_ = lean_unsigned_to_nat(16u);
v___x_695_ = lean_mk_array(v___x_694_, v___x_693_);
return v___x_695_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__2(void){
_start:
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_696_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__1, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__1_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__1);
v___x_697_ = lean_unsigned_to_nat(0u);
v___x_698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_698_, 0, v___x_697_);
lean_ctor_set(v___x_698_, 1, v___x_696_);
return v___x_698_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__5(void){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_701_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__2));
v___x_702_ = lean_unsigned_to_nat(34u);
v___x_703_ = lean_unsigned_to_nat(20u);
v___x_704_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__4));
v___x_705_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__3));
v___x_706_ = l_mkPanicMessageWithDecl(v___x_705_, v___x_704_, v___x_703_, v___x_702_, v___x_701_);
return v___x_706_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__6(void){
_start:
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_707_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__2));
v___x_708_ = lean_unsigned_to_nat(32u);
v___x_709_ = lean_unsigned_to_nat(19u);
v___x_710_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__4));
v___x_711_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__3));
v___x_712_ = l_mkPanicMessageWithDecl(v___x_711_, v___x_710_, v___x_709_, v___x_708_, v___x_707_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevRangeS(lean_object* v_e_713_, lean_object* v_beginIdx_714_, lean_object* v_endIdx_715_, lean_object* v_subst_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_){
_start:
{
uint8_t v___x_724_; 
v___x_724_ = lean_nat_dec_lt(v_endIdx_715_, v_beginIdx_714_);
if (v___x_724_ == 0)
{
lean_object* v___x_725_; uint8_t v___x_726_; 
v___x_725_ = lean_array_get_size(v_subst_716_);
v___x_726_ = lean_nat_dec_lt(v___x_725_, v_endIdx_715_);
if (v___x_726_ == 0)
{
lean_object* v___x_727_; lean_object* v_share_728_; lean_object* v_maxFVar_729_; lean_object* v_proofInstInfo_730_; lean_object* v_inferType_731_; lean_object* v_getLevel_732_; lean_object* v_congrInfo_733_; lean_object* v_defEqI_734_; uint8_t v_debug_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_790_; 
lean_dec(v_a_722_);
lean_dec_ref(v_a_721_);
lean_dec(v_a_720_);
lean_dec_ref(v_a_719_);
lean_dec_ref(v_a_717_);
v___x_727_ = lean_st_ref_take(v_a_718_);
v_share_728_ = lean_ctor_get(v___x_727_, 0);
v_maxFVar_729_ = lean_ctor_get(v___x_727_, 1);
v_proofInstInfo_730_ = lean_ctor_get(v___x_727_, 2);
v_inferType_731_ = lean_ctor_get(v___x_727_, 3);
v_getLevel_732_ = lean_ctor_get(v___x_727_, 4);
v_congrInfo_733_ = lean_ctor_get(v___x_727_, 5);
v_defEqI_734_ = lean_ctor_get(v___x_727_, 6);
v_debug_735_ = lean_ctor_get_uint8(v___x_727_, sizeof(void*)*7);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_790_ == 0)
{
v___x_737_ = v___x_727_;
v_isShared_738_ = v_isSharedCheck_790_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_defEqI_734_);
lean_inc(v_congrInfo_733_);
lean_inc(v_getLevel_732_);
lean_inc(v_inferType_731_);
lean_inc(v_proofInstInfo_730_);
lean_inc(v_maxFVar_729_);
lean_inc(v_share_728_);
lean_dec(v___x_727_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_790_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_739_; lean_object* v___x_741_; 
v___x_739_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__0, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__0_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__0);
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 0, v___x_739_);
v___x_741_ = v___x_737_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v___x_739_);
lean_ctor_set(v_reuseFailAlloc_789_, 1, v_maxFVar_729_);
lean_ctor_set(v_reuseFailAlloc_789_, 2, v_proofInstInfo_730_);
lean_ctor_set(v_reuseFailAlloc_789_, 3, v_inferType_731_);
lean_ctor_set(v_reuseFailAlloc_789_, 4, v_getLevel_732_);
lean_ctor_set(v_reuseFailAlloc_789_, 5, v_congrInfo_733_);
lean_ctor_set(v_reuseFailAlloc_789_, 6, v_defEqI_734_);
lean_ctor_set_uint8(v_reuseFailAlloc_789_, sizeof(void*)*7, v_debug_735_);
v___x_741_ = v_reuseFailAlloc_789_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v_fst_745_; lean_object* v_snd_746_; uint8_t v_debug_765_; lean_object* v_n_766_; lean_object* v___x_767_; 
v___x_742_ = lean_st_ref_set(v_a_718_, v___x_741_);
v___x_743_ = lean_st_ref_get(v_a_718_);
v_debug_765_ = lean_ctor_get_uint8(v___x_743_, sizeof(void*)*7);
lean_dec(v___x_743_);
v_n_766_ = lean_nat_sub(v_endIdx_715_, v_beginIdx_714_);
v___x_767_ = lean_unsigned_to_nat(0u);
switch(lean_obj_tag(v_e_713_))
{
case 0:
{
lean_object* v_deBruijnIndex_768_; uint8_t v___x_769_; 
v_deBruijnIndex_768_ = lean_ctor_get(v_e_713_, 0);
v___x_769_ = lean_nat_dec_le(v_beginIdx_714_, v_deBruijnIndex_768_);
if (v___x_769_ == 0)
{
lean_dec(v_n_766_);
v_fst_745_ = v_e_713_;
v_snd_746_ = v_share_728_;
goto v___jp_744_;
}
else
{
uint8_t v___x_770_; 
lean_inc(v_deBruijnIndex_768_);
lean_dec_ref(v_e_713_);
v___x_770_ = lean_nat_dec_lt(v_deBruijnIndex_768_, v_n_766_);
if (v___x_770_ == 0)
{
lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v_fst_773_; lean_object* v_snd_774_; 
v___x_771_ = lean_nat_sub(v_deBruijnIndex_768_, v_n_766_);
lean_dec(v_n_766_);
lean_dec(v_deBruijnIndex_768_);
v___x_772_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___redArg(v___x_771_, v_share_728_);
v_fst_773_ = lean_ctor_get(v___x_772_, 0);
lean_inc(v_fst_773_);
v_snd_774_ = lean_ctor_get(v___x_772_, 1);
lean_inc(v_snd_774_);
lean_dec_ref(v___x_772_);
v_fst_745_ = v_fst_773_;
v_snd_746_ = v_snd_774_;
goto v___jp_744_;
}
else
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v_v_778_; lean_object* v___x_779_; lean_object* v_fst_780_; lean_object* v_snd_781_; 
v___x_775_ = lean_nat_sub(v_n_766_, v_deBruijnIndex_768_);
lean_dec(v_deBruijnIndex_768_);
lean_dec(v_n_766_);
v___x_776_ = lean_unsigned_to_nat(1u);
v___x_777_ = lean_nat_sub(v___x_775_, v___x_776_);
lean_dec(v___x_775_);
v_v_778_ = lean_array_fget_borrowed(v_subst_716_, v___x_777_);
lean_dec(v___x_777_);
lean_inc(v_v_778_);
v___x_779_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(v_v_778_, v___x_767_, v___x_767_, v_debug_765_, v_share_728_);
v_fst_780_ = lean_ctor_get(v___x_779_, 0);
lean_inc(v_fst_780_);
v_snd_781_ = lean_ctor_get(v___x_779_, 1);
lean_inc(v_snd_781_);
lean_dec_ref(v___x_779_);
v_fst_745_ = v_fst_780_;
v_snd_746_ = v_snd_781_;
goto v___jp_744_;
}
}
}
case 9:
{
lean_dec(v_n_766_);
v_fst_745_ = v_e_713_;
v_snd_746_ = v_share_728_;
goto v___jp_744_;
}
case 2:
{
lean_dec(v_n_766_);
v_fst_745_ = v_e_713_;
v_snd_746_ = v_share_728_;
goto v___jp_744_;
}
case 1:
{
lean_dec(v_n_766_);
v_fst_745_ = v_e_713_;
v_snd_746_ = v_share_728_;
goto v___jp_744_;
}
case 4:
{
lean_dec(v_n_766_);
v_fst_745_ = v_e_713_;
v_snd_746_ = v_share_728_;
goto v___jp_744_;
}
case 3:
{
lean_dec(v_n_766_);
v_fst_745_ = v_e_713_;
v_snd_746_ = v_share_728_;
goto v___jp_744_;
}
default: 
{
lean_object* v___x_782_; uint8_t v___x_783_; 
v___x_782_ = l_Lean_Expr_looseBVarRange(v_e_713_);
v___x_783_ = lean_nat_dec_le(v___x_782_, v_beginIdx_714_);
lean_dec(v___x_782_);
if (v___x_783_ == 0)
{
switch(lean_obj_tag(v_e_713_))
{
case 9:
{
lean_dec(v_n_766_);
v_fst_745_ = v_e_713_;
v_snd_746_ = v_share_728_;
goto v___jp_744_;
}
case 2:
{
lean_dec(v_n_766_);
v_fst_745_ = v_e_713_;
v_snd_746_ = v_share_728_;
goto v___jp_744_;
}
case 0:
{
lean_dec(v_n_766_);
v_fst_745_ = v_e_713_;
v_snd_746_ = v_share_728_;
goto v___jp_744_;
}
case 1:
{
lean_dec(v_n_766_);
v_fst_745_ = v_e_713_;
v_snd_746_ = v_share_728_;
goto v___jp_744_;
}
case 4:
{
lean_dec(v_n_766_);
v_fst_745_ = v_e_713_;
v_snd_746_ = v_share_728_;
goto v___jp_744_;
}
case 3:
{
lean_dec(v_n_766_);
v_fst_745_ = v_e_713_;
v_snd_746_ = v_share_728_;
goto v___jp_744_;
}
default: 
{
lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v_fst_786_; lean_object* v_snd_787_; lean_object* v_fst_788_; 
v___x_784_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__2, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__2_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__2);
v___x_785_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(v_beginIdx_714_, v_n_766_, v_subst_716_, v_e_713_, v___x_767_, v___x_784_, v_debug_765_, v_share_728_);
lean_dec(v_n_766_);
v_fst_786_ = lean_ctor_get(v___x_785_, 0);
lean_inc(v_fst_786_);
v_snd_787_ = lean_ctor_get(v___x_785_, 1);
lean_inc(v_snd_787_);
lean_dec_ref(v___x_785_);
v_fst_788_ = lean_ctor_get(v_fst_786_, 0);
lean_inc(v_fst_788_);
lean_dec(v_fst_786_);
v_fst_745_ = v_fst_788_;
v_snd_746_ = v_snd_787_;
goto v___jp_744_;
}
}
}
else
{
lean_dec(v_n_766_);
v_fst_745_ = v_e_713_;
v_snd_746_ = v_share_728_;
goto v___jp_744_;
}
}
}
v___jp_744_:
{
lean_object* v___x_747_; lean_object* v_maxFVar_748_; lean_object* v_proofInstInfo_749_; lean_object* v_inferType_750_; lean_object* v_getLevel_751_; lean_object* v_congrInfo_752_; lean_object* v_defEqI_753_; uint8_t v_debug_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_763_; 
v___x_747_ = lean_st_ref_take(v_a_718_);
v_maxFVar_748_ = lean_ctor_get(v___x_747_, 1);
v_proofInstInfo_749_ = lean_ctor_get(v___x_747_, 2);
v_inferType_750_ = lean_ctor_get(v___x_747_, 3);
v_getLevel_751_ = lean_ctor_get(v___x_747_, 4);
v_congrInfo_752_ = lean_ctor_get(v___x_747_, 5);
v_defEqI_753_ = lean_ctor_get(v___x_747_, 6);
v_debug_754_ = lean_ctor_get_uint8(v___x_747_, sizeof(void*)*7);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_747_);
if (v_isSharedCheck_763_ == 0)
{
lean_object* v_unused_764_; 
v_unused_764_ = lean_ctor_get(v___x_747_, 0);
lean_dec(v_unused_764_);
v___x_756_ = v___x_747_;
v_isShared_757_ = v_isSharedCheck_763_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_defEqI_753_);
lean_inc(v_congrInfo_752_);
lean_inc(v_getLevel_751_);
lean_inc(v_inferType_750_);
lean_inc(v_proofInstInfo_749_);
lean_inc(v_maxFVar_748_);
lean_dec(v___x_747_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_763_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_759_; 
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 0, v_snd_746_);
v___x_759_ = v___x_756_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_snd_746_);
lean_ctor_set(v_reuseFailAlloc_762_, 1, v_maxFVar_748_);
lean_ctor_set(v_reuseFailAlloc_762_, 2, v_proofInstInfo_749_);
lean_ctor_set(v_reuseFailAlloc_762_, 3, v_inferType_750_);
lean_ctor_set(v_reuseFailAlloc_762_, 4, v_getLevel_751_);
lean_ctor_set(v_reuseFailAlloc_762_, 5, v_congrInfo_752_);
lean_ctor_set(v_reuseFailAlloc_762_, 6, v_defEqI_753_);
lean_ctor_set_uint8(v_reuseFailAlloc_762_, sizeof(void*)*7, v_debug_754_);
v___x_759_ = v_reuseFailAlloc_762_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_760_ = lean_st_ref_set(v_a_718_, v___x_759_);
lean_dec(v_a_718_);
v___x_761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_761_, 0, v_fst_745_);
return v___x_761_;
}
}
}
}
}
}
else
{
lean_object* v___x_791_; lean_object* v___x_792_; 
lean_dec_ref(v_e_713_);
v___x_791_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__5, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__5_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__5);
v___x_792_ = l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3(v___x_791_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_);
return v___x_792_;
}
}
else
{
lean_object* v___x_793_; lean_object* v___x_794_; 
lean_dec_ref(v_e_713_);
v___x_793_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__6, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__6_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__6);
v___x_794_ = l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3(v___x_793_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_);
return v___x_794_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevRangeS___boxed(lean_object* v_e_795_, lean_object* v_beginIdx_796_, lean_object* v_endIdx_797_, lean_object* v_subst_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_e_795_, v_beginIdx_796_, v_endIdx_797_, v_subst_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_);
lean_dec_ref(v_subst_798_);
lean_dec(v_endIdx_797_);
lean_dec(v_beginIdx_796_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4(lean_object* v_00_u03b2_807_, lean_object* v_m_808_, lean_object* v_a_809_){
_start:
{
lean_object* v___x_810_; 
v___x_810_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___redArg(v_m_808_, v_a_809_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___boxed(lean_object* v_00_u03b2_811_, lean_object* v_m_812_, lean_object* v_a_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4(v_00_u03b2_811_, v_m_812_, v_a_813_);
lean_dec_ref(v_a_813_);
lean_dec_ref(v_m_812_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4_spec__12(lean_object* v_00_u03b2_815_, lean_object* v_a_816_, lean_object* v_x_817_){
_start:
{
lean_object* v___x_818_; 
v___x_818_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4_spec__12___redArg(v_a_816_, v_x_817_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4_spec__12___boxed(lean_object* v_00_u03b2_819_, lean_object* v_a_820_, lean_object* v_x_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4_spec__12(v_00_u03b2_819_, v_a_820_, v_x_821_);
lean_dec(v_x_821_);
lean_dec_ref(v_a_820_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevS(lean_object* v_e_823_, lean_object* v_subst_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_){
_start:
{
lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_832_ = lean_unsigned_to_nat(0u);
v___x_833_ = lean_array_get_size(v_subst_824_);
v___x_834_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_e_823_, v___x_832_, v___x_833_, v_subst_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_, v_a_830_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevS___boxed(lean_object* v_e_835_, lean_object* v_subst_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l_Lean_Meta_Sym_instantiateRevS(v_e_835_, v_subst_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_);
lean_dec_ref(v_subst_836_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1(lean_object* v_msg_845_, uint8_t v___y_846_, lean_object* v___y_847_){
_start:
{
lean_object* v___f_848_; lean_object* v___f_849_; lean_object* v___f_850_; lean_object* v___f_851_; lean_object* v___f_852_; lean_object* v___f_853_; lean_object* v___f_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___f_858_; lean_object* v___f_859_; lean_object* v___f_860_; lean_object* v___f_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___f_870_; lean_object* v___x_3114__overap_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
v___f_848_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__0));
v___f_849_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__1));
v___f_850_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__2));
v___f_851_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__3));
v___f_852_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__4));
v___f_853_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__5));
v___f_854_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__6));
v___x_855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_855_, 0, v___f_848_);
lean_ctor_set(v___x_855_, 1, v___f_849_);
v___x_856_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_856_, 0, v___x_855_);
lean_ctor_set(v___x_856_, 1, v___f_850_);
lean_ctor_set(v___x_856_, 2, v___f_851_);
lean_ctor_set(v___x_856_, 3, v___f_852_);
lean_ctor_set(v___x_856_, 4, v___f_853_);
v___x_857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_857_, 0, v___x_856_);
lean_ctor_set(v___x_857_, 1, v___f_854_);
lean_inc_ref(v___x_857_);
v___f_858_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_858_, 0, v___x_857_);
lean_inc_ref(v___x_857_);
v___f_859_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_859_, 0, v___x_857_);
lean_inc_ref(v___x_857_);
v___f_860_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_860_, 0, v___x_857_);
lean_inc_ref(v___x_857_);
v___f_861_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_861_, 0, v___x_857_);
lean_inc_ref(v___x_857_);
v___x_862_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_862_, 0, lean_box(0));
lean_closure_set(v___x_862_, 1, lean_box(0));
lean_closure_set(v___x_862_, 2, v___x_857_);
v___x_863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_863_, 0, v___x_862_);
lean_ctor_set(v___x_863_, 1, v___f_858_);
lean_inc_ref(v___x_857_);
v___x_864_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_864_, 0, lean_box(0));
lean_closure_set(v___x_864_, 1, lean_box(0));
lean_closure_set(v___x_864_, 2, v___x_857_);
v___x_865_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_865_, 0, v___x_863_);
lean_ctor_set(v___x_865_, 1, v___x_864_);
lean_ctor_set(v___x_865_, 2, v___f_859_);
lean_ctor_set(v___x_865_, 3, v___f_860_);
lean_ctor_set(v___x_865_, 4, v___f_861_);
v___x_866_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_866_, 0, lean_box(0));
lean_closure_set(v___x_866_, 1, lean_box(0));
lean_closure_set(v___x_866_, 2, v___x_857_);
v___x_867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_867_, 0, v___x_865_);
lean_ctor_set(v___x_867_, 1, v___x_866_);
v___x_868_ = l_Lean_instInhabitedExpr;
v___x_869_ = l_instInhabitedOfMonad___redArg(v___x_867_, v___x_868_);
v___f_870_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_870_, 0, v___x_869_);
v___x_3114__overap_871_ = lean_panic_fn(v___f_870_, v_msg_845_);
v___x_872_ = lean_box(v___y_846_);
v___x_873_ = lean_apply_2(v___x_3114__overap_871_, v___x_872_, v___y_847_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1___boxed(lean_object* v_msg_874_, lean_object* v___y_875_, lean_object* v___y_876_){
_start:
{
uint8_t v___y_3553__boxed_877_; lean_object* v_res_878_; 
v___y_3553__boxed_877_ = lean_unbox(v___y_875_);
v_res_878_ = l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1(v_msg_874_, v___y_3553__boxed_877_, v___y_876_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0(lean_object* v_n_879_, lean_object* v_beginIdx_880_, lean_object* v_subst_881_, lean_object* v_e_882_, lean_object* v_offset_883_, lean_object* v_a_884_, uint8_t v_a_885_, lean_object* v_a_886_){
_start:
{
switch(lean_obj_tag(v_e_882_))
{
case 5:
{
lean_object* v_fn_887_; lean_object* v_arg_888_; lean_object* v___x_889_; lean_object* v_fst_890_; lean_object* v_snd_891_; lean_object* v_fst_892_; lean_object* v_snd_893_; lean_object* v___x_894_; lean_object* v_fst_895_; lean_object* v_snd_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_917_; 
v_fn_887_ = lean_ctor_get(v_e_882_, 0);
v_arg_888_ = lean_ctor_get(v_e_882_, 1);
lean_inc(v_offset_883_);
lean_inc_ref(v_fn_887_);
v___x_889_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_879_, v_beginIdx_880_, v_subst_881_, v_fn_887_, v_offset_883_, v_a_884_, v_a_885_, v_a_886_);
v_fst_890_ = lean_ctor_get(v___x_889_, 0);
lean_inc(v_fst_890_);
v_snd_891_ = lean_ctor_get(v___x_889_, 1);
lean_inc(v_snd_891_);
lean_dec_ref(v___x_889_);
v_fst_892_ = lean_ctor_get(v_fst_890_, 0);
lean_inc(v_fst_892_);
v_snd_893_ = lean_ctor_get(v_fst_890_, 1);
lean_inc(v_snd_893_);
lean_dec(v_fst_890_);
lean_inc_ref(v_arg_888_);
v___x_894_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_879_, v_beginIdx_880_, v_subst_881_, v_arg_888_, v_offset_883_, v_snd_893_, v_a_885_, v_snd_891_);
v_fst_895_ = lean_ctor_get(v___x_894_, 0);
v_snd_896_ = lean_ctor_get(v___x_894_, 1);
v_isSharedCheck_917_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_917_ == 0)
{
v___x_898_ = v___x_894_;
v_isShared_899_ = v_isSharedCheck_917_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_snd_896_);
lean_inc(v_fst_895_);
lean_dec(v___x_894_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_917_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v_fst_900_; lean_object* v_snd_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_916_; 
v_fst_900_ = lean_ctor_get(v_fst_895_, 0);
v_snd_901_ = lean_ctor_get(v_fst_895_, 1);
v_isSharedCheck_916_ = !lean_is_exclusive(v_fst_895_);
if (v_isSharedCheck_916_ == 0)
{
v___x_903_ = v_fst_895_;
v_isShared_904_ = v_isSharedCheck_916_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_snd_901_);
lean_inc(v_fst_900_);
lean_dec(v_fst_895_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_916_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
uint8_t v___y_906_; uint8_t v___x_914_; 
v___x_914_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_887_, v_fst_892_);
if (v___x_914_ == 0)
{
v___y_906_ = v___x_914_;
goto v___jp_905_;
}
else
{
uint8_t v___x_915_; 
v___x_915_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_888_, v_fst_900_);
v___y_906_ = v___x_915_;
goto v___jp_905_;
}
v___jp_905_:
{
if (v___y_906_ == 0)
{
lean_object* v___x_907_; 
lean_del_object(v___x_903_);
lean_del_object(v___x_898_);
lean_dec_ref(v_e_882_);
v___x_907_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__3(v_fst_892_, v_fst_900_, v_snd_901_, v_a_885_, v_snd_896_);
return v___x_907_;
}
else
{
lean_object* v___x_909_; 
lean_dec(v_fst_900_);
lean_dec(v_fst_892_);
if (v_isShared_904_ == 0)
{
lean_ctor_set(v___x_903_, 0, v_e_882_);
v___x_909_ = v___x_903_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_e_882_);
lean_ctor_set(v_reuseFailAlloc_913_, 1, v_snd_901_);
v___x_909_ = v_reuseFailAlloc_913_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
lean_object* v___x_911_; 
if (v_isShared_899_ == 0)
{
lean_ctor_set(v___x_898_, 0, v___x_909_);
v___x_911_ = v___x_898_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v___x_909_);
lean_ctor_set(v_reuseFailAlloc_912_, 1, v_snd_896_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
}
}
}
}
}
case 6:
{
lean_object* v_binderName_918_; lean_object* v_binderType_919_; lean_object* v_body_920_; uint8_t v_binderInfo_921_; lean_object* v___x_922_; lean_object* v_fst_923_; lean_object* v_snd_924_; lean_object* v_fst_925_; lean_object* v_snd_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v_fst_930_; lean_object* v_snd_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_952_; 
v_binderName_918_ = lean_ctor_get(v_e_882_, 0);
v_binderType_919_ = lean_ctor_get(v_e_882_, 1);
v_body_920_ = lean_ctor_get(v_e_882_, 2);
v_binderInfo_921_ = lean_ctor_get_uint8(v_e_882_, sizeof(void*)*3 + 8);
lean_inc(v_offset_883_);
lean_inc_ref(v_binderType_919_);
v___x_922_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_879_, v_beginIdx_880_, v_subst_881_, v_binderType_919_, v_offset_883_, v_a_884_, v_a_885_, v_a_886_);
v_fst_923_ = lean_ctor_get(v___x_922_, 0);
lean_inc(v_fst_923_);
v_snd_924_ = lean_ctor_get(v___x_922_, 1);
lean_inc(v_snd_924_);
lean_dec_ref(v___x_922_);
v_fst_925_ = lean_ctor_get(v_fst_923_, 0);
lean_inc(v_fst_925_);
v_snd_926_ = lean_ctor_get(v_fst_923_, 1);
lean_inc(v_snd_926_);
lean_dec(v_fst_923_);
v___x_927_ = lean_unsigned_to_nat(1u);
v___x_928_ = lean_nat_add(v_offset_883_, v___x_927_);
lean_dec(v_offset_883_);
lean_inc_ref(v_body_920_);
v___x_929_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_879_, v_beginIdx_880_, v_subst_881_, v_body_920_, v___x_928_, v_snd_926_, v_a_885_, v_snd_924_);
v_fst_930_ = lean_ctor_get(v___x_929_, 0);
v_snd_931_ = lean_ctor_get(v___x_929_, 1);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_952_ == 0)
{
v___x_933_ = v___x_929_;
v_isShared_934_ = v_isSharedCheck_952_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_snd_931_);
lean_inc(v_fst_930_);
lean_dec(v___x_929_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_952_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v_fst_935_; lean_object* v_snd_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_951_; 
v_fst_935_ = lean_ctor_get(v_fst_930_, 0);
v_snd_936_ = lean_ctor_get(v_fst_930_, 1);
v_isSharedCheck_951_ = !lean_is_exclusive(v_fst_930_);
if (v_isSharedCheck_951_ == 0)
{
v___x_938_ = v_fst_930_;
v_isShared_939_ = v_isSharedCheck_951_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_snd_936_);
lean_inc(v_fst_935_);
lean_dec(v_fst_930_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_951_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
uint8_t v___y_941_; uint8_t v___x_949_; 
v___x_949_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_919_, v_fst_925_);
if (v___x_949_ == 0)
{
v___y_941_ = v___x_949_;
goto v___jp_940_;
}
else
{
uint8_t v___x_950_; 
v___x_950_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_920_, v_fst_935_);
v___y_941_ = v___x_950_;
goto v___jp_940_;
}
v___jp_940_:
{
if (v___y_941_ == 0)
{
lean_object* v___x_942_; 
lean_inc(v_binderName_918_);
lean_del_object(v___x_938_);
lean_del_object(v___x_933_);
lean_dec_ref(v_e_882_);
v___x_942_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__4(v_binderName_918_, v_binderInfo_921_, v_fst_925_, v_fst_935_, v_snd_936_, v_a_885_, v_snd_931_);
return v___x_942_;
}
else
{
lean_object* v___x_944_; 
lean_dec(v_fst_935_);
lean_dec(v_fst_925_);
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 0, v_e_882_);
v___x_944_ = v___x_938_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_e_882_);
lean_ctor_set(v_reuseFailAlloc_948_, 1, v_snd_936_);
v___x_944_ = v_reuseFailAlloc_948_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
lean_object* v___x_946_; 
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 0, v___x_944_);
v___x_946_ = v___x_933_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v___x_944_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v_snd_931_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
}
}
}
}
case 7:
{
lean_object* v_binderName_953_; lean_object* v_binderType_954_; lean_object* v_body_955_; uint8_t v_binderInfo_956_; lean_object* v___x_957_; lean_object* v_fst_958_; lean_object* v_snd_959_; lean_object* v_fst_960_; lean_object* v_snd_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v_fst_965_; lean_object* v_snd_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_987_; 
v_binderName_953_ = lean_ctor_get(v_e_882_, 0);
v_binderType_954_ = lean_ctor_get(v_e_882_, 1);
v_body_955_ = lean_ctor_get(v_e_882_, 2);
v_binderInfo_956_ = lean_ctor_get_uint8(v_e_882_, sizeof(void*)*3 + 8);
lean_inc(v_offset_883_);
lean_inc_ref(v_binderType_954_);
v___x_957_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_879_, v_beginIdx_880_, v_subst_881_, v_binderType_954_, v_offset_883_, v_a_884_, v_a_885_, v_a_886_);
v_fst_958_ = lean_ctor_get(v___x_957_, 0);
lean_inc(v_fst_958_);
v_snd_959_ = lean_ctor_get(v___x_957_, 1);
lean_inc(v_snd_959_);
lean_dec_ref(v___x_957_);
v_fst_960_ = lean_ctor_get(v_fst_958_, 0);
lean_inc(v_fst_960_);
v_snd_961_ = lean_ctor_get(v_fst_958_, 1);
lean_inc(v_snd_961_);
lean_dec(v_fst_958_);
v___x_962_ = lean_unsigned_to_nat(1u);
v___x_963_ = lean_nat_add(v_offset_883_, v___x_962_);
lean_dec(v_offset_883_);
lean_inc_ref(v_body_955_);
v___x_964_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_879_, v_beginIdx_880_, v_subst_881_, v_body_955_, v___x_963_, v_snd_961_, v_a_885_, v_snd_959_);
v_fst_965_ = lean_ctor_get(v___x_964_, 0);
v_snd_966_ = lean_ctor_get(v___x_964_, 1);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_964_);
if (v_isSharedCheck_987_ == 0)
{
v___x_968_ = v___x_964_;
v_isShared_969_ = v_isSharedCheck_987_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_snd_966_);
lean_inc(v_fst_965_);
lean_dec(v___x_964_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_987_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v_fst_970_; lean_object* v_snd_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_986_; 
v_fst_970_ = lean_ctor_get(v_fst_965_, 0);
v_snd_971_ = lean_ctor_get(v_fst_965_, 1);
v_isSharedCheck_986_ = !lean_is_exclusive(v_fst_965_);
if (v_isSharedCheck_986_ == 0)
{
v___x_973_ = v_fst_965_;
v_isShared_974_ = v_isSharedCheck_986_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_snd_971_);
lean_inc(v_fst_970_);
lean_dec(v_fst_965_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_986_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
uint8_t v___y_976_; uint8_t v___x_984_; 
v___x_984_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_954_, v_fst_960_);
if (v___x_984_ == 0)
{
v___y_976_ = v___x_984_;
goto v___jp_975_;
}
else
{
uint8_t v___x_985_; 
v___x_985_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_955_, v_fst_970_);
v___y_976_ = v___x_985_;
goto v___jp_975_;
}
v___jp_975_:
{
if (v___y_976_ == 0)
{
lean_object* v___x_977_; 
lean_inc(v_binderName_953_);
lean_del_object(v___x_973_);
lean_del_object(v___x_968_);
lean_dec_ref(v_e_882_);
v___x_977_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__5(v_binderName_953_, v_binderInfo_956_, v_fst_960_, v_fst_970_, v_snd_971_, v_a_885_, v_snd_966_);
return v___x_977_;
}
else
{
lean_object* v___x_979_; 
lean_dec(v_fst_970_);
lean_dec(v_fst_960_);
if (v_isShared_974_ == 0)
{
lean_ctor_set(v___x_973_, 0, v_e_882_);
v___x_979_ = v___x_973_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v_e_882_);
lean_ctor_set(v_reuseFailAlloc_983_, 1, v_snd_971_);
v___x_979_ = v_reuseFailAlloc_983_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
lean_object* v___x_981_; 
if (v_isShared_969_ == 0)
{
lean_ctor_set(v___x_968_, 0, v___x_979_);
v___x_981_ = v___x_968_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v___x_979_);
lean_ctor_set(v_reuseFailAlloc_982_, 1, v_snd_966_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
}
}
}
}
}
case 8:
{
lean_object* v_declName_988_; lean_object* v_type_989_; lean_object* v_value_990_; lean_object* v_body_991_; uint8_t v_nondep_992_; lean_object* v___x_993_; lean_object* v_fst_994_; lean_object* v_snd_995_; lean_object* v_fst_996_; lean_object* v_snd_997_; lean_object* v___x_998_; lean_object* v_fst_999_; lean_object* v_snd_1000_; lean_object* v_fst_1001_; lean_object* v_snd_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v_fst_1006_; lean_object* v_snd_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1030_; 
v_declName_988_ = lean_ctor_get(v_e_882_, 0);
v_type_989_ = lean_ctor_get(v_e_882_, 1);
v_value_990_ = lean_ctor_get(v_e_882_, 2);
v_body_991_ = lean_ctor_get(v_e_882_, 3);
v_nondep_992_ = lean_ctor_get_uint8(v_e_882_, sizeof(void*)*4 + 8);
lean_inc(v_offset_883_);
lean_inc_ref(v_type_989_);
v___x_993_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_879_, v_beginIdx_880_, v_subst_881_, v_type_989_, v_offset_883_, v_a_884_, v_a_885_, v_a_886_);
v_fst_994_ = lean_ctor_get(v___x_993_, 0);
lean_inc(v_fst_994_);
v_snd_995_ = lean_ctor_get(v___x_993_, 1);
lean_inc(v_snd_995_);
lean_dec_ref(v___x_993_);
v_fst_996_ = lean_ctor_get(v_fst_994_, 0);
lean_inc(v_fst_996_);
v_snd_997_ = lean_ctor_get(v_fst_994_, 1);
lean_inc(v_snd_997_);
lean_dec(v_fst_994_);
lean_inc(v_offset_883_);
lean_inc_ref(v_value_990_);
v___x_998_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_879_, v_beginIdx_880_, v_subst_881_, v_value_990_, v_offset_883_, v_snd_997_, v_a_885_, v_snd_995_);
v_fst_999_ = lean_ctor_get(v___x_998_, 0);
lean_inc(v_fst_999_);
v_snd_1000_ = lean_ctor_get(v___x_998_, 1);
lean_inc(v_snd_1000_);
lean_dec_ref(v___x_998_);
v_fst_1001_ = lean_ctor_get(v_fst_999_, 0);
lean_inc(v_fst_1001_);
v_snd_1002_ = lean_ctor_get(v_fst_999_, 1);
lean_inc(v_snd_1002_);
lean_dec(v_fst_999_);
v___x_1003_ = lean_unsigned_to_nat(1u);
v___x_1004_ = lean_nat_add(v_offset_883_, v___x_1003_);
lean_dec(v_offset_883_);
lean_inc_ref(v_body_991_);
v___x_1005_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_879_, v_beginIdx_880_, v_subst_881_, v_body_991_, v___x_1004_, v_snd_1002_, v_a_885_, v_snd_1000_);
v_fst_1006_ = lean_ctor_get(v___x_1005_, 0);
v_snd_1007_ = lean_ctor_get(v___x_1005_, 1);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1009_ = v___x_1005_;
v_isShared_1010_ = v_isSharedCheck_1030_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_snd_1007_);
lean_inc(v_fst_1006_);
lean_dec(v___x_1005_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1030_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v_fst_1011_; lean_object* v_snd_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1029_; 
v_fst_1011_ = lean_ctor_get(v_fst_1006_, 0);
v_snd_1012_ = lean_ctor_get(v_fst_1006_, 1);
v_isSharedCheck_1029_ = !lean_is_exclusive(v_fst_1006_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1014_ = v_fst_1006_;
v_isShared_1015_ = v_isSharedCheck_1029_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_snd_1012_);
lean_inc(v_fst_1011_);
lean_dec(v_fst_1006_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1029_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
uint8_t v___y_1017_; uint8_t v___x_1027_; 
v___x_1027_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_type_989_, v_fst_996_);
if (v___x_1027_ == 0)
{
v___y_1017_ = v___x_1027_;
goto v___jp_1016_;
}
else
{
uint8_t v___x_1028_; 
v___x_1028_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_value_990_, v_fst_1001_);
v___y_1017_ = v___x_1028_;
goto v___jp_1016_;
}
v___jp_1016_:
{
if (v___y_1017_ == 0)
{
lean_object* v___x_1018_; 
lean_inc(v_declName_988_);
lean_del_object(v___x_1014_);
lean_del_object(v___x_1009_);
lean_dec_ref(v_e_882_);
v___x_1018_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6(v_declName_988_, v_fst_996_, v_fst_1001_, v_fst_1011_, v_nondep_992_, v_snd_1012_, v_a_885_, v_snd_1007_);
return v___x_1018_;
}
else
{
uint8_t v___x_1019_; 
v___x_1019_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_991_, v_fst_1011_);
if (v___x_1019_ == 0)
{
lean_object* v___x_1020_; 
lean_inc(v_declName_988_);
lean_del_object(v___x_1014_);
lean_del_object(v___x_1009_);
lean_dec_ref(v_e_882_);
v___x_1020_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6(v_declName_988_, v_fst_996_, v_fst_1001_, v_fst_1011_, v_nondep_992_, v_snd_1012_, v_a_885_, v_snd_1007_);
return v___x_1020_;
}
else
{
lean_object* v___x_1022_; 
lean_dec(v_fst_1011_);
lean_dec(v_fst_1001_);
lean_dec(v_fst_996_);
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 0, v_e_882_);
v___x_1022_ = v___x_1014_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v_e_882_);
lean_ctor_set(v_reuseFailAlloc_1026_, 1, v_snd_1012_);
v___x_1022_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
lean_object* v___x_1024_; 
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 0, v___x_1022_);
v___x_1024_ = v___x_1009_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v___x_1022_);
lean_ctor_set(v_reuseFailAlloc_1025_, 1, v_snd_1007_);
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
}
}
}
}
case 10:
{
lean_object* v_data_1031_; lean_object* v_expr_1032_; lean_object* v___x_1033_; lean_object* v_fst_1034_; lean_object* v_snd_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1053_; 
v_data_1031_ = lean_ctor_get(v_e_882_, 0);
v_expr_1032_ = lean_ctor_get(v_e_882_, 1);
lean_inc_ref(v_expr_1032_);
v___x_1033_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_879_, v_beginIdx_880_, v_subst_881_, v_expr_1032_, v_offset_883_, v_a_884_, v_a_885_, v_a_886_);
v_fst_1034_ = lean_ctor_get(v___x_1033_, 0);
v_snd_1035_ = lean_ctor_get(v___x_1033_, 1);
v_isSharedCheck_1053_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1037_ = v___x_1033_;
v_isShared_1038_ = v_isSharedCheck_1053_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_snd_1035_);
lean_inc(v_fst_1034_);
lean_dec(v___x_1033_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1053_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v_fst_1039_; lean_object* v_snd_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1052_; 
v_fst_1039_ = lean_ctor_get(v_fst_1034_, 0);
v_snd_1040_ = lean_ctor_get(v_fst_1034_, 1);
v_isSharedCheck_1052_ = !lean_is_exclusive(v_fst_1034_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1042_ = v_fst_1034_;
v_isShared_1043_ = v_isSharedCheck_1052_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_snd_1040_);
lean_inc(v_fst_1039_);
lean_dec(v_fst_1034_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1052_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
uint8_t v___x_1044_; 
v___x_1044_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_expr_1032_, v_fst_1039_);
if (v___x_1044_ == 0)
{
lean_object* v___x_1045_; 
lean_inc(v_data_1031_);
lean_del_object(v___x_1042_);
lean_del_object(v___x_1037_);
lean_dec_ref(v_e_882_);
v___x_1045_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__7(v_data_1031_, v_fst_1039_, v_snd_1040_, v_a_885_, v_snd_1035_);
return v___x_1045_;
}
else
{
lean_object* v___x_1047_; 
lean_dec(v_fst_1039_);
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 0, v_e_882_);
v___x_1047_ = v___x_1042_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_e_882_);
lean_ctor_set(v_reuseFailAlloc_1051_, 1, v_snd_1040_);
v___x_1047_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
lean_object* v___x_1049_; 
if (v_isShared_1038_ == 0)
{
lean_ctor_set(v___x_1037_, 0, v___x_1047_);
v___x_1049_ = v___x_1037_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v___x_1047_);
lean_ctor_set(v_reuseFailAlloc_1050_, 1, v_snd_1035_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
return v___x_1049_;
}
}
}
}
}
}
case 11:
{
lean_object* v_typeName_1054_; lean_object* v_idx_1055_; lean_object* v_struct_1056_; lean_object* v___x_1057_; lean_object* v_fst_1058_; lean_object* v_snd_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1077_; 
v_typeName_1054_ = lean_ctor_get(v_e_882_, 0);
v_idx_1055_ = lean_ctor_get(v_e_882_, 1);
v_struct_1056_ = lean_ctor_get(v_e_882_, 2);
lean_inc_ref(v_struct_1056_);
v___x_1057_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_879_, v_beginIdx_880_, v_subst_881_, v_struct_1056_, v_offset_883_, v_a_884_, v_a_885_, v_a_886_);
v_fst_1058_ = lean_ctor_get(v___x_1057_, 0);
v_snd_1059_ = lean_ctor_get(v___x_1057_, 1);
v_isSharedCheck_1077_ = !lean_is_exclusive(v___x_1057_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1061_ = v___x_1057_;
v_isShared_1062_ = v_isSharedCheck_1077_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_snd_1059_);
lean_inc(v_fst_1058_);
lean_dec(v___x_1057_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1077_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v_fst_1063_; lean_object* v_snd_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1076_; 
v_fst_1063_ = lean_ctor_get(v_fst_1058_, 0);
v_snd_1064_ = lean_ctor_get(v_fst_1058_, 1);
v_isSharedCheck_1076_ = !lean_is_exclusive(v_fst_1058_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1066_ = v_fst_1058_;
v_isShared_1067_ = v_isSharedCheck_1076_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_snd_1064_);
lean_inc(v_fst_1063_);
lean_dec(v_fst_1058_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1076_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
uint8_t v___x_1068_; 
v___x_1068_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_1056_, v_fst_1063_);
if (v___x_1068_ == 0)
{
lean_object* v___x_1069_; 
lean_inc(v_idx_1055_);
lean_inc(v_typeName_1054_);
lean_del_object(v___x_1066_);
lean_del_object(v___x_1061_);
lean_dec_ref(v_e_882_);
v___x_1069_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__8(v_typeName_1054_, v_idx_1055_, v_fst_1063_, v_snd_1064_, v_a_885_, v_snd_1059_);
return v___x_1069_;
}
else
{
lean_object* v___x_1071_; 
lean_dec(v_fst_1063_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 0, v_e_882_);
v___x_1071_ = v___x_1066_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v_e_882_);
lean_ctor_set(v_reuseFailAlloc_1075_, 1, v_snd_1064_);
v___x_1071_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
lean_object* v___x_1073_; 
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 0, v___x_1071_);
v___x_1073_ = v___x_1061_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v___x_1071_);
lean_ctor_set(v_reuseFailAlloc_1074_, 1, v_snd_1059_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
lean_dec(v_offset_883_);
lean_dec_ref(v_e_882_);
v___x_1078_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__3);
v___x_1079_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9(v___x_1078_, v_a_884_, v_a_885_, v_a_886_);
return v___x_1079_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(lean_object* v_n_1080_, lean_object* v_beginIdx_1081_, lean_object* v_subst_1082_, lean_object* v_e_1083_, lean_object* v_offset_1084_, lean_object* v_a_1085_, uint8_t v_a_1086_, lean_object* v_a_1087_){
_start:
{
lean_object* v_key_1088_; lean_object* v___x_1089_; 
lean_inc(v_offset_1084_);
lean_inc_ref(v_e_1083_);
v_key_1088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1088_, 0, v_e_1083_);
lean_ctor_set(v_key_1088_, 1, v_offset_1084_);
v___x_1089_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___redArg(v_a_1085_, v_key_1088_);
if (lean_obj_tag(v___x_1089_) == 1)
{
lean_object* v_val_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; 
lean_dec_ref(v_key_1088_);
lean_dec(v_offset_1084_);
lean_dec_ref(v_e_1083_);
v_val_1090_ = lean_ctor_get(v___x_1089_, 0);
lean_inc(v_val_1090_);
lean_dec_ref(v___x_1089_);
v___x_1091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1091_, 0, v_val_1090_);
lean_ctor_set(v___x_1091_, 1, v_a_1085_);
v___x_1092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1091_);
lean_ctor_set(v___x_1092_, 1, v_a_1087_);
return v___x_1092_;
}
else
{
lean_dec(v___x_1089_);
switch(lean_obj_tag(v_e_1083_))
{
case 0:
{
lean_object* v_deBruijnIndex_1093_; uint8_t v___x_1094_; 
v_deBruijnIndex_1093_ = lean_ctor_get(v_e_1083_, 0);
v___x_1094_ = lean_nat_dec_le(v_offset_1084_, v_deBruijnIndex_1093_);
if (v___x_1094_ == 0)
{
lean_object* v___x_1095_; 
lean_dec(v_offset_1084_);
v___x_1095_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1088_, v_e_1083_, v_a_1085_, v_a_1086_, v_a_1087_);
return v___x_1095_;
}
else
{
lean_object* v___x_1096_; uint8_t v___x_1097_; 
lean_inc(v_deBruijnIndex_1093_);
lean_dec_ref(v_e_1083_);
v___x_1096_ = lean_nat_add(v_offset_1084_, v_n_1080_);
v___x_1097_ = lean_nat_dec_lt(v_deBruijnIndex_1093_, v___x_1096_);
lean_dec(v___x_1096_);
if (v___x_1097_ == 0)
{
lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v_fst_1100_; lean_object* v_snd_1101_; lean_object* v___x_1102_; 
lean_dec(v_offset_1084_);
v___x_1098_ = lean_nat_sub(v_deBruijnIndex_1093_, v_n_1080_);
lean_dec(v_deBruijnIndex_1093_);
v___x_1099_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___redArg(v___x_1098_, v_a_1087_);
v_fst_1100_ = lean_ctor_get(v___x_1099_, 0);
lean_inc(v_fst_1100_);
v_snd_1101_ = lean_ctor_get(v___x_1099_, 1);
lean_inc(v_snd_1101_);
lean_dec_ref(v___x_1099_);
v___x_1102_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1088_, v_fst_1100_, v_a_1085_, v_a_1086_, v_snd_1101_);
return v___x_1102_;
}
else
{
lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v_v_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v_fst_1108_; lean_object* v_snd_1109_; lean_object* v___x_1110_; 
v___x_1103_ = lean_nat_add(v_beginIdx_1081_, v_deBruijnIndex_1093_);
lean_dec(v_deBruijnIndex_1093_);
v___x_1104_ = lean_nat_sub(v___x_1103_, v_offset_1084_);
lean_dec(v___x_1103_);
v_v_1105_ = lean_array_fget_borrowed(v_subst_1082_, v___x_1104_);
lean_dec(v___x_1104_);
v___x_1106_ = lean_unsigned_to_nat(0u);
lean_inc(v_v_1105_);
v___x_1107_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(v_v_1105_, v___x_1106_, v_offset_1084_, v_a_1086_, v_a_1087_);
lean_dec(v_offset_1084_);
v_fst_1108_ = lean_ctor_get(v___x_1107_, 0);
lean_inc(v_fst_1108_);
v_snd_1109_ = lean_ctor_get(v___x_1107_, 1);
lean_inc(v_snd_1109_);
lean_dec_ref(v___x_1107_);
v___x_1110_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1088_, v_fst_1108_, v_a_1085_, v_a_1086_, v_snd_1109_);
return v___x_1110_;
}
}
}
case 9:
{
lean_object* v___x_1111_; 
lean_dec(v_offset_1084_);
v___x_1111_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1088_, v_e_1083_, v_a_1085_, v_a_1086_, v_a_1087_);
return v___x_1111_;
}
case 2:
{
lean_object* v___x_1112_; 
lean_dec(v_offset_1084_);
v___x_1112_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1088_, v_e_1083_, v_a_1085_, v_a_1086_, v_a_1087_);
return v___x_1112_;
}
case 1:
{
lean_object* v___x_1113_; 
lean_dec(v_offset_1084_);
v___x_1113_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1088_, v_e_1083_, v_a_1085_, v_a_1086_, v_a_1087_);
return v___x_1113_;
}
case 4:
{
lean_object* v___x_1114_; 
lean_dec(v_offset_1084_);
v___x_1114_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1088_, v_e_1083_, v_a_1085_, v_a_1086_, v_a_1087_);
return v___x_1114_;
}
case 3:
{
lean_object* v___x_1115_; 
lean_dec(v_offset_1084_);
v___x_1115_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1088_, v_e_1083_, v_a_1085_, v_a_1086_, v_a_1087_);
return v___x_1115_;
}
default: 
{
lean_object* v___x_1116_; uint8_t v___x_1117_; 
v___x_1116_ = l_Lean_Expr_looseBVarRange(v_e_1083_);
v___x_1117_ = lean_nat_dec_le(v___x_1116_, v_offset_1084_);
lean_dec(v___x_1116_);
if (v___x_1117_ == 0)
{
switch(lean_obj_tag(v_e_1083_))
{
case 9:
{
lean_object* v___x_1118_; 
lean_dec(v_offset_1084_);
v___x_1118_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1088_, v_e_1083_, v_a_1085_, v_a_1086_, v_a_1087_);
return v___x_1118_;
}
case 2:
{
lean_object* v___x_1119_; 
lean_dec(v_offset_1084_);
v___x_1119_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1088_, v_e_1083_, v_a_1085_, v_a_1086_, v_a_1087_);
return v___x_1119_;
}
case 0:
{
lean_object* v___x_1120_; 
lean_dec(v_offset_1084_);
v___x_1120_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1088_, v_e_1083_, v_a_1085_, v_a_1086_, v_a_1087_);
return v___x_1120_;
}
case 1:
{
lean_object* v___x_1121_; 
lean_dec(v_offset_1084_);
v___x_1121_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1088_, v_e_1083_, v_a_1085_, v_a_1086_, v_a_1087_);
return v___x_1121_;
}
case 4:
{
lean_object* v___x_1122_; 
lean_dec(v_offset_1084_);
v___x_1122_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1088_, v_e_1083_, v_a_1085_, v_a_1086_, v_a_1087_);
return v___x_1122_;
}
case 3:
{
lean_object* v___x_1123_; 
lean_dec(v_offset_1084_);
v___x_1123_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1088_, v_e_1083_, v_a_1085_, v_a_1086_, v_a_1087_);
return v___x_1123_;
}
default: 
{
lean_object* v___x_1124_; lean_object* v_fst_1125_; lean_object* v_snd_1126_; lean_object* v_fst_1127_; lean_object* v_snd_1128_; lean_object* v___x_1129_; 
v___x_1124_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0(v_n_1080_, v_beginIdx_1081_, v_subst_1082_, v_e_1083_, v_offset_1084_, v_a_1085_, v_a_1086_, v_a_1087_);
v_fst_1125_ = lean_ctor_get(v___x_1124_, 0);
lean_inc(v_fst_1125_);
v_snd_1126_ = lean_ctor_get(v___x_1124_, 1);
lean_inc(v_snd_1126_);
lean_dec_ref(v___x_1124_);
v_fst_1127_ = lean_ctor_get(v_fst_1125_, 0);
lean_inc(v_fst_1127_);
v_snd_1128_ = lean_ctor_get(v_fst_1125_, 1);
lean_inc(v_snd_1128_);
lean_dec(v_fst_1125_);
v___x_1129_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1088_, v_fst_1127_, v_snd_1128_, v_a_1086_, v_snd_1126_);
return v___x_1129_;
}
}
}
else
{
lean_object* v___x_1130_; 
lean_dec(v_offset_1084_);
v___x_1130_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1088_, v_e_1083_, v_a_1085_, v_a_1086_, v_a_1087_);
return v___x_1130_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0___boxed(lean_object* v_n_1131_, lean_object* v_beginIdx_1132_, lean_object* v_subst_1133_, lean_object* v_e_1134_, lean_object* v_offset_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_){
_start:
{
uint8_t v_a_3619__boxed_1139_; lean_object* v_res_1140_; 
v_a_3619__boxed_1139_ = lean_unbox(v_a_1137_);
v_res_1140_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1131_, v_beginIdx_1132_, v_subst_1133_, v_e_1134_, v_offset_1135_, v_a_1136_, v_a_3619__boxed_1139_, v_a_1138_);
lean_dec_ref(v_subst_1133_);
lean_dec(v_beginIdx_1132_);
lean_dec(v_n_1131_);
return v_res_1140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0___boxed(lean_object* v_n_1141_, lean_object* v_beginIdx_1142_, lean_object* v_subst_1143_, lean_object* v_e_1144_, lean_object* v_offset_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_){
_start:
{
uint8_t v_a_3676__boxed_1149_; lean_object* v_res_1150_; 
v_a_3676__boxed_1149_ = lean_unbox(v_a_1147_);
v_res_1150_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0(v_n_1141_, v_beginIdx_1142_, v_subst_1143_, v_e_1144_, v_offset_1145_, v_a_1146_, v_a_3676__boxed_1149_, v_a_1148_);
lean_dec_ref(v_subst_1143_);
lean_dec(v_beginIdx_1142_);
lean_dec(v_n_1141_);
return v_res_1150_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__1(void){
_start:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1152_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__2));
v___x_1153_ = lean_unsigned_to_nat(34u);
v___x_1154_ = lean_unsigned_to_nat(57u);
v___x_1155_ = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__0));
v___x_1156_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__3));
v___x_1157_ = l_mkPanicMessageWithDecl(v___x_1156_, v___x_1155_, v___x_1154_, v___x_1153_, v___x_1152_);
return v___x_1157_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__2(void){
_start:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1158_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__2));
v___x_1159_ = lean_unsigned_to_nat(32u);
v___x_1160_ = lean_unsigned_to_nat(56u);
v___x_1161_ = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__0));
v___x_1162_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__3));
v___x_1163_ = l_mkPanicMessageWithDecl(v___x_1162_, v___x_1161_, v___x_1160_, v___x_1159_, v___x_1158_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27(lean_object* v_e_1164_, lean_object* v_beginIdx_1165_, lean_object* v_endIdx_1166_, lean_object* v_subst_1167_, uint8_t v_a_1168_, lean_object* v_a_1169_){
_start:
{
uint8_t v___x_1170_; 
v___x_1170_ = lean_nat_dec_lt(v_endIdx_1166_, v_beginIdx_1165_);
if (v___x_1170_ == 0)
{
lean_object* v___x_1171_; uint8_t v___x_1172_; 
v___x_1171_ = lean_array_get_size(v_subst_1167_);
v___x_1172_ = lean_nat_dec_lt(v___x_1171_, v_endIdx_1166_);
if (v___x_1172_ == 0)
{
lean_object* v_n_1173_; lean_object* v___x_1174_; 
v_n_1173_ = lean_nat_sub(v_endIdx_1166_, v_beginIdx_1165_);
v___x_1174_ = lean_unsigned_to_nat(0u);
switch(lean_obj_tag(v_e_1164_))
{
case 0:
{
lean_object* v_deBruijnIndex_1175_; uint8_t v___x_1176_; 
v_deBruijnIndex_1175_ = lean_ctor_get(v_e_1164_, 0);
v___x_1176_ = lean_nat_dec_le(v___x_1174_, v_deBruijnIndex_1175_);
if (v___x_1176_ == 0)
{
lean_object* v___x_1177_; 
lean_dec(v_n_1173_);
v___x_1177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1177_, 0, v_e_1164_);
lean_ctor_set(v___x_1177_, 1, v_a_1169_);
return v___x_1177_;
}
else
{
uint8_t v___x_1178_; 
lean_inc(v_deBruijnIndex_1175_);
lean_dec_ref(v_e_1164_);
v___x_1178_ = lean_nat_dec_lt(v_deBruijnIndex_1175_, v_n_1173_);
if (v___x_1178_ == 0)
{
lean_object* v___x_1179_; lean_object* v___x_1180_; 
v___x_1179_ = lean_nat_sub(v_deBruijnIndex_1175_, v_n_1173_);
lean_dec(v_n_1173_);
lean_dec(v_deBruijnIndex_1175_);
v___x_1180_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___redArg(v___x_1179_, v_a_1169_);
return v___x_1180_;
}
else
{
lean_object* v___x_1181_; lean_object* v_v_1182_; lean_object* v___x_1183_; 
lean_dec(v_n_1173_);
v___x_1181_ = lean_nat_add(v_beginIdx_1165_, v_deBruijnIndex_1175_);
lean_dec(v_deBruijnIndex_1175_);
v_v_1182_ = lean_array_fget_borrowed(v_subst_1167_, v___x_1181_);
lean_dec(v___x_1181_);
lean_inc(v_v_1182_);
v___x_1183_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(v_v_1182_, v___x_1174_, v___x_1174_, v_a_1168_, v_a_1169_);
return v___x_1183_;
}
}
}
case 9:
{
lean_object* v___x_1184_; 
lean_dec(v_n_1173_);
v___x_1184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1184_, 0, v_e_1164_);
lean_ctor_set(v___x_1184_, 1, v_a_1169_);
return v___x_1184_;
}
case 2:
{
lean_object* v___x_1185_; 
lean_dec(v_n_1173_);
v___x_1185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1185_, 0, v_e_1164_);
lean_ctor_set(v___x_1185_, 1, v_a_1169_);
return v___x_1185_;
}
case 1:
{
lean_object* v___x_1186_; 
lean_dec(v_n_1173_);
v___x_1186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1186_, 0, v_e_1164_);
lean_ctor_set(v___x_1186_, 1, v_a_1169_);
return v___x_1186_;
}
case 4:
{
lean_object* v___x_1187_; 
lean_dec(v_n_1173_);
v___x_1187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1187_, 0, v_e_1164_);
lean_ctor_set(v___x_1187_, 1, v_a_1169_);
return v___x_1187_;
}
case 3:
{
lean_object* v___x_1188_; 
lean_dec(v_n_1173_);
v___x_1188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1188_, 0, v_e_1164_);
lean_ctor_set(v___x_1188_, 1, v_a_1169_);
return v___x_1188_;
}
default: 
{
lean_object* v___x_1189_; uint8_t v___x_1190_; 
v___x_1189_ = l_Lean_Expr_looseBVarRange(v_e_1164_);
v___x_1190_ = lean_nat_dec_le(v___x_1189_, v___x_1174_);
lean_dec(v___x_1189_);
if (v___x_1190_ == 0)
{
switch(lean_obj_tag(v_e_1164_))
{
case 9:
{
lean_object* v___x_1191_; 
lean_dec(v_n_1173_);
v___x_1191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1191_, 0, v_e_1164_);
lean_ctor_set(v___x_1191_, 1, v_a_1169_);
return v___x_1191_;
}
case 2:
{
lean_object* v___x_1192_; 
lean_dec(v_n_1173_);
v___x_1192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1192_, 0, v_e_1164_);
lean_ctor_set(v___x_1192_, 1, v_a_1169_);
return v___x_1192_;
}
case 0:
{
lean_object* v___x_1193_; 
lean_dec(v_n_1173_);
v___x_1193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1193_, 0, v_e_1164_);
lean_ctor_set(v___x_1193_, 1, v_a_1169_);
return v___x_1193_;
}
case 1:
{
lean_object* v___x_1194_; 
lean_dec(v_n_1173_);
v___x_1194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1194_, 0, v_e_1164_);
lean_ctor_set(v___x_1194_, 1, v_a_1169_);
return v___x_1194_;
}
case 4:
{
lean_object* v___x_1195_; 
lean_dec(v_n_1173_);
v___x_1195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1195_, 0, v_e_1164_);
lean_ctor_set(v___x_1195_, 1, v_a_1169_);
return v___x_1195_;
}
case 3:
{
lean_object* v___x_1196_; 
lean_dec(v_n_1173_);
v___x_1196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1196_, 0, v_e_1164_);
lean_ctor_set(v___x_1196_, 1, v_a_1169_);
return v___x_1196_;
}
default: 
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v_fst_1199_; lean_object* v_snd_1200_; lean_object* v_fst_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1208_; 
v___x_1197_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__2, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__2_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__2);
v___x_1198_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0(v_n_1173_, v_beginIdx_1165_, v_subst_1167_, v_e_1164_, v___x_1174_, v___x_1197_, v_a_1168_, v_a_1169_);
lean_dec(v_n_1173_);
v_fst_1199_ = lean_ctor_get(v___x_1198_, 0);
lean_inc(v_fst_1199_);
v_snd_1200_ = lean_ctor_get(v___x_1198_, 1);
lean_inc(v_snd_1200_);
lean_dec_ref(v___x_1198_);
v_fst_1201_ = lean_ctor_get(v_fst_1199_, 0);
v_isSharedCheck_1208_ = !lean_is_exclusive(v_fst_1199_);
if (v_isSharedCheck_1208_ == 0)
{
lean_object* v_unused_1209_; 
v_unused_1209_ = lean_ctor_get(v_fst_1199_, 1);
lean_dec(v_unused_1209_);
v___x_1203_ = v_fst_1199_;
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_fst_1201_);
lean_dec(v_fst_1199_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1206_; 
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 1, v_snd_1200_);
v___x_1206_ = v___x_1203_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_fst_1201_);
lean_ctor_set(v_reuseFailAlloc_1207_, 1, v_snd_1200_);
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
else
{
lean_object* v___x_1210_; 
lean_dec(v_n_1173_);
v___x_1210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1210_, 0, v_e_1164_);
lean_ctor_set(v___x_1210_, 1, v_a_1169_);
return v___x_1210_;
}
}
}
}
else
{
lean_object* v___x_1211_; lean_object* v___x_1212_; 
lean_dec_ref(v_e_1164_);
v___x_1211_ = lean_obj_once(&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__1, &l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__1_once, _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__1);
v___x_1212_ = l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1(v___x_1211_, v_a_1168_, v_a_1169_);
return v___x_1212_;
}
}
else
{
lean_object* v___x_1213_; lean_object* v___x_1214_; 
lean_dec_ref(v_e_1164_);
v___x_1213_ = lean_obj_once(&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__2, &l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__2_once, _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__2);
v___x_1214_ = l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1(v___x_1213_, v_a_1168_, v_a_1169_);
return v___x_1214_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___boxed(lean_object* v_e_1215_, lean_object* v_beginIdx_1216_, lean_object* v_endIdx_1217_, lean_object* v_subst_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_){
_start:
{
uint8_t v_a_4159__boxed_1221_; lean_object* v_res_1222_; 
v_a_4159__boxed_1221_ = lean_unbox(v_a_1219_);
v_res_1222_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27(v_e_1215_, v_beginIdx_1216_, v_endIdx_1217_, v_subst_1218_, v_a_4159__boxed_1221_, v_a_1220_);
lean_dec_ref(v_subst_1218_);
lean_dec(v_endIdx_1217_);
lean_dec(v_beginIdx_1216_);
return v_res_1222_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27(lean_object* v_e_1223_, lean_object* v_subst_1224_, uint8_t v_a_1225_, lean_object* v_a_1226_){
_start:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1227_ = lean_unsigned_to_nat(0u);
v___x_1228_ = lean_array_get_size(v_subst_1224_);
v___x_1229_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27(v_e_1223_, v___x_1227_, v___x_1228_, v_subst_1224_, v_a_1225_, v_a_1226_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27___boxed(lean_object* v_e_1230_, lean_object* v_subst_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_){
_start:
{
uint8_t v_a_10__boxed_1234_; lean_object* v_res_1235_; 
v_a_10__boxed_1234_ = lean_unbox(v_a_1232_);
v_res_1235_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27(v_e_1230_, v_subst_1231_, v_a_10__boxed_1234_, v_a_1233_);
lean_dec_ref(v_subst_1231_);
return v_res_1235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateS___redArg(lean_object* v_e_1236_, lean_object* v_subst_1237_, lean_object* v_a_1238_){
_start:
{
lean_object* v___x_1240_; lean_object* v_share_1241_; lean_object* v_maxFVar_1242_; lean_object* v_proofInstInfo_1243_; lean_object* v_inferType_1244_; lean_object* v_getLevel_1245_; lean_object* v_congrInfo_1246_; lean_object* v_defEqI_1247_; uint8_t v_debug_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1280_; 
v___x_1240_ = lean_st_ref_take(v_a_1238_);
v_share_1241_ = lean_ctor_get(v___x_1240_, 0);
v_maxFVar_1242_ = lean_ctor_get(v___x_1240_, 1);
v_proofInstInfo_1243_ = lean_ctor_get(v___x_1240_, 2);
v_inferType_1244_ = lean_ctor_get(v___x_1240_, 3);
v_getLevel_1245_ = lean_ctor_get(v___x_1240_, 4);
v_congrInfo_1246_ = lean_ctor_get(v___x_1240_, 5);
v_defEqI_1247_ = lean_ctor_get(v___x_1240_, 6);
v_debug_1248_ = lean_ctor_get_uint8(v___x_1240_, sizeof(void*)*7);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1250_ = v___x_1240_;
v_isShared_1251_ = v_isSharedCheck_1280_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_defEqI_1247_);
lean_inc(v_congrInfo_1246_);
lean_inc(v_getLevel_1245_);
lean_inc(v_inferType_1244_);
lean_inc(v_proofInstInfo_1243_);
lean_inc(v_maxFVar_1242_);
lean_inc(v_share_1241_);
lean_dec(v___x_1240_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1280_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1252_; lean_object* v___x_1254_; 
v___x_1252_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__0, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__0_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__0);
if (v_isShared_1251_ == 0)
{
lean_ctor_set(v___x_1250_, 0, v___x_1252_);
v___x_1254_ = v___x_1250_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v___x_1252_);
lean_ctor_set(v_reuseFailAlloc_1279_, 1, v_maxFVar_1242_);
lean_ctor_set(v_reuseFailAlloc_1279_, 2, v_proofInstInfo_1243_);
lean_ctor_set(v_reuseFailAlloc_1279_, 3, v_inferType_1244_);
lean_ctor_set(v_reuseFailAlloc_1279_, 4, v_getLevel_1245_);
lean_ctor_set(v_reuseFailAlloc_1279_, 5, v_congrInfo_1246_);
lean_ctor_set(v_reuseFailAlloc_1279_, 6, v_defEqI_1247_);
lean_ctor_set_uint8(v_reuseFailAlloc_1279_, sizeof(void*)*7, v_debug_1248_);
v___x_1254_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; uint8_t v_debug_1257_; lean_object* v___x_1258_; lean_object* v_fst_1259_; lean_object* v_snd_1260_; lean_object* v___x_1261_; lean_object* v_maxFVar_1262_; lean_object* v_proofInstInfo_1263_; lean_object* v_inferType_1264_; lean_object* v_getLevel_1265_; lean_object* v_congrInfo_1266_; lean_object* v_defEqI_1267_; uint8_t v_debug_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1277_; 
v___x_1255_ = lean_st_ref_set(v_a_1238_, v___x_1254_);
v___x_1256_ = lean_st_ref_get(v_a_1238_);
v_debug_1257_ = lean_ctor_get_uint8(v___x_1256_, sizeof(void*)*7);
lean_dec(v___x_1256_);
v___x_1258_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27(v_e_1236_, v_subst_1237_, v_debug_1257_, v_share_1241_);
v_fst_1259_ = lean_ctor_get(v___x_1258_, 0);
lean_inc(v_fst_1259_);
v_snd_1260_ = lean_ctor_get(v___x_1258_, 1);
lean_inc(v_snd_1260_);
lean_dec_ref(v___x_1258_);
v___x_1261_ = lean_st_ref_take(v_a_1238_);
v_maxFVar_1262_ = lean_ctor_get(v___x_1261_, 1);
v_proofInstInfo_1263_ = lean_ctor_get(v___x_1261_, 2);
v_inferType_1264_ = lean_ctor_get(v___x_1261_, 3);
v_getLevel_1265_ = lean_ctor_get(v___x_1261_, 4);
v_congrInfo_1266_ = lean_ctor_get(v___x_1261_, 5);
v_defEqI_1267_ = lean_ctor_get(v___x_1261_, 6);
v_debug_1268_ = lean_ctor_get_uint8(v___x_1261_, sizeof(void*)*7);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1277_ == 0)
{
lean_object* v_unused_1278_; 
v_unused_1278_ = lean_ctor_get(v___x_1261_, 0);
lean_dec(v_unused_1278_);
v___x_1270_ = v___x_1261_;
v_isShared_1271_ = v_isSharedCheck_1277_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_defEqI_1267_);
lean_inc(v_congrInfo_1266_);
lean_inc(v_getLevel_1265_);
lean_inc(v_inferType_1264_);
lean_inc(v_proofInstInfo_1263_);
lean_inc(v_maxFVar_1262_);
lean_dec(v___x_1261_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1277_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1273_; 
if (v_isShared_1271_ == 0)
{
lean_ctor_set(v___x_1270_, 0, v_snd_1260_);
v___x_1273_ = v___x_1270_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_snd_1260_);
lean_ctor_set(v_reuseFailAlloc_1276_, 1, v_maxFVar_1262_);
lean_ctor_set(v_reuseFailAlloc_1276_, 2, v_proofInstInfo_1263_);
lean_ctor_set(v_reuseFailAlloc_1276_, 3, v_inferType_1264_);
lean_ctor_set(v_reuseFailAlloc_1276_, 4, v_getLevel_1265_);
lean_ctor_set(v_reuseFailAlloc_1276_, 5, v_congrInfo_1266_);
lean_ctor_set(v_reuseFailAlloc_1276_, 6, v_defEqI_1267_);
lean_ctor_set_uint8(v_reuseFailAlloc_1276_, sizeof(void*)*7, v_debug_1268_);
v___x_1273_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1274_ = lean_st_ref_set(v_a_1238_, v___x_1273_);
v___x_1275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1275_, 0, v_fst_1259_);
return v___x_1275_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateS___redArg___boxed(lean_object* v_e_1281_, lean_object* v_subst_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_){
_start:
{
lean_object* v_res_1285_; 
v_res_1285_ = l_Lean_Meta_Sym_instantiateS___redArg(v_e_1281_, v_subst_1282_, v_a_1283_);
lean_dec(v_a_1283_);
lean_dec_ref(v_subst_1282_);
return v_res_1285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateS(lean_object* v_e_1286_, lean_object* v_subst_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_){
_start:
{
lean_object* v___x_1295_; 
v___x_1295_ = l_Lean_Meta_Sym_instantiateS___redArg(v_e_1286_, v_subst_1287_, v_a_1289_);
return v___x_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateS___boxed(lean_object* v_e_1296_, lean_object* v_subst_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_){
_start:
{
lean_object* v_res_1305_; 
v_res_1305_ = l_Lean_Meta_Sym_instantiateS(v_e_1296_, v_subst_1297_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_);
lean_dec(v_a_1303_);
lean_dec_ref(v_a_1302_);
lean_dec(v_a_1301_);
lean_dec_ref(v_a_1300_);
lean_dec(v_a_1299_);
lean_dec_ref(v_a_1298_);
lean_dec_ref(v_subst_1297_);
return v_res_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS_loop_spec__0(lean_object* v_f_1306_, lean_object* v_a_1307_, uint8_t v___y_1308_, lean_object* v___y_1309_){
_start:
{
lean_object* v___y_1311_; 
if (v___y_1308_ == 0)
{
v___y_1311_ = v___y_1309_;
goto v___jp_1310_;
}
else
{
lean_object* v___x_1314_; lean_object* v_snd_1315_; lean_object* v___x_1316_; lean_object* v_snd_1317_; 
lean_inc_ref(v_f_1306_);
v___x_1314_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_f_1306_, v___y_1308_, v___y_1309_);
v_snd_1315_ = lean_ctor_get(v___x_1314_, 1);
lean_inc(v_snd_1315_);
lean_dec_ref(v___x_1314_);
lean_inc_ref(v_a_1307_);
v___x_1316_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_a_1307_, v___y_1308_, v_snd_1315_);
v_snd_1317_ = lean_ctor_get(v___x_1316_, 1);
lean_inc(v_snd_1317_);
lean_dec_ref(v___x_1316_);
v___y_1311_ = v_snd_1317_;
goto v___jp_1310_;
}
v___jp_1310_:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1312_ = l_Lean_Expr_app___override(v_f_1306_, v_a_1307_);
v___x_1313_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1312_, v___y_1311_);
return v___x_1313_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS_loop_spec__0___boxed(lean_object* v_f_1318_, lean_object* v_a_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_){
_start:
{
uint8_t v___y_1245__boxed_1322_; lean_object* v_res_1323_; 
v___y_1245__boxed_1322_ = lean_unbox(v___y_1320_);
v_res_1323_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS_loop_spec__0(v_f_1318_, v_a_1319_, v___y_1245__boxed_1322_, v___y_1321_);
return v_res_1323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS_loop(lean_object* v_revArgs_1324_, lean_object* v_start_1325_, lean_object* v_b_1326_, lean_object* v_i_1327_, uint8_t v_a_1328_, lean_object* v_a_1329_){
_start:
{
uint8_t v___x_1330_; 
v___x_1330_ = lean_nat_dec_le(v_i_1327_, v_start_1325_);
if (v___x_1330_ == 0)
{
lean_object* v___x_1331_; lean_object* v_i_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v_fst_1336_; lean_object* v_snd_1337_; 
v___x_1331_ = lean_unsigned_to_nat(1u);
v_i_1332_ = lean_nat_sub(v_i_1327_, v___x_1331_);
lean_dec(v_i_1327_);
v___x_1333_ = l_Lean_instInhabitedExpr;
v___x_1334_ = lean_array_get_borrowed(v___x_1333_, v_revArgs_1324_, v_i_1332_);
lean_inc(v___x_1334_);
v___x_1335_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS_loop_spec__0(v_b_1326_, v___x_1334_, v_a_1328_, v_a_1329_);
v_fst_1336_ = lean_ctor_get(v___x_1335_, 0);
lean_inc(v_fst_1336_);
v_snd_1337_ = lean_ctor_get(v___x_1335_, 1);
lean_inc(v_snd_1337_);
lean_dec_ref(v___x_1335_);
v_b_1326_ = v_fst_1336_;
v_i_1327_ = v_i_1332_;
v_a_1329_ = v_snd_1337_;
goto _start;
}
else
{
lean_object* v___x_1339_; 
lean_dec(v_i_1327_);
v___x_1339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1339_, 0, v_b_1326_);
lean_ctor_set(v___x_1339_, 1, v_a_1329_);
return v___x_1339_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS_loop___boxed(lean_object* v_revArgs_1340_, lean_object* v_start_1341_, lean_object* v_b_1342_, lean_object* v_i_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_){
_start:
{
uint8_t v_a_1269__boxed_1346_; lean_object* v_res_1347_; 
v_a_1269__boxed_1346_ = lean_unbox(v_a_1344_);
v_res_1347_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS_loop(v_revArgs_1340_, v_start_1341_, v_b_1342_, v_i_1343_, v_a_1269__boxed_1346_, v_a_1345_);
lean_dec(v_start_1341_);
lean_dec_ref(v_revArgs_1340_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS(lean_object* v_f_1348_, lean_object* v_beginIdx_1349_, lean_object* v_endIdx_1350_, lean_object* v_revArgs_1351_, uint8_t v_a_1352_, lean_object* v_a_1353_){
_start:
{
lean_object* v___x_1354_; 
v___x_1354_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS_loop(v_revArgs_1351_, v_beginIdx_1349_, v_f_1348_, v_endIdx_1350_, v_a_1352_, v_a_1353_);
return v___x_1354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS___boxed(lean_object* v_f_1355_, lean_object* v_beginIdx_1356_, lean_object* v_endIdx_1357_, lean_object* v_revArgs_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_){
_start:
{
uint8_t v_a_5__boxed_1361_; lean_object* v_res_1362_; 
v_a_5__boxed_1361_ = lean_unbox(v_a_1359_);
v_res_1362_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS(v_f_1355_, v_beginIdx_1356_, v_endIdx_1357_, v_revArgs_1358_, v_a_5__boxed_1361_, v_a_1360_);
lean_dec_ref(v_revArgs_1358_);
lean_dec(v_beginIdx_1356_);
return v_res_1362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_go(lean_object* v_revArgs_1363_, lean_object* v_sz_1364_, lean_object* v_e_1365_, lean_object* v_i_1366_, uint8_t v_a_1367_, lean_object* v_a_1368_){
_start:
{
switch(lean_obj_tag(v_e_1365_))
{
case 6:
{
lean_object* v_body_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; uint8_t v___x_1372_; 
v_body_1369_ = lean_ctor_get(v_e_1365_, 2);
lean_inc_ref(v_body_1369_);
lean_dec_ref(v_e_1365_);
v___x_1370_ = lean_unsigned_to_nat(1u);
v___x_1371_ = lean_nat_add(v_i_1366_, v___x_1370_);
lean_dec(v_i_1366_);
v___x_1372_ = lean_nat_dec_lt(v___x_1371_, v_sz_1364_);
if (v___x_1372_ == 0)
{
lean_object* v___x_1373_; 
lean_dec(v___x_1371_);
v___x_1373_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27(v_body_1369_, v_revArgs_1363_, v_a_1367_, v_a_1368_);
return v___x_1373_;
}
else
{
v_e_1365_ = v_body_1369_;
v_i_1366_ = v___x_1371_;
goto _start;
}
}
case 10:
{
lean_object* v_expr_1375_; 
v_expr_1375_ = lean_ctor_get(v_e_1365_, 1);
lean_inc_ref(v_expr_1375_);
lean_dec_ref(v_e_1365_);
v_e_1365_ = v_expr_1375_;
goto _start;
}
default: 
{
lean_object* v_n_1377_; lean_object* v___x_1378_; lean_object* v_fst_1379_; lean_object* v_snd_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
v_n_1377_ = lean_nat_sub(v_sz_1364_, v_i_1366_);
lean_dec(v_i_1366_);
v___x_1378_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27(v_e_1365_, v_n_1377_, v_sz_1364_, v_revArgs_1363_, v_a_1367_, v_a_1368_);
v_fst_1379_ = lean_ctor_get(v___x_1378_, 0);
lean_inc(v_fst_1379_);
v_snd_1380_ = lean_ctor_get(v___x_1378_, 1);
lean_inc(v_snd_1380_);
lean_dec_ref(v___x_1378_);
v___x_1381_ = lean_unsigned_to_nat(0u);
v___x_1382_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS_loop(v_revArgs_1363_, v___x_1381_, v_fst_1379_, v_n_1377_, v_a_1367_, v_snd_1380_);
return v___x_1382_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_go___boxed(lean_object* v_revArgs_1383_, lean_object* v_sz_1384_, lean_object* v_e_1385_, lean_object* v_i_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_){
_start:
{
uint8_t v_a_384__boxed_1389_; lean_object* v_res_1390_; 
v_a_384__boxed_1389_ = lean_unbox(v_a_1387_);
v_res_1390_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_go(v_revArgs_1383_, v_sz_1384_, v_e_1385_, v_i_1386_, v_a_384__boxed_1389_, v_a_1388_);
lean_dec(v_sz_1384_);
lean_dec_ref(v_revArgs_1383_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS(lean_object* v_f_1391_, lean_object* v_revArgs_1392_, uint8_t v_a_1393_, lean_object* v_a_1394_){
_start:
{
lean_object* v_sz_1395_; lean_object* v___x_1396_; uint8_t v___x_1397_; 
v_sz_1395_ = lean_array_get_size(v_revArgs_1392_);
v___x_1396_ = lean_unsigned_to_nat(0u);
v___x_1397_ = lean_nat_dec_eq(v_sz_1395_, v___x_1396_);
if (v___x_1397_ == 0)
{
lean_object* v___x_1398_; 
v___x_1398_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_go(v_revArgs_1392_, v_sz_1395_, v_f_1391_, v___x_1396_, v_a_1393_, v_a_1394_);
return v___x_1398_;
}
else
{
lean_object* v___x_1399_; 
v___x_1399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1399_, 0, v_f_1391_);
lean_ctor_set(v___x_1399_, 1, v_a_1394_);
return v___x_1399_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS___boxed(lean_object* v_f_1400_, lean_object* v_revArgs_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_){
_start:
{
uint8_t v_a_251__boxed_1404_; lean_object* v_res_1405_; 
v_a_251__boxed_1404_ = lean_unbox(v_a_1402_);
v_res_1405_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS(v_f_1400_, v_revArgs_1401_, v_a_251__boxed_1404_, v_a_1403_);
lean_dec_ref(v_revArgs_1401_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_1406_, lean_object* v_x_1407_){
_start:
{
if (lean_obj_tag(v_x_1407_) == 0)
{
return v_x_1406_;
}
else
{
lean_object* v_key_1408_; lean_object* v_value_1409_; lean_object* v_tail_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1437_; 
v_key_1408_ = lean_ctor_get(v_x_1407_, 0);
v_value_1409_ = lean_ctor_get(v_x_1407_, 1);
v_tail_1410_ = lean_ctor_get(v_x_1407_, 2);
v_isSharedCheck_1437_ = !lean_is_exclusive(v_x_1407_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1412_ = v_x_1407_;
v_isShared_1413_ = v_isSharedCheck_1437_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_tail_1410_);
lean_inc(v_value_1409_);
lean_inc(v_key_1408_);
lean_dec(v_x_1407_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1437_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v_fst_1414_; lean_object* v_snd_1415_; lean_object* v___x_1416_; uint64_t v___x_1417_; uint64_t v___x_1418_; uint64_t v___x_1419_; uint64_t v___x_1420_; uint64_t v___x_1421_; uint64_t v_fold_1422_; uint64_t v___x_1423_; uint64_t v___x_1424_; uint64_t v___x_1425_; size_t v___x_1426_; size_t v___x_1427_; size_t v___x_1428_; size_t v___x_1429_; size_t v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1433_; 
v_fst_1414_ = lean_ctor_get(v_key_1408_, 0);
v_snd_1415_ = lean_ctor_get(v_key_1408_, 1);
v___x_1416_ = lean_array_get_size(v_x_1406_);
v___x_1417_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_1414_);
v___x_1418_ = lean_uint64_of_nat(v_snd_1415_);
v___x_1419_ = lean_uint64_mix_hash(v___x_1417_, v___x_1418_);
v___x_1420_ = 32ULL;
v___x_1421_ = lean_uint64_shift_right(v___x_1419_, v___x_1420_);
v_fold_1422_ = lean_uint64_xor(v___x_1419_, v___x_1421_);
v___x_1423_ = 16ULL;
v___x_1424_ = lean_uint64_shift_right(v_fold_1422_, v___x_1423_);
v___x_1425_ = lean_uint64_xor(v_fold_1422_, v___x_1424_);
v___x_1426_ = lean_uint64_to_usize(v___x_1425_);
v___x_1427_ = lean_usize_of_nat(v___x_1416_);
v___x_1428_ = ((size_t)1ULL);
v___x_1429_ = lean_usize_sub(v___x_1427_, v___x_1428_);
v___x_1430_ = lean_usize_land(v___x_1426_, v___x_1429_);
v___x_1431_ = lean_array_uget_borrowed(v_x_1406_, v___x_1430_);
lean_inc(v___x_1431_);
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 2, v___x_1431_);
v___x_1433_ = v___x_1412_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_key_1408_);
lean_ctor_set(v_reuseFailAlloc_1436_, 1, v_value_1409_);
lean_ctor_set(v_reuseFailAlloc_1436_, 2, v___x_1431_);
v___x_1433_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
lean_object* v___x_1434_; 
v___x_1434_ = lean_array_uset(v_x_1406_, v___x_1430_, v___x_1433_);
v_x_1406_ = v___x_1434_;
v_x_1407_ = v_tail_1410_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2___redArg(lean_object* v_i_1438_, lean_object* v_source_1439_, lean_object* v_target_1440_){
_start:
{
lean_object* v___x_1441_; uint8_t v___x_1442_; 
v___x_1441_ = lean_array_get_size(v_source_1439_);
v___x_1442_ = lean_nat_dec_lt(v_i_1438_, v___x_1441_);
if (v___x_1442_ == 0)
{
lean_dec_ref(v_source_1439_);
lean_dec(v_i_1438_);
return v_target_1440_;
}
else
{
lean_object* v_es_1443_; lean_object* v___x_1444_; lean_object* v_source_1445_; lean_object* v_target_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; 
v_es_1443_ = lean_array_fget(v_source_1439_, v_i_1438_);
v___x_1444_ = lean_box(0);
v_source_1445_ = lean_array_fset(v_source_1439_, v_i_1438_, v___x_1444_);
v_target_1446_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3___redArg(v_target_1440_, v_es_1443_);
v___x_1447_ = lean_unsigned_to_nat(1u);
v___x_1448_ = lean_nat_add(v_i_1438_, v___x_1447_);
lean_dec(v_i_1438_);
v_i_1438_ = v___x_1448_;
v_source_1439_ = v_source_1445_;
v_target_1440_ = v_target_1446_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1___redArg(lean_object* v_data_1450_){
_start:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v_nbuckets_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1451_ = lean_array_get_size(v_data_1450_);
v___x_1452_ = lean_unsigned_to_nat(2u);
v_nbuckets_1453_ = lean_nat_mul(v___x_1451_, v___x_1452_);
v___x_1454_ = lean_unsigned_to_nat(0u);
v___x_1455_ = lean_box(0);
v___x_1456_ = lean_mk_array(v_nbuckets_1453_, v___x_1455_);
v___x_1457_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2___redArg(v___x_1454_, v_data_1450_, v___x_1456_);
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(lean_object* v_a_1458_, lean_object* v_b_1459_, lean_object* v_x_1460_){
_start:
{
if (lean_obj_tag(v_x_1460_) == 0)
{
lean_dec(v_b_1459_);
lean_dec_ref(v_a_1458_);
return v_x_1460_;
}
else
{
lean_object* v_key_1461_; lean_object* v_value_1462_; lean_object* v_tail_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1482_; 
v_key_1461_ = lean_ctor_get(v_x_1460_, 0);
v_value_1462_ = lean_ctor_get(v_x_1460_, 1);
v_tail_1463_ = lean_ctor_get(v_x_1460_, 2);
v_isSharedCheck_1482_ = !lean_is_exclusive(v_x_1460_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1465_ = v_x_1460_;
v_isShared_1466_ = v_isSharedCheck_1482_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_tail_1463_);
lean_inc(v_value_1462_);
lean_inc(v_key_1461_);
lean_dec(v_x_1460_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1482_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
uint8_t v___y_1468_; lean_object* v_fst_1476_; lean_object* v_snd_1477_; lean_object* v_fst_1478_; lean_object* v_snd_1479_; uint8_t v___x_1480_; 
v_fst_1476_ = lean_ctor_get(v_key_1461_, 0);
v_snd_1477_ = lean_ctor_get(v_key_1461_, 1);
v_fst_1478_ = lean_ctor_get(v_a_1458_, 0);
v_snd_1479_ = lean_ctor_get(v_a_1458_, 1);
v___x_1480_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_1476_, v_fst_1478_);
if (v___x_1480_ == 0)
{
v___y_1468_ = v___x_1480_;
goto v___jp_1467_;
}
else
{
uint8_t v___x_1481_; 
v___x_1481_ = lean_nat_dec_eq(v_snd_1477_, v_snd_1479_);
v___y_1468_ = v___x_1481_;
goto v___jp_1467_;
}
v___jp_1467_:
{
if (v___y_1468_ == 0)
{
lean_object* v___x_1469_; lean_object* v___x_1471_; 
v___x_1469_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(v_a_1458_, v_b_1459_, v_tail_1463_);
if (v_isShared_1466_ == 0)
{
lean_ctor_set(v___x_1465_, 2, v___x_1469_);
v___x_1471_ = v___x_1465_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v_key_1461_);
lean_ctor_set(v_reuseFailAlloc_1472_, 1, v_value_1462_);
lean_ctor_set(v_reuseFailAlloc_1472_, 2, v___x_1469_);
v___x_1471_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
return v___x_1471_;
}
}
else
{
lean_object* v___x_1474_; 
lean_dec(v_value_1462_);
lean_dec(v_key_1461_);
if (v_isShared_1466_ == 0)
{
lean_ctor_set(v___x_1465_, 1, v_b_1459_);
lean_ctor_set(v___x_1465_, 0, v_a_1458_);
v___x_1474_ = v___x_1465_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_a_1458_);
lean_ctor_set(v_reuseFailAlloc_1475_, 1, v_b_1459_);
lean_ctor_set(v_reuseFailAlloc_1475_, 2, v_tail_1463_);
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
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(lean_object* v_a_1483_, lean_object* v_x_1484_){
_start:
{
if (lean_obj_tag(v_x_1484_) == 0)
{
uint8_t v___x_1485_; 
v___x_1485_ = 0;
return v___x_1485_;
}
else
{
lean_object* v_key_1486_; lean_object* v_tail_1487_; uint8_t v___y_1489_; lean_object* v_fst_1491_; lean_object* v_snd_1492_; lean_object* v_fst_1493_; lean_object* v_snd_1494_; uint8_t v___x_1495_; 
v_key_1486_ = lean_ctor_get(v_x_1484_, 0);
v_tail_1487_ = lean_ctor_get(v_x_1484_, 2);
v_fst_1491_ = lean_ctor_get(v_key_1486_, 0);
v_snd_1492_ = lean_ctor_get(v_key_1486_, 1);
v_fst_1493_ = lean_ctor_get(v_a_1483_, 0);
v_snd_1494_ = lean_ctor_get(v_a_1483_, 1);
v___x_1495_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_1491_, v_fst_1493_);
if (v___x_1495_ == 0)
{
v___y_1489_ = v___x_1495_;
goto v___jp_1488_;
}
else
{
uint8_t v___x_1496_; 
v___x_1496_ = lean_nat_dec_eq(v_snd_1492_, v_snd_1494_);
v___y_1489_ = v___x_1496_;
goto v___jp_1488_;
}
v___jp_1488_:
{
if (v___y_1489_ == 0)
{
v_x_1484_ = v_tail_1487_;
goto _start;
}
else
{
return v___y_1489_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg___boxed(lean_object* v_a_1497_, lean_object* v_x_1498_){
_start:
{
uint8_t v_res_1499_; lean_object* v_r_1500_; 
v_res_1499_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_a_1497_, v_x_1498_);
lean_dec(v_x_1498_);
lean_dec_ref(v_a_1497_);
v_r_1500_ = lean_box(v_res_1499_);
return v_r_1500_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0___redArg(lean_object* v_m_1501_, lean_object* v_a_1502_, lean_object* v_b_1503_){
_start:
{
lean_object* v_size_1504_; lean_object* v_buckets_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1552_; 
v_size_1504_ = lean_ctor_get(v_m_1501_, 0);
v_buckets_1505_ = lean_ctor_get(v_m_1501_, 1);
v_isSharedCheck_1552_ = !lean_is_exclusive(v_m_1501_);
if (v_isSharedCheck_1552_ == 0)
{
v___x_1507_ = v_m_1501_;
v_isShared_1508_ = v_isSharedCheck_1552_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_buckets_1505_);
lean_inc(v_size_1504_);
lean_dec(v_m_1501_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1552_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v_fst_1509_; lean_object* v_snd_1510_; lean_object* v___x_1511_; uint64_t v___x_1512_; uint64_t v___x_1513_; uint64_t v___x_1514_; uint64_t v___x_1515_; uint64_t v___x_1516_; uint64_t v_fold_1517_; uint64_t v___x_1518_; uint64_t v___x_1519_; uint64_t v___x_1520_; size_t v___x_1521_; size_t v___x_1522_; size_t v___x_1523_; size_t v___x_1524_; size_t v___x_1525_; lean_object* v_bkt_1526_; uint8_t v___x_1527_; 
v_fst_1509_ = lean_ctor_get(v_a_1502_, 0);
v_snd_1510_ = lean_ctor_get(v_a_1502_, 1);
v___x_1511_ = lean_array_get_size(v_buckets_1505_);
v___x_1512_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_1509_);
v___x_1513_ = lean_uint64_of_nat(v_snd_1510_);
v___x_1514_ = lean_uint64_mix_hash(v___x_1512_, v___x_1513_);
v___x_1515_ = 32ULL;
v___x_1516_ = lean_uint64_shift_right(v___x_1514_, v___x_1515_);
v_fold_1517_ = lean_uint64_xor(v___x_1514_, v___x_1516_);
v___x_1518_ = 16ULL;
v___x_1519_ = lean_uint64_shift_right(v_fold_1517_, v___x_1518_);
v___x_1520_ = lean_uint64_xor(v_fold_1517_, v___x_1519_);
v___x_1521_ = lean_uint64_to_usize(v___x_1520_);
v___x_1522_ = lean_usize_of_nat(v___x_1511_);
v___x_1523_ = ((size_t)1ULL);
v___x_1524_ = lean_usize_sub(v___x_1522_, v___x_1523_);
v___x_1525_ = lean_usize_land(v___x_1521_, v___x_1524_);
v_bkt_1526_ = lean_array_uget_borrowed(v_buckets_1505_, v___x_1525_);
v___x_1527_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_a_1502_, v_bkt_1526_);
if (v___x_1527_ == 0)
{
lean_object* v___x_1528_; lean_object* v_size_x27_1529_; lean_object* v___x_1530_; lean_object* v_buckets_x27_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; uint8_t v___x_1537_; 
v___x_1528_ = lean_unsigned_to_nat(1u);
v_size_x27_1529_ = lean_nat_add(v_size_1504_, v___x_1528_);
lean_dec(v_size_1504_);
lean_inc(v_bkt_1526_);
v___x_1530_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1530_, 0, v_a_1502_);
lean_ctor_set(v___x_1530_, 1, v_b_1503_);
lean_ctor_set(v___x_1530_, 2, v_bkt_1526_);
v_buckets_x27_1531_ = lean_array_uset(v_buckets_1505_, v___x_1525_, v___x_1530_);
v___x_1532_ = lean_unsigned_to_nat(4u);
v___x_1533_ = lean_nat_mul(v_size_x27_1529_, v___x_1532_);
v___x_1534_ = lean_unsigned_to_nat(3u);
v___x_1535_ = lean_nat_div(v___x_1533_, v___x_1534_);
lean_dec(v___x_1533_);
v___x_1536_ = lean_array_get_size(v_buckets_x27_1531_);
v___x_1537_ = lean_nat_dec_le(v___x_1535_, v___x_1536_);
lean_dec(v___x_1535_);
if (v___x_1537_ == 0)
{
lean_object* v_val_1538_; lean_object* v___x_1540_; 
v_val_1538_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1___redArg(v_buckets_x27_1531_);
if (v_isShared_1508_ == 0)
{
lean_ctor_set(v___x_1507_, 1, v_val_1538_);
lean_ctor_set(v___x_1507_, 0, v_size_x27_1529_);
v___x_1540_ = v___x_1507_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_size_x27_1529_);
lean_ctor_set(v_reuseFailAlloc_1541_, 1, v_val_1538_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
return v___x_1540_;
}
}
else
{
lean_object* v___x_1543_; 
if (v_isShared_1508_ == 0)
{
lean_ctor_set(v___x_1507_, 1, v_buckets_x27_1531_);
lean_ctor_set(v___x_1507_, 0, v_size_x27_1529_);
v___x_1543_ = v___x_1507_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_size_x27_1529_);
lean_ctor_set(v_reuseFailAlloc_1544_, 1, v_buckets_x27_1531_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
}
else
{
lean_object* v___x_1545_; lean_object* v_buckets_x27_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1550_; 
lean_inc(v_bkt_1526_);
v___x_1545_ = lean_box(0);
v_buckets_x27_1546_ = lean_array_uset(v_buckets_1505_, v___x_1525_, v___x_1545_);
v___x_1547_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(v_a_1502_, v_b_1503_, v_bkt_1526_);
v___x_1548_ = lean_array_uset(v_buckets_x27_1546_, v___x_1525_, v___x_1547_);
if (v_isShared_1508_ == 0)
{
lean_ctor_set(v___x_1507_, 1, v___x_1548_);
v___x_1550_ = v___x_1507_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v_size_1504_);
lean_ctor_set(v_reuseFailAlloc_1551_, 1, v___x_1548_);
v___x_1550_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
return v___x_1550_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(lean_object* v_key_1553_, lean_object* v_r_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_){
_start:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; 
lean_inc_ref(v_r_1554_);
v___x_1557_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1555_, v_key_1553_, v_r_1554_);
v___x_1558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1558_, 0, v_r_1554_);
lean_ctor_set(v___x_1558_, 1, v___x_1557_);
v___x_1559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1558_);
lean_ctor_set(v___x_1559_, 1, v_a_1556_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save(lean_object* v_key_1560_, lean_object* v_r_1561_, lean_object* v_a_1562_, uint8_t v_a_1563_, lean_object* v_a_1564_){
_start:
{
lean_object* v___x_1565_; 
v___x_1565_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_1560_, v_r_1561_, v_a_1562_, v_a_1564_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___boxed(lean_object* v_key_1566_, lean_object* v_r_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_){
_start:
{
uint8_t v_a_1659__boxed_1571_; lean_object* v_res_1572_; 
v_a_1659__boxed_1571_ = lean_unbox(v_a_1569_);
v_res_1572_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save(v_key_1566_, v_r_1567_, v_a_1568_, v_a_1659__boxed_1571_, v_a_1570_);
return v_res_1572_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0(lean_object* v_00_u03b2_1573_, lean_object* v_m_1574_, lean_object* v_a_1575_, lean_object* v_b_1576_){
_start:
{
lean_object* v___x_1577_; 
v___x_1577_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0___redArg(v_m_1574_, v_a_1575_, v_b_1576_);
return v___x_1577_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0(lean_object* v_00_u03b2_1578_, lean_object* v_a_1579_, lean_object* v_x_1580_){
_start:
{
uint8_t v___x_1581_; 
v___x_1581_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_a_1579_, v_x_1580_);
return v___x_1581_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1582_, lean_object* v_a_1583_, lean_object* v_x_1584_){
_start:
{
uint8_t v_res_1585_; lean_object* v_r_1586_; 
v_res_1585_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0(v_00_u03b2_1582_, v_a_1583_, v_x_1584_);
lean_dec(v_x_1584_);
lean_dec_ref(v_a_1583_);
v_r_1586_ = lean_box(v_res_1585_);
return v_r_1586_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1(lean_object* v_00_u03b2_1587_, lean_object* v_data_1588_){
_start:
{
lean_object* v___x_1589_; 
v___x_1589_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1___redArg(v_data_1588_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2(lean_object* v_00_u03b2_1590_, lean_object* v_a_1591_, lean_object* v_b_1592_, lean_object* v_x_1593_){
_start:
{
lean_object* v___x_1594_; 
v___x_1594_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(v_a_1591_, v_b_1592_, v_x_1593_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1595_, lean_object* v_i_1596_, lean_object* v_source_1597_, lean_object* v_target_1598_){
_start:
{
lean_object* v___x_1599_; 
v___x_1599_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2___redArg(v_i_1596_, v_source_1597_, v_target_1598_);
return v___x_1599_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1600_, lean_object* v_x_1601_, lean_object* v_x_1602_){
_start:
{
lean_object* v___x_1603_; 
v___x_1603_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1601_, v_x_1602_);
return v___x_1603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0___redArg(lean_object* v_idx_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_){
_start:
{
lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v_fst_1609_; lean_object* v_snd_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1618_; 
v___x_1607_ = l_Lean_Expr_bvar___override(v_idx_1604_);
v___x_1608_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1607_, v___y_1606_);
v_fst_1609_ = lean_ctor_get(v___x_1608_, 0);
v_snd_1610_ = lean_ctor_get(v___x_1608_, 1);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1612_ = v___x_1608_;
v_isShared_1613_ = v_isSharedCheck_1618_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_snd_1610_);
lean_inc(v_fst_1609_);
lean_dec(v___x_1608_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1618_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v___x_1615_; 
if (v_isShared_1613_ == 0)
{
lean_ctor_set(v___x_1612_, 1, v___y_1605_);
v___x_1615_ = v___x_1612_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_fst_1609_);
lean_ctor_set(v_reuseFailAlloc_1617_, 1, v___y_1605_);
v___x_1615_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
lean_object* v___x_1616_; 
v___x_1616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1616_, 0, v___x_1615_);
lean_ctor_set(v___x_1616_, 1, v_snd_1610_);
return v___x_1616_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0(lean_object* v_idx_1619_, lean_object* v___y_1620_, uint8_t v___y_1621_, lean_object* v___y_1622_){
_start:
{
lean_object* v___x_1623_; 
v___x_1623_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0___redArg(v_idx_1619_, v___y_1620_, v___y_1622_);
return v___x_1623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0___boxed(lean_object* v_idx_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_){
_start:
{
uint8_t v___y_1292__boxed_1628_; lean_object* v_res_1629_; 
v___y_1292__boxed_1628_ = lean_unbox(v___y_1626_);
v_res_1629_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0(v_idx_1624_, v___y_1625_, v___y_1292__boxed_1628_, v___y_1627_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(lean_object* v_subst_1630_, lean_object* v_e_1631_, lean_object* v_bidx_1632_, lean_object* v_offset_1633_, lean_object* v_a_1634_, uint8_t v_a_1635_, lean_object* v_a_1636_){
_start:
{
uint8_t v___x_1637_; 
v___x_1637_ = lean_nat_dec_le(v_offset_1633_, v_bidx_1632_);
if (v___x_1637_ == 0)
{
lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___x_1638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1638_, 0, v_e_1631_);
lean_ctor_set(v___x_1638_, 1, v_a_1634_);
v___x_1639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1638_);
lean_ctor_set(v___x_1639_, 1, v_a_1636_);
return v___x_1639_;
}
else
{
lean_object* v_n_1640_; lean_object* v___x_1641_; uint8_t v___x_1642_; 
lean_dec_ref(v_e_1631_);
v_n_1640_ = lean_array_get_size(v_subst_1630_);
v___x_1641_ = lean_nat_add(v_offset_1633_, v_n_1640_);
v___x_1642_ = lean_nat_dec_lt(v_bidx_1632_, v___x_1641_);
lean_dec(v___x_1641_);
if (v___x_1642_ == 0)
{
lean_object* v___x_1643_; lean_object* v___x_1644_; 
v___x_1643_ = lean_nat_sub(v_bidx_1632_, v_n_1640_);
v___x_1644_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0___redArg(v___x_1643_, v_a_1634_, v_a_1636_);
return v___x_1644_;
}
else
{
lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v_v_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v_fst_1652_; lean_object* v_snd_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1661_; 
v___x_1645_ = lean_nat_sub(v_bidx_1632_, v_offset_1633_);
v___x_1646_ = lean_nat_sub(v_n_1640_, v___x_1645_);
lean_dec(v___x_1645_);
v___x_1647_ = lean_unsigned_to_nat(1u);
v___x_1648_ = lean_nat_sub(v___x_1646_, v___x_1647_);
lean_dec(v___x_1646_);
v_v_1649_ = lean_array_fget_borrowed(v_subst_1630_, v___x_1648_);
lean_dec(v___x_1648_);
v___x_1650_ = lean_unsigned_to_nat(0u);
lean_inc(v_v_1649_);
v___x_1651_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(v_v_1649_, v___x_1650_, v_offset_1633_, v_a_1635_, v_a_1636_);
v_fst_1652_ = lean_ctor_get(v___x_1651_, 0);
v_snd_1653_ = lean_ctor_get(v___x_1651_, 1);
v_isSharedCheck_1661_ = !lean_is_exclusive(v___x_1651_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1655_ = v___x_1651_;
v_isShared_1656_ = v_isSharedCheck_1661_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_snd_1653_);
lean_inc(v_fst_1652_);
lean_dec(v___x_1651_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1661_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1658_; 
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 1, v_a_1634_);
v___x_1658_ = v___x_1655_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_fst_1652_);
lean_ctor_set(v_reuseFailAlloc_1660_, 1, v_a_1634_);
v___x_1658_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
lean_object* v___x_1659_; 
v___x_1659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1659_, 0, v___x_1658_);
lean_ctor_set(v___x_1659_, 1, v_snd_1653_);
return v___x_1659_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar___boxed(lean_object* v_subst_1662_, lean_object* v_e_1663_, lean_object* v_bidx_1664_, lean_object* v_offset_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_){
_start:
{
uint8_t v_a_1303__boxed_1669_; lean_object* v_res_1670_; 
v_a_1303__boxed_1669_ = lean_unbox(v_a_1667_);
v_res_1670_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(v_subst_1662_, v_e_1663_, v_bidx_1664_, v_offset_1665_, v_a_1666_, v_a_1303__boxed_1669_, v_a_1668_);
lean_dec(v_offset_1665_);
lean_dec(v_bidx_1664_);
lean_dec_ref(v_subst_1662_);
return v_res_1670_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__3(void){
_start:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1674_ = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__2));
v___x_1675_ = lean_unsigned_to_nat(25u);
v___x_1676_ = lean_unsigned_to_nat(148u);
v___x_1677_ = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__1));
v___x_1678_ = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__0));
v___x_1679_ = l_mkPanicMessageWithDecl(v___x_1678_, v___x_1677_, v___x_1676_, v___x_1675_, v___x_1674_);
return v___x_1679_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__1(void){
_start:
{
lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1681_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__2));
v___x_1682_ = lean_unsigned_to_nat(11u);
v___x_1683_ = lean_unsigned_to_nat(179u);
v___x_1684_ = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__0));
v___x_1685_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__3));
v___x_1686_ = l_mkPanicMessageWithDecl(v___x_1685_, v___x_1684_, v___x_1683_, v___x_1682_, v___x_1681_);
return v___x_1686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta(lean_object* v_subst_1687_, lean_object* v_e_1688_, lean_object* v_f_1689_, lean_object* v_argsRev_1690_, lean_object* v_offset_1691_, uint8_t v_modified_1692_, lean_object* v_a_1693_, uint8_t v_a_1694_, lean_object* v_a_1695_){
_start:
{
switch(lean_obj_tag(v_f_1689_))
{
case 5:
{
lean_object* v_fn_1696_; lean_object* v_arg_1697_; lean_object* v___x_1698_; lean_object* v_fst_1699_; lean_object* v_snd_1700_; lean_object* v_fst_1701_; lean_object* v_snd_1702_; lean_object* v___x_1703_; 
v_fn_1696_ = lean_ctor_get(v_f_1689_, 0);
lean_inc_ref(v_fn_1696_);
v_arg_1697_ = lean_ctor_get(v_f_1689_, 1);
lean_inc_ref(v_arg_1697_);
lean_dec_ref(v_f_1689_);
lean_inc(v_offset_1691_);
lean_inc_ref(v_arg_1697_);
v___x_1698_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1687_, v_arg_1697_, v_offset_1691_, v_a_1693_, v_a_1694_, v_a_1695_);
v_fst_1699_ = lean_ctor_get(v___x_1698_, 0);
lean_inc(v_fst_1699_);
v_snd_1700_ = lean_ctor_get(v___x_1698_, 1);
lean_inc(v_snd_1700_);
lean_dec_ref(v___x_1698_);
v_fst_1701_ = lean_ctor_get(v_fst_1699_, 0);
lean_inc(v_fst_1701_);
v_snd_1702_ = lean_ctor_get(v_fst_1699_, 1);
lean_inc(v_snd_1702_);
lean_dec(v_fst_1699_);
lean_inc(v_fst_1701_);
v___x_1703_ = lean_array_push(v_argsRev_1690_, v_fst_1701_);
if (v_modified_1692_ == 0)
{
uint8_t v___x_1704_; 
v___x_1704_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_1697_, v_fst_1701_);
lean_dec(v_fst_1701_);
lean_dec_ref(v_arg_1697_);
if (v___x_1704_ == 0)
{
uint8_t v___x_1705_; 
v___x_1705_ = 1;
v_f_1689_ = v_fn_1696_;
v_argsRev_1690_ = v___x_1703_;
v_modified_1692_ = v___x_1705_;
v_a_1693_ = v_snd_1702_;
v_a_1695_ = v_snd_1700_;
goto _start;
}
else
{
v_f_1689_ = v_fn_1696_;
v_argsRev_1690_ = v___x_1703_;
v_a_1693_ = v_snd_1702_;
v_a_1695_ = v_snd_1700_;
goto _start;
}
}
else
{
lean_dec(v_fst_1701_);
lean_dec_ref(v_arg_1697_);
v_f_1689_ = v_fn_1696_;
v_argsRev_1690_ = v___x_1703_;
v_a_1693_ = v_snd_1702_;
v_a_1695_ = v_snd_1700_;
goto _start;
}
}
case 0:
{
lean_object* v_deBruijnIndex_1709_; lean_object* v___x_1710_; lean_object* v_fst_1711_; lean_object* v_snd_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1741_; 
v_deBruijnIndex_1709_ = lean_ctor_get(v_f_1689_, 0);
lean_inc_ref(v_f_1689_);
v___x_1710_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(v_subst_1687_, v_f_1689_, v_deBruijnIndex_1709_, v_offset_1691_, v_a_1693_, v_a_1694_, v_a_1695_);
lean_dec(v_offset_1691_);
v_fst_1711_ = lean_ctor_get(v___x_1710_, 0);
v_snd_1712_ = lean_ctor_get(v___x_1710_, 1);
v_isSharedCheck_1741_ = !lean_is_exclusive(v___x_1710_);
if (v_isSharedCheck_1741_ == 0)
{
v___x_1714_ = v___x_1710_;
v_isShared_1715_ = v_isSharedCheck_1741_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_snd_1712_);
lean_inc(v_fst_1711_);
lean_dec(v___x_1710_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1741_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v_fst_1716_; lean_object* v_snd_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1740_; 
v_fst_1716_ = lean_ctor_get(v_fst_1711_, 0);
v_snd_1717_ = lean_ctor_get(v_fst_1711_, 1);
v_isSharedCheck_1740_ = !lean_is_exclusive(v_fst_1711_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1719_ = v_fst_1711_;
v_isShared_1720_ = v_isSharedCheck_1740_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_snd_1717_);
lean_inc(v_fst_1716_);
lean_dec(v_fst_1711_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1740_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
if (v_modified_1692_ == 0)
{
uint8_t v___x_1735_; 
v___x_1735_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_f_1689_, v_fst_1716_);
lean_dec_ref(v_f_1689_);
if (v___x_1735_ == 0)
{
lean_del_object(v___x_1714_);
lean_dec_ref(v_e_1688_);
goto v___jp_1721_;
}
else
{
lean_object* v___x_1737_; 
lean_del_object(v___x_1719_);
lean_dec(v_fst_1716_);
lean_dec_ref(v_argsRev_1690_);
if (v_isShared_1715_ == 0)
{
lean_ctor_set(v___x_1714_, 1, v_snd_1717_);
lean_ctor_set(v___x_1714_, 0, v_e_1688_);
v___x_1737_ = v___x_1714_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_e_1688_);
lean_ctor_set(v_reuseFailAlloc_1739_, 1, v_snd_1717_);
v___x_1737_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
lean_object* v___x_1738_; 
v___x_1738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1738_, 0, v___x_1737_);
lean_ctor_set(v___x_1738_, 1, v_snd_1712_);
return v___x_1738_;
}
}
}
else
{
lean_del_object(v___x_1714_);
lean_dec_ref(v_f_1689_);
lean_dec_ref(v_e_1688_);
goto v___jp_1721_;
}
v___jp_1721_:
{
lean_object* v___x_1722_; lean_object* v_fst_1723_; lean_object* v_snd_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1734_; 
v___x_1722_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS(v_fst_1716_, v_argsRev_1690_, v_a_1694_, v_snd_1712_);
lean_dec_ref(v_argsRev_1690_);
v_fst_1723_ = lean_ctor_get(v___x_1722_, 0);
v_snd_1724_ = lean_ctor_get(v___x_1722_, 1);
v_isSharedCheck_1734_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1726_ = v___x_1722_;
v_isShared_1727_ = v_isSharedCheck_1734_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_snd_1724_);
lean_inc(v_fst_1723_);
lean_dec(v___x_1722_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1734_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___x_1729_; 
if (v_isShared_1727_ == 0)
{
lean_ctor_set(v___x_1726_, 1, v_snd_1717_);
v___x_1729_ = v___x_1726_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_fst_1723_);
lean_ctor_set(v_reuseFailAlloc_1733_, 1, v_snd_1717_);
v___x_1729_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
lean_object* v___x_1731_; 
if (v_isShared_1720_ == 0)
{
lean_ctor_set(v___x_1719_, 1, v_snd_1724_);
lean_ctor_set(v___x_1719_, 0, v___x_1729_);
v___x_1731_ = v___x_1719_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v___x_1729_);
lean_ctor_set(v_reuseFailAlloc_1732_, 1, v_snd_1724_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
return v___x_1731_;
}
}
}
}
}
}
}
default: 
{
lean_object* v___x_1742_; lean_object* v___x_1743_; 
lean_dec(v_offset_1691_);
lean_dec_ref(v_argsRev_1690_);
lean_dec_ref(v_f_1689_);
lean_dec_ref(v_e_1688_);
v___x_1742_ = lean_obj_once(&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__1, &l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__1_once, _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__1);
v___x_1743_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9(v___x_1742_, v_a_1693_, v_a_1694_, v_a_1695_);
return v___x_1743_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg(lean_object* v_subst_1744_, lean_object* v_e_1745_, lean_object* v_f_1746_, lean_object* v_arg_1747_, lean_object* v_offset_1748_, lean_object* v_a_1749_, uint8_t v_a_1750_, lean_object* v_a_1751_){
_start:
{
lean_object* v___x_1752_; lean_object* v_fst_1753_; lean_object* v_snd_1754_; lean_object* v_fst_1755_; lean_object* v_snd_1756_; lean_object* v___x_1757_; uint8_t v___x_1758_; 
lean_inc(v_offset_1748_);
lean_inc_ref(v_arg_1747_);
v___x_1752_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1744_, v_arg_1747_, v_offset_1748_, v_a_1749_, v_a_1750_, v_a_1751_);
v_fst_1753_ = lean_ctor_get(v___x_1752_, 0);
lean_inc(v_fst_1753_);
v_snd_1754_ = lean_ctor_get(v___x_1752_, 1);
lean_inc(v_snd_1754_);
lean_dec_ref(v___x_1752_);
v_fst_1755_ = lean_ctor_get(v_fst_1753_, 0);
lean_inc(v_fst_1755_);
v_snd_1756_ = lean_ctor_get(v_fst_1753_, 1);
lean_inc(v_snd_1756_);
lean_dec(v_fst_1753_);
v___x_1757_ = l_Lean_Expr_getAppFn(v_f_1746_);
v___x_1758_ = l_Lean_Expr_isBVar(v___x_1757_);
lean_dec_ref(v___x_1757_);
if (v___x_1758_ == 0)
{
lean_object* v___x_1759_; lean_object* v_fst_1760_; lean_object* v_snd_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1786_; 
lean_dec_ref(v_arg_1747_);
v___x_1759_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault(v_subst_1744_, v_f_1746_, v_offset_1748_, v_snd_1756_, v_a_1750_, v_snd_1754_);
v_fst_1760_ = lean_ctor_get(v___x_1759_, 0);
v_snd_1761_ = lean_ctor_get(v___x_1759_, 1);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1759_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1763_ = v___x_1759_;
v_isShared_1764_ = v_isSharedCheck_1786_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_snd_1761_);
lean_inc(v_fst_1760_);
lean_dec(v___x_1759_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1786_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v_fst_1765_; lean_object* v_snd_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1785_; 
v_fst_1765_ = lean_ctor_get(v_fst_1760_, 0);
v_snd_1766_ = lean_ctor_get(v_fst_1760_, 1);
v_isSharedCheck_1785_ = !lean_is_exclusive(v_fst_1760_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1768_ = v_fst_1760_;
v_isShared_1769_ = v_isSharedCheck_1785_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_snd_1766_);
lean_inc(v_fst_1765_);
lean_dec(v_fst_1760_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1785_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
uint8_t v___y_1771_; 
if (lean_obj_tag(v_e_1745_) == 5)
{
lean_object* v_fn_1779_; lean_object* v_arg_1780_; uint8_t v___x_1781_; 
v_fn_1779_ = lean_ctor_get(v_e_1745_, 0);
v_arg_1780_ = lean_ctor_get(v_e_1745_, 1);
v___x_1781_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_1779_, v_fst_1765_);
if (v___x_1781_ == 0)
{
v___y_1771_ = v___x_1781_;
goto v___jp_1770_;
}
else
{
uint8_t v___x_1782_; 
v___x_1782_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_1780_, v_fst_1755_);
v___y_1771_ = v___x_1782_;
goto v___jp_1770_;
}
}
else
{
lean_object* v___x_1783_; lean_object* v___x_1784_; 
lean_del_object(v___x_1768_);
lean_dec(v_fst_1765_);
lean_del_object(v___x_1763_);
lean_dec(v_fst_1755_);
lean_dec_ref(v_e_1745_);
v___x_1783_ = lean_obj_once(&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__3, &l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__3_once, _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__3);
v___x_1784_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9(v___x_1783_, v_snd_1766_, v_a_1750_, v_snd_1761_);
return v___x_1784_;
}
v___jp_1770_:
{
if (v___y_1771_ == 0)
{
lean_object* v___x_1772_; 
lean_del_object(v___x_1768_);
lean_del_object(v___x_1763_);
lean_dec_ref(v_e_1745_);
v___x_1772_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__3(v_fst_1765_, v_fst_1755_, v_snd_1766_, v_a_1750_, v_snd_1761_);
return v___x_1772_;
}
else
{
lean_object* v___x_1774_; 
lean_dec(v_fst_1765_);
lean_dec(v_fst_1755_);
if (v_isShared_1769_ == 0)
{
lean_ctor_set(v___x_1768_, 0, v_e_1745_);
v___x_1774_ = v___x_1768_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_e_1745_);
lean_ctor_set(v_reuseFailAlloc_1778_, 1, v_snd_1766_);
v___x_1774_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
lean_object* v___x_1776_; 
if (v_isShared_1764_ == 0)
{
lean_ctor_set(v___x_1763_, 0, v___x_1774_);
v___x_1776_ = v___x_1763_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v___x_1774_);
lean_ctor_set(v_reuseFailAlloc_1777_, 1, v_snd_1761_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
return v___x_1776_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; uint8_t v___x_1790_; 
v___x_1787_ = lean_unsigned_to_nat(1u);
v___x_1788_ = lean_mk_empty_array_with_capacity(v___x_1787_);
lean_inc(v_fst_1755_);
v___x_1789_ = lean_array_push(v___x_1788_, v_fst_1755_);
v___x_1790_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_1747_, v_fst_1755_);
lean_dec(v_fst_1755_);
lean_dec_ref(v_arg_1747_);
if (v___x_1790_ == 0)
{
lean_object* v___x_1791_; 
v___x_1791_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta(v_subst_1744_, v_e_1745_, v_f_1746_, v___x_1789_, v_offset_1748_, v___x_1758_, v_snd_1756_, v_a_1750_, v_snd_1754_);
return v___x_1791_;
}
else
{
uint8_t v___x_1792_; lean_object* v___x_1793_; 
v___x_1792_ = 0;
v___x_1793_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta(v_subst_1744_, v_e_1745_, v_f_1746_, v___x_1789_, v_offset_1748_, v___x_1792_, v_snd_1756_, v_a_1750_, v_snd_1754_);
return v___x_1793_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__1(void){
_start:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1795_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__2));
v___x_1796_ = lean_unsigned_to_nat(59u);
v___x_1797_ = lean_unsigned_to_nat(190u);
v___x_1798_ = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__0));
v___x_1799_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__3));
v___x_1800_ = l_mkPanicMessageWithDecl(v___x_1799_, v___x_1798_, v___x_1797_, v___x_1796_, v___x_1795_);
return v___x_1800_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit(lean_object* v_subst_1801_, lean_object* v_e_1802_, lean_object* v_offset_1803_, lean_object* v_a_1804_, uint8_t v_a_1805_, lean_object* v_a_1806_){
_start:
{
switch(lean_obj_tag(v_e_1802_))
{
case 0:
{
lean_object* v_deBruijnIndex_1807_; lean_object* v___x_1808_; 
v_deBruijnIndex_1807_ = lean_ctor_get(v_e_1802_, 0);
lean_inc(v_deBruijnIndex_1807_);
v___x_1808_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(v_subst_1801_, v_e_1802_, v_deBruijnIndex_1807_, v_offset_1803_, v_a_1804_, v_a_1805_, v_a_1806_);
lean_dec(v_offset_1803_);
lean_dec(v_deBruijnIndex_1807_);
return v___x_1808_;
}
case 5:
{
lean_object* v_fn_1809_; lean_object* v_arg_1810_; lean_object* v___x_1811_; 
v_fn_1809_ = lean_ctor_get(v_e_1802_, 0);
lean_inc_ref(v_fn_1809_);
v_arg_1810_ = lean_ctor_get(v_e_1802_, 1);
lean_inc_ref(v_arg_1810_);
v___x_1811_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg(v_subst_1801_, v_e_1802_, v_fn_1809_, v_arg_1810_, v_offset_1803_, v_a_1804_, v_a_1805_, v_a_1806_);
return v___x_1811_;
}
case 6:
{
lean_object* v_binderName_1812_; lean_object* v_binderType_1813_; lean_object* v_body_1814_; uint8_t v_binderInfo_1815_; lean_object* v___x_1816_; lean_object* v_fst_1817_; lean_object* v_snd_1818_; lean_object* v_fst_1819_; lean_object* v_snd_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v_fst_1824_; lean_object* v_snd_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1846_; 
v_binderName_1812_ = lean_ctor_get(v_e_1802_, 0);
v_binderType_1813_ = lean_ctor_get(v_e_1802_, 1);
v_body_1814_ = lean_ctor_get(v_e_1802_, 2);
v_binderInfo_1815_ = lean_ctor_get_uint8(v_e_1802_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1803_);
lean_inc_ref(v_binderType_1813_);
v___x_1816_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1801_, v_binderType_1813_, v_offset_1803_, v_a_1804_, v_a_1805_, v_a_1806_);
v_fst_1817_ = lean_ctor_get(v___x_1816_, 0);
lean_inc(v_fst_1817_);
v_snd_1818_ = lean_ctor_get(v___x_1816_, 1);
lean_inc(v_snd_1818_);
lean_dec_ref(v___x_1816_);
v_fst_1819_ = lean_ctor_get(v_fst_1817_, 0);
lean_inc(v_fst_1819_);
v_snd_1820_ = lean_ctor_get(v_fst_1817_, 1);
lean_inc(v_snd_1820_);
lean_dec(v_fst_1817_);
v___x_1821_ = lean_unsigned_to_nat(1u);
v___x_1822_ = lean_nat_add(v_offset_1803_, v___x_1821_);
lean_dec(v_offset_1803_);
lean_inc_ref(v_body_1814_);
v___x_1823_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1801_, v_body_1814_, v___x_1822_, v_snd_1820_, v_a_1805_, v_snd_1818_);
v_fst_1824_ = lean_ctor_get(v___x_1823_, 0);
v_snd_1825_ = lean_ctor_get(v___x_1823_, 1);
v_isSharedCheck_1846_ = !lean_is_exclusive(v___x_1823_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1827_ = v___x_1823_;
v_isShared_1828_ = v_isSharedCheck_1846_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_snd_1825_);
lean_inc(v_fst_1824_);
lean_dec(v___x_1823_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1846_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v_fst_1829_; lean_object* v_snd_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1845_; 
v_fst_1829_ = lean_ctor_get(v_fst_1824_, 0);
v_snd_1830_ = lean_ctor_get(v_fst_1824_, 1);
v_isSharedCheck_1845_ = !lean_is_exclusive(v_fst_1824_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1832_ = v_fst_1824_;
v_isShared_1833_ = v_isSharedCheck_1845_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_snd_1830_);
lean_inc(v_fst_1829_);
lean_dec(v_fst_1824_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1845_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
uint8_t v___y_1835_; uint8_t v___x_1843_; 
v___x_1843_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_1813_, v_fst_1819_);
if (v___x_1843_ == 0)
{
v___y_1835_ = v___x_1843_;
goto v___jp_1834_;
}
else
{
uint8_t v___x_1844_; 
v___x_1844_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1814_, v_fst_1829_);
v___y_1835_ = v___x_1844_;
goto v___jp_1834_;
}
v___jp_1834_:
{
if (v___y_1835_ == 0)
{
lean_object* v___x_1836_; 
lean_inc(v_binderName_1812_);
lean_del_object(v___x_1832_);
lean_del_object(v___x_1827_);
lean_dec_ref(v_e_1802_);
v___x_1836_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__4(v_binderName_1812_, v_binderInfo_1815_, v_fst_1819_, v_fst_1829_, v_snd_1830_, v_a_1805_, v_snd_1825_);
return v___x_1836_;
}
else
{
lean_object* v___x_1838_; 
lean_dec(v_fst_1829_);
lean_dec(v_fst_1819_);
if (v_isShared_1833_ == 0)
{
lean_ctor_set(v___x_1832_, 0, v_e_1802_);
v___x_1838_ = v___x_1832_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v_e_1802_);
lean_ctor_set(v_reuseFailAlloc_1842_, 1, v_snd_1830_);
v___x_1838_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
lean_object* v___x_1840_; 
if (v_isShared_1828_ == 0)
{
lean_ctor_set(v___x_1827_, 0, v___x_1838_);
v___x_1840_ = v___x_1827_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v___x_1838_);
lean_ctor_set(v_reuseFailAlloc_1841_, 1, v_snd_1825_);
v___x_1840_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
return v___x_1840_;
}
}
}
}
}
}
}
case 7:
{
lean_object* v_binderName_1847_; lean_object* v_binderType_1848_; lean_object* v_body_1849_; uint8_t v_binderInfo_1850_; lean_object* v___x_1851_; lean_object* v_fst_1852_; lean_object* v_snd_1853_; lean_object* v_fst_1854_; lean_object* v_snd_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v_fst_1859_; lean_object* v_snd_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1881_; 
v_binderName_1847_ = lean_ctor_get(v_e_1802_, 0);
v_binderType_1848_ = lean_ctor_get(v_e_1802_, 1);
v_body_1849_ = lean_ctor_get(v_e_1802_, 2);
v_binderInfo_1850_ = lean_ctor_get_uint8(v_e_1802_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1803_);
lean_inc_ref(v_binderType_1848_);
v___x_1851_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1801_, v_binderType_1848_, v_offset_1803_, v_a_1804_, v_a_1805_, v_a_1806_);
v_fst_1852_ = lean_ctor_get(v___x_1851_, 0);
lean_inc(v_fst_1852_);
v_snd_1853_ = lean_ctor_get(v___x_1851_, 1);
lean_inc(v_snd_1853_);
lean_dec_ref(v___x_1851_);
v_fst_1854_ = lean_ctor_get(v_fst_1852_, 0);
lean_inc(v_fst_1854_);
v_snd_1855_ = lean_ctor_get(v_fst_1852_, 1);
lean_inc(v_snd_1855_);
lean_dec(v_fst_1852_);
v___x_1856_ = lean_unsigned_to_nat(1u);
v___x_1857_ = lean_nat_add(v_offset_1803_, v___x_1856_);
lean_dec(v_offset_1803_);
lean_inc_ref(v_body_1849_);
v___x_1858_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1801_, v_body_1849_, v___x_1857_, v_snd_1855_, v_a_1805_, v_snd_1853_);
v_fst_1859_ = lean_ctor_get(v___x_1858_, 0);
v_snd_1860_ = lean_ctor_get(v___x_1858_, 1);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1858_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1862_ = v___x_1858_;
v_isShared_1863_ = v_isSharedCheck_1881_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_snd_1860_);
lean_inc(v_fst_1859_);
lean_dec(v___x_1858_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1881_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v_fst_1864_; lean_object* v_snd_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1880_; 
v_fst_1864_ = lean_ctor_get(v_fst_1859_, 0);
v_snd_1865_ = lean_ctor_get(v_fst_1859_, 1);
v_isSharedCheck_1880_ = !lean_is_exclusive(v_fst_1859_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1867_ = v_fst_1859_;
v_isShared_1868_ = v_isSharedCheck_1880_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_snd_1865_);
lean_inc(v_fst_1864_);
lean_dec(v_fst_1859_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1880_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
uint8_t v___y_1870_; uint8_t v___x_1878_; 
v___x_1878_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_1848_, v_fst_1854_);
if (v___x_1878_ == 0)
{
v___y_1870_ = v___x_1878_;
goto v___jp_1869_;
}
else
{
uint8_t v___x_1879_; 
v___x_1879_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1849_, v_fst_1864_);
v___y_1870_ = v___x_1879_;
goto v___jp_1869_;
}
v___jp_1869_:
{
if (v___y_1870_ == 0)
{
lean_object* v___x_1871_; 
lean_inc(v_binderName_1847_);
lean_del_object(v___x_1867_);
lean_del_object(v___x_1862_);
lean_dec_ref(v_e_1802_);
v___x_1871_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__5(v_binderName_1847_, v_binderInfo_1850_, v_fst_1854_, v_fst_1864_, v_snd_1865_, v_a_1805_, v_snd_1860_);
return v___x_1871_;
}
else
{
lean_object* v___x_1873_; 
lean_dec(v_fst_1864_);
lean_dec(v_fst_1854_);
if (v_isShared_1868_ == 0)
{
lean_ctor_set(v___x_1867_, 0, v_e_1802_);
v___x_1873_ = v___x_1867_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v_e_1802_);
lean_ctor_set(v_reuseFailAlloc_1877_, 1, v_snd_1865_);
v___x_1873_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
lean_object* v___x_1875_; 
if (v_isShared_1863_ == 0)
{
lean_ctor_set(v___x_1862_, 0, v___x_1873_);
v___x_1875_ = v___x_1862_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v___x_1873_);
lean_ctor_set(v_reuseFailAlloc_1876_, 1, v_snd_1860_);
v___x_1875_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
return v___x_1875_;
}
}
}
}
}
}
}
case 8:
{
lean_object* v_declName_1882_; lean_object* v_type_1883_; lean_object* v_value_1884_; lean_object* v_body_1885_; uint8_t v_nondep_1886_; lean_object* v___x_1887_; lean_object* v_fst_1888_; lean_object* v_snd_1889_; lean_object* v_fst_1890_; lean_object* v_snd_1891_; lean_object* v___x_1892_; lean_object* v_fst_1893_; lean_object* v_snd_1894_; lean_object* v_fst_1895_; lean_object* v_snd_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v_fst_1900_; lean_object* v_snd_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1924_; 
v_declName_1882_ = lean_ctor_get(v_e_1802_, 0);
v_type_1883_ = lean_ctor_get(v_e_1802_, 1);
v_value_1884_ = lean_ctor_get(v_e_1802_, 2);
v_body_1885_ = lean_ctor_get(v_e_1802_, 3);
v_nondep_1886_ = lean_ctor_get_uint8(v_e_1802_, sizeof(void*)*4 + 8);
lean_inc(v_offset_1803_);
lean_inc_ref(v_type_1883_);
v___x_1887_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1801_, v_type_1883_, v_offset_1803_, v_a_1804_, v_a_1805_, v_a_1806_);
v_fst_1888_ = lean_ctor_get(v___x_1887_, 0);
lean_inc(v_fst_1888_);
v_snd_1889_ = lean_ctor_get(v___x_1887_, 1);
lean_inc(v_snd_1889_);
lean_dec_ref(v___x_1887_);
v_fst_1890_ = lean_ctor_get(v_fst_1888_, 0);
lean_inc(v_fst_1890_);
v_snd_1891_ = lean_ctor_get(v_fst_1888_, 1);
lean_inc(v_snd_1891_);
lean_dec(v_fst_1888_);
lean_inc(v_offset_1803_);
lean_inc_ref(v_value_1884_);
v___x_1892_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1801_, v_value_1884_, v_offset_1803_, v_snd_1891_, v_a_1805_, v_snd_1889_);
v_fst_1893_ = lean_ctor_get(v___x_1892_, 0);
lean_inc(v_fst_1893_);
v_snd_1894_ = lean_ctor_get(v___x_1892_, 1);
lean_inc(v_snd_1894_);
lean_dec_ref(v___x_1892_);
v_fst_1895_ = lean_ctor_get(v_fst_1893_, 0);
lean_inc(v_fst_1895_);
v_snd_1896_ = lean_ctor_get(v_fst_1893_, 1);
lean_inc(v_snd_1896_);
lean_dec(v_fst_1893_);
v___x_1897_ = lean_unsigned_to_nat(1u);
v___x_1898_ = lean_nat_add(v_offset_1803_, v___x_1897_);
lean_dec(v_offset_1803_);
lean_inc_ref(v_body_1885_);
v___x_1899_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1801_, v_body_1885_, v___x_1898_, v_snd_1896_, v_a_1805_, v_snd_1894_);
v_fst_1900_ = lean_ctor_get(v___x_1899_, 0);
v_snd_1901_ = lean_ctor_get(v___x_1899_, 1);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1903_ = v___x_1899_;
v_isShared_1904_ = v_isSharedCheck_1924_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_snd_1901_);
lean_inc(v_fst_1900_);
lean_dec(v___x_1899_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1924_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v_fst_1905_; lean_object* v_snd_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1923_; 
v_fst_1905_ = lean_ctor_get(v_fst_1900_, 0);
v_snd_1906_ = lean_ctor_get(v_fst_1900_, 1);
v_isSharedCheck_1923_ = !lean_is_exclusive(v_fst_1900_);
if (v_isSharedCheck_1923_ == 0)
{
v___x_1908_ = v_fst_1900_;
v_isShared_1909_ = v_isSharedCheck_1923_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_snd_1906_);
lean_inc(v_fst_1905_);
lean_dec(v_fst_1900_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1923_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
uint8_t v___y_1911_; uint8_t v___x_1921_; 
v___x_1921_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_type_1883_, v_fst_1890_);
if (v___x_1921_ == 0)
{
v___y_1911_ = v___x_1921_;
goto v___jp_1910_;
}
else
{
uint8_t v___x_1922_; 
v___x_1922_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_value_1884_, v_fst_1895_);
v___y_1911_ = v___x_1922_;
goto v___jp_1910_;
}
v___jp_1910_:
{
if (v___y_1911_ == 0)
{
lean_object* v___x_1912_; 
lean_inc(v_declName_1882_);
lean_del_object(v___x_1908_);
lean_del_object(v___x_1903_);
lean_dec_ref(v_e_1802_);
v___x_1912_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6(v_declName_1882_, v_fst_1890_, v_fst_1895_, v_fst_1905_, v_nondep_1886_, v_snd_1906_, v_a_1805_, v_snd_1901_);
return v___x_1912_;
}
else
{
uint8_t v___x_1913_; 
v___x_1913_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1885_, v_fst_1905_);
if (v___x_1913_ == 0)
{
lean_object* v___x_1914_; 
lean_inc(v_declName_1882_);
lean_del_object(v___x_1908_);
lean_del_object(v___x_1903_);
lean_dec_ref(v_e_1802_);
v___x_1914_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6(v_declName_1882_, v_fst_1890_, v_fst_1895_, v_fst_1905_, v_nondep_1886_, v_snd_1906_, v_a_1805_, v_snd_1901_);
return v___x_1914_;
}
else
{
lean_object* v___x_1916_; 
lean_dec(v_fst_1905_);
lean_dec(v_fst_1895_);
lean_dec(v_fst_1890_);
if (v_isShared_1909_ == 0)
{
lean_ctor_set(v___x_1908_, 0, v_e_1802_);
v___x_1916_ = v___x_1908_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_e_1802_);
lean_ctor_set(v_reuseFailAlloc_1920_, 1, v_snd_1906_);
v___x_1916_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
lean_object* v___x_1918_; 
if (v_isShared_1904_ == 0)
{
lean_ctor_set(v___x_1903_, 0, v___x_1916_);
v___x_1918_ = v___x_1903_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v___x_1916_);
lean_ctor_set(v_reuseFailAlloc_1919_, 1, v_snd_1901_);
v___x_1918_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
return v___x_1918_;
}
}
}
}
}
}
}
}
case 10:
{
lean_object* v_data_1925_; lean_object* v_expr_1926_; lean_object* v___x_1927_; lean_object* v_fst_1928_; lean_object* v_snd_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1947_; 
v_data_1925_ = lean_ctor_get(v_e_1802_, 0);
v_expr_1926_ = lean_ctor_get(v_e_1802_, 1);
lean_inc_ref(v_expr_1926_);
v___x_1927_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1801_, v_expr_1926_, v_offset_1803_, v_a_1804_, v_a_1805_, v_a_1806_);
v_fst_1928_ = lean_ctor_get(v___x_1927_, 0);
v_snd_1929_ = lean_ctor_get(v___x_1927_, 1);
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1931_ = v___x_1927_;
v_isShared_1932_ = v_isSharedCheck_1947_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_snd_1929_);
lean_inc(v_fst_1928_);
lean_dec(v___x_1927_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1947_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v_fst_1933_; lean_object* v_snd_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1946_; 
v_fst_1933_ = lean_ctor_get(v_fst_1928_, 0);
v_snd_1934_ = lean_ctor_get(v_fst_1928_, 1);
v_isSharedCheck_1946_ = !lean_is_exclusive(v_fst_1928_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1936_ = v_fst_1928_;
v_isShared_1937_ = v_isSharedCheck_1946_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_snd_1934_);
lean_inc(v_fst_1933_);
lean_dec(v_fst_1928_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1946_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
uint8_t v___x_1938_; 
v___x_1938_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_expr_1926_, v_fst_1933_);
if (v___x_1938_ == 0)
{
lean_object* v___x_1939_; 
lean_inc(v_data_1925_);
lean_del_object(v___x_1936_);
lean_del_object(v___x_1931_);
lean_dec_ref(v_e_1802_);
v___x_1939_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__7(v_data_1925_, v_fst_1933_, v_snd_1934_, v_a_1805_, v_snd_1929_);
return v___x_1939_;
}
else
{
lean_object* v___x_1941_; 
lean_dec(v_fst_1933_);
if (v_isShared_1937_ == 0)
{
lean_ctor_set(v___x_1936_, 0, v_e_1802_);
v___x_1941_ = v___x_1936_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_e_1802_);
lean_ctor_set(v_reuseFailAlloc_1945_, 1, v_snd_1934_);
v___x_1941_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
lean_object* v___x_1943_; 
if (v_isShared_1932_ == 0)
{
lean_ctor_set(v___x_1931_, 0, v___x_1941_);
v___x_1943_ = v___x_1931_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v___x_1941_);
lean_ctor_set(v_reuseFailAlloc_1944_, 1, v_snd_1929_);
v___x_1943_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
return v___x_1943_;
}
}
}
}
}
}
case 11:
{
lean_object* v_typeName_1948_; lean_object* v_idx_1949_; lean_object* v_struct_1950_; lean_object* v___x_1951_; lean_object* v_fst_1952_; lean_object* v_snd_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1971_; 
v_typeName_1948_ = lean_ctor_get(v_e_1802_, 0);
v_idx_1949_ = lean_ctor_get(v_e_1802_, 1);
v_struct_1950_ = lean_ctor_get(v_e_1802_, 2);
lean_inc_ref(v_struct_1950_);
v___x_1951_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1801_, v_struct_1950_, v_offset_1803_, v_a_1804_, v_a_1805_, v_a_1806_);
v_fst_1952_ = lean_ctor_get(v___x_1951_, 0);
v_snd_1953_ = lean_ctor_get(v___x_1951_, 1);
v_isSharedCheck_1971_ = !lean_is_exclusive(v___x_1951_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1955_ = v___x_1951_;
v_isShared_1956_ = v_isSharedCheck_1971_;
goto v_resetjp_1954_;
}
else
{
lean_inc(v_snd_1953_);
lean_inc(v_fst_1952_);
lean_dec(v___x_1951_);
v___x_1955_ = lean_box(0);
v_isShared_1956_ = v_isSharedCheck_1971_;
goto v_resetjp_1954_;
}
v_resetjp_1954_:
{
lean_object* v_fst_1957_; lean_object* v_snd_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1970_; 
v_fst_1957_ = lean_ctor_get(v_fst_1952_, 0);
v_snd_1958_ = lean_ctor_get(v_fst_1952_, 1);
v_isSharedCheck_1970_ = !lean_is_exclusive(v_fst_1952_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1960_ = v_fst_1952_;
v_isShared_1961_ = v_isSharedCheck_1970_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_snd_1958_);
lean_inc(v_fst_1957_);
lean_dec(v_fst_1952_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1970_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
uint8_t v___x_1962_; 
v___x_1962_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_1950_, v_fst_1957_);
if (v___x_1962_ == 0)
{
lean_object* v___x_1963_; 
lean_inc(v_idx_1949_);
lean_inc(v_typeName_1948_);
lean_del_object(v___x_1960_);
lean_del_object(v___x_1955_);
lean_dec_ref(v_e_1802_);
v___x_1963_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__8(v_typeName_1948_, v_idx_1949_, v_fst_1957_, v_snd_1958_, v_a_1805_, v_snd_1953_);
return v___x_1963_;
}
else
{
lean_object* v___x_1965_; 
lean_dec(v_fst_1957_);
if (v_isShared_1961_ == 0)
{
lean_ctor_set(v___x_1960_, 0, v_e_1802_);
v___x_1965_ = v___x_1960_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v_e_1802_);
lean_ctor_set(v_reuseFailAlloc_1969_, 1, v_snd_1958_);
v___x_1965_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
lean_object* v___x_1967_; 
if (v_isShared_1956_ == 0)
{
lean_ctor_set(v___x_1955_, 0, v___x_1965_);
v___x_1967_ = v___x_1955_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v___x_1965_);
lean_ctor_set(v_reuseFailAlloc_1968_, 1, v_snd_1953_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_1972_; lean_object* v___x_1973_; 
lean_dec(v_offset_1803_);
lean_dec_ref(v_e_1802_);
v___x_1972_ = lean_obj_once(&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__1, &l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__1_once, _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__1);
v___x_1973_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9(v___x_1972_, v_a_1804_, v_a_1805_, v_a_1806_);
return v___x_1973_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(lean_object* v_subst_1974_, lean_object* v_e_1975_, lean_object* v_offset_1976_, lean_object* v_a_1977_, uint8_t v_a_1978_, lean_object* v_a_1979_){
_start:
{
lean_object* v___x_1980_; uint8_t v___x_1981_; 
v___x_1980_ = l_Lean_Expr_looseBVarRange(v_e_1975_);
v___x_1981_ = lean_nat_dec_le(v___x_1980_, v_offset_1976_);
lean_dec(v___x_1980_);
if (v___x_1981_ == 0)
{
lean_object* v_key_1982_; lean_object* v___x_1983_; 
lean_inc(v_offset_1976_);
lean_inc_ref(v_e_1975_);
v_key_1982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1982_, 0, v_e_1975_);
lean_ctor_set(v_key_1982_, 1, v_offset_1976_);
v___x_1983_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___redArg(v_a_1977_, v_key_1982_);
if (lean_obj_tag(v___x_1983_) == 1)
{
lean_object* v_val_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; 
lean_dec_ref(v_key_1982_);
lean_dec(v_offset_1976_);
lean_dec_ref(v_e_1975_);
v_val_1984_ = lean_ctor_get(v___x_1983_, 0);
lean_inc(v_val_1984_);
lean_dec_ref(v___x_1983_);
v___x_1985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1985_, 0, v_val_1984_);
lean_ctor_set(v___x_1985_, 1, v_a_1977_);
v___x_1986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1986_, 0, v___x_1985_);
lean_ctor_set(v___x_1986_, 1, v_a_1979_);
return v___x_1986_;
}
else
{
lean_dec(v___x_1983_);
switch(lean_obj_tag(v_e_1975_))
{
case 0:
{
lean_object* v_deBruijnIndex_1987_; lean_object* v___x_1988_; lean_object* v_fst_1989_; lean_object* v_snd_1990_; lean_object* v_fst_1991_; lean_object* v_snd_1992_; lean_object* v___x_1993_; 
v_deBruijnIndex_1987_ = lean_ctor_get(v_e_1975_, 0);
lean_inc(v_deBruijnIndex_1987_);
v___x_1988_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(v_subst_1974_, v_e_1975_, v_deBruijnIndex_1987_, v_offset_1976_, v_a_1977_, v_a_1978_, v_a_1979_);
lean_dec(v_offset_1976_);
lean_dec(v_deBruijnIndex_1987_);
v_fst_1989_ = lean_ctor_get(v___x_1988_, 0);
lean_inc(v_fst_1989_);
v_snd_1990_ = lean_ctor_get(v___x_1988_, 1);
lean_inc(v_snd_1990_);
lean_dec_ref(v___x_1988_);
v_fst_1991_ = lean_ctor_get(v_fst_1989_, 0);
lean_inc(v_fst_1991_);
v_snd_1992_ = lean_ctor_get(v_fst_1989_, 1);
lean_inc(v_snd_1992_);
lean_dec(v_fst_1989_);
v___x_1993_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_1982_, v_fst_1991_, v_snd_1992_, v_snd_1990_);
return v___x_1993_;
}
case 9:
{
lean_object* v___x_1994_; 
lean_dec(v_offset_1976_);
v___x_1994_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_1982_, v_e_1975_, v_a_1977_, v_a_1979_);
return v___x_1994_;
}
case 2:
{
lean_object* v___x_1995_; 
lean_dec(v_offset_1976_);
v___x_1995_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_1982_, v_e_1975_, v_a_1977_, v_a_1979_);
return v___x_1995_;
}
case 1:
{
lean_object* v___x_1996_; 
lean_dec(v_offset_1976_);
v___x_1996_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_1982_, v_e_1975_, v_a_1977_, v_a_1979_);
return v___x_1996_;
}
case 4:
{
lean_object* v___x_1997_; 
lean_dec(v_offset_1976_);
v___x_1997_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_1982_, v_e_1975_, v_a_1977_, v_a_1979_);
return v___x_1997_;
}
case 3:
{
lean_object* v___x_1998_; 
lean_dec(v_offset_1976_);
v___x_1998_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_1982_, v_e_1975_, v_a_1977_, v_a_1979_);
return v___x_1998_;
}
default: 
{
lean_object* v___x_1999_; lean_object* v_fst_2000_; lean_object* v_snd_2001_; lean_object* v_fst_2002_; lean_object* v_snd_2003_; lean_object* v___x_2004_; 
v___x_1999_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit(v_subst_1974_, v_e_1975_, v_offset_1976_, v_a_1977_, v_a_1978_, v_a_1979_);
v_fst_2000_ = lean_ctor_get(v___x_1999_, 0);
lean_inc(v_fst_2000_);
v_snd_2001_ = lean_ctor_get(v___x_1999_, 1);
lean_inc(v_snd_2001_);
lean_dec_ref(v___x_1999_);
v_fst_2002_ = lean_ctor_get(v_fst_2000_, 0);
lean_inc(v_fst_2002_);
v_snd_2003_ = lean_ctor_get(v_fst_2000_, 1);
lean_inc(v_snd_2003_);
lean_dec(v_fst_2000_);
v___x_2004_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_1982_, v_fst_2002_, v_snd_2003_, v_snd_2001_);
return v___x_2004_;
}
}
}
}
else
{
lean_object* v___x_2005_; lean_object* v___x_2006_; 
lean_dec(v_offset_1976_);
v___x_2005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2005_, 0, v_e_1975_);
lean_ctor_set(v___x_2005_, 1, v_a_1977_);
v___x_2006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2006_, 0, v___x_2005_);
lean_ctor_set(v___x_2006_, 1, v_a_1979_);
return v___x_2006_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault(lean_object* v_subst_2007_, lean_object* v_e_2008_, lean_object* v_offset_2009_, lean_object* v_a_2010_, uint8_t v_a_2011_, lean_object* v_a_2012_){
_start:
{
if (lean_obj_tag(v_e_2008_) == 5)
{
lean_object* v_fn_2013_; lean_object* v_arg_2014_; lean_object* v_key_2015_; lean_object* v___x_2016_; 
v_fn_2013_ = lean_ctor_get(v_e_2008_, 0);
v_arg_2014_ = lean_ctor_get(v_e_2008_, 1);
lean_inc(v_offset_2009_);
lean_inc_ref(v_e_2008_);
v_key_2015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_2015_, 0, v_e_2008_);
lean_ctor_set(v_key_2015_, 1, v_offset_2009_);
v___x_2016_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___redArg(v_a_2010_, v_key_2015_);
if (lean_obj_tag(v___x_2016_) == 1)
{
lean_object* v_val_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; 
lean_dec_ref(v_key_2015_);
lean_dec_ref(v_e_2008_);
lean_dec(v_offset_2009_);
v_val_2017_ = lean_ctor_get(v___x_2016_, 0);
lean_inc(v_val_2017_);
lean_dec_ref(v___x_2016_);
v___x_2018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2018_, 0, v_val_2017_);
lean_ctor_set(v___x_2018_, 1, v_a_2010_);
v___x_2019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2019_, 0, v___x_2018_);
lean_ctor_set(v___x_2019_, 1, v_a_2012_);
return v___x_2019_;
}
else
{
lean_object* v___x_2020_; lean_object* v_fst_2021_; lean_object* v_snd_2022_; lean_object* v_fst_2023_; lean_object* v_snd_2024_; lean_object* v___x_2025_; lean_object* v_fst_2026_; lean_object* v_snd_2027_; lean_object* v_fst_2028_; lean_object* v_snd_2029_; uint8_t v___y_2031_; uint8_t v___x_2039_; 
lean_dec(v___x_2016_);
lean_inc(v_offset_2009_);
lean_inc_ref(v_fn_2013_);
v___x_2020_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault(v_subst_2007_, v_fn_2013_, v_offset_2009_, v_a_2010_, v_a_2011_, v_a_2012_);
v_fst_2021_ = lean_ctor_get(v___x_2020_, 0);
lean_inc(v_fst_2021_);
v_snd_2022_ = lean_ctor_get(v___x_2020_, 1);
lean_inc(v_snd_2022_);
lean_dec_ref(v___x_2020_);
v_fst_2023_ = lean_ctor_get(v_fst_2021_, 0);
lean_inc(v_fst_2023_);
v_snd_2024_ = lean_ctor_get(v_fst_2021_, 1);
lean_inc(v_snd_2024_);
lean_dec(v_fst_2021_);
lean_inc_ref(v_arg_2014_);
v___x_2025_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_2007_, v_arg_2014_, v_offset_2009_, v_snd_2024_, v_a_2011_, v_snd_2022_);
v_fst_2026_ = lean_ctor_get(v___x_2025_, 0);
lean_inc(v_fst_2026_);
v_snd_2027_ = lean_ctor_get(v___x_2025_, 1);
lean_inc(v_snd_2027_);
lean_dec_ref(v___x_2025_);
v_fst_2028_ = lean_ctor_get(v_fst_2026_, 0);
lean_inc(v_fst_2028_);
v_snd_2029_ = lean_ctor_get(v_fst_2026_, 1);
lean_inc(v_snd_2029_);
lean_dec(v_fst_2026_);
v___x_2039_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_2013_, v_fst_2023_);
if (v___x_2039_ == 0)
{
v___y_2031_ = v___x_2039_;
goto v___jp_2030_;
}
else
{
uint8_t v___x_2040_; 
v___x_2040_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_2014_, v_fst_2028_);
v___y_2031_ = v___x_2040_;
goto v___jp_2030_;
}
v___jp_2030_:
{
if (v___y_2031_ == 0)
{
lean_object* v___x_2032_; lean_object* v_fst_2033_; lean_object* v_snd_2034_; lean_object* v_fst_2035_; lean_object* v_snd_2036_; lean_object* v___x_2037_; 
lean_dec_ref(v_e_2008_);
v___x_2032_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__3(v_fst_2023_, v_fst_2028_, v_snd_2029_, v_a_2011_, v_snd_2027_);
v_fst_2033_ = lean_ctor_get(v___x_2032_, 0);
lean_inc(v_fst_2033_);
v_snd_2034_ = lean_ctor_get(v___x_2032_, 1);
lean_inc(v_snd_2034_);
lean_dec_ref(v___x_2032_);
v_fst_2035_ = lean_ctor_get(v_fst_2033_, 0);
lean_inc(v_fst_2035_);
v_snd_2036_ = lean_ctor_get(v_fst_2033_, 1);
lean_inc(v_snd_2036_);
lean_dec(v_fst_2033_);
v___x_2037_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_2015_, v_fst_2035_, v_snd_2036_, v_snd_2034_);
return v___x_2037_;
}
else
{
lean_object* v___x_2038_; 
lean_dec(v_fst_2028_);
lean_dec(v_fst_2023_);
v___x_2038_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_2015_, v_e_2008_, v_snd_2029_, v_snd_2027_);
return v___x_2038_;
}
}
}
}
else
{
lean_object* v___x_2041_; 
v___x_2041_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_2007_, v_e_2008_, v_offset_2009_, v_a_2010_, v_a_2011_, v_a_2012_);
return v___x_2041_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault___boxed(lean_object* v_subst_2042_, lean_object* v_e_2043_, lean_object* v_offset_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_){
_start:
{
uint8_t v_a_17006__boxed_2048_; lean_object* v_res_2049_; 
v_a_17006__boxed_2048_ = lean_unbox(v_a_2046_);
v_res_2049_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault(v_subst_2042_, v_e_2043_, v_offset_2044_, v_a_2045_, v_a_17006__boxed_2048_, v_a_2047_);
lean_dec_ref(v_subst_2042_);
return v_res_2049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild___boxed(lean_object* v_subst_2050_, lean_object* v_e_2051_, lean_object* v_offset_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_){
_start:
{
uint8_t v_a_17037__boxed_2056_; lean_object* v_res_2057_; 
v_a_17037__boxed_2056_ = lean_unbox(v_a_2054_);
v_res_2057_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_2050_, v_e_2051_, v_offset_2052_, v_a_2053_, v_a_17037__boxed_2056_, v_a_2055_);
lean_dec_ref(v_subst_2050_);
return v_res_2057_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___boxed(lean_object* v_subst_2058_, lean_object* v_e_2059_, lean_object* v_f_2060_, lean_object* v_arg_2061_, lean_object* v_offset_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_){
_start:
{
uint8_t v_a_17081__boxed_2066_; lean_object* v_res_2067_; 
v_a_17081__boxed_2066_ = lean_unbox(v_a_2064_);
v_res_2067_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg(v_subst_2058_, v_e_2059_, v_f_2060_, v_arg_2061_, v_offset_2062_, v_a_2063_, v_a_17081__boxed_2066_, v_a_2065_);
lean_dec_ref(v_subst_2058_);
return v_res_2067_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___boxed(lean_object* v_subst_2068_, lean_object* v_e_2069_, lean_object* v_f_2070_, lean_object* v_argsRev_2071_, lean_object* v_offset_2072_, lean_object* v_modified_2073_, lean_object* v_a_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_){
_start:
{
uint8_t v_modified_boxed_2077_; uint8_t v_a_17121__boxed_2078_; lean_object* v_res_2079_; 
v_modified_boxed_2077_ = lean_unbox(v_modified_2073_);
v_a_17121__boxed_2078_ = lean_unbox(v_a_2075_);
v_res_2079_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta(v_subst_2068_, v_e_2069_, v_f_2070_, v_argsRev_2071_, v_offset_2072_, v_modified_boxed_2077_, v_a_2074_, v_a_17121__boxed_2078_, v_a_2076_);
lean_dec_ref(v_subst_2068_);
return v_res_2079_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___boxed(lean_object* v_subst_2080_, lean_object* v_e_2081_, lean_object* v_offset_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_){
_start:
{
uint8_t v_a_17161__boxed_2086_; lean_object* v_res_2087_; 
v_a_17161__boxed_2086_ = lean_unbox(v_a_2084_);
v_res_2087_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit(v_subst_2080_, v_e_2081_, v_offset_2082_, v_a_2083_, v_a_17161__boxed_2086_, v_a_2085_);
lean_dec_ref(v_subst_2080_);
return v_res_2087_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp(lean_object* v_subst_2088_, lean_object* v_e_2089_, lean_object* v_f_2090_, lean_object* v_arg_2091_, lean_object* v_offset_2092_, lean_object* v_x_2093_, lean_object* v_a_2094_, uint8_t v_a_2095_, lean_object* v_a_2096_){
_start:
{
lean_object* v___x_2097_; 
v___x_2097_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg(v_subst_2088_, v_e_2089_, v_f_2090_, v_arg_2091_, v_offset_2092_, v_a_2094_, v_a_2095_, v_a_2096_);
return v___x_2097_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___boxed(lean_object* v_subst_2098_, lean_object* v_e_2099_, lean_object* v_f_2100_, lean_object* v_arg_2101_, lean_object* v_offset_2102_, lean_object* v_x_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_){
_start:
{
uint8_t v_a_17726__boxed_2107_; lean_object* v_res_2108_; 
v_a_17726__boxed_2107_ = lean_unbox(v_a_2105_);
v_res_2108_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp(v_subst_2098_, v_e_2099_, v_f_2100_, v_arg_2101_, v_offset_2102_, v_x_2103_, v_a_2104_, v_a_17726__boxed_2107_, v_a_2106_);
lean_dec_ref(v_subst_2098_);
return v_res_2108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27(lean_object* v_e_2109_, lean_object* v_subst_2110_, uint8_t v_a_2111_, lean_object* v_a_2112_){
_start:
{
uint8_t v___y_2114_; lean_object* v___x_2130_; lean_object* v___x_2131_; uint8_t v___x_2132_; 
v___x_2130_ = lean_array_get_size(v_subst_2110_);
v___x_2131_ = lean_unsigned_to_nat(0u);
v___x_2132_ = lean_nat_dec_eq(v___x_2130_, v___x_2131_);
if (v___x_2132_ == 0)
{
uint8_t v___x_2133_; 
v___x_2133_ = l_Lean_Expr_hasLooseBVars(v_e_2109_);
if (v___x_2133_ == 0)
{
lean_object* v___x_2134_; 
v___x_2134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2134_, 0, v_e_2109_);
lean_ctor_set(v___x_2134_, 1, v_a_2112_);
return v___x_2134_;
}
else
{
v___y_2114_ = v___x_2132_;
goto v___jp_2113_;
}
}
else
{
v___y_2114_ = v___x_2132_;
goto v___jp_2113_;
}
v___jp_2113_:
{
if (v___y_2114_ == 0)
{
lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v_fst_2118_; lean_object* v_snd_2119_; lean_object* v_fst_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2127_; 
v___x_2115_ = lean_unsigned_to_nat(0u);
v___x_2116_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__2, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__2_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__2);
v___x_2117_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit(v_subst_2110_, v_e_2109_, v___x_2115_, v___x_2116_, v_a_2111_, v_a_2112_);
v_fst_2118_ = lean_ctor_get(v___x_2117_, 0);
lean_inc(v_fst_2118_);
v_snd_2119_ = lean_ctor_get(v___x_2117_, 1);
lean_inc(v_snd_2119_);
lean_dec_ref(v___x_2117_);
v_fst_2120_ = lean_ctor_get(v_fst_2118_, 0);
v_isSharedCheck_2127_ = !lean_is_exclusive(v_fst_2118_);
if (v_isSharedCheck_2127_ == 0)
{
lean_object* v_unused_2128_; 
v_unused_2128_ = lean_ctor_get(v_fst_2118_, 1);
lean_dec(v_unused_2128_);
v___x_2122_ = v_fst_2118_;
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_fst_2120_);
lean_dec(v_fst_2118_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___x_2125_; 
if (v_isShared_2123_ == 0)
{
lean_ctor_set(v___x_2122_, 1, v_snd_2119_);
v___x_2125_ = v___x_2122_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_fst_2120_);
lean_ctor_set(v_reuseFailAlloc_2126_, 1, v_snd_2119_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
}
else
{
lean_object* v___x_2129_; 
v___x_2129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2129_, 0, v_e_2109_);
lean_ctor_set(v___x_2129_, 1, v_a_2112_);
return v___x_2129_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27___boxed(lean_object* v_e_2135_, lean_object* v_subst_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_){
_start:
{
uint8_t v_a_594__boxed_2139_; lean_object* v_res_2140_; 
v_a_594__boxed_2139_ = lean_unbox(v_a_2137_);
v_res_2140_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27(v_e_2135_, v_subst_2136_, v_a_594__boxed_2139_, v_a_2138_);
lean_dec_ref(v_subst_2136_);
return v_res_2140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevBetaS___redArg(lean_object* v_e_2141_, lean_object* v_subst_2142_, lean_object* v_a_2143_){
_start:
{
uint8_t v___x_2145_; 
v___x_2145_ = l_Lean_Expr_hasLooseBVars(v_e_2141_);
if (v___x_2145_ == 0)
{
lean_object* v___x_2146_; 
v___x_2146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2146_, 0, v_e_2141_);
return v___x_2146_;
}
else
{
lean_object* v___x_2147_; lean_object* v___x_2148_; uint8_t v___x_2149_; 
v___x_2147_ = lean_array_get_size(v_subst_2142_);
v___x_2148_ = lean_unsigned_to_nat(0u);
v___x_2149_ = lean_nat_dec_eq(v___x_2147_, v___x_2148_);
if (v___x_2149_ == 0)
{
lean_object* v___x_2150_; lean_object* v_share_2151_; lean_object* v_maxFVar_2152_; lean_object* v_proofInstInfo_2153_; lean_object* v_inferType_2154_; lean_object* v_getLevel_2155_; lean_object* v_congrInfo_2156_; lean_object* v_defEqI_2157_; uint8_t v_debug_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2190_; 
v___x_2150_ = lean_st_ref_take(v_a_2143_);
v_share_2151_ = lean_ctor_get(v___x_2150_, 0);
v_maxFVar_2152_ = lean_ctor_get(v___x_2150_, 1);
v_proofInstInfo_2153_ = lean_ctor_get(v___x_2150_, 2);
v_inferType_2154_ = lean_ctor_get(v___x_2150_, 3);
v_getLevel_2155_ = lean_ctor_get(v___x_2150_, 4);
v_congrInfo_2156_ = lean_ctor_get(v___x_2150_, 5);
v_defEqI_2157_ = lean_ctor_get(v___x_2150_, 6);
v_debug_2158_ = lean_ctor_get_uint8(v___x_2150_, sizeof(void*)*7);
v_isSharedCheck_2190_ = !lean_is_exclusive(v___x_2150_);
if (v_isSharedCheck_2190_ == 0)
{
v___x_2160_ = v___x_2150_;
v_isShared_2161_ = v_isSharedCheck_2190_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_defEqI_2157_);
lean_inc(v_congrInfo_2156_);
lean_inc(v_getLevel_2155_);
lean_inc(v_inferType_2154_);
lean_inc(v_proofInstInfo_2153_);
lean_inc(v_maxFVar_2152_);
lean_inc(v_share_2151_);
lean_dec(v___x_2150_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2190_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v___x_2162_; lean_object* v___x_2164_; 
v___x_2162_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__0, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__0_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__0);
if (v_isShared_2161_ == 0)
{
lean_ctor_set(v___x_2160_, 0, v___x_2162_);
v___x_2164_ = v___x_2160_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v___x_2162_);
lean_ctor_set(v_reuseFailAlloc_2189_, 1, v_maxFVar_2152_);
lean_ctor_set(v_reuseFailAlloc_2189_, 2, v_proofInstInfo_2153_);
lean_ctor_set(v_reuseFailAlloc_2189_, 3, v_inferType_2154_);
lean_ctor_set(v_reuseFailAlloc_2189_, 4, v_getLevel_2155_);
lean_ctor_set(v_reuseFailAlloc_2189_, 5, v_congrInfo_2156_);
lean_ctor_set(v_reuseFailAlloc_2189_, 6, v_defEqI_2157_);
lean_ctor_set_uint8(v_reuseFailAlloc_2189_, sizeof(void*)*7, v_debug_2158_);
v___x_2164_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
lean_object* v___x_2165_; lean_object* v___x_2166_; uint8_t v_debug_2167_; lean_object* v___x_2168_; lean_object* v_fst_2169_; lean_object* v_snd_2170_; lean_object* v___x_2171_; lean_object* v_maxFVar_2172_; lean_object* v_proofInstInfo_2173_; lean_object* v_inferType_2174_; lean_object* v_getLevel_2175_; lean_object* v_congrInfo_2176_; lean_object* v_defEqI_2177_; uint8_t v_debug_2178_; lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2187_; 
v___x_2165_ = lean_st_ref_set(v_a_2143_, v___x_2164_);
v___x_2166_ = lean_st_ref_get(v_a_2143_);
v_debug_2167_ = lean_ctor_get_uint8(v___x_2166_, sizeof(void*)*7);
lean_dec(v___x_2166_);
v___x_2168_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27(v_e_2141_, v_subst_2142_, v_debug_2167_, v_share_2151_);
v_fst_2169_ = lean_ctor_get(v___x_2168_, 0);
lean_inc(v_fst_2169_);
v_snd_2170_ = lean_ctor_get(v___x_2168_, 1);
lean_inc(v_snd_2170_);
lean_dec_ref(v___x_2168_);
v___x_2171_ = lean_st_ref_take(v_a_2143_);
v_maxFVar_2172_ = lean_ctor_get(v___x_2171_, 1);
v_proofInstInfo_2173_ = lean_ctor_get(v___x_2171_, 2);
v_inferType_2174_ = lean_ctor_get(v___x_2171_, 3);
v_getLevel_2175_ = lean_ctor_get(v___x_2171_, 4);
v_congrInfo_2176_ = lean_ctor_get(v___x_2171_, 5);
v_defEqI_2177_ = lean_ctor_get(v___x_2171_, 6);
v_debug_2178_ = lean_ctor_get_uint8(v___x_2171_, sizeof(void*)*7);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2171_);
if (v_isSharedCheck_2187_ == 0)
{
lean_object* v_unused_2188_; 
v_unused_2188_ = lean_ctor_get(v___x_2171_, 0);
lean_dec(v_unused_2188_);
v___x_2180_ = v___x_2171_;
v_isShared_2181_ = v_isSharedCheck_2187_;
goto v_resetjp_2179_;
}
else
{
lean_inc(v_defEqI_2177_);
lean_inc(v_congrInfo_2176_);
lean_inc(v_getLevel_2175_);
lean_inc(v_inferType_2174_);
lean_inc(v_proofInstInfo_2173_);
lean_inc(v_maxFVar_2172_);
lean_dec(v___x_2171_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2187_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
lean_object* v___x_2183_; 
if (v_isShared_2181_ == 0)
{
lean_ctor_set(v___x_2180_, 0, v_snd_2170_);
v___x_2183_ = v___x_2180_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_snd_2170_);
lean_ctor_set(v_reuseFailAlloc_2186_, 1, v_maxFVar_2172_);
lean_ctor_set(v_reuseFailAlloc_2186_, 2, v_proofInstInfo_2173_);
lean_ctor_set(v_reuseFailAlloc_2186_, 3, v_inferType_2174_);
lean_ctor_set(v_reuseFailAlloc_2186_, 4, v_getLevel_2175_);
lean_ctor_set(v_reuseFailAlloc_2186_, 5, v_congrInfo_2176_);
lean_ctor_set(v_reuseFailAlloc_2186_, 6, v_defEqI_2177_);
lean_ctor_set_uint8(v_reuseFailAlloc_2186_, sizeof(void*)*7, v_debug_2178_);
v___x_2183_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
lean_object* v___x_2184_; lean_object* v___x_2185_; 
v___x_2184_ = lean_st_ref_set(v_a_2143_, v___x_2183_);
v___x_2185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2185_, 0, v_fst_2169_);
return v___x_2185_;
}
}
}
}
}
else
{
lean_object* v___x_2191_; 
v___x_2191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2191_, 0, v_e_2141_);
return v___x_2191_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevBetaS___redArg___boxed(lean_object* v_e_2192_, lean_object* v_subst_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_){
_start:
{
lean_object* v_res_2196_; 
v_res_2196_ = l_Lean_Meta_Sym_instantiateRevBetaS___redArg(v_e_2192_, v_subst_2193_, v_a_2194_);
lean_dec(v_a_2194_);
lean_dec_ref(v_subst_2193_);
return v_res_2196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevBetaS(lean_object* v_e_2197_, lean_object* v_subst_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_){
_start:
{
lean_object* v___x_2206_; 
v___x_2206_ = l_Lean_Meta_Sym_instantiateRevBetaS___redArg(v_e_2197_, v_subst_2198_, v_a_2200_);
return v___x_2206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevBetaS___boxed(lean_object* v_e_2207_, lean_object* v_subst_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_){
_start:
{
lean_object* v_res_2216_; 
v_res_2216_ = l_Lean_Meta_Sym_instantiateRevBetaS(v_e_2207_, v_subst_2208_, v_a_2209_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_);
lean_dec(v_a_2214_);
lean_dec_ref(v_a_2213_);
lean_dec(v_a_2212_);
lean_dec_ref(v_a_2211_);
lean_dec(v_a_2210_);
lean_dec_ref(v_a_2209_);
lean_dec_ref(v_subst_2208_);
return v_res_2216_;
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
