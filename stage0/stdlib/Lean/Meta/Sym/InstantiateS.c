// Lean compiler output
// Module: Lean.Meta.Sym.InstantiateS
// Imports: public import Lean.Meta.Sym.SymM import Lean.Meta.Sym.ReplaceS import Lean.Meta.Sym.LooseBVarsS import Init.Grind
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___closed__0;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0(lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Builder_share1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
static lean_object* l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__0;
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__1 = (const lean_object*)&l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__1_value;
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__2 = (const lean_object*)&l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__2_value;
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__3 = (const lean_object*)&l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__3_value;
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__4 = (const lean_object*)&l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__4_value;
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_Sym_Internal_Builder_assertShared(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__0_value;
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__1_value;
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__2_value;
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__3 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__3_value;
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__4 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__4_value;
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__5 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__5_value;
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__6 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__6_value;
lean_object* l_StateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__7(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4_spec__12___redArg(lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4_spec__12___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "_private.Lean.Meta.Sym.ReplaceS.0.Lean.Meta.Sym.visit"};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Meta.Sym.ReplaceS"};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__0_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_liftLooseBVarsS_x27(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Expr_looseBVarRange(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Sym_instantiateRevRangeS___closed__0;
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Sym_instantiateRevRangeS___closed__1;
static lean_object* l_Lean_Meta_Sym_instantiateRevRangeS___closed__2;
static const lean_string_object l_Lean_Meta_Sym_instantiateRevRangeS___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Lean.Meta.Sym.InstantiateS"};
static const lean_object* l_Lean_Meta_Sym_instantiateRevRangeS___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_instantiateRevRangeS___closed__3_value;
static const lean_string_object l_Lean_Meta_Sym_instantiateRevRangeS___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Lean.Meta.Sym.instantiateRevRangeS"};
static const lean_object* l_Lean_Meta_Sym_instantiateRevRangeS___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_instantiateRevRangeS___closed__4_value;
static lean_object* l_Lean_Meta_Sym_instantiateRevRangeS___closed__5;
static lean_object* l_Lean_Meta_Sym_instantiateRevRangeS___closed__6;
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 70, .m_data = "_private.Lean.Meta.Sym.InstantiateS.0.Lean.Meta.Sym.instantiateRangeS'"};
static const lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__0_value;
static lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__1;
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
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS_loop(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_go(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
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
static lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__3;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__4;
static const lean_string_object l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 86, .m_capacity = 86, .m_length = 85, .m_data = "_private.Lean.Meta.Sym.InstantiateS.0.Lean.Meta.Sym.instantiateRevBetaS'.visitAppBeta"};
static const lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__0_value;
static lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_Lean_Expr_isBVar(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "_private.Lean.Meta.Sym.InstantiateS.0.Lean.Meta.Sym.instantiateRevBetaS'.visit"};
static const lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__0_value;
static lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevBetaS___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevBetaS___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevBetaS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevBetaS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___closed__1;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Expr_bvar___override(x_1);
x_4 = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
x_5 = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1(x_1, x_4, x_3);
return x_5;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEST(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__0;
x_10 = l_ReaderT_instMonad___redArg(x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 2);
x_17 = lean_ctor_get(x_12, 3);
x_18 = lean_ctor_get(x_12, 4);
x_19 = lean_ctor_get(x_12, 1);
lean_dec(x_19);
x_20 = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__1));
x_21 = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__2));
lean_inc_ref(x_15);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_22, 0, x_15);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_23, 0, x_15);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_25, 0, x_18);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_26, 0, x_17);
x_27 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_27, 0, x_16);
lean_ctor_set(x_12, 4, x_25);
lean_ctor_set(x_12, 3, x_26);
lean_ctor_set(x_12, 2, x_27);
lean_ctor_set(x_12, 1, x_20);
lean_ctor_set(x_12, 0, x_24);
lean_ctor_set(x_10, 1, x_21);
x_28 = l_ReaderT_instMonad___redArg(x_10);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_33 = lean_ctor_get(x_30, 0);
x_34 = lean_ctor_get(x_30, 2);
x_35 = lean_ctor_get(x_30, 3);
x_36 = lean_ctor_get(x_30, 4);
x_37 = lean_ctor_get(x_30, 1);
lean_dec(x_37);
x_38 = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__3));
x_39 = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__4));
lean_inc_ref(x_33);
x_40 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_40, 0, x_33);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_41, 0, x_33);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_43, 0, x_36);
x_44 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_44, 0, x_35);
x_45 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_45, 0, x_34);
lean_ctor_set(x_30, 4, x_43);
lean_ctor_set(x_30, 3, x_44);
lean_ctor_set(x_30, 2, x_45);
lean_ctor_set(x_30, 1, x_38);
lean_ctor_set(x_30, 0, x_42);
lean_ctor_set(x_28, 1, x_39);
x_46 = l_ReaderT_instMonad___redArg(x_28);
x_47 = l_Lean_instInhabitedExpr;
x_48 = l_instInhabitedOfMonad___redArg(x_46, x_47);
x_49 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_49, 0, x_48);
x_50 = lean_panic_fn(x_49, x_1);
x_51 = lean_apply_7(x_50, x_2, x_3, x_4, x_5, x_6, x_7, lean_box(0));
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_52 = lean_ctor_get(x_30, 0);
x_53 = lean_ctor_get(x_30, 2);
x_54 = lean_ctor_get(x_30, 3);
x_55 = lean_ctor_get(x_30, 4);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_30);
x_56 = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__3));
x_57 = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__4));
lean_inc_ref(x_52);
x_58 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_58, 0, x_52);
x_59 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_59, 0, x_52);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_61, 0, x_55);
x_62 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_62, 0, x_54);
x_63 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_63, 0, x_53);
x_64 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_64, 0, x_60);
lean_ctor_set(x_64, 1, x_56);
lean_ctor_set(x_64, 2, x_63);
lean_ctor_set(x_64, 3, x_62);
lean_ctor_set(x_64, 4, x_61);
lean_ctor_set(x_28, 1, x_57);
lean_ctor_set(x_28, 0, x_64);
x_65 = l_ReaderT_instMonad___redArg(x_28);
x_66 = l_Lean_instInhabitedExpr;
x_67 = l_instInhabitedOfMonad___redArg(x_65, x_66);
x_68 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_68, 0, x_67);
x_69 = lean_panic_fn(x_68, x_1);
x_70 = lean_apply_7(x_69, x_2, x_3, x_4, x_5, x_6, x_7, lean_box(0));
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_71 = lean_ctor_get(x_28, 0);
lean_inc(x_71);
lean_dec(x_28);
x_72 = lean_ctor_get(x_71, 0);
lean_inc_ref(x_72);
x_73 = lean_ctor_get(x_71, 2);
lean_inc(x_73);
x_74 = lean_ctor_get(x_71, 3);
lean_inc(x_74);
x_75 = lean_ctor_get(x_71, 4);
lean_inc(x_75);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 lean_ctor_release(x_71, 2);
 lean_ctor_release(x_71, 3);
 lean_ctor_release(x_71, 4);
 x_76 = x_71;
} else {
 lean_dec_ref(x_71);
 x_76 = lean_box(0);
}
x_77 = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__3));
x_78 = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__4));
lean_inc_ref(x_72);
x_79 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_79, 0, x_72);
x_80 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_80, 0, x_72);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_82, 0, x_75);
x_83 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_83, 0, x_74);
x_84 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_84, 0, x_73);
if (lean_is_scalar(x_76)) {
 x_85 = lean_alloc_ctor(0, 5, 0);
} else {
 x_85 = x_76;
}
lean_ctor_set(x_85, 0, x_81);
lean_ctor_set(x_85, 1, x_77);
lean_ctor_set(x_85, 2, x_84);
lean_ctor_set(x_85, 3, x_83);
lean_ctor_set(x_85, 4, x_82);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_78);
x_87 = l_ReaderT_instMonad___redArg(x_86);
x_88 = l_Lean_instInhabitedExpr;
x_89 = l_instInhabitedOfMonad___redArg(x_87, x_88);
x_90 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_90, 0, x_89);
x_91 = lean_panic_fn(x_90, x_1);
x_92 = lean_apply_7(x_91, x_2, x_3, x_4, x_5, x_6, x_7, lean_box(0));
return x_92;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_93 = lean_ctor_get(x_12, 0);
x_94 = lean_ctor_get(x_12, 2);
x_95 = lean_ctor_get(x_12, 3);
x_96 = lean_ctor_get(x_12, 4);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_12);
x_97 = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__1));
x_98 = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__2));
lean_inc_ref(x_93);
x_99 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_99, 0, x_93);
x_100 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_100, 0, x_93);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_102, 0, x_96);
x_103 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_103, 0, x_95);
x_104 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_104, 0, x_94);
x_105 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_105, 0, x_101);
lean_ctor_set(x_105, 1, x_97);
lean_ctor_set(x_105, 2, x_104);
lean_ctor_set(x_105, 3, x_103);
lean_ctor_set(x_105, 4, x_102);
lean_ctor_set(x_10, 1, x_98);
lean_ctor_set(x_10, 0, x_105);
x_106 = l_ReaderT_instMonad___redArg(x_10);
x_107 = lean_ctor_get(x_106, 0);
lean_inc_ref(x_107);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_108 = x_106;
} else {
 lean_dec_ref(x_106);
 x_108 = lean_box(0);
}
x_109 = lean_ctor_get(x_107, 0);
lean_inc_ref(x_109);
x_110 = lean_ctor_get(x_107, 2);
lean_inc(x_110);
x_111 = lean_ctor_get(x_107, 3);
lean_inc(x_111);
x_112 = lean_ctor_get(x_107, 4);
lean_inc(x_112);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 lean_ctor_release(x_107, 2);
 lean_ctor_release(x_107, 3);
 lean_ctor_release(x_107, 4);
 x_113 = x_107;
} else {
 lean_dec_ref(x_107);
 x_113 = lean_box(0);
}
x_114 = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__3));
x_115 = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__4));
lean_inc_ref(x_109);
x_116 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_116, 0, x_109);
x_117 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_117, 0, x_109);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
x_119 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_119, 0, x_112);
x_120 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_120, 0, x_111);
x_121 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_121, 0, x_110);
if (lean_is_scalar(x_113)) {
 x_122 = lean_alloc_ctor(0, 5, 0);
} else {
 x_122 = x_113;
}
lean_ctor_set(x_122, 0, x_118);
lean_ctor_set(x_122, 1, x_114);
lean_ctor_set(x_122, 2, x_121);
lean_ctor_set(x_122, 3, x_120);
lean_ctor_set(x_122, 4, x_119);
if (lean_is_scalar(x_108)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_108;
}
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_115);
x_124 = l_ReaderT_instMonad___redArg(x_123);
x_125 = l_Lean_instInhabitedExpr;
x_126 = l_instInhabitedOfMonad___redArg(x_124, x_125);
x_127 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_127, 0, x_126);
x_128 = lean_panic_fn(x_127, x_1);
x_129 = lean_apply_7(x_128, x_2, x_3, x_4, x_5, x_6, x_7, lean_box(0));
return x_129;
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_130 = lean_ctor_get(x_10, 0);
lean_inc(x_130);
lean_dec(x_10);
x_131 = lean_ctor_get(x_130, 0);
lean_inc_ref(x_131);
x_132 = lean_ctor_get(x_130, 2);
lean_inc(x_132);
x_133 = lean_ctor_get(x_130, 3);
lean_inc(x_133);
x_134 = lean_ctor_get(x_130, 4);
lean_inc(x_134);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 lean_ctor_release(x_130, 2);
 lean_ctor_release(x_130, 3);
 lean_ctor_release(x_130, 4);
 x_135 = x_130;
} else {
 lean_dec_ref(x_130);
 x_135 = lean_box(0);
}
x_136 = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__1));
x_137 = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__2));
lean_inc_ref(x_131);
x_138 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_138, 0, x_131);
x_139 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_139, 0, x_131);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
x_141 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_141, 0, x_134);
x_142 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_142, 0, x_133);
x_143 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_143, 0, x_132);
if (lean_is_scalar(x_135)) {
 x_144 = lean_alloc_ctor(0, 5, 0);
} else {
 x_144 = x_135;
}
lean_ctor_set(x_144, 0, x_140);
lean_ctor_set(x_144, 1, x_136);
lean_ctor_set(x_144, 2, x_143);
lean_ctor_set(x_144, 3, x_142);
lean_ctor_set(x_144, 4, x_141);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_137);
x_146 = l_ReaderT_instMonad___redArg(x_145);
x_147 = lean_ctor_get(x_146, 0);
lean_inc_ref(x_147);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_148 = x_146;
} else {
 lean_dec_ref(x_146);
 x_148 = lean_box(0);
}
x_149 = lean_ctor_get(x_147, 0);
lean_inc_ref(x_149);
x_150 = lean_ctor_get(x_147, 2);
lean_inc(x_150);
x_151 = lean_ctor_get(x_147, 3);
lean_inc(x_151);
x_152 = lean_ctor_get(x_147, 4);
lean_inc(x_152);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 lean_ctor_release(x_147, 2);
 lean_ctor_release(x_147, 3);
 lean_ctor_release(x_147, 4);
 x_153 = x_147;
} else {
 lean_dec_ref(x_147);
 x_153 = lean_box(0);
}
x_154 = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__3));
x_155 = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__4));
lean_inc_ref(x_149);
x_156 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_156, 0, x_149);
x_157 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_157, 0, x_149);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_157);
x_159 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_159, 0, x_152);
x_160 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_160, 0, x_151);
x_161 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_161, 0, x_150);
if (lean_is_scalar(x_153)) {
 x_162 = lean_alloc_ctor(0, 5, 0);
} else {
 x_162 = x_153;
}
lean_ctor_set(x_162, 0, x_158);
lean_ctor_set(x_162, 1, x_154);
lean_ctor_set(x_162, 2, x_161);
lean_ctor_set(x_162, 3, x_160);
lean_ctor_set(x_162, 4, x_159);
if (lean_is_scalar(x_148)) {
 x_163 = lean_alloc_ctor(0, 2, 0);
} else {
 x_163 = x_148;
}
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_155);
x_164 = l_ReaderT_instMonad___redArg(x_163);
x_165 = l_Lean_instInhabitedExpr;
x_166 = l_instInhabitedOfMonad___redArg(x_164, x_165);
x_167 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_167, 0, x_166);
x_168 = lean_panic_fn(x_167, x_1);
x_169 = lean_apply_7(x_168, x_2, x_3, x_4, x_5, x_6, x_7, lean_box(0));
return x_169;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__5(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
if (x_6 == 0)
{
x_8 = x_5;
x_9 = x_7;
goto block_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_inc_ref(x_3);
x_20 = l_Lean_Meta_Sym_Internal_Builder_assertShared(x_3, x_6, x_7);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec_ref(x_20);
lean_inc_ref(x_4);
x_22 = l_Lean_Meta_Sym_Internal_Builder_assertShared(x_4, x_6, x_21);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec_ref(x_22);
x_8 = x_5;
x_9 = x_23;
goto block_19;
}
block_19:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Lean_Expr_forallE___override(x_1, x_3, x_4, x_2);
x_11 = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(x_10, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 1);
lean_ctor_set(x_11, 1, x_8);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_8);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_2);
x_9 = lean_unbox(x_6);
x_10 = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__5(x_1, x_8, x_3, x_4, x_5, x_9, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_5 = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__0));
x_6 = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__1));
x_7 = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__2));
x_8 = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__3));
x_9 = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__4));
x_10 = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__5));
x_11 = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__6));
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_6);
x_13 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
lean_ctor_set(x_13, 2, x_8);
lean_ctor_set(x_13, 3, x_9);
lean_ctor_set(x_13, 4, x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
lean_inc_ref(x_14);
x_15 = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_15, 0, x_14);
lean_inc_ref(x_14);
x_16 = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_16, 0, x_14);
lean_inc_ref(x_14);
x_17 = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(x_17, 0, x_14);
lean_inc_ref(x_14);
x_18 = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(x_18, 0, x_14);
lean_inc_ref(x_14);
x_19 = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(x_19, 0, lean_box(0));
lean_closure_set(x_19, 1, lean_box(0));
lean_closure_set(x_19, 2, x_14);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_15);
lean_inc_ref(x_14);
x_21 = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(x_21, 0, lean_box(0));
lean_closure_set(x_21, 1, lean_box(0));
lean_closure_set(x_21, 2, x_14);
x_22 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_22, 2, x_16);
lean_ctor_set(x_22, 3, x_17);
lean_ctor_set(x_22, 4, x_18);
x_23 = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(x_23, 0, lean_box(0));
lean_closure_set(x_23, 1, lean_box(0));
lean_closure_set(x_23, 2, x_14);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_ReaderT_instMonad___redArg(x_24);
lean_inc_ref(x_25);
x_26 = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_26, 0, x_25);
lean_inc_ref(x_25);
x_27 = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_27, 0, x_25);
lean_inc_ref(x_25);
x_28 = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(x_28, 0, x_25);
lean_inc_ref(x_25);
x_29 = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(x_29, 0, x_25);
lean_inc_ref(x_25);
x_30 = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(x_30, 0, lean_box(0));
lean_closure_set(x_30, 1, lean_box(0));
lean_closure_set(x_30, 2, x_25);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_26);
lean_inc_ref(x_25);
x_32 = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(x_32, 0, lean_box(0));
lean_closure_set(x_32, 1, lean_box(0));
lean_closure_set(x_32, 2, x_25);
x_33 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_27);
lean_ctor_set(x_33, 3, x_28);
lean_ctor_set(x_33, 4, x_29);
x_34 = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(x_34, 0, lean_box(0));
lean_closure_set(x_34, 1, lean_box(0));
lean_closure_set(x_34, 2, x_25);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_instInhabitedExpr;
x_37 = l_instInhabitedOfMonad___redArg(x_35, x_36);
x_38 = lean_panic_fn(x_37, x_1);
x_39 = lean_box(x_3);
x_40 = lean_apply_3(x_38, x_2, x_39, x_4);
return x_40;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
x_6 = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
if (x_5 == 0)
{
x_7 = x_4;
x_8 = x_6;
goto block_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_inc_ref(x_3);
x_19 = l_Lean_Meta_Sym_Internal_Builder_assertShared(x_3, x_5, x_6);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec_ref(x_19);
x_7 = x_4;
x_8 = x_20;
goto block_18;
}
block_18:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_10 = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(x_9, x_8);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 1);
lean_ctor_set(x_10, 1, x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_7);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_5);
x_8 = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__8(x_1, x_2, x_3, x_4, x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__4(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
if (x_6 == 0)
{
x_8 = x_5;
x_9 = x_7;
goto block_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_inc_ref(x_3);
x_20 = l_Lean_Meta_Sym_Internal_Builder_assertShared(x_3, x_6, x_7);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec_ref(x_20);
lean_inc_ref(x_4);
x_22 = l_Lean_Meta_Sym_Internal_Builder_assertShared(x_4, x_6, x_21);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec_ref(x_22);
x_8 = x_5;
x_9 = x_23;
goto block_19;
}
block_19:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Lean_Expr_lam___override(x_1, x_3, x_4, x_2);
x_11 = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(x_10, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 1);
lean_ctor_set(x_11, 1, x_8);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_8);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_2);
x_9 = lean_unbox(x_6);
x_10 = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__4(x_1, x_8, x_3, x_4, x_5, x_9, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
if (x_4 == 0)
{
x_6 = x_3;
x_7 = x_5;
goto block_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_inc_ref(x_2);
x_18 = l_Lean_Meta_Sym_Internal_Builder_assertShared(x_2, x_4, x_5);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec_ref(x_18);
x_6 = x_3;
x_7 = x_19;
goto block_17;
}
block_17:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = l_Lean_Expr_mdata___override(x_1, x_2);
x_9 = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(x_8, x_7);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 1);
lean_ctor_set(x_9, 1, x_6);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_6);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
x_7 = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__7(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4_spec__12___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
x_15 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_11, x_13);
if (x_15 == 0)
{
x_7 = x_15;
goto block_10;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_eq(x_12, x_14);
x_7 = x_16;
goto block_10;
}
block_10:
{
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4_spec__12___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4_spec__12___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_array_get_size(x_3);
x_7 = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(x_4);
x_8 = lean_uint64_of_nat(x_5);
x_9 = lean_uint64_mix_hash(x_7, x_8);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_6);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget(x_3, x_20);
x_22 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4_spec__12___redArg(x_2, x_21);
lean_dec(x_21);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___redArg(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
if (x_4 == 0)
{
x_6 = x_3;
x_7 = x_5;
goto block_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_inc_ref(x_1);
x_18 = l_Lean_Meta_Sym_Internal_Builder_assertShared(x_1, x_4, x_5);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec_ref(x_18);
lean_inc_ref(x_2);
x_20 = l_Lean_Meta_Sym_Internal_Builder_assertShared(x_2, x_4, x_19);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec_ref(x_20);
x_6 = x_3;
x_7 = x_21;
goto block_17;
}
block_17:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = l_Lean_Expr_app___override(x_1, x_2);
x_9 = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(x_8, x_7);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 1);
lean_ctor_set(x_9, 1, x_6);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_6);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
x_7 = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__3(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
if (x_7 == 0)
{
x_9 = x_6;
x_10 = x_8;
goto block_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_inc_ref(x_2);
x_21 = l_Lean_Meta_Sym_Internal_Builder_assertShared(x_2, x_7, x_8);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec_ref(x_21);
lean_inc_ref(x_3);
x_23 = l_Lean_Meta_Sym_Internal_Builder_assertShared(x_3, x_7, x_22);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec_ref(x_23);
lean_inc_ref(x_4);
x_25 = l_Lean_Meta_Sym_Internal_Builder_assertShared(x_4, x_7, x_24);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec_ref(x_25);
x_9 = x_6;
x_10 = x_26;
goto block_20;
}
block_20:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = l_Lean_Expr_letE___override(x_1, x_2, x_3, x_4, x_5);
x_12 = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(x_11, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 1);
lean_ctor_set(x_12, 1, x_9);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_9);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_5);
x_10 = lean_unbox(x_7);
x_11 = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6(x_1, x_2, x_3, x_4, x_9, x_6, x_10, x_8);
return x_11;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__2));
x_2 = lean_unsigned_to_nat(67u);
x_3 = lean_unsigned_to_nat(35u);
x_4 = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__1));
x_5 = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_4)) {
case 5:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_28; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_inc_ref(x_9);
x_11 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(x_1, x_2, x_3, x_9, x_5, x_6, x_7, x_8);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
lean_inc_ref(x_10);
x_16 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(x_1, x_2, x_3, x_10, x_5, x_15, x_7, x_13);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_19 = x_16;
} else {
 lean_dec_ref(x_16);
 x_19 = lean_box(0);
}
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_22 = x_17;
} else {
 lean_dec_ref(x_17);
 x_22 = lean_box(0);
}
x_28 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_9, x_14);
if (x_28 == 0)
{
x_23 = x_28;
goto block_27;
}
else
{
uint8_t x_29; 
x_29 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_10, x_20);
x_23 = x_29;
goto block_27;
}
block_27:
{
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec_ref(x_4);
x_24 = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__3(x_14, x_20, x_21, x_7, x_18);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_20);
lean_dec(x_14);
if (lean_is_scalar(x_22)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_22;
}
lean_ctor_set(x_25, 0, x_4);
lean_ctor_set(x_25, 1, x_21);
if (lean_is_scalar(x_19)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_19;
}
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_18);
return x_26;
}
}
}
case 6:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_53; 
x_30 = lean_ctor_get(x_4, 0);
x_31 = lean_ctor_get(x_4, 1);
x_32 = lean_ctor_get(x_4, 2);
x_33 = lean_ctor_get_uint8(x_4, sizeof(void*)*3 + 8);
lean_inc(x_5);
lean_inc_ref(x_31);
x_34 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(x_1, x_2, x_3, x_31, x_5, x_6, x_7, x_8);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec_ref(x_34);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_5, x_39);
lean_dec(x_5);
lean_inc_ref(x_32);
x_41 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(x_1, x_2, x_3, x_32, x_40, x_38, x_7, x_36);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_44 = x_41;
} else {
 lean_dec_ref(x_41);
 x_44 = lean_box(0);
}
x_45 = lean_ctor_get(x_42, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_47 = x_42;
} else {
 lean_dec_ref(x_42);
 x_47 = lean_box(0);
}
x_53 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_31, x_37);
if (x_53 == 0)
{
x_48 = x_53;
goto block_52;
}
else
{
uint8_t x_54; 
x_54 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_32, x_45);
x_48 = x_54;
goto block_52;
}
block_52:
{
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_47);
lean_dec(x_44);
lean_inc(x_30);
lean_dec_ref(x_4);
x_49 = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__4(x_30, x_33, x_37, x_45, x_46, x_7, x_43);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_45);
lean_dec(x_37);
if (lean_is_scalar(x_47)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_47;
}
lean_ctor_set(x_50, 0, x_4);
lean_ctor_set(x_50, 1, x_46);
if (lean_is_scalar(x_44)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_44;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_43);
return x_51;
}
}
}
case 7:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; uint8_t x_78; 
x_55 = lean_ctor_get(x_4, 0);
x_56 = lean_ctor_get(x_4, 1);
x_57 = lean_ctor_get(x_4, 2);
x_58 = lean_ctor_get_uint8(x_4, sizeof(void*)*3 + 8);
lean_inc(x_5);
lean_inc_ref(x_56);
x_59 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(x_1, x_2, x_3, x_56, x_5, x_6, x_7, x_8);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec_ref(x_59);
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_dec(x_60);
x_64 = lean_unsigned_to_nat(1u);
x_65 = lean_nat_add(x_5, x_64);
lean_dec(x_5);
lean_inc_ref(x_57);
x_66 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(x_1, x_2, x_3, x_57, x_65, x_63, x_7, x_61);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_69 = x_66;
} else {
 lean_dec_ref(x_66);
 x_69 = lean_box(0);
}
x_70 = lean_ctor_get(x_67, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_67, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_72 = x_67;
} else {
 lean_dec_ref(x_67);
 x_72 = lean_box(0);
}
x_78 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_56, x_62);
if (x_78 == 0)
{
x_73 = x_78;
goto block_77;
}
else
{
uint8_t x_79; 
x_79 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_57, x_70);
x_73 = x_79;
goto block_77;
}
block_77:
{
if (x_73 == 0)
{
lean_object* x_74; 
lean_dec(x_72);
lean_dec(x_69);
lean_inc(x_55);
lean_dec_ref(x_4);
x_74 = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__5(x_55, x_58, x_62, x_70, x_71, x_7, x_68);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_70);
lean_dec(x_62);
if (lean_is_scalar(x_72)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_72;
}
lean_ctor_set(x_75, 0, x_4);
lean_ctor_set(x_75, 1, x_71);
if (lean_is_scalar(x_69)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_69;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_68);
return x_76;
}
}
}
case 8:
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; uint8_t x_111; 
x_80 = lean_ctor_get(x_4, 0);
x_81 = lean_ctor_get(x_4, 1);
x_82 = lean_ctor_get(x_4, 2);
x_83 = lean_ctor_get(x_4, 3);
x_84 = lean_ctor_get_uint8(x_4, sizeof(void*)*4 + 8);
lean_inc(x_5);
lean_inc_ref(x_81);
x_85 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(x_1, x_2, x_3, x_81, x_5, x_6, x_7, x_8);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec_ref(x_85);
x_88 = lean_ctor_get(x_86, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_86, 1);
lean_inc(x_89);
lean_dec(x_86);
lean_inc(x_5);
lean_inc_ref(x_82);
x_90 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(x_1, x_2, x_3, x_82, x_5, x_89, x_7, x_87);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec_ref(x_90);
x_93 = lean_ctor_get(x_91, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_91, 1);
lean_inc(x_94);
lean_dec(x_91);
x_95 = lean_unsigned_to_nat(1u);
x_96 = lean_nat_add(x_5, x_95);
lean_dec(x_5);
lean_inc_ref(x_83);
x_97 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(x_1, x_2, x_3, x_83, x_96, x_94, x_7, x_92);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_100 = x_97;
} else {
 lean_dec_ref(x_97);
 x_100 = lean_box(0);
}
x_101 = lean_ctor_get(x_98, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_98, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_103 = x_98;
} else {
 lean_dec_ref(x_98);
 x_103 = lean_box(0);
}
x_111 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_81, x_88);
if (x_111 == 0)
{
x_104 = x_111;
goto block_110;
}
else
{
uint8_t x_112; 
x_112 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_82, x_93);
x_104 = x_112;
goto block_110;
}
block_110:
{
if (x_104 == 0)
{
lean_object* x_105; 
lean_dec(x_103);
lean_dec(x_100);
lean_inc(x_80);
lean_dec_ref(x_4);
x_105 = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6(x_80, x_88, x_93, x_101, x_84, x_102, x_7, x_99);
return x_105;
}
else
{
uint8_t x_106; 
x_106 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_83, x_101);
if (x_106 == 0)
{
lean_object* x_107; 
lean_dec(x_103);
lean_dec(x_100);
lean_inc(x_80);
lean_dec_ref(x_4);
x_107 = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6(x_80, x_88, x_93, x_101, x_84, x_102, x_7, x_99);
return x_107;
}
else
{
lean_object* x_108; lean_object* x_109; 
lean_dec(x_101);
lean_dec(x_93);
lean_dec(x_88);
if (lean_is_scalar(x_103)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_103;
}
lean_ctor_set(x_108, 0, x_4);
lean_ctor_set(x_108, 1, x_102);
if (lean_is_scalar(x_100)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_100;
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_99);
return x_109;
}
}
}
}
case 10:
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_113 = lean_ctor_get(x_4, 0);
x_114 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_114);
x_115 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(x_1, x_2, x_3, x_114, x_5, x_6, x_7, x_8);
x_116 = !lean_is_exclusive(x_115);
if (x_116 == 0)
{
lean_object* x_117; uint8_t x_118; 
x_117 = lean_ctor_get(x_115, 0);
x_118 = !lean_is_exclusive(x_117);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_119 = lean_ctor_get(x_115, 1);
x_120 = lean_ctor_get(x_117, 0);
x_121 = lean_ctor_get(x_117, 1);
x_122 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_114, x_120);
if (x_122 == 0)
{
lean_object* x_123; 
lean_free_object(x_117);
lean_free_object(x_115);
lean_inc(x_113);
lean_dec_ref(x_4);
x_123 = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__7(x_113, x_120, x_121, x_7, x_119);
return x_123;
}
else
{
lean_dec(x_120);
lean_ctor_set(x_117, 0, x_4);
return x_115;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_124 = lean_ctor_get(x_115, 1);
x_125 = lean_ctor_get(x_117, 0);
x_126 = lean_ctor_get(x_117, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_117);
x_127 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_114, x_125);
if (x_127 == 0)
{
lean_object* x_128; 
lean_free_object(x_115);
lean_inc(x_113);
lean_dec_ref(x_4);
x_128 = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__7(x_113, x_125, x_126, x_7, x_124);
return x_128;
}
else
{
lean_object* x_129; 
lean_dec(x_125);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_4);
lean_ctor_set(x_129, 1, x_126);
lean_ctor_set(x_115, 0, x_129);
return x_115;
}
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_130 = lean_ctor_get(x_115, 0);
x_131 = lean_ctor_get(x_115, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_115);
x_132 = lean_ctor_get(x_130, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_130, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_134 = x_130;
} else {
 lean_dec_ref(x_130);
 x_134 = lean_box(0);
}
x_135 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_114, x_132);
if (x_135 == 0)
{
lean_object* x_136; 
lean_dec(x_134);
lean_inc(x_113);
lean_dec_ref(x_4);
x_136 = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__7(x_113, x_132, x_133, x_7, x_131);
return x_136;
}
else
{
lean_object* x_137; lean_object* x_138; 
lean_dec(x_132);
if (lean_is_scalar(x_134)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_134;
}
lean_ctor_set(x_137, 0, x_4);
lean_ctor_set(x_137, 1, x_133);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_131);
return x_138;
}
}
}
case 11:
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_139 = lean_ctor_get(x_4, 0);
x_140 = lean_ctor_get(x_4, 1);
x_141 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_141);
x_142 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(x_1, x_2, x_3, x_141, x_5, x_6, x_7, x_8);
x_143 = !lean_is_exclusive(x_142);
if (x_143 == 0)
{
lean_object* x_144; uint8_t x_145; 
x_144 = lean_ctor_get(x_142, 0);
x_145 = !lean_is_exclusive(x_144);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_146 = lean_ctor_get(x_142, 1);
x_147 = lean_ctor_get(x_144, 0);
x_148 = lean_ctor_get(x_144, 1);
x_149 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_141, x_147);
if (x_149 == 0)
{
lean_object* x_150; 
lean_free_object(x_144);
lean_free_object(x_142);
lean_inc(x_140);
lean_inc(x_139);
lean_dec_ref(x_4);
x_150 = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__8(x_139, x_140, x_147, x_148, x_7, x_146);
return x_150;
}
else
{
lean_dec(x_147);
lean_ctor_set(x_144, 0, x_4);
return x_142;
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_151 = lean_ctor_get(x_142, 1);
x_152 = lean_ctor_get(x_144, 0);
x_153 = lean_ctor_get(x_144, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_144);
x_154 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_141, x_152);
if (x_154 == 0)
{
lean_object* x_155; 
lean_free_object(x_142);
lean_inc(x_140);
lean_inc(x_139);
lean_dec_ref(x_4);
x_155 = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__8(x_139, x_140, x_152, x_153, x_7, x_151);
return x_155;
}
else
{
lean_object* x_156; 
lean_dec(x_152);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_4);
lean_ctor_set(x_156, 1, x_153);
lean_ctor_set(x_142, 0, x_156);
return x_142;
}
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_157 = lean_ctor_get(x_142, 0);
x_158 = lean_ctor_get(x_142, 1);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_142);
x_159 = lean_ctor_get(x_157, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_157, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_161 = x_157;
} else {
 lean_dec_ref(x_157);
 x_161 = lean_box(0);
}
x_162 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_141, x_159);
if (x_162 == 0)
{
lean_object* x_163; 
lean_dec(x_161);
lean_inc(x_140);
lean_inc(x_139);
lean_dec_ref(x_4);
x_163 = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__8(x_139, x_140, x_159, x_160, x_7, x_158);
return x_163;
}
else
{
lean_object* x_164; lean_object* x_165; 
lean_dec(x_159);
if (lean_is_scalar(x_161)) {
 x_164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_164 = x_161;
}
lean_ctor_set(x_164, 0, x_4);
lean_ctor_set(x_164, 1, x_160);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_158);
return x_165;
}
}
}
default: 
{
lean_object* x_166; lean_object* x_167; 
lean_dec(x_5);
lean_dec_ref(x_4);
x_166 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__3;
x_167 = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9(x_166, x_6, x_7, x_8);
return x_167;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
lean_inc(x_5);
lean_inc_ref(x_4);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_5);
x_10 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___redArg(x_6, x_9);
if (lean_obj_tag(x_10) == 1)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec_ref(x_9);
lean_dec(x_5);
lean_dec_ref(x_4);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
else
{
lean_object* x_14; 
lean_dec(x_10);
x_14 = lean_nat_add(x_1, x_5);
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_nat_dec_le(x_14, x_15);
lean_dec(x_14);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_5);
x_17 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(x_9, x_4, x_6, x_7, x_8);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; 
lean_inc(x_15);
lean_dec_ref(x_4);
x_18 = lean_nat_add(x_5, x_2);
x_19 = lean_nat_dec_lt(x_15, x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_5);
x_20 = lean_nat_sub(x_15, x_2);
lean_dec(x_15);
x_21 = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___redArg(x_20, x_8);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec_ref(x_21);
x_24 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(x_9, x_22, x_6, x_7, x_23);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_25 = lean_nat_sub(x_15, x_5);
lean_dec(x_15);
x_26 = lean_nat_sub(x_2, x_25);
lean_dec(x_25);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_sub(x_26, x_27);
lean_dec(x_26);
x_29 = lean_array_fget_borrowed(x_3, x_28);
lean_dec(x_28);
x_30 = lean_unsigned_to_nat(0u);
lean_inc(x_29);
x_31 = l_Lean_Meta_Sym_liftLooseBVarsS_x27(x_29, x_30, x_5, x_7, x_8);
lean_dec(x_5);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec_ref(x_31);
x_34 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(x_9, x_32, x_6, x_7, x_33);
return x_34;
}
}
}
case 9:
{
lean_object* x_35; 
lean_dec(x_14);
lean_dec(x_5);
x_35 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(x_9, x_4, x_6, x_7, x_8);
return x_35;
}
case 2:
{
lean_object* x_36; 
lean_dec(x_14);
lean_dec(x_5);
x_36 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(x_9, x_4, x_6, x_7, x_8);
return x_36;
}
case 1:
{
lean_object* x_37; 
lean_dec(x_14);
lean_dec(x_5);
x_37 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(x_9, x_4, x_6, x_7, x_8);
return x_37;
}
case 4:
{
lean_object* x_38; 
lean_dec(x_14);
lean_dec(x_5);
x_38 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(x_9, x_4, x_6, x_7, x_8);
return x_38;
}
case 3:
{
lean_object* x_39; 
lean_dec(x_14);
lean_dec(x_5);
x_39 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(x_9, x_4, x_6, x_7, x_8);
return x_39;
}
default: 
{
lean_object* x_40; uint8_t x_41; 
x_40 = l_Lean_Expr_looseBVarRange(x_4);
x_41 = lean_nat_dec_le(x_40, x_14);
lean_dec(x_14);
lean_dec(x_40);
if (x_41 == 0)
{
switch (lean_obj_tag(x_4)) {
case 9:
{
lean_object* x_42; 
lean_dec(x_5);
x_42 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(x_9, x_4, x_6, x_7, x_8);
return x_42;
}
case 2:
{
lean_object* x_43; 
lean_dec(x_5);
x_43 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(x_9, x_4, x_6, x_7, x_8);
return x_43;
}
case 0:
{
lean_object* x_44; 
lean_dec(x_5);
x_44 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(x_9, x_4, x_6, x_7, x_8);
return x_44;
}
case 1:
{
lean_object* x_45; 
lean_dec(x_5);
x_45 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(x_9, x_4, x_6, x_7, x_8);
return x_45;
}
case 4:
{
lean_object* x_46; 
lean_dec(x_5);
x_46 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(x_9, x_4, x_6, x_7, x_8);
return x_46;
}
case 3:
{
lean_object* x_47; 
lean_dec(x_5);
x_47 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(x_9, x_4, x_6, x_7, x_8);
return x_47;
}
default: 
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_48 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec_ref(x_48);
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(x_9, x_51, x_52, x_7, x_50);
return x_53;
}
}
}
else
{
lean_object* x_54; 
lean_dec(x_5);
x_54 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(x_9, x_4, x_6, x_7, x_8);
return x_54;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_7);
x_10 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_9, x_8);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_7);
x_10 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_9, x_8);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Sym_instantiateRevRangeS___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__2));
x_2 = lean_unsigned_to_nat(34u);
x_3 = lean_unsigned_to_nat(21u);
x_4 = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__4));
x_5 = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__3));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__2));
x_2 = lean_unsigned_to_nat(32u);
x_3 = lean_unsigned_to_nat(20u);
x_4 = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__4));
x_5 = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__3));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevRangeS(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_12; 
x_12 = lean_nat_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_4);
x_14 = lean_nat_dec_lt(x_13, x_3);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
x_15 = lean_st_ref_take(x_6);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = l_Lean_Meta_Sym_instantiateRevRangeS___closed__0;
lean_ctor_set(x_15, 0, x_18);
x_19 = lean_st_ref_set(x_6, x_15);
x_20 = lean_st_ref_get(x_6);
x_38 = lean_ctor_get_uint8(x_20, sizeof(void*)*6);
lean_dec(x_20);
x_39 = lean_nat_sub(x_3, x_2);
x_40 = lean_unsigned_to_nat(0u);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_1, 0);
x_42 = lean_nat_dec_le(x_2, x_41);
if (x_42 == 0)
{
lean_dec(x_39);
x_21 = x_1;
x_22 = x_17;
goto block_37;
}
else
{
uint8_t x_43; 
lean_inc(x_41);
lean_dec_ref(x_1);
x_43 = lean_nat_dec_lt(x_41, x_39);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_nat_sub(x_41, x_39);
lean_dec(x_39);
lean_dec(x_41);
x_45 = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___redArg(x_44, x_17);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec_ref(x_45);
x_21 = x_46;
x_22 = x_47;
goto block_37;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_48 = lean_nat_sub(x_39, x_41);
lean_dec(x_41);
lean_dec(x_39);
x_49 = lean_unsigned_to_nat(1u);
x_50 = lean_nat_sub(x_48, x_49);
lean_dec(x_48);
x_51 = lean_array_fget_borrowed(x_4, x_50);
lean_dec(x_50);
lean_inc(x_51);
x_52 = l_Lean_Meta_Sym_liftLooseBVarsS_x27(x_51, x_40, x_40, x_38, x_17);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec_ref(x_52);
x_21 = x_53;
x_22 = x_54;
goto block_37;
}
}
}
case 9:
{
lean_dec(x_39);
x_21 = x_1;
x_22 = x_17;
goto block_37;
}
case 2:
{
lean_dec(x_39);
x_21 = x_1;
x_22 = x_17;
goto block_37;
}
case 1:
{
lean_dec(x_39);
x_21 = x_1;
x_22 = x_17;
goto block_37;
}
case 4:
{
lean_dec(x_39);
x_21 = x_1;
x_22 = x_17;
goto block_37;
}
case 3:
{
lean_dec(x_39);
x_21 = x_1;
x_22 = x_17;
goto block_37;
}
default: 
{
lean_object* x_55; uint8_t x_56; 
x_55 = l_Lean_Expr_looseBVarRange(x_1);
x_56 = lean_nat_dec_le(x_55, x_2);
lean_dec(x_55);
if (x_56 == 0)
{
switch (lean_obj_tag(x_1)) {
case 9:
{
lean_dec(x_39);
x_21 = x_1;
x_22 = x_17;
goto block_37;
}
case 2:
{
lean_dec(x_39);
x_21 = x_1;
x_22 = x_17;
goto block_37;
}
case 0:
{
lean_dec(x_39);
x_21 = x_1;
x_22 = x_17;
goto block_37;
}
case 1:
{
lean_dec(x_39);
x_21 = x_1;
x_22 = x_17;
goto block_37;
}
case 4:
{
lean_dec(x_39);
x_21 = x_1;
x_22 = x_17;
goto block_37;
}
case 3:
{
lean_dec(x_39);
x_21 = x_1;
x_22 = x_17;
goto block_37;
}
default: 
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_57 = l_Lean_Meta_Sym_instantiateRevRangeS___closed__2;
x_58 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(x_2, x_39, x_4, x_1, x_40, x_57, x_38, x_17);
lean_dec(x_39);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec_ref(x_58);
x_61 = lean_ctor_get(x_59, 0);
lean_inc(x_61);
lean_dec(x_59);
x_21 = x_61;
x_22 = x_60;
goto block_37;
}
}
}
else
{
lean_dec(x_39);
x_21 = x_1;
x_22 = x_17;
goto block_37;
}
}
}
block_37:
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_st_ref_take(x_6);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_22);
x_26 = lean_st_ref_set(x_6, x_23);
lean_dec(x_6);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_21);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_28 = lean_ctor_get(x_23, 1);
x_29 = lean_ctor_get(x_23, 2);
x_30 = lean_ctor_get(x_23, 3);
x_31 = lean_ctor_get(x_23, 4);
x_32 = lean_ctor_get(x_23, 5);
x_33 = lean_ctor_get_uint8(x_23, sizeof(void*)*6);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_23);
x_34 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_34, 0, x_22);
lean_ctor_set(x_34, 1, x_28);
lean_ctor_set(x_34, 2, x_29);
lean_ctor_set(x_34, 3, x_30);
lean_ctor_set(x_34, 4, x_31);
lean_ctor_set(x_34, 5, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*6, x_33);
x_35 = lean_st_ref_set(x_6, x_34);
lean_dec(x_6);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_21);
return x_36;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_87; lean_object* x_88; lean_object* x_89; 
x_62 = lean_ctor_get(x_15, 0);
x_63 = lean_ctor_get(x_15, 1);
x_64 = lean_ctor_get(x_15, 2);
x_65 = lean_ctor_get(x_15, 3);
x_66 = lean_ctor_get(x_15, 4);
x_67 = lean_ctor_get(x_15, 5);
x_68 = lean_ctor_get_uint8(x_15, sizeof(void*)*6);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_15);
x_69 = l_Lean_Meta_Sym_instantiateRevRangeS___closed__0;
x_70 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_63);
lean_ctor_set(x_70, 2, x_64);
lean_ctor_set(x_70, 3, x_65);
lean_ctor_set(x_70, 4, x_66);
lean_ctor_set(x_70, 5, x_67);
lean_ctor_set_uint8(x_70, sizeof(void*)*6, x_68);
x_71 = lean_st_ref_set(x_6, x_70);
x_72 = lean_st_ref_get(x_6);
x_87 = lean_ctor_get_uint8(x_72, sizeof(void*)*6);
lean_dec(x_72);
x_88 = lean_nat_sub(x_3, x_2);
x_89 = lean_unsigned_to_nat(0u);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_90; uint8_t x_91; 
x_90 = lean_ctor_get(x_1, 0);
x_91 = lean_nat_dec_le(x_2, x_90);
if (x_91 == 0)
{
lean_dec(x_88);
x_73 = x_1;
x_74 = x_62;
goto block_86;
}
else
{
uint8_t x_92; 
lean_inc(x_90);
lean_dec_ref(x_1);
x_92 = lean_nat_dec_lt(x_90, x_88);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_nat_sub(x_90, x_88);
lean_dec(x_88);
lean_dec(x_90);
x_94 = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___redArg(x_93, x_62);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec_ref(x_94);
x_73 = x_95;
x_74 = x_96;
goto block_86;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_97 = lean_nat_sub(x_88, x_90);
lean_dec(x_90);
lean_dec(x_88);
x_98 = lean_unsigned_to_nat(1u);
x_99 = lean_nat_sub(x_97, x_98);
lean_dec(x_97);
x_100 = lean_array_fget_borrowed(x_4, x_99);
lean_dec(x_99);
lean_inc(x_100);
x_101 = l_Lean_Meta_Sym_liftLooseBVarsS_x27(x_100, x_89, x_89, x_87, x_62);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec_ref(x_101);
x_73 = x_102;
x_74 = x_103;
goto block_86;
}
}
}
case 9:
{
lean_dec(x_88);
x_73 = x_1;
x_74 = x_62;
goto block_86;
}
case 2:
{
lean_dec(x_88);
x_73 = x_1;
x_74 = x_62;
goto block_86;
}
case 1:
{
lean_dec(x_88);
x_73 = x_1;
x_74 = x_62;
goto block_86;
}
case 4:
{
lean_dec(x_88);
x_73 = x_1;
x_74 = x_62;
goto block_86;
}
case 3:
{
lean_dec(x_88);
x_73 = x_1;
x_74 = x_62;
goto block_86;
}
default: 
{
lean_object* x_104; uint8_t x_105; 
x_104 = l_Lean_Expr_looseBVarRange(x_1);
x_105 = lean_nat_dec_le(x_104, x_2);
lean_dec(x_104);
if (x_105 == 0)
{
switch (lean_obj_tag(x_1)) {
case 9:
{
lean_dec(x_88);
x_73 = x_1;
x_74 = x_62;
goto block_86;
}
case 2:
{
lean_dec(x_88);
x_73 = x_1;
x_74 = x_62;
goto block_86;
}
case 0:
{
lean_dec(x_88);
x_73 = x_1;
x_74 = x_62;
goto block_86;
}
case 1:
{
lean_dec(x_88);
x_73 = x_1;
x_74 = x_62;
goto block_86;
}
case 4:
{
lean_dec(x_88);
x_73 = x_1;
x_74 = x_62;
goto block_86;
}
case 3:
{
lean_dec(x_88);
x_73 = x_1;
x_74 = x_62;
goto block_86;
}
default: 
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_106 = l_Lean_Meta_Sym_instantiateRevRangeS___closed__2;
x_107 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(x_2, x_88, x_4, x_1, x_89, x_106, x_87, x_62);
lean_dec(x_88);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec_ref(x_107);
x_110 = lean_ctor_get(x_108, 0);
lean_inc(x_110);
lean_dec(x_108);
x_73 = x_110;
x_74 = x_109;
goto block_86;
}
}
}
else
{
lean_dec(x_88);
x_73 = x_1;
x_74 = x_62;
goto block_86;
}
}
}
block_86:
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_75 = lean_st_ref_take(x_6);
x_76 = lean_ctor_get(x_75, 1);
lean_inc_ref(x_76);
x_77 = lean_ctor_get(x_75, 2);
lean_inc_ref(x_77);
x_78 = lean_ctor_get(x_75, 3);
lean_inc_ref(x_78);
x_79 = lean_ctor_get(x_75, 4);
lean_inc_ref(x_79);
x_80 = lean_ctor_get(x_75, 5);
lean_inc_ref(x_80);
x_81 = lean_ctor_get_uint8(x_75, sizeof(void*)*6);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 lean_ctor_release(x_75, 2);
 lean_ctor_release(x_75, 3);
 lean_ctor_release(x_75, 4);
 lean_ctor_release(x_75, 5);
 x_82 = x_75;
} else {
 lean_dec_ref(x_75);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(0, 6, 1);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_74);
lean_ctor_set(x_83, 1, x_76);
lean_ctor_set(x_83, 2, x_77);
lean_ctor_set(x_83, 3, x_78);
lean_ctor_set(x_83, 4, x_79);
lean_ctor_set(x_83, 5, x_80);
lean_ctor_set_uint8(x_83, sizeof(void*)*6, x_81);
x_84 = lean_st_ref_set(x_6, x_83);
lean_dec(x_6);
x_85 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_85, 0, x_73);
return x_85;
}
}
}
else
{
lean_object* x_111; lean_object* x_112; 
lean_dec_ref(x_1);
x_111 = l_Lean_Meta_Sym_instantiateRevRangeS___closed__5;
x_112 = l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3(x_111, x_5, x_6, x_7, x_8, x_9, x_10);
return x_112;
}
}
else
{
lean_object* x_113; lean_object* x_114; 
lean_dec_ref(x_1);
x_113 = l_Lean_Meta_Sym_instantiateRevRangeS___closed__6;
x_114 = l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3(x_113, x_5, x_6, x_7, x_8, x_9, x_10);
return x_114;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevRangeS___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Sym_instantiateRevRangeS(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4_spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4_spec__12___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4_spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4_spec__12(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevS(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_get_size(x_2);
x_12 = l_Lean_Meta_Sym_instantiateRevRangeS(x_1, x_10, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevS___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Sym_instantiateRevS(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_4 = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__0));
x_5 = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__1));
x_6 = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__2));
x_7 = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__3));
x_8 = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__4));
x_9 = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__5));
x_10 = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__6));
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_5);
x_12 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
lean_ctor_set(x_12, 2, x_7);
lean_ctor_set(x_12, 3, x_8);
lean_ctor_set(x_12, 4, x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
lean_inc_ref(x_13);
x_14 = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_14, 0, x_13);
lean_inc_ref(x_13);
x_15 = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_15, 0, x_13);
lean_inc_ref(x_13);
x_16 = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(x_16, 0, x_13);
lean_inc_ref(x_13);
x_17 = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(x_17, 0, x_13);
lean_inc_ref(x_13);
x_18 = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(x_18, 0, lean_box(0));
lean_closure_set(x_18, 1, lean_box(0));
lean_closure_set(x_18, 2, x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_14);
lean_inc_ref(x_13);
x_20 = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(x_20, 0, lean_box(0));
lean_closure_set(x_20, 1, lean_box(0));
lean_closure_set(x_20, 2, x_13);
x_21 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_21, 2, x_15);
lean_ctor_set(x_21, 3, x_16);
lean_ctor_set(x_21, 4, x_17);
x_22 = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(x_22, 0, lean_box(0));
lean_closure_set(x_22, 1, lean_box(0));
lean_closure_set(x_22, 2, x_13);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_instInhabitedExpr;
x_25 = l_instInhabitedOfMonad___redArg(x_23, x_24);
x_26 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_26, 0, x_25);
x_27 = lean_panic_fn(x_26, x_1);
x_28 = lean_box(x_2);
x_29 = lean_apply_2(x_27, x_28, x_3);
return x_29;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
x_5 = l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_4)) {
case 5:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_28; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_inc_ref(x_9);
x_11 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(x_1, x_2, x_3, x_9, x_5, x_6, x_7, x_8);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
lean_inc_ref(x_10);
x_16 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(x_1, x_2, x_3, x_10, x_5, x_15, x_7, x_13);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_19 = x_16;
} else {
 lean_dec_ref(x_16);
 x_19 = lean_box(0);
}
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_22 = x_17;
} else {
 lean_dec_ref(x_17);
 x_22 = lean_box(0);
}
x_28 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_9, x_14);
if (x_28 == 0)
{
x_23 = x_28;
goto block_27;
}
else
{
uint8_t x_29; 
x_29 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_10, x_20);
x_23 = x_29;
goto block_27;
}
block_27:
{
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec_ref(x_4);
x_24 = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__3(x_14, x_20, x_21, x_7, x_18);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_20);
lean_dec(x_14);
if (lean_is_scalar(x_22)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_22;
}
lean_ctor_set(x_25, 0, x_4);
lean_ctor_set(x_25, 1, x_21);
if (lean_is_scalar(x_19)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_19;
}
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_18);
return x_26;
}
}
}
case 6:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_53; 
x_30 = lean_ctor_get(x_4, 0);
x_31 = lean_ctor_get(x_4, 1);
x_32 = lean_ctor_get(x_4, 2);
x_33 = lean_ctor_get_uint8(x_4, sizeof(void*)*3 + 8);
lean_inc(x_5);
lean_inc_ref(x_31);
x_34 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(x_1, x_2, x_3, x_31, x_5, x_6, x_7, x_8);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec_ref(x_34);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_5, x_39);
lean_dec(x_5);
lean_inc_ref(x_32);
x_41 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(x_1, x_2, x_3, x_32, x_40, x_38, x_7, x_36);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_44 = x_41;
} else {
 lean_dec_ref(x_41);
 x_44 = lean_box(0);
}
x_45 = lean_ctor_get(x_42, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_47 = x_42;
} else {
 lean_dec_ref(x_42);
 x_47 = lean_box(0);
}
x_53 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_31, x_37);
if (x_53 == 0)
{
x_48 = x_53;
goto block_52;
}
else
{
uint8_t x_54; 
x_54 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_32, x_45);
x_48 = x_54;
goto block_52;
}
block_52:
{
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_47);
lean_dec(x_44);
lean_inc(x_30);
lean_dec_ref(x_4);
x_49 = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__4(x_30, x_33, x_37, x_45, x_46, x_7, x_43);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_45);
lean_dec(x_37);
if (lean_is_scalar(x_47)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_47;
}
lean_ctor_set(x_50, 0, x_4);
lean_ctor_set(x_50, 1, x_46);
if (lean_is_scalar(x_44)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_44;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_43);
return x_51;
}
}
}
case 7:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; uint8_t x_78; 
x_55 = lean_ctor_get(x_4, 0);
x_56 = lean_ctor_get(x_4, 1);
x_57 = lean_ctor_get(x_4, 2);
x_58 = lean_ctor_get_uint8(x_4, sizeof(void*)*3 + 8);
lean_inc(x_5);
lean_inc_ref(x_56);
x_59 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(x_1, x_2, x_3, x_56, x_5, x_6, x_7, x_8);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec_ref(x_59);
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_dec(x_60);
x_64 = lean_unsigned_to_nat(1u);
x_65 = lean_nat_add(x_5, x_64);
lean_dec(x_5);
lean_inc_ref(x_57);
x_66 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(x_1, x_2, x_3, x_57, x_65, x_63, x_7, x_61);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_69 = x_66;
} else {
 lean_dec_ref(x_66);
 x_69 = lean_box(0);
}
x_70 = lean_ctor_get(x_67, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_67, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_72 = x_67;
} else {
 lean_dec_ref(x_67);
 x_72 = lean_box(0);
}
x_78 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_56, x_62);
if (x_78 == 0)
{
x_73 = x_78;
goto block_77;
}
else
{
uint8_t x_79; 
x_79 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_57, x_70);
x_73 = x_79;
goto block_77;
}
block_77:
{
if (x_73 == 0)
{
lean_object* x_74; 
lean_dec(x_72);
lean_dec(x_69);
lean_inc(x_55);
lean_dec_ref(x_4);
x_74 = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__5(x_55, x_58, x_62, x_70, x_71, x_7, x_68);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_70);
lean_dec(x_62);
if (lean_is_scalar(x_72)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_72;
}
lean_ctor_set(x_75, 0, x_4);
lean_ctor_set(x_75, 1, x_71);
if (lean_is_scalar(x_69)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_69;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_68);
return x_76;
}
}
}
case 8:
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; uint8_t x_111; 
x_80 = lean_ctor_get(x_4, 0);
x_81 = lean_ctor_get(x_4, 1);
x_82 = lean_ctor_get(x_4, 2);
x_83 = lean_ctor_get(x_4, 3);
x_84 = lean_ctor_get_uint8(x_4, sizeof(void*)*4 + 8);
lean_inc(x_5);
lean_inc_ref(x_81);
x_85 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(x_1, x_2, x_3, x_81, x_5, x_6, x_7, x_8);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec_ref(x_85);
x_88 = lean_ctor_get(x_86, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_86, 1);
lean_inc(x_89);
lean_dec(x_86);
lean_inc(x_5);
lean_inc_ref(x_82);
x_90 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(x_1, x_2, x_3, x_82, x_5, x_89, x_7, x_87);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec_ref(x_90);
x_93 = lean_ctor_get(x_91, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_91, 1);
lean_inc(x_94);
lean_dec(x_91);
x_95 = lean_unsigned_to_nat(1u);
x_96 = lean_nat_add(x_5, x_95);
lean_dec(x_5);
lean_inc_ref(x_83);
x_97 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(x_1, x_2, x_3, x_83, x_96, x_94, x_7, x_92);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_100 = x_97;
} else {
 lean_dec_ref(x_97);
 x_100 = lean_box(0);
}
x_101 = lean_ctor_get(x_98, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_98, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_103 = x_98;
} else {
 lean_dec_ref(x_98);
 x_103 = lean_box(0);
}
x_111 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_81, x_88);
if (x_111 == 0)
{
x_104 = x_111;
goto block_110;
}
else
{
uint8_t x_112; 
x_112 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_82, x_93);
x_104 = x_112;
goto block_110;
}
block_110:
{
if (x_104 == 0)
{
lean_object* x_105; 
lean_dec(x_103);
lean_dec(x_100);
lean_inc(x_80);
lean_dec_ref(x_4);
x_105 = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6(x_80, x_88, x_93, x_101, x_84, x_102, x_7, x_99);
return x_105;
}
else
{
uint8_t x_106; 
x_106 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_83, x_101);
if (x_106 == 0)
{
lean_object* x_107; 
lean_dec(x_103);
lean_dec(x_100);
lean_inc(x_80);
lean_dec_ref(x_4);
x_107 = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6(x_80, x_88, x_93, x_101, x_84, x_102, x_7, x_99);
return x_107;
}
else
{
lean_object* x_108; lean_object* x_109; 
lean_dec(x_101);
lean_dec(x_93);
lean_dec(x_88);
if (lean_is_scalar(x_103)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_103;
}
lean_ctor_set(x_108, 0, x_4);
lean_ctor_set(x_108, 1, x_102);
if (lean_is_scalar(x_100)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_100;
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_99);
return x_109;
}
}
}
}
case 10:
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_113 = lean_ctor_get(x_4, 0);
x_114 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_114);
x_115 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(x_1, x_2, x_3, x_114, x_5, x_6, x_7, x_8);
x_116 = !lean_is_exclusive(x_115);
if (x_116 == 0)
{
lean_object* x_117; uint8_t x_118; 
x_117 = lean_ctor_get(x_115, 0);
x_118 = !lean_is_exclusive(x_117);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_119 = lean_ctor_get(x_115, 1);
x_120 = lean_ctor_get(x_117, 0);
x_121 = lean_ctor_get(x_117, 1);
x_122 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_114, x_120);
if (x_122 == 0)
{
lean_object* x_123; 
lean_free_object(x_117);
lean_free_object(x_115);
lean_inc(x_113);
lean_dec_ref(x_4);
x_123 = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__7(x_113, x_120, x_121, x_7, x_119);
return x_123;
}
else
{
lean_dec(x_120);
lean_ctor_set(x_117, 0, x_4);
return x_115;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_124 = lean_ctor_get(x_115, 1);
x_125 = lean_ctor_get(x_117, 0);
x_126 = lean_ctor_get(x_117, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_117);
x_127 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_114, x_125);
if (x_127 == 0)
{
lean_object* x_128; 
lean_free_object(x_115);
lean_inc(x_113);
lean_dec_ref(x_4);
x_128 = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__7(x_113, x_125, x_126, x_7, x_124);
return x_128;
}
else
{
lean_object* x_129; 
lean_dec(x_125);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_4);
lean_ctor_set(x_129, 1, x_126);
lean_ctor_set(x_115, 0, x_129);
return x_115;
}
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_130 = lean_ctor_get(x_115, 0);
x_131 = lean_ctor_get(x_115, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_115);
x_132 = lean_ctor_get(x_130, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_130, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_134 = x_130;
} else {
 lean_dec_ref(x_130);
 x_134 = lean_box(0);
}
x_135 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_114, x_132);
if (x_135 == 0)
{
lean_object* x_136; 
lean_dec(x_134);
lean_inc(x_113);
lean_dec_ref(x_4);
x_136 = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__7(x_113, x_132, x_133, x_7, x_131);
return x_136;
}
else
{
lean_object* x_137; lean_object* x_138; 
lean_dec(x_132);
if (lean_is_scalar(x_134)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_134;
}
lean_ctor_set(x_137, 0, x_4);
lean_ctor_set(x_137, 1, x_133);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_131);
return x_138;
}
}
}
case 11:
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_139 = lean_ctor_get(x_4, 0);
x_140 = lean_ctor_get(x_4, 1);
x_141 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_141);
x_142 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(x_1, x_2, x_3, x_141, x_5, x_6, x_7, x_8);
x_143 = !lean_is_exclusive(x_142);
if (x_143 == 0)
{
lean_object* x_144; uint8_t x_145; 
x_144 = lean_ctor_get(x_142, 0);
x_145 = !lean_is_exclusive(x_144);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_146 = lean_ctor_get(x_142, 1);
x_147 = lean_ctor_get(x_144, 0);
x_148 = lean_ctor_get(x_144, 1);
x_149 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_141, x_147);
if (x_149 == 0)
{
lean_object* x_150; 
lean_free_object(x_144);
lean_free_object(x_142);
lean_inc(x_140);
lean_inc(x_139);
lean_dec_ref(x_4);
x_150 = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__8(x_139, x_140, x_147, x_148, x_7, x_146);
return x_150;
}
else
{
lean_dec(x_147);
lean_ctor_set(x_144, 0, x_4);
return x_142;
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_151 = lean_ctor_get(x_142, 1);
x_152 = lean_ctor_get(x_144, 0);
x_153 = lean_ctor_get(x_144, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_144);
x_154 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_141, x_152);
if (x_154 == 0)
{
lean_object* x_155; 
lean_free_object(x_142);
lean_inc(x_140);
lean_inc(x_139);
lean_dec_ref(x_4);
x_155 = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__8(x_139, x_140, x_152, x_153, x_7, x_151);
return x_155;
}
else
{
lean_object* x_156; 
lean_dec(x_152);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_4);
lean_ctor_set(x_156, 1, x_153);
lean_ctor_set(x_142, 0, x_156);
return x_142;
}
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_157 = lean_ctor_get(x_142, 0);
x_158 = lean_ctor_get(x_142, 1);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_142);
x_159 = lean_ctor_get(x_157, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_157, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_161 = x_157;
} else {
 lean_dec_ref(x_157);
 x_161 = lean_box(0);
}
x_162 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_141, x_159);
if (x_162 == 0)
{
lean_object* x_163; 
lean_dec(x_161);
lean_inc(x_140);
lean_inc(x_139);
lean_dec_ref(x_4);
x_163 = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__8(x_139, x_140, x_159, x_160, x_7, x_158);
return x_163;
}
else
{
lean_object* x_164; lean_object* x_165; 
lean_dec(x_159);
if (lean_is_scalar(x_161)) {
 x_164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_164 = x_161;
}
lean_ctor_set(x_164, 0, x_4);
lean_ctor_set(x_164, 1, x_160);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_158);
return x_165;
}
}
}
default: 
{
lean_object* x_166; lean_object* x_167; 
lean_dec(x_5);
lean_dec_ref(x_4);
x_166 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__3;
x_167 = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9(x_166, x_6, x_7, x_8);
return x_167;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
lean_inc(x_5);
lean_inc_ref(x_4);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_5);
x_10 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___redArg(x_6, x_9);
if (lean_obj_tag(x_10) == 1)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec_ref(x_9);
lean_dec(x_5);
lean_dec_ref(x_4);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
else
{
lean_dec(x_10);
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_4, 0);
x_15 = lean_nat_dec_le(x_5, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_5);
x_16 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(x_9, x_4, x_6, x_7, x_8);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_inc(x_14);
lean_dec_ref(x_4);
x_17 = lean_nat_add(x_5, x_1);
x_18 = lean_nat_dec_lt(x_14, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_5);
x_19 = lean_nat_sub(x_14, x_1);
lean_dec(x_14);
x_20 = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___redArg(x_19, x_8);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec_ref(x_20);
x_23 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(x_9, x_21, x_6, x_7, x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_24 = lean_nat_add(x_2, x_14);
lean_dec(x_14);
x_25 = lean_nat_sub(x_24, x_5);
lean_dec(x_24);
x_26 = lean_array_fget_borrowed(x_3, x_25);
lean_dec(x_25);
x_27 = lean_unsigned_to_nat(0u);
lean_inc(x_26);
x_28 = l_Lean_Meta_Sym_liftLooseBVarsS_x27(x_26, x_27, x_5, x_7, x_8);
lean_dec(x_5);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec_ref(x_28);
x_31 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(x_9, x_29, x_6, x_7, x_30);
return x_31;
}
}
}
case 9:
{
lean_object* x_32; 
lean_dec(x_5);
x_32 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(x_9, x_4, x_6, x_7, x_8);
return x_32;
}
case 2:
{
lean_object* x_33; 
lean_dec(x_5);
x_33 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(x_9, x_4, x_6, x_7, x_8);
return x_33;
}
case 1:
{
lean_object* x_34; 
lean_dec(x_5);
x_34 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(x_9, x_4, x_6, x_7, x_8);
return x_34;
}
case 4:
{
lean_object* x_35; 
lean_dec(x_5);
x_35 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(x_9, x_4, x_6, x_7, x_8);
return x_35;
}
case 3:
{
lean_object* x_36; 
lean_dec(x_5);
x_36 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(x_9, x_4, x_6, x_7, x_8);
return x_36;
}
default: 
{
lean_object* x_37; uint8_t x_38; 
x_37 = l_Lean_Expr_looseBVarRange(x_4);
x_38 = lean_nat_dec_le(x_37, x_5);
lean_dec(x_37);
if (x_38 == 0)
{
switch (lean_obj_tag(x_4)) {
case 9:
{
lean_object* x_39; 
lean_dec(x_5);
x_39 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(x_9, x_4, x_6, x_7, x_8);
return x_39;
}
case 2:
{
lean_object* x_40; 
lean_dec(x_5);
x_40 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(x_9, x_4, x_6, x_7, x_8);
return x_40;
}
case 0:
{
lean_object* x_41; 
lean_dec(x_5);
x_41 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(x_9, x_4, x_6, x_7, x_8);
return x_41;
}
case 1:
{
lean_object* x_42; 
lean_dec(x_5);
x_42 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(x_9, x_4, x_6, x_7, x_8);
return x_42;
}
case 4:
{
lean_object* x_43; 
lean_dec(x_5);
x_43 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(x_9, x_4, x_6, x_7, x_8);
return x_43;
}
case 3:
{
lean_object* x_44; 
lean_dec(x_5);
x_44 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(x_9, x_4, x_6, x_7, x_8);
return x_44;
}
default: 
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_45 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec_ref(x_45);
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
x_50 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(x_9, x_48, x_49, x_7, x_47);
return x_50;
}
}
}
else
{
lean_object* x_51; 
lean_dec(x_5);
x_51 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(x_9, x_4, x_6, x_7, x_8);
return x_51;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_7);
x_10 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_9, x_8);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_7);
x_10 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_9, x_8);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__2));
x_2 = lean_unsigned_to_nat(34u);
x_3 = lean_unsigned_to_nat(58u);
x_4 = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__0));
x_5 = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__3));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__2));
x_2 = lean_unsigned_to_nat(32u);
x_3 = lean_unsigned_to_nat(57u);
x_4 = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__0));
x_5 = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__3));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_lt(x_3, x_2);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_4);
x_9 = lean_nat_dec_lt(x_8, x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_nat_sub(x_3, x_2);
x_11 = lean_unsigned_to_nat(0u);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_nat_dec_le(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_6);
return x_14;
}
else
{
uint8_t x_15; 
lean_inc(x_12);
lean_dec_ref(x_1);
x_15 = lean_nat_dec_lt(x_12, x_10);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_nat_sub(x_12, x_10);
lean_dec(x_10);
lean_dec(x_12);
x_17 = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___redArg(x_16, x_6);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_10);
x_18 = lean_nat_add(x_2, x_12);
lean_dec(x_12);
x_19 = lean_array_fget_borrowed(x_4, x_18);
lean_dec(x_18);
lean_inc(x_19);
x_20 = l_Lean_Meta_Sym_liftLooseBVarsS_x27(x_19, x_11, x_11, x_5, x_6);
return x_20;
}
}
}
case 9:
{
lean_object* x_21; 
lean_dec(x_10);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_6);
return x_21;
}
case 2:
{
lean_object* x_22; 
lean_dec(x_10);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_6);
return x_22;
}
case 1:
{
lean_object* x_23; 
lean_dec(x_10);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_6);
return x_23;
}
case 4:
{
lean_object* x_24; 
lean_dec(x_10);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_6);
return x_24;
}
case 3:
{
lean_object* x_25; 
lean_dec(x_10);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_6);
return x_25;
}
default: 
{
lean_object* x_26; uint8_t x_27; 
x_26 = l_Lean_Expr_looseBVarRange(x_1);
x_27 = lean_nat_dec_le(x_26, x_11);
lean_dec(x_26);
if (x_27 == 0)
{
switch (lean_obj_tag(x_1)) {
case 9:
{
lean_object* x_28; 
lean_dec(x_10);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_6);
return x_28;
}
case 2:
{
lean_object* x_29; 
lean_dec(x_10);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_6);
return x_29;
}
case 0:
{
lean_object* x_30; 
lean_dec(x_10);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_6);
return x_30;
}
case 1:
{
lean_object* x_31; 
lean_dec(x_10);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_6);
return x_31;
}
case 4:
{
lean_object* x_32; 
lean_dec(x_10);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_6);
return x_32;
}
case 3:
{
lean_object* x_33; 
lean_dec(x_10);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_6);
return x_33;
}
default: 
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = l_Lean_Meta_Sym_instantiateRevRangeS___closed__2;
x_35 = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0(x_10, x_2, x_4, x_1, x_11, x_34, x_5, x_6);
lean_dec(x_10);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec_ref(x_35);
x_38 = !lean_is_exclusive(x_36);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_36, 1);
lean_dec(x_39);
lean_ctor_set(x_36, 1, x_37);
return x_36;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_36, 0);
lean_inc(x_40);
lean_dec(x_36);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_37);
return x_41;
}
}
}
}
else
{
lean_object* x_42; 
lean_dec(x_10);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_1);
lean_ctor_set(x_42, 1, x_6);
return x_42;
}
}
}
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_dec_ref(x_1);
x_43 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__1;
x_44 = l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1(x_43, x_5, x_6);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec_ref(x_1);
x_45 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__2;
x_46 = l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1(x_45, x_5, x_6);
return x_46;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_5);
x_8 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27(x_1, x_2, x_3, x_4, x_7, x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_array_get_size(x_2);
x_7 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27(x_1, x_5, x_6, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
x_6 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27(x_1, x_2, x_5, x_4);
lean_dec_ref(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateS___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_take(x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = l_Lean_Meta_Sym_instantiateRevRangeS___closed__0;
lean_ctor_set(x_5, 0, x_8);
x_9 = lean_st_ref_set(x_3, x_5);
x_10 = lean_st_ref_get(x_3);
x_11 = lean_ctor_get_uint8(x_10, sizeof(void*)*6);
lean_dec(x_10);
x_12 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27(x_1, x_2, x_11, x_7);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = lean_st_ref_take(x_3);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_14);
x_18 = lean_st_ref_set(x_3, x_15);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_13);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_15, 1);
x_21 = lean_ctor_get(x_15, 2);
x_22 = lean_ctor_get(x_15, 3);
x_23 = lean_ctor_get(x_15, 4);
x_24 = lean_ctor_get(x_15, 5);
x_25 = lean_ctor_get_uint8(x_15, sizeof(void*)*6);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_15);
x_26 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_26, 0, x_14);
lean_ctor_set(x_26, 1, x_20);
lean_ctor_set(x_26, 2, x_21);
lean_ctor_set(x_26, 3, x_22);
lean_ctor_set(x_26, 4, x_23);
lean_ctor_set(x_26, 5, x_24);
lean_ctor_set_uint8(x_26, sizeof(void*)*6, x_25);
x_27 = lean_st_ref_set(x_3, x_26);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_13);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_29 = lean_ctor_get(x_5, 0);
x_30 = lean_ctor_get(x_5, 1);
x_31 = lean_ctor_get(x_5, 2);
x_32 = lean_ctor_get(x_5, 3);
x_33 = lean_ctor_get(x_5, 4);
x_34 = lean_ctor_get(x_5, 5);
x_35 = lean_ctor_get_uint8(x_5, sizeof(void*)*6);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_5);
x_36 = l_Lean_Meta_Sym_instantiateRevRangeS___closed__0;
x_37 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_30);
lean_ctor_set(x_37, 2, x_31);
lean_ctor_set(x_37, 3, x_32);
lean_ctor_set(x_37, 4, x_33);
lean_ctor_set(x_37, 5, x_34);
lean_ctor_set_uint8(x_37, sizeof(void*)*6, x_35);
x_38 = lean_st_ref_set(x_3, x_37);
x_39 = lean_st_ref_get(x_3);
x_40 = lean_ctor_get_uint8(x_39, sizeof(void*)*6);
lean_dec(x_39);
x_41 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27(x_1, x_2, x_40, x_29);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec_ref(x_41);
x_44 = lean_st_ref_take(x_3);
x_45 = lean_ctor_get(x_44, 1);
lean_inc_ref(x_45);
x_46 = lean_ctor_get(x_44, 2);
lean_inc_ref(x_46);
x_47 = lean_ctor_get(x_44, 3);
lean_inc_ref(x_47);
x_48 = lean_ctor_get(x_44, 4);
lean_inc_ref(x_48);
x_49 = lean_ctor_get(x_44, 5);
lean_inc_ref(x_49);
x_50 = lean_ctor_get_uint8(x_44, sizeof(void*)*6);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 lean_ctor_release(x_44, 2);
 lean_ctor_release(x_44, 3);
 lean_ctor_release(x_44, 4);
 lean_ctor_release(x_44, 5);
 x_51 = x_44;
} else {
 lean_dec_ref(x_44);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(0, 6, 1);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_43);
lean_ctor_set(x_52, 1, x_45);
lean_ctor_set(x_52, 2, x_46);
lean_ctor_set(x_52, 3, x_47);
lean_ctor_set(x_52, 4, x_48);
lean_ctor_set(x_52, 5, x_49);
lean_ctor_set_uint8(x_52, sizeof(void*)*6, x_50);
x_53 = lean_st_ref_set(x_3, x_52);
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_42);
return x_54;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateS___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Sym_instantiateS___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateS(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Sym_instantiateS___redArg(x_1, x_2, x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateS___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Sym_instantiateS(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS_loop_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
if (x_3 == 0)
{
x_5 = x_4;
goto block_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc_ref(x_1);
x_9 = l_Lean_Meta_Sym_Internal_Builder_assertShared(x_1, x_3, x_4);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec_ref(x_9);
lean_inc_ref(x_2);
x_11 = l_Lean_Meta_Sym_Internal_Builder_assertShared(x_2, x_3, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec_ref(x_11);
x_5 = x_12;
goto block_8;
}
block_8:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_Expr_app___override(x_1, x_2);
x_7 = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(x_6, x_5);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS_loop_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
x_6 = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS_loop_spec__0(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_4, x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_4, x_8);
lean_dec(x_4);
x_10 = l_Lean_instInhabitedExpr;
x_11 = lean_array_get_borrowed(x_10, x_1, x_9);
lean_inc(x_11);
x_12 = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS_loop_spec__0(x_3, x_11, x_5, x_6);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_3 = x_13;
x_4 = x_9;
x_6 = x_14;
goto _start;
}
else
{
lean_object* x_16; 
lean_dec(x_4);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_3);
lean_ctor_set(x_16, 1, x_6);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_5);
x_8 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS_loop(x_1, x_2, x_3, x_4, x_7, x_6);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS_loop(x_4, x_2, x_1, x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_5);
x_8 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS(x_1, x_2, x_3, x_4, x_7, x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 6:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_7);
lean_dec_ref(x_3);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_4, x_8);
lean_dec(x_4);
x_10 = lean_nat_dec_lt(x_9, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_9);
x_11 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27(x_7, x_1, x_5, x_6);
return x_11;
}
else
{
x_3 = x_7;
x_4 = x_9;
goto _start;
}
}
case 10:
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_13);
lean_dec_ref(x_3);
x_3 = x_13;
goto _start;
}
default: 
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_nat_sub(x_2, x_4);
lean_dec(x_4);
x_16 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27(x_3, x_15, x_2, x_1, x_5, x_6);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS_loop(x_1, x_19, x_17, x_15, x_5, x_18);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_5);
x_8 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_go(x_1, x_2, x_3, x_4, x_7, x_6);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_go(x_2, x_5, x_1, x_6, x_3, x_4);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
x_6 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS(x_1, x_2, x_5, x_4);
lean_dec_ref(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; size_t x_18; size_t x_19; size_t x_20; size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_get_size(x_1);
x_9 = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(x_6);
x_10 = lean_uint64_of_nat(x_7);
x_11 = lean_uint64_mix_hash(x_9, x_10);
x_12 = 32;
x_13 = lean_uint64_shift_right(x_11, x_12);
x_14 = lean_uint64_xor(x_11, x_13);
x_15 = 16;
x_16 = lean_uint64_shift_right(x_14, x_15);
x_17 = lean_uint64_xor(x_14, x_16);
x_18 = lean_uint64_to_usize(x_17);
x_19 = lean_usize_of_nat(x_8);
x_20 = 1;
x_21 = lean_usize_sub(x_19, x_20);
x_22 = lean_usize_land(x_18, x_21);
x_23 = lean_array_uget(x_1, x_22);
lean_ctor_set(x_2, 2, x_23);
x_24 = lean_array_uset(x_1, x_22, x_2);
x_1 = x_24;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; size_t x_41; size_t x_42; size_t x_43; size_t x_44; size_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_26 = lean_ctor_get(x_2, 0);
x_27 = lean_ctor_get(x_2, 1);
x_28 = lean_ctor_get(x_2, 2);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_2);
x_29 = lean_ctor_get(x_26, 0);
x_30 = lean_ctor_get(x_26, 1);
x_31 = lean_array_get_size(x_1);
x_32 = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(x_29);
x_33 = lean_uint64_of_nat(x_30);
x_34 = lean_uint64_mix_hash(x_32, x_33);
x_35 = 32;
x_36 = lean_uint64_shift_right(x_34, x_35);
x_37 = lean_uint64_xor(x_34, x_36);
x_38 = 16;
x_39 = lean_uint64_shift_right(x_37, x_38);
x_40 = lean_uint64_xor(x_37, x_39);
x_41 = lean_uint64_to_usize(x_40);
x_42 = lean_usize_of_nat(x_31);
x_43 = 1;
x_44 = lean_usize_sub(x_42, x_43);
x_45 = lean_usize_land(x_41, x_44);
x_46 = lean_array_uget(x_1, x_45);
x_47 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_47, 0, x_26);
lean_ctor_set(x_47, 1, x_27);
lean_ctor_set(x_47, 2, x_46);
x_48 = lean_array_uset(x_1, x_45, x_47);
x_1 = x_48;
x_2 = x_28;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
if (x_5 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3___redArg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 x_7 = x_3;
} else {
 lean_dec_ref(x_3);
 x_7 = lean_box(0);
}
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
x_17 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_13, x_15);
if (x_17 == 0)
{
x_8 = x_17;
goto block_12;
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_eq(x_14, x_16);
x_8 = x_18;
goto block_12;
}
block_12:
{
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(x_1, x_2, x_6);
if (lean_is_scalar(x_7)) {
 x_10 = lean_alloc_ctor(1, 3, 0);
} else {
 x_10 = x_7;
}
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_5);
lean_ctor_set(x_10, 2, x_9);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_7)) {
 x_11 = lean_alloc_ctor(1, 3, 0);
} else {
 x_11 = x_7;
}
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_2);
lean_ctor_set(x_11, 2, x_6);
return x_11;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_9, x_11);
if (x_13 == 0)
{
x_6 = x_13;
goto block_8;
}
else
{
uint8_t x_14; 
x_14 = lean_nat_dec_eq(x_10, x_12);
x_6 = x_14;
goto block_8;
}
block_8:
{
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_6;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; size_t x_19; size_t x_20; size_t x_21; size_t x_22; size_t x_23; lean_object* x_24; uint8_t x_25; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_array_get_size(x_6);
x_10 = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(x_7);
x_11 = lean_uint64_of_nat(x_8);
x_12 = lean_uint64_mix_hash(x_10, x_11);
x_13 = 32;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = 16;
x_17 = lean_uint64_shift_right(x_15, x_16);
x_18 = lean_uint64_xor(x_15, x_17);
x_19 = lean_uint64_to_usize(x_18);
x_20 = lean_usize_of_nat(x_9);
x_21 = 1;
x_22 = lean_usize_sub(x_20, x_21);
x_23 = lean_usize_land(x_19, x_22);
x_24 = lean_array_uget(x_6, x_23);
x_25 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(x_2, x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_5, x_26);
lean_dec(x_5);
x_28 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_3);
lean_ctor_set(x_28, 2, x_24);
x_29 = lean_array_uset(x_6, x_23, x_28);
x_30 = lean_unsigned_to_nat(4u);
x_31 = lean_nat_mul(x_27, x_30);
x_32 = lean_unsigned_to_nat(3u);
x_33 = lean_nat_div(x_31, x_32);
lean_dec(x_31);
x_34 = lean_array_get_size(x_29);
x_35 = lean_nat_dec_le(x_33, x_34);
lean_dec(x_33);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1___redArg(x_29);
lean_ctor_set(x_1, 1, x_36);
lean_ctor_set(x_1, 0, x_27);
return x_1;
}
else
{
lean_ctor_set(x_1, 1, x_29);
lean_ctor_set(x_1, 0, x_27);
return x_1;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_box(0);
x_38 = lean_array_uset(x_6, x_23, x_37);
x_39 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(x_2, x_3, x_24);
x_40 = lean_array_uset(x_38, x_23, x_39);
lean_ctor_set(x_1, 1, x_40);
return x_1;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint64_t x_46; uint64_t x_47; uint64_t x_48; uint64_t x_49; uint64_t x_50; uint64_t x_51; uint64_t x_52; uint64_t x_53; uint64_t x_54; size_t x_55; size_t x_56; size_t x_57; size_t x_58; size_t x_59; lean_object* x_60; uint8_t x_61; 
x_41 = lean_ctor_get(x_1, 0);
x_42 = lean_ctor_get(x_1, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_1);
x_43 = lean_ctor_get(x_2, 0);
x_44 = lean_ctor_get(x_2, 1);
x_45 = lean_array_get_size(x_42);
x_46 = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(x_43);
x_47 = lean_uint64_of_nat(x_44);
x_48 = lean_uint64_mix_hash(x_46, x_47);
x_49 = 32;
x_50 = lean_uint64_shift_right(x_48, x_49);
x_51 = lean_uint64_xor(x_48, x_50);
x_52 = 16;
x_53 = lean_uint64_shift_right(x_51, x_52);
x_54 = lean_uint64_xor(x_51, x_53);
x_55 = lean_uint64_to_usize(x_54);
x_56 = lean_usize_of_nat(x_45);
x_57 = 1;
x_58 = lean_usize_sub(x_56, x_57);
x_59 = lean_usize_land(x_55, x_58);
x_60 = lean_array_uget(x_42, x_59);
x_61 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(x_2, x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_62 = lean_unsigned_to_nat(1u);
x_63 = lean_nat_add(x_41, x_62);
lean_dec(x_41);
x_64 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_64, 0, x_2);
lean_ctor_set(x_64, 1, x_3);
lean_ctor_set(x_64, 2, x_60);
x_65 = lean_array_uset(x_42, x_59, x_64);
x_66 = lean_unsigned_to_nat(4u);
x_67 = lean_nat_mul(x_63, x_66);
x_68 = lean_unsigned_to_nat(3u);
x_69 = lean_nat_div(x_67, x_68);
lean_dec(x_67);
x_70 = lean_array_get_size(x_65);
x_71 = lean_nat_dec_le(x_69, x_70);
lean_dec(x_69);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1___redArg(x_65);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_63);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
else
{
lean_object* x_74; 
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_63);
lean_ctor_set(x_74, 1, x_65);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_75 = lean_box(0);
x_76 = lean_array_uset(x_42, x_59, x_75);
x_77 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(x_2, x_3, x_60);
x_78 = lean_array_uset(x_76, x_59, x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_41);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc_ref(x_2);
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0___redArg(x_3, x_1, x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
x_7 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = l_Lean_Expr_bvar___override(x_1);
x_5 = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(x_4, x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 1);
lean_ctor_set(x_5, 1, x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0___redArg(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
x_6 = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_4, x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_5);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_dec_ref(x_2);
x_11 = lean_array_get_size(x_1);
x_12 = lean_nat_add(x_4, x_11);
x_13 = lean_nat_dec_lt(x_3, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_nat_sub(x_3, x_11);
x_15 = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0___redArg(x_14, x_5, x_7);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_16 = lean_nat_sub(x_3, x_4);
x_17 = lean_nat_sub(x_11, x_16);
lean_dec(x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_17, x_18);
lean_dec(x_17);
x_20 = lean_array_fget_borrowed(x_1, x_19);
lean_dec(x_19);
x_21 = lean_unsigned_to_nat(0u);
lean_inc(x_20);
x_22 = l_Lean_Meta_Sym_liftLooseBVarsS_x27(x_20, x_21, x_4, x_6, x_7);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 1);
lean_ctor_set(x_22, 1, x_5);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_22, 0);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_22);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_5);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_6);
x_9 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(x_1, x_2, x_3, x_4, x_5, x_8, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_9;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__2));
x_2 = lean_unsigned_to_nat(25u);
x_3 = lean_unsigned_to_nat(148u);
x_4 = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__1));
x_5 = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__2));
x_2 = lean_unsigned_to_nat(11u);
x_3 = lean_unsigned_to_nat(180u);
x_4 = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__0));
x_5 = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__3));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 5:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_11);
lean_dec_ref(x_3);
lean_inc(x_5);
lean_inc_ref(x_11);
x_12 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(x_1, x_11, x_5, x_7, x_8, x_9);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
lean_inc(x_15);
x_17 = lean_array_push(x_4, x_15);
if (x_6 == 0)
{
uint8_t x_18; 
x_18 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_11, x_15);
lean_dec(x_15);
lean_dec_ref(x_11);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = 1;
x_3 = x_10;
x_4 = x_17;
x_6 = x_19;
x_7 = x_16;
x_9 = x_14;
goto _start;
}
else
{
x_3 = x_10;
x_4 = x_17;
x_7 = x_16;
x_9 = x_14;
goto _start;
}
}
else
{
lean_dec(x_15);
lean_dec_ref(x_11);
x_3 = x_10;
x_4 = x_17;
x_7 = x_16;
x_9 = x_14;
goto _start;
}
}
case 0:
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_3);
x_24 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(x_1, x_3, x_23, x_5, x_7, x_8, x_9);
lean_dec(x_5);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_30 = x_26;
} else {
 lean_dec_ref(x_26);
 x_30 = lean_box(0);
}
if (x_6 == 0)
{
uint8_t x_40; 
x_40 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_3, x_28);
lean_dec_ref(x_3);
if (x_40 == 0)
{
lean_free_object(x_24);
lean_dec_ref(x_2);
goto block_39;
}
else
{
lean_object* x_41; 
lean_dec(x_30);
lean_dec(x_28);
lean_dec_ref(x_4);
lean_ctor_set(x_24, 1, x_29);
lean_ctor_set(x_24, 0, x_2);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_24);
lean_ctor_set(x_41, 1, x_27);
return x_41;
}
}
else
{
lean_free_object(x_24);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
goto block_39;
}
block_39:
{
lean_object* x_31; uint8_t x_32; 
x_31 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS(x_28, x_4, x_8, x_27);
lean_dec_ref(x_4);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 1);
lean_ctor_set(x_31, 1, x_29);
if (lean_is_scalar(x_30)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_30;
}
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_31, 0);
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_31);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_29);
if (lean_is_scalar(x_30)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_30;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_24, 0);
x_43 = lean_ctor_get(x_24, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_24);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_46 = x_42;
} else {
 lean_dec_ref(x_42);
 x_46 = lean_box(0);
}
if (x_6 == 0)
{
uint8_t x_54; 
x_54 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_3, x_44);
lean_dec_ref(x_3);
if (x_54 == 0)
{
lean_dec_ref(x_2);
goto block_53;
}
else
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_46);
lean_dec(x_44);
lean_dec_ref(x_4);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_2);
lean_ctor_set(x_55, 1, x_45);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_43);
return x_56;
}
}
else
{
lean_dec_ref(x_3);
lean_dec_ref(x_2);
goto block_53;
}
block_53:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS(x_44, x_4, x_8, x_43);
lean_dec_ref(x_4);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_50 = x_47;
} else {
 lean_dec_ref(x_47);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_45);
if (lean_is_scalar(x_46)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_46;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_49);
return x_52;
}
}
}
default: 
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_57 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__1;
x_58 = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9(x_57, x_7, x_8, x_9);
return x_58;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_inc(x_5);
lean_inc_ref(x_4);
x_9 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(x_1, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = l_Lean_Expr_getAppFn(x_3);
x_15 = l_Lean_Expr_isBVar(x_14);
lean_dec_ref(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_dec_ref(x_4);
x_16 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault(x_1, x_3, x_5, x_13, x_7, x_11);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_19 = x_16;
} else {
 lean_dec_ref(x_16);
 x_19 = lean_box(0);
}
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_22 = x_17;
} else {
 lean_dec_ref(x_17);
 x_22 = lean_box(0);
}
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_2, 0);
x_29 = lean_ctor_get(x_2, 1);
x_30 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_28, x_20);
if (x_30 == 0)
{
x_23 = x_30;
goto block_27;
}
else
{
uint8_t x_31; 
x_31 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_29, x_12);
x_23 = x_31;
goto block_27;
}
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_12);
lean_dec_ref(x_2);
x_32 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__3;
x_33 = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9(x_32, x_21, x_7, x_18);
return x_33;
}
block_27:
{
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec_ref(x_2);
x_24 = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__3(x_20, x_12, x_21, x_7, x_18);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_20);
lean_dec(x_12);
if (lean_is_scalar(x_22)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_22;
}
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_21);
if (lean_is_scalar(x_19)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_19;
}
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_18);
return x_26;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__4;
lean_inc(x_12);
x_35 = lean_array_push(x_34, x_12);
x_36 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_4, x_12);
lean_dec(x_12);
lean_dec_ref(x_4);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta(x_1, x_2, x_3, x_35, x_5, x_15, x_13, x_7, x_11);
return x_37;
}
else
{
uint8_t x_38; lean_object* x_39; 
x_38 = 0;
x_39 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta(x_1, x_2, x_3, x_35, x_5, x_38, x_13, x_7, x_11);
return x_39;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__2));
x_2 = lean_unsigned_to_nat(59u);
x_3 = lean_unsigned_to_nat(191u);
x_4 = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__0));
x_5 = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__3));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(x_1, x_2, x_7, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_7);
return x_8;
}
case 5:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_10);
x_11 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg(x_1, x_2, x_9, x_10, x_3, x_4, x_5, x_6);
return x_11;
}
case 6:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_35; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 2);
x_15 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc(x_3);
lean_inc_ref(x_13);
x_16 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(x_1, x_13, x_3, x_4, x_5, x_6);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_3, x_21);
lean_dec(x_3);
lean_inc_ref(x_14);
x_23 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(x_1, x_14, x_22, x_20, x_5, x_18);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_26 = x_23;
} else {
 lean_dec_ref(x_23);
 x_26 = lean_box(0);
}
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_29 = x_24;
} else {
 lean_dec_ref(x_24);
 x_29 = lean_box(0);
}
x_35 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_13, x_19);
if (x_35 == 0)
{
x_30 = x_35;
goto block_34;
}
else
{
uint8_t x_36; 
x_36 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_14, x_27);
x_30 = x_36;
goto block_34;
}
block_34:
{
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec(x_29);
lean_dec(x_26);
lean_inc(x_12);
lean_dec_ref(x_2);
x_31 = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__4(x_12, x_15, x_19, x_27, x_28, x_5, x_25);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_27);
lean_dec(x_19);
if (lean_is_scalar(x_29)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_29;
}
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_28);
if (lean_is_scalar(x_26)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_26;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_25);
return x_33;
}
}
}
case 7:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_60; 
x_37 = lean_ctor_get(x_2, 0);
x_38 = lean_ctor_get(x_2, 1);
x_39 = lean_ctor_get(x_2, 2);
x_40 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc(x_3);
lean_inc_ref(x_38);
x_41 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(x_1, x_38, x_3, x_4, x_5, x_6);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec_ref(x_41);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = lean_unsigned_to_nat(1u);
x_47 = lean_nat_add(x_3, x_46);
lean_dec(x_3);
lean_inc_ref(x_39);
x_48 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(x_1, x_39, x_47, x_45, x_5, x_43);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_51 = x_48;
} else {
 lean_dec_ref(x_48);
 x_51 = lean_box(0);
}
x_52 = lean_ctor_get(x_49, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_49, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_54 = x_49;
} else {
 lean_dec_ref(x_49);
 x_54 = lean_box(0);
}
x_60 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_38, x_44);
if (x_60 == 0)
{
x_55 = x_60;
goto block_59;
}
else
{
uint8_t x_61; 
x_61 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_39, x_52);
x_55 = x_61;
goto block_59;
}
block_59:
{
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_54);
lean_dec(x_51);
lean_inc(x_37);
lean_dec_ref(x_2);
x_56 = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__5(x_37, x_40, x_44, x_52, x_53, x_5, x_50);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_52);
lean_dec(x_44);
if (lean_is_scalar(x_54)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_54;
}
lean_ctor_set(x_57, 0, x_2);
lean_ctor_set(x_57, 1, x_53);
if (lean_is_scalar(x_51)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_51;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_50);
return x_58;
}
}
}
case 8:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; uint8_t x_93; 
x_62 = lean_ctor_get(x_2, 0);
x_63 = lean_ctor_get(x_2, 1);
x_64 = lean_ctor_get(x_2, 2);
x_65 = lean_ctor_get(x_2, 3);
x_66 = lean_ctor_get_uint8(x_2, sizeof(void*)*4 + 8);
lean_inc(x_3);
lean_inc_ref(x_63);
x_67 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(x_1, x_63, x_3, x_4, x_5, x_6);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec_ref(x_67);
x_70 = lean_ctor_get(x_68, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_dec(x_68);
lean_inc(x_3);
lean_inc_ref(x_64);
x_72 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(x_1, x_64, x_3, x_71, x_5, x_69);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec_ref(x_72);
x_75 = lean_ctor_get(x_73, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_dec(x_73);
x_77 = lean_unsigned_to_nat(1u);
x_78 = lean_nat_add(x_3, x_77);
lean_dec(x_3);
lean_inc_ref(x_65);
x_79 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(x_1, x_65, x_78, x_76, x_5, x_74);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_82 = x_79;
} else {
 lean_dec_ref(x_79);
 x_82 = lean_box(0);
}
x_83 = lean_ctor_get(x_80, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_80, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_85 = x_80;
} else {
 lean_dec_ref(x_80);
 x_85 = lean_box(0);
}
x_93 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_63, x_70);
if (x_93 == 0)
{
x_86 = x_93;
goto block_92;
}
else
{
uint8_t x_94; 
x_94 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_64, x_75);
x_86 = x_94;
goto block_92;
}
block_92:
{
if (x_86 == 0)
{
lean_object* x_87; 
lean_dec(x_85);
lean_dec(x_82);
lean_inc(x_62);
lean_dec_ref(x_2);
x_87 = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6(x_62, x_70, x_75, x_83, x_66, x_84, x_5, x_81);
return x_87;
}
else
{
uint8_t x_88; 
x_88 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_65, x_83);
if (x_88 == 0)
{
lean_object* x_89; 
lean_dec(x_85);
lean_dec(x_82);
lean_inc(x_62);
lean_dec_ref(x_2);
x_89 = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6(x_62, x_70, x_75, x_83, x_66, x_84, x_5, x_81);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_83);
lean_dec(x_75);
lean_dec(x_70);
if (lean_is_scalar(x_85)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_85;
}
lean_ctor_set(x_90, 0, x_2);
lean_ctor_set(x_90, 1, x_84);
if (lean_is_scalar(x_82)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_82;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_81);
return x_91;
}
}
}
}
case 10:
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_95 = lean_ctor_get(x_2, 0);
x_96 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_96);
x_97 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(x_1, x_96, x_3, x_4, x_5, x_6);
x_98 = !lean_is_exclusive(x_97);
if (x_98 == 0)
{
lean_object* x_99; uint8_t x_100; 
x_99 = lean_ctor_get(x_97, 0);
x_100 = !lean_is_exclusive(x_99);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_101 = lean_ctor_get(x_97, 1);
x_102 = lean_ctor_get(x_99, 0);
x_103 = lean_ctor_get(x_99, 1);
x_104 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_96, x_102);
if (x_104 == 0)
{
lean_object* x_105; 
lean_free_object(x_99);
lean_free_object(x_97);
lean_inc(x_95);
lean_dec_ref(x_2);
x_105 = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__7(x_95, x_102, x_103, x_5, x_101);
return x_105;
}
else
{
lean_dec(x_102);
lean_ctor_set(x_99, 0, x_2);
return x_97;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_106 = lean_ctor_get(x_97, 1);
x_107 = lean_ctor_get(x_99, 0);
x_108 = lean_ctor_get(x_99, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_99);
x_109 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_96, x_107);
if (x_109 == 0)
{
lean_object* x_110; 
lean_free_object(x_97);
lean_inc(x_95);
lean_dec_ref(x_2);
x_110 = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__7(x_95, x_107, x_108, x_5, x_106);
return x_110;
}
else
{
lean_object* x_111; 
lean_dec(x_107);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_2);
lean_ctor_set(x_111, 1, x_108);
lean_ctor_set(x_97, 0, x_111);
return x_97;
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_112 = lean_ctor_get(x_97, 0);
x_113 = lean_ctor_get(x_97, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_97);
x_114 = lean_ctor_get(x_112, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_112, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_116 = x_112;
} else {
 lean_dec_ref(x_112);
 x_116 = lean_box(0);
}
x_117 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_96, x_114);
if (x_117 == 0)
{
lean_object* x_118; 
lean_dec(x_116);
lean_inc(x_95);
lean_dec_ref(x_2);
x_118 = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__7(x_95, x_114, x_115, x_5, x_113);
return x_118;
}
else
{
lean_object* x_119; lean_object* x_120; 
lean_dec(x_114);
if (lean_is_scalar(x_116)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_116;
}
lean_ctor_set(x_119, 0, x_2);
lean_ctor_set(x_119, 1, x_115);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_113);
return x_120;
}
}
}
case 11:
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_121 = lean_ctor_get(x_2, 0);
x_122 = lean_ctor_get(x_2, 1);
x_123 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_123);
x_124 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(x_1, x_123, x_3, x_4, x_5, x_6);
x_125 = !lean_is_exclusive(x_124);
if (x_125 == 0)
{
lean_object* x_126; uint8_t x_127; 
x_126 = lean_ctor_get(x_124, 0);
x_127 = !lean_is_exclusive(x_126);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_128 = lean_ctor_get(x_124, 1);
x_129 = lean_ctor_get(x_126, 0);
x_130 = lean_ctor_get(x_126, 1);
x_131 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_123, x_129);
if (x_131 == 0)
{
lean_object* x_132; 
lean_free_object(x_126);
lean_free_object(x_124);
lean_inc(x_122);
lean_inc(x_121);
lean_dec_ref(x_2);
x_132 = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__8(x_121, x_122, x_129, x_130, x_5, x_128);
return x_132;
}
else
{
lean_dec(x_129);
lean_ctor_set(x_126, 0, x_2);
return x_124;
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_133 = lean_ctor_get(x_124, 1);
x_134 = lean_ctor_get(x_126, 0);
x_135 = lean_ctor_get(x_126, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_126);
x_136 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_123, x_134);
if (x_136 == 0)
{
lean_object* x_137; 
lean_free_object(x_124);
lean_inc(x_122);
lean_inc(x_121);
lean_dec_ref(x_2);
x_137 = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__8(x_121, x_122, x_134, x_135, x_5, x_133);
return x_137;
}
else
{
lean_object* x_138; 
lean_dec(x_134);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_2);
lean_ctor_set(x_138, 1, x_135);
lean_ctor_set(x_124, 0, x_138);
return x_124;
}
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_139 = lean_ctor_get(x_124, 0);
x_140 = lean_ctor_get(x_124, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_124);
x_141 = lean_ctor_get(x_139, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_139, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_143 = x_139;
} else {
 lean_dec_ref(x_139);
 x_143 = lean_box(0);
}
x_144 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_123, x_141);
if (x_144 == 0)
{
lean_object* x_145; 
lean_dec(x_143);
lean_inc(x_122);
lean_inc(x_121);
lean_dec_ref(x_2);
x_145 = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__8(x_121, x_122, x_141, x_142, x_5, x_140);
return x_145;
}
else
{
lean_object* x_146; lean_object* x_147; 
lean_dec(x_141);
if (lean_is_scalar(x_143)) {
 x_146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_146 = x_143;
}
lean_ctor_set(x_146, 0, x_2);
lean_ctor_set(x_146, 1, x_142);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_140);
return x_147;
}
}
}
default: 
{
lean_object* x_148; lean_object* x_149; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_148 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__1;
x_149 = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9(x_148, x_4, x_5, x_6);
return x_149;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Expr_looseBVarRange(x_2);
x_8 = lean_nat_dec_le(x_7, x_3);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_inc(x_3);
lean_inc_ref(x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_3);
x_10 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___redArg(x_4, x_9);
if (lean_obj_tag(x_10) == 1)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec_ref(x_9);
lean_dec(x_3);
lean_dec_ref(x_2);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_4);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_6);
return x_13;
}
else
{
lean_dec(x_10);
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(x_1, x_2, x_14, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(x_9, x_18, x_19, x_17);
return x_20;
}
case 9:
{
lean_object* x_21; 
lean_dec(x_3);
x_21 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(x_9, x_2, x_4, x_6);
return x_21;
}
case 2:
{
lean_object* x_22; 
lean_dec(x_3);
x_22 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(x_9, x_2, x_4, x_6);
return x_22;
}
case 1:
{
lean_object* x_23; 
lean_dec(x_3);
x_23 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(x_9, x_2, x_4, x_6);
return x_23;
}
case 4:
{
lean_object* x_24; 
lean_dec(x_3);
x_24 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(x_9, x_2, x_4, x_6);
return x_24;
}
case 3:
{
lean_object* x_25; 
lean_dec(x_3);
x_25 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(x_9, x_2, x_4, x_6);
return x_25;
}
default: 
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit(x_1, x_2, x_3, x_4, x_5, x_6);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec_ref(x_26);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(x_9, x_29, x_30, x_28);
return x_31;
}
}
}
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_3);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_4);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_6);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
lean_inc_ref(x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_3);
x_10 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___redArg(x_4, x_9);
if (lean_obj_tag(x_10) == 1)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec_ref(x_9);
lean_dec(x_3);
lean_dec_ref(x_2);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_4);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_6);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_33; 
lean_dec(x_10);
lean_inc(x_3);
lean_inc_ref(x_7);
x_14 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault(x_1, x_7, x_3, x_4, x_5, x_6);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
lean_inc_ref(x_8);
x_19 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(x_1, x_8, x_3, x_18, x_5, x_16);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_33 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_7, x_17);
if (x_33 == 0)
{
x_24 = x_33;
goto block_32;
}
else
{
uint8_t x_34; 
x_34 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_8, x_22);
x_24 = x_34;
goto block_32;
}
block_32:
{
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec_ref(x_2);
x_25 = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__3(x_17, x_22, x_23, x_5, x_21);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec_ref(x_25);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(x_9, x_28, x_29, x_27);
return x_30;
}
else
{
lean_object* x_31; 
lean_dec(x_22);
lean_dec(x_17);
x_31 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(x_9, x_2, x_23, x_21);
return x_31;
}
}
}
}
else
{
lean_object* x_35; 
x_35 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(x_1, x_2, x_3, x_4, x_5, x_6);
return x_35;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_5);
x_8 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault(x_1, x_2, x_3, x_4, x_7, x_6);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_5);
x_8 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(x_1, x_2, x_3, x_4, x_7, x_6);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_7);
x_10 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_9, x_8);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_6);
x_11 = lean_unbox(x_8);
x_12 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta(x_1, x_2, x_3, x_4, x_5, x_10, x_7, x_11, x_9);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_5);
x_8 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit(x_1, x_2, x_3, x_4, x_7, x_6);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg(x_1, x_2, x_3, x_4, x_5, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_8);
x_11 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_10, x_9);
lean_dec_ref(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_17; 
x_17 = l_Array_isEmpty___redArg(x_2);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = l_Lean_Expr_hasLooseBVars(x_1);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_4);
return x_19;
}
else
{
x_5 = x_17;
goto block_16;
}
}
else
{
x_5 = x_17;
goto block_16;
}
block_16:
{
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Meta_Sym_instantiateRevRangeS___closed__2;
x_8 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit(x_2, x_1, x_6, x_7, x_3, x_4);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_9, 1);
lean_dec(x_12);
lean_ctor_set(x_9, 1, x_10);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_4);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
x_6 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27(x_1, x_2, x_5, x_4);
lean_dec_ref(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevBetaS___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_Expr_hasLooseBVars(x_1);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_1);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = l_Array_isEmpty___redArg(x_2);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_st_ref_take(x_3);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_Lean_Meta_Sym_instantiateRevRangeS___closed__0;
lean_ctor_set(x_8, 0, x_11);
x_12 = lean_st_ref_set(x_3, x_8);
x_13 = lean_st_ref_get(x_3);
x_14 = lean_ctor_get_uint8(x_13, sizeof(void*)*6);
lean_dec(x_13);
x_15 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27(x_1, x_2, x_14, x_10);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = lean_st_ref_take(x_3);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_17);
x_21 = lean_st_ref_set(x_3, x_18);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_16);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_18, 1);
x_24 = lean_ctor_get(x_18, 2);
x_25 = lean_ctor_get(x_18, 3);
x_26 = lean_ctor_get(x_18, 4);
x_27 = lean_ctor_get(x_18, 5);
x_28 = lean_ctor_get_uint8(x_18, sizeof(void*)*6);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_18);
x_29 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_29, 0, x_17);
lean_ctor_set(x_29, 1, x_23);
lean_ctor_set(x_29, 2, x_24);
lean_ctor_set(x_29, 3, x_25);
lean_ctor_set(x_29, 4, x_26);
lean_ctor_set(x_29, 5, x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*6, x_28);
x_30 = lean_st_ref_set(x_3, x_29);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_16);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_32 = lean_ctor_get(x_8, 0);
x_33 = lean_ctor_get(x_8, 1);
x_34 = lean_ctor_get(x_8, 2);
x_35 = lean_ctor_get(x_8, 3);
x_36 = lean_ctor_get(x_8, 4);
x_37 = lean_ctor_get(x_8, 5);
x_38 = lean_ctor_get_uint8(x_8, sizeof(void*)*6);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_8);
x_39 = l_Lean_Meta_Sym_instantiateRevRangeS___closed__0;
x_40 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_33);
lean_ctor_set(x_40, 2, x_34);
lean_ctor_set(x_40, 3, x_35);
lean_ctor_set(x_40, 4, x_36);
lean_ctor_set(x_40, 5, x_37);
lean_ctor_set_uint8(x_40, sizeof(void*)*6, x_38);
x_41 = lean_st_ref_set(x_3, x_40);
x_42 = lean_st_ref_get(x_3);
x_43 = lean_ctor_get_uint8(x_42, sizeof(void*)*6);
lean_dec(x_42);
x_44 = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27(x_1, x_2, x_43, x_32);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec_ref(x_44);
x_47 = lean_st_ref_take(x_3);
x_48 = lean_ctor_get(x_47, 1);
lean_inc_ref(x_48);
x_49 = lean_ctor_get(x_47, 2);
lean_inc_ref(x_49);
x_50 = lean_ctor_get(x_47, 3);
lean_inc_ref(x_50);
x_51 = lean_ctor_get(x_47, 4);
lean_inc_ref(x_51);
x_52 = lean_ctor_get(x_47, 5);
lean_inc_ref(x_52);
x_53 = lean_ctor_get_uint8(x_47, sizeof(void*)*6);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 lean_ctor_release(x_47, 3);
 lean_ctor_release(x_47, 4);
 lean_ctor_release(x_47, 5);
 x_54 = x_47;
} else {
 lean_dec_ref(x_47);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(0, 6, 1);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_46);
lean_ctor_set(x_55, 1, x_48);
lean_ctor_set(x_55, 2, x_49);
lean_ctor_set(x_55, 3, x_50);
lean_ctor_set(x_55, 4, x_51);
lean_ctor_set(x_55, 5, x_52);
lean_ctor_set_uint8(x_55, sizeof(void*)*6, x_53);
x_56 = lean_st_ref_set(x_3, x_55);
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_45);
return x_57;
}
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_1);
return x_58;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevBetaS___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Sym_instantiateRevBetaS___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevBetaS(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Sym_instantiateRevBetaS___redArg(x_1, x_2, x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevBetaS___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Sym_instantiateRevBetaS(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_10;
}
}
lean_object* initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_ReplaceS(uint8_t builtin);
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
res = initialize_Lean_Meta_Sym_ReplaceS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_LooseBVarsS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___closed__0 = _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___closed__0();
lean_mark_persistent(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___closed__0);
l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___closed__1 = _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___closed__1();
lean_mark_persistent(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___closed__1);
l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__0 = _init_l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__0();
lean_mark_persistent(l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__0);
l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__3 = _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__3);
l_Lean_Meta_Sym_instantiateRevRangeS___closed__0 = _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__0();
lean_mark_persistent(l_Lean_Meta_Sym_instantiateRevRangeS___closed__0);
l_Lean_Meta_Sym_instantiateRevRangeS___closed__1 = _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__1();
lean_mark_persistent(l_Lean_Meta_Sym_instantiateRevRangeS___closed__1);
l_Lean_Meta_Sym_instantiateRevRangeS___closed__2 = _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__2();
lean_mark_persistent(l_Lean_Meta_Sym_instantiateRevRangeS___closed__2);
l_Lean_Meta_Sym_instantiateRevRangeS___closed__5 = _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__5();
lean_mark_persistent(l_Lean_Meta_Sym_instantiateRevRangeS___closed__5);
l_Lean_Meta_Sym_instantiateRevRangeS___closed__6 = _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__6();
lean_mark_persistent(l_Lean_Meta_Sym_instantiateRevRangeS___closed__6);
l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__1 = _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__1);
l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__2 = _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__2);
l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__3 = _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__3);
l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__4 = _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__4);
l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__1 = _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__1);
l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__1 = _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
