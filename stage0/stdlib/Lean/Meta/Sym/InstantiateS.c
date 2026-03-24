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
lean_object* l_Lean_Meta_Sym_instInhabitedSymM(lean_object*);
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
uint8_t v___y_22947__boxed_17_; lean_object* v_res_18_; 
v___y_22947__boxed_17_ = lean_unbox(v___y_15_);
v_res_18_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1(v_idx_14_, v___y_22947__boxed_17_, v___y_16_);
return v_res_18_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__0(void){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = l_Lean_Meta_Sym_instInhabitedSymM(lean_box(0));
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3(lean_object* v_msg_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_){
_start:
{
lean_object* v___x_28_; lean_object* v___x_3187__overap_29_; lean_object* v___x_30_; 
v___x_28_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__0, &l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__0);
v___x_3187__overap_29_ = lean_panic_fn(v___x_28_, v_msg_20_);
lean_inc(v___y_26_);
lean_inc_ref(v___y_25_);
lean_inc(v___y_24_);
lean_inc_ref(v___y_23_);
lean_inc(v___y_22_);
lean_inc_ref(v___y_21_);
v___x_30_ = lean_apply_7(v___x_3187__overap_29_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_, lean_box(0));
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___boxed(lean_object* v_msg_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3(v_msg_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_, v___y_36_, v___y_37_);
lean_dec(v___y_37_);
lean_dec_ref(v___y_36_);
lean_dec(v___y_35_);
lean_dec_ref(v___y_34_);
lean_dec(v___y_33_);
lean_dec_ref(v___y_32_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__5(lean_object* v_x_40_, uint8_t v_bi_41_, lean_object* v_t_42_, lean_object* v_b_43_, lean_object* v___y_44_, uint8_t v___y_45_, lean_object* v___y_46_){
_start:
{
lean_object* v___y_48_; lean_object* v___y_49_; 
if (v___y_45_ == 0)
{
v___y_48_ = v___y_44_;
v___y_49_ = v___y_46_;
goto v___jp_47_;
}
else
{
lean_object* v___x_62_; lean_object* v_snd_63_; lean_object* v___x_64_; lean_object* v_snd_65_; 
lean_inc_ref(v_t_42_);
v___x_62_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_42_, v___y_45_, v___y_46_);
v_snd_63_ = lean_ctor_get(v___x_62_, 1);
lean_inc(v_snd_63_);
lean_dec_ref(v___x_62_);
lean_inc_ref(v_b_43_);
v___x_64_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_43_, v___y_45_, v_snd_63_);
v_snd_65_ = lean_ctor_get(v___x_64_, 1);
lean_inc(v_snd_65_);
lean_dec_ref(v___x_64_);
v___y_48_ = v___y_44_;
v___y_49_ = v_snd_65_;
goto v___jp_47_;
}
v___jp_47_:
{
lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v_fst_52_; lean_object* v_snd_53_; lean_object* v___x_55_; uint8_t v_isShared_56_; uint8_t v_isSharedCheck_61_; 
v___x_50_ = l_Lean_Expr_forallE___override(v_x_40_, v_t_42_, v_b_43_, v_bi_41_);
v___x_51_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_50_, v___y_49_);
v_fst_52_ = lean_ctor_get(v___x_51_, 0);
v_snd_53_ = lean_ctor_get(v___x_51_, 1);
v_isSharedCheck_61_ = !lean_is_exclusive(v___x_51_);
if (v_isSharedCheck_61_ == 0)
{
v___x_55_ = v___x_51_;
v_isShared_56_ = v_isSharedCheck_61_;
goto v_resetjp_54_;
}
else
{
lean_inc(v_snd_53_);
lean_inc(v_fst_52_);
lean_dec(v___x_51_);
v___x_55_ = lean_box(0);
v_isShared_56_ = v_isSharedCheck_61_;
goto v_resetjp_54_;
}
v_resetjp_54_:
{
lean_object* v___x_58_; 
if (v_isShared_56_ == 0)
{
lean_ctor_set(v___x_55_, 1, v___y_48_);
v___x_58_ = v___x_55_;
goto v_reusejp_57_;
}
else
{
lean_object* v_reuseFailAlloc_60_; 
v_reuseFailAlloc_60_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_60_, 0, v_fst_52_);
lean_ctor_set(v_reuseFailAlloc_60_, 1, v___y_48_);
v___x_58_ = v_reuseFailAlloc_60_;
goto v_reusejp_57_;
}
v_reusejp_57_:
{
lean_object* v___x_59_; 
v___x_59_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_59_, 0, v___x_58_);
lean_ctor_set(v___x_59_, 1, v_snd_53_);
return v___x_59_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__5___boxed(lean_object* v_x_66_, lean_object* v_bi_67_, lean_object* v_t_68_, lean_object* v_b_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_){
_start:
{
uint8_t v_bi_boxed_73_; uint8_t v___y_22984__boxed_74_; lean_object* v_res_75_; 
v_bi_boxed_73_ = lean_unbox(v_bi_67_);
v___y_22984__boxed_74_ = lean_unbox(v___y_71_);
v_res_75_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__5(v_x_66_, v_bi_boxed_73_, v_t_68_, v_b_69_, v___y_70_, v___y_22984__boxed_74_, v___y_72_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9(lean_object* v_msg_83_, lean_object* v___y_84_, uint8_t v___y_85_, lean_object* v___y_86_){
_start:
{
lean_object* v___f_87_; lean_object* v___f_88_; lean_object* v___f_89_; lean_object* v___f_90_; lean_object* v___f_91_; lean_object* v___f_92_; lean_object* v___f_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___f_97_; lean_object* v___f_98_; lean_object* v___f_99_; lean_object* v___f_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___f_108_; lean_object* v___f_109_; lean_object* v___f_110_; lean_object* v___f_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_22613__overap_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v___f_87_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__0));
v___f_88_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__1));
v___f_89_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__2));
v___f_90_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__3));
v___f_91_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__4));
v___f_92_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__5));
v___f_93_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__6));
v___x_94_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_94_, 0, v___f_87_);
lean_ctor_set(v___x_94_, 1, v___f_88_);
v___x_95_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_95_, 0, v___x_94_);
lean_ctor_set(v___x_95_, 1, v___f_89_);
lean_ctor_set(v___x_95_, 2, v___f_90_);
lean_ctor_set(v___x_95_, 3, v___f_91_);
lean_ctor_set(v___x_95_, 4, v___f_92_);
v___x_96_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_96_, 0, v___x_95_);
lean_ctor_set(v___x_96_, 1, v___f_93_);
lean_inc_ref(v___x_96_);
v___f_97_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_97_, 0, v___x_96_);
lean_inc_ref(v___x_96_);
v___f_98_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_98_, 0, v___x_96_);
lean_inc_ref(v___x_96_);
v___f_99_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_99_, 0, v___x_96_);
lean_inc_ref(v___x_96_);
v___f_100_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_100_, 0, v___x_96_);
lean_inc_ref(v___x_96_);
v___x_101_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_101_, 0, lean_box(0));
lean_closure_set(v___x_101_, 1, lean_box(0));
lean_closure_set(v___x_101_, 2, v___x_96_);
v___x_102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
lean_ctor_set(v___x_102_, 1, v___f_97_);
lean_inc_ref(v___x_96_);
v___x_103_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_103_, 0, lean_box(0));
lean_closure_set(v___x_103_, 1, lean_box(0));
lean_closure_set(v___x_103_, 2, v___x_96_);
v___x_104_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_104_, 0, v___x_102_);
lean_ctor_set(v___x_104_, 1, v___x_103_);
lean_ctor_set(v___x_104_, 2, v___f_98_);
lean_ctor_set(v___x_104_, 3, v___f_99_);
lean_ctor_set(v___x_104_, 4, v___f_100_);
v___x_105_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_105_, 0, lean_box(0));
lean_closure_set(v___x_105_, 1, lean_box(0));
lean_closure_set(v___x_105_, 2, v___x_96_);
v___x_106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_106_, 0, v___x_104_);
lean_ctor_set(v___x_106_, 1, v___x_105_);
v___x_107_ = l_ReaderT_instMonad___redArg(v___x_106_);
lean_inc_ref(v___x_107_);
v___f_108_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_108_, 0, v___x_107_);
lean_inc_ref(v___x_107_);
v___f_109_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_109_, 0, v___x_107_);
lean_inc_ref(v___x_107_);
v___f_110_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_110_, 0, v___x_107_);
lean_inc_ref(v___x_107_);
v___f_111_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_111_, 0, v___x_107_);
lean_inc_ref(v___x_107_);
v___x_112_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_112_, 0, lean_box(0));
lean_closure_set(v___x_112_, 1, lean_box(0));
lean_closure_set(v___x_112_, 2, v___x_107_);
v___x_113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_113_, 0, v___x_112_);
lean_ctor_set(v___x_113_, 1, v___f_108_);
lean_inc_ref(v___x_107_);
v___x_114_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_114_, 0, lean_box(0));
lean_closure_set(v___x_114_, 1, lean_box(0));
lean_closure_set(v___x_114_, 2, v___x_107_);
v___x_115_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_115_, 0, v___x_113_);
lean_ctor_set(v___x_115_, 1, v___x_114_);
lean_ctor_set(v___x_115_, 2, v___f_109_);
lean_ctor_set(v___x_115_, 3, v___f_110_);
lean_ctor_set(v___x_115_, 4, v___f_111_);
v___x_116_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_116_, 0, lean_box(0));
lean_closure_set(v___x_116_, 1, lean_box(0));
lean_closure_set(v___x_116_, 2, v___x_107_);
v___x_117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_117_, 0, v___x_115_);
lean_ctor_set(v___x_117_, 1, v___x_116_);
v___x_118_ = l_Lean_instInhabitedExpr;
v___x_119_ = l_instInhabitedOfMonad___redArg(v___x_117_, v___x_118_);
v___x_22613__overap_120_ = lean_panic_fn(v___x_119_, v_msg_83_);
v___x_121_ = lean_box(v___y_85_);
v___x_122_ = lean_apply_3(v___x_22613__overap_120_, v___y_84_, v___x_121_, v___y_86_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___boxed(lean_object* v_msg_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_){
_start:
{
uint8_t v___y_23047__boxed_127_; lean_object* v_res_128_; 
v___y_23047__boxed_127_ = lean_unbox(v___y_125_);
v_res_128_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9(v_msg_123_, v___y_124_, v___y_23047__boxed_127_, v___y_126_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__8(lean_object* v_structName_129_, lean_object* v_idx_130_, lean_object* v_struct_131_, lean_object* v___y_132_, uint8_t v___y_133_, lean_object* v___y_134_){
_start:
{
lean_object* v___y_136_; lean_object* v___y_137_; 
if (v___y_133_ == 0)
{
v___y_136_ = v___y_132_;
v___y_137_ = v___y_134_;
goto v___jp_135_;
}
else
{
lean_object* v___x_150_; lean_object* v_snd_151_; 
lean_inc_ref(v_struct_131_);
v___x_150_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_struct_131_, v___y_133_, v___y_134_);
v_snd_151_ = lean_ctor_get(v___x_150_, 1);
lean_inc(v_snd_151_);
lean_dec_ref(v___x_150_);
v___y_136_ = v___y_132_;
v___y_137_ = v_snd_151_;
goto v___jp_135_;
}
v___jp_135_:
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v_fst_140_; lean_object* v_snd_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_149_; 
v___x_138_ = l_Lean_Expr_proj___override(v_structName_129_, v_idx_130_, v_struct_131_);
v___x_139_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_138_, v___y_137_);
v_fst_140_ = lean_ctor_get(v___x_139_, 0);
v_snd_141_ = lean_ctor_get(v___x_139_, 1);
v_isSharedCheck_149_ = !lean_is_exclusive(v___x_139_);
if (v_isSharedCheck_149_ == 0)
{
v___x_143_ = v___x_139_;
v_isShared_144_ = v_isSharedCheck_149_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_snd_141_);
lean_inc(v_fst_140_);
lean_dec(v___x_139_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_149_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_146_; 
if (v_isShared_144_ == 0)
{
lean_ctor_set(v___x_143_, 1, v___y_136_);
v___x_146_ = v___x_143_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v_fst_140_);
lean_ctor_set(v_reuseFailAlloc_148_, 1, v___y_136_);
v___x_146_ = v_reuseFailAlloc_148_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
lean_object* v___x_147_; 
v___x_147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
lean_ctor_set(v___x_147_, 1, v_snd_141_);
return v___x_147_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__8___boxed(lean_object* v_structName_152_, lean_object* v_idx_153_, lean_object* v_struct_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_){
_start:
{
uint8_t v___y_23133__boxed_158_; lean_object* v_res_159_; 
v___y_23133__boxed_158_ = lean_unbox(v___y_156_);
v_res_159_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__8(v_structName_152_, v_idx_153_, v_struct_154_, v___y_155_, v___y_23133__boxed_158_, v___y_157_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__4(lean_object* v_x_160_, uint8_t v_bi_161_, lean_object* v_t_162_, lean_object* v_b_163_, lean_object* v___y_164_, uint8_t v___y_165_, lean_object* v___y_166_){
_start:
{
lean_object* v___y_168_; lean_object* v___y_169_; 
if (v___y_165_ == 0)
{
v___y_168_ = v___y_164_;
v___y_169_ = v___y_166_;
goto v___jp_167_;
}
else
{
lean_object* v___x_182_; lean_object* v_snd_183_; lean_object* v___x_184_; lean_object* v_snd_185_; 
lean_inc_ref(v_t_162_);
v___x_182_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_162_, v___y_165_, v___y_166_);
v_snd_183_ = lean_ctor_get(v___x_182_, 1);
lean_inc(v_snd_183_);
lean_dec_ref(v___x_182_);
lean_inc_ref(v_b_163_);
v___x_184_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_163_, v___y_165_, v_snd_183_);
v_snd_185_ = lean_ctor_get(v___x_184_, 1);
lean_inc(v_snd_185_);
lean_dec_ref(v___x_184_);
v___y_168_ = v___y_164_;
v___y_169_ = v_snd_185_;
goto v___jp_167_;
}
v___jp_167_:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v_fst_172_; lean_object* v_snd_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_181_; 
v___x_170_ = l_Lean_Expr_lam___override(v_x_160_, v_t_162_, v_b_163_, v_bi_161_);
v___x_171_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_170_, v___y_169_);
v_fst_172_ = lean_ctor_get(v___x_171_, 0);
v_snd_173_ = lean_ctor_get(v___x_171_, 1);
v_isSharedCheck_181_ = !lean_is_exclusive(v___x_171_);
if (v_isSharedCheck_181_ == 0)
{
v___x_175_ = v___x_171_;
v_isShared_176_ = v_isSharedCheck_181_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_snd_173_);
lean_inc(v_fst_172_);
lean_dec(v___x_171_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_181_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_178_; 
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 1, v___y_168_);
v___x_178_ = v___x_175_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v_fst_172_);
lean_ctor_set(v_reuseFailAlloc_180_, 1, v___y_168_);
v___x_178_ = v_reuseFailAlloc_180_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
lean_object* v___x_179_; 
v___x_179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_179_, 0, v___x_178_);
lean_ctor_set(v___x_179_, 1, v_snd_173_);
return v___x_179_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__4___boxed(lean_object* v_x_186_, lean_object* v_bi_187_, lean_object* v_t_188_, lean_object* v_b_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_){
_start:
{
uint8_t v_bi_boxed_193_; uint8_t v___y_23177__boxed_194_; lean_object* v_res_195_; 
v_bi_boxed_193_ = lean_unbox(v_bi_187_);
v___y_23177__boxed_194_ = lean_unbox(v___y_191_);
v_res_195_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__4(v_x_186_, v_bi_boxed_193_, v_t_188_, v_b_189_, v___y_190_, v___y_23177__boxed_194_, v___y_192_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__7(lean_object* v_d_196_, lean_object* v_e_197_, lean_object* v___y_198_, uint8_t v___y_199_, lean_object* v___y_200_){
_start:
{
lean_object* v___y_202_; lean_object* v___y_203_; 
if (v___y_199_ == 0)
{
v___y_202_ = v___y_198_;
v___y_203_ = v___y_200_;
goto v___jp_201_;
}
else
{
lean_object* v___x_216_; lean_object* v_snd_217_; 
lean_inc_ref(v_e_197_);
v___x_216_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_e_197_, v___y_199_, v___y_200_);
v_snd_217_ = lean_ctor_get(v___x_216_, 1);
lean_inc(v_snd_217_);
lean_dec_ref(v___x_216_);
v___y_202_ = v___y_198_;
v___y_203_ = v_snd_217_;
goto v___jp_201_;
}
v___jp_201_:
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v_fst_206_; lean_object* v_snd_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_215_; 
v___x_204_ = l_Lean_Expr_mdata___override(v_d_196_, v_e_197_);
v___x_205_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_204_, v___y_203_);
v_fst_206_ = lean_ctor_get(v___x_205_, 0);
v_snd_207_ = lean_ctor_get(v___x_205_, 1);
v_isSharedCheck_215_ = !lean_is_exclusive(v___x_205_);
if (v_isSharedCheck_215_ == 0)
{
v___x_209_ = v___x_205_;
v_isShared_210_ = v_isSharedCheck_215_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_snd_207_);
lean_inc(v_fst_206_);
lean_dec(v___x_205_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_215_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_212_; 
if (v_isShared_210_ == 0)
{
lean_ctor_set(v___x_209_, 1, v___y_202_);
v___x_212_ = v___x_209_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_fst_206_);
lean_ctor_set(v_reuseFailAlloc_214_, 1, v___y_202_);
v___x_212_ = v_reuseFailAlloc_214_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
lean_object* v___x_213_; 
v___x_213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
lean_ctor_set(v___x_213_, 1, v_snd_207_);
return v___x_213_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__7___boxed(lean_object* v_d_218_, lean_object* v_e_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_){
_start:
{
uint8_t v___y_23226__boxed_223_; lean_object* v_res_224_; 
v___y_23226__boxed_223_ = lean_unbox(v___y_221_);
v_res_224_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__7(v_d_218_, v_e_219_, v___y_220_, v___y_23226__boxed_223_, v___y_222_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4_spec__12___redArg(lean_object* v_a_225_, lean_object* v_x_226_){
_start:
{
if (lean_obj_tag(v_x_226_) == 0)
{
lean_object* v___x_227_; 
v___x_227_ = lean_box(0);
return v___x_227_;
}
else
{
lean_object* v_key_228_; lean_object* v_value_229_; lean_object* v_tail_230_; uint8_t v___y_232_; lean_object* v_fst_235_; lean_object* v_snd_236_; lean_object* v_fst_237_; lean_object* v_snd_238_; uint8_t v___x_239_; 
v_key_228_ = lean_ctor_get(v_x_226_, 0);
v_value_229_ = lean_ctor_get(v_x_226_, 1);
v_tail_230_ = lean_ctor_get(v_x_226_, 2);
v_fst_235_ = lean_ctor_get(v_key_228_, 0);
v_snd_236_ = lean_ctor_get(v_key_228_, 1);
v_fst_237_ = lean_ctor_get(v_a_225_, 0);
v_snd_238_ = lean_ctor_get(v_a_225_, 1);
v___x_239_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_235_, v_fst_237_);
if (v___x_239_ == 0)
{
v___y_232_ = v___x_239_;
goto v___jp_231_;
}
else
{
uint8_t v___x_240_; 
v___x_240_ = lean_nat_dec_eq(v_snd_236_, v_snd_238_);
v___y_232_ = v___x_240_;
goto v___jp_231_;
}
v___jp_231_:
{
if (v___y_232_ == 0)
{
v_x_226_ = v_tail_230_;
goto _start;
}
else
{
lean_object* v___x_234_; 
lean_inc(v_value_229_);
v___x_234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_234_, 0, v_value_229_);
return v___x_234_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4_spec__12___redArg___boxed(lean_object* v_a_241_, lean_object* v_x_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4_spec__12___redArg(v_a_241_, v_x_242_);
lean_dec(v_x_242_);
lean_dec_ref(v_a_241_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___redArg(lean_object* v_m_244_, lean_object* v_a_245_){
_start:
{
lean_object* v_buckets_246_; lean_object* v_fst_247_; lean_object* v_snd_248_; lean_object* v___x_249_; uint64_t v___x_250_; uint64_t v___x_251_; uint64_t v___x_252_; uint64_t v___x_253_; uint64_t v___x_254_; uint64_t v_fold_255_; uint64_t v___x_256_; uint64_t v___x_257_; uint64_t v___x_258_; size_t v___x_259_; size_t v___x_260_; size_t v___x_261_; size_t v___x_262_; size_t v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v_buckets_246_ = lean_ctor_get(v_m_244_, 1);
v_fst_247_ = lean_ctor_get(v_a_245_, 0);
v_snd_248_ = lean_ctor_get(v_a_245_, 1);
v___x_249_ = lean_array_get_size(v_buckets_246_);
v___x_250_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_247_);
v___x_251_ = lean_uint64_of_nat(v_snd_248_);
v___x_252_ = lean_uint64_mix_hash(v___x_250_, v___x_251_);
v___x_253_ = 32ULL;
v___x_254_ = lean_uint64_shift_right(v___x_252_, v___x_253_);
v_fold_255_ = lean_uint64_xor(v___x_252_, v___x_254_);
v___x_256_ = 16ULL;
v___x_257_ = lean_uint64_shift_right(v_fold_255_, v___x_256_);
v___x_258_ = lean_uint64_xor(v_fold_255_, v___x_257_);
v___x_259_ = lean_uint64_to_usize(v___x_258_);
v___x_260_ = lean_usize_of_nat(v___x_249_);
v___x_261_ = ((size_t)1ULL);
v___x_262_ = lean_usize_sub(v___x_260_, v___x_261_);
v___x_263_ = lean_usize_land(v___x_259_, v___x_262_);
v___x_264_ = lean_array_uget_borrowed(v_buckets_246_, v___x_263_);
v___x_265_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4_spec__12___redArg(v_a_245_, v___x_264_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___redArg___boxed(lean_object* v_m_266_, lean_object* v_a_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___redArg(v_m_266_, v_a_267_);
lean_dec_ref(v_a_267_);
lean_dec_ref(v_m_266_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__3(lean_object* v_f_269_, lean_object* v_a_270_, lean_object* v___y_271_, uint8_t v___y_272_, lean_object* v___y_273_){
_start:
{
lean_object* v___y_275_; lean_object* v___y_276_; 
if (v___y_272_ == 0)
{
v___y_275_ = v___y_271_;
v___y_276_ = v___y_273_;
goto v___jp_274_;
}
else
{
lean_object* v___x_289_; lean_object* v_snd_290_; lean_object* v___x_291_; lean_object* v_snd_292_; 
lean_inc_ref(v_f_269_);
v___x_289_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_f_269_, v___y_272_, v___y_273_);
v_snd_290_ = lean_ctor_get(v___x_289_, 1);
lean_inc(v_snd_290_);
lean_dec_ref(v___x_289_);
lean_inc_ref(v_a_270_);
v___x_291_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_a_270_, v___y_272_, v_snd_290_);
v_snd_292_ = lean_ctor_get(v___x_291_, 1);
lean_inc(v_snd_292_);
lean_dec_ref(v___x_291_);
v___y_275_ = v___y_271_;
v___y_276_ = v_snd_292_;
goto v___jp_274_;
}
v___jp_274_:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v_fst_279_; lean_object* v_snd_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_288_; 
v___x_277_ = l_Lean_Expr_app___override(v_f_269_, v_a_270_);
v___x_278_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_277_, v___y_276_);
v_fst_279_ = lean_ctor_get(v___x_278_, 0);
v_snd_280_ = lean_ctor_get(v___x_278_, 1);
v_isSharedCheck_288_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_288_ == 0)
{
v___x_282_ = v___x_278_;
v_isShared_283_ = v_isSharedCheck_288_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_snd_280_);
lean_inc(v_fst_279_);
lean_dec(v___x_278_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_288_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___x_285_; 
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 1, v___y_275_);
v___x_285_ = v___x_282_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v_fst_279_);
lean_ctor_set(v_reuseFailAlloc_287_, 1, v___y_275_);
v___x_285_ = v_reuseFailAlloc_287_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
lean_object* v___x_286_; 
v___x_286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_285_);
lean_ctor_set(v___x_286_, 1, v_snd_280_);
return v___x_286_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__3___boxed(lean_object* v_f_293_, lean_object* v_a_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_){
_start:
{
uint8_t v___y_23339__boxed_298_; lean_object* v_res_299_; 
v___y_23339__boxed_298_ = lean_unbox(v___y_296_);
v_res_299_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__3(v_f_293_, v_a_294_, v___y_295_, v___y_23339__boxed_298_, v___y_297_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6(lean_object* v_x_300_, lean_object* v_t_301_, lean_object* v_v_302_, lean_object* v_b_303_, uint8_t v_nondep_304_, lean_object* v___y_305_, uint8_t v___y_306_, lean_object* v___y_307_){
_start:
{
lean_object* v___y_309_; lean_object* v___y_310_; 
if (v___y_306_ == 0)
{
v___y_309_ = v___y_305_;
v___y_310_ = v___y_307_;
goto v___jp_308_;
}
else
{
lean_object* v___x_323_; lean_object* v_snd_324_; lean_object* v___x_325_; lean_object* v_snd_326_; lean_object* v___x_327_; lean_object* v_snd_328_; 
lean_inc_ref(v_t_301_);
v___x_323_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_301_, v___y_306_, v___y_307_);
v_snd_324_ = lean_ctor_get(v___x_323_, 1);
lean_inc(v_snd_324_);
lean_dec_ref(v___x_323_);
lean_inc_ref(v_v_302_);
v___x_325_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_v_302_, v___y_306_, v_snd_324_);
v_snd_326_ = lean_ctor_get(v___x_325_, 1);
lean_inc(v_snd_326_);
lean_dec_ref(v___x_325_);
lean_inc_ref(v_b_303_);
v___x_327_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_303_, v___y_306_, v_snd_326_);
v_snd_328_ = lean_ctor_get(v___x_327_, 1);
lean_inc(v_snd_328_);
lean_dec_ref(v___x_327_);
v___y_309_ = v___y_305_;
v___y_310_ = v_snd_328_;
goto v___jp_308_;
}
v___jp_308_:
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v_fst_313_; lean_object* v_snd_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_322_; 
v___x_311_ = l_Lean_Expr_letE___override(v_x_300_, v_t_301_, v_v_302_, v_b_303_, v_nondep_304_);
v___x_312_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_311_, v___y_310_);
v_fst_313_ = lean_ctor_get(v___x_312_, 0);
v_snd_314_ = lean_ctor_get(v___x_312_, 1);
v_isSharedCheck_322_ = !lean_is_exclusive(v___x_312_);
if (v_isSharedCheck_322_ == 0)
{
v___x_316_ = v___x_312_;
v_isShared_317_ = v_isSharedCheck_322_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_snd_314_);
lean_inc(v_fst_313_);
lean_dec(v___x_312_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_322_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_319_; 
if (v_isShared_317_ == 0)
{
lean_ctor_set(v___x_316_, 1, v___y_309_);
v___x_319_ = v___x_316_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v_fst_313_);
lean_ctor_set(v_reuseFailAlloc_321_, 1, v___y_309_);
v___x_319_ = v_reuseFailAlloc_321_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
lean_object* v___x_320_; 
v___x_320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
lean_ctor_set(v___x_320_, 1, v_snd_314_);
return v___x_320_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6___boxed(lean_object* v_x_329_, lean_object* v_t_330_, lean_object* v_v_331_, lean_object* v_b_332_, lean_object* v_nondep_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_){
_start:
{
uint8_t v_nondep_boxed_337_; uint8_t v___y_23388__boxed_338_; lean_object* v_res_339_; 
v_nondep_boxed_337_ = lean_unbox(v_nondep_333_);
v___y_23388__boxed_338_ = lean_unbox(v___y_335_);
v_res_339_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6(v_x_329_, v_t_330_, v_v_331_, v_b_332_, v_nondep_boxed_337_, v___y_334_, v___y_23388__boxed_338_, v___y_336_);
return v_res_339_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__3(void){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_343_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__2));
v___x_344_ = lean_unsigned_to_nat(67u);
v___x_345_ = lean_unsigned_to_nat(35u);
v___x_346_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__1));
v___x_347_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__0));
v___x_348_ = l_mkPanicMessageWithDecl(v___x_347_, v___x_346_, v___x_345_, v___x_344_, v___x_343_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(lean_object* v_beginIdx_349_, lean_object* v_n_350_, lean_object* v_subst_351_, lean_object* v_e_352_, lean_object* v_offset_353_, lean_object* v_a_354_, uint8_t v_a_355_, lean_object* v_a_356_){
_start:
{
switch(lean_obj_tag(v_e_352_))
{
case 5:
{
lean_object* v_fn_357_; lean_object* v_arg_358_; lean_object* v___x_359_; lean_object* v_fst_360_; lean_object* v_snd_361_; lean_object* v_fst_362_; lean_object* v_snd_363_; lean_object* v___x_364_; lean_object* v_fst_365_; lean_object* v_snd_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_387_; 
v_fn_357_ = lean_ctor_get(v_e_352_, 0);
v_arg_358_ = lean_ctor_get(v_e_352_, 1);
lean_inc(v_offset_353_);
lean_inc_ref(v_fn_357_);
v___x_359_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(v_beginIdx_349_, v_n_350_, v_subst_351_, v_fn_357_, v_offset_353_, v_a_354_, v_a_355_, v_a_356_);
v_fst_360_ = lean_ctor_get(v___x_359_, 0);
lean_inc(v_fst_360_);
v_snd_361_ = lean_ctor_get(v___x_359_, 1);
lean_inc(v_snd_361_);
lean_dec_ref(v___x_359_);
v_fst_362_ = lean_ctor_get(v_fst_360_, 0);
lean_inc(v_fst_362_);
v_snd_363_ = lean_ctor_get(v_fst_360_, 1);
lean_inc(v_snd_363_);
lean_dec(v_fst_360_);
lean_inc_ref(v_arg_358_);
v___x_364_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(v_beginIdx_349_, v_n_350_, v_subst_351_, v_arg_358_, v_offset_353_, v_snd_363_, v_a_355_, v_snd_361_);
v_fst_365_ = lean_ctor_get(v___x_364_, 0);
v_snd_366_ = lean_ctor_get(v___x_364_, 1);
v_isSharedCheck_387_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_387_ == 0)
{
v___x_368_ = v___x_364_;
v_isShared_369_ = v_isSharedCheck_387_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_snd_366_);
lean_inc(v_fst_365_);
lean_dec(v___x_364_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_387_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v_fst_370_; lean_object* v_snd_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_386_; 
v_fst_370_ = lean_ctor_get(v_fst_365_, 0);
v_snd_371_ = lean_ctor_get(v_fst_365_, 1);
v_isSharedCheck_386_ = !lean_is_exclusive(v_fst_365_);
if (v_isSharedCheck_386_ == 0)
{
v___x_373_ = v_fst_365_;
v_isShared_374_ = v_isSharedCheck_386_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_snd_371_);
lean_inc(v_fst_370_);
lean_dec(v_fst_365_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_386_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
uint8_t v___y_376_; uint8_t v___x_384_; 
v___x_384_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_357_, v_fst_362_);
if (v___x_384_ == 0)
{
v___y_376_ = v___x_384_;
goto v___jp_375_;
}
else
{
uint8_t v___x_385_; 
v___x_385_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_358_, v_fst_370_);
v___y_376_ = v___x_385_;
goto v___jp_375_;
}
v___jp_375_:
{
if (v___y_376_ == 0)
{
lean_object* v___x_377_; 
lean_del_object(v___x_373_);
lean_del_object(v___x_368_);
lean_dec_ref(v_e_352_);
v___x_377_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__3(v_fst_362_, v_fst_370_, v_snd_371_, v_a_355_, v_snd_366_);
return v___x_377_;
}
else
{
lean_object* v___x_379_; 
lean_dec(v_fst_370_);
lean_dec(v_fst_362_);
if (v_isShared_374_ == 0)
{
lean_ctor_set(v___x_373_, 0, v_e_352_);
v___x_379_ = v___x_373_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_e_352_);
lean_ctor_set(v_reuseFailAlloc_383_, 1, v_snd_371_);
v___x_379_ = v_reuseFailAlloc_383_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
lean_object* v___x_381_; 
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 0, v___x_379_);
v___x_381_ = v___x_368_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v___x_379_);
lean_ctor_set(v_reuseFailAlloc_382_, 1, v_snd_366_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
}
}
}
}
}
case 6:
{
lean_object* v_binderName_388_; lean_object* v_binderType_389_; lean_object* v_body_390_; uint8_t v_binderInfo_391_; lean_object* v___x_392_; lean_object* v_fst_393_; lean_object* v_snd_394_; lean_object* v_fst_395_; lean_object* v_snd_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v_fst_400_; lean_object* v_snd_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_422_; 
v_binderName_388_ = lean_ctor_get(v_e_352_, 0);
v_binderType_389_ = lean_ctor_get(v_e_352_, 1);
v_body_390_ = lean_ctor_get(v_e_352_, 2);
v_binderInfo_391_ = lean_ctor_get_uint8(v_e_352_, sizeof(void*)*3 + 8);
lean_inc(v_offset_353_);
lean_inc_ref(v_binderType_389_);
v___x_392_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(v_beginIdx_349_, v_n_350_, v_subst_351_, v_binderType_389_, v_offset_353_, v_a_354_, v_a_355_, v_a_356_);
v_fst_393_ = lean_ctor_get(v___x_392_, 0);
lean_inc(v_fst_393_);
v_snd_394_ = lean_ctor_get(v___x_392_, 1);
lean_inc(v_snd_394_);
lean_dec_ref(v___x_392_);
v_fst_395_ = lean_ctor_get(v_fst_393_, 0);
lean_inc(v_fst_395_);
v_snd_396_ = lean_ctor_get(v_fst_393_, 1);
lean_inc(v_snd_396_);
lean_dec(v_fst_393_);
v___x_397_ = lean_unsigned_to_nat(1u);
v___x_398_ = lean_nat_add(v_offset_353_, v___x_397_);
lean_dec(v_offset_353_);
lean_inc_ref(v_body_390_);
v___x_399_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(v_beginIdx_349_, v_n_350_, v_subst_351_, v_body_390_, v___x_398_, v_snd_396_, v_a_355_, v_snd_394_);
v_fst_400_ = lean_ctor_get(v___x_399_, 0);
v_snd_401_ = lean_ctor_get(v___x_399_, 1);
v_isSharedCheck_422_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_422_ == 0)
{
v___x_403_ = v___x_399_;
v_isShared_404_ = v_isSharedCheck_422_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_snd_401_);
lean_inc(v_fst_400_);
lean_dec(v___x_399_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_422_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v_fst_405_; lean_object* v_snd_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_421_; 
v_fst_405_ = lean_ctor_get(v_fst_400_, 0);
v_snd_406_ = lean_ctor_get(v_fst_400_, 1);
v_isSharedCheck_421_ = !lean_is_exclusive(v_fst_400_);
if (v_isSharedCheck_421_ == 0)
{
v___x_408_ = v_fst_400_;
v_isShared_409_ = v_isSharedCheck_421_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_snd_406_);
lean_inc(v_fst_405_);
lean_dec(v_fst_400_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_421_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
uint8_t v___y_411_; uint8_t v___x_419_; 
v___x_419_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_389_, v_fst_395_);
if (v___x_419_ == 0)
{
v___y_411_ = v___x_419_;
goto v___jp_410_;
}
else
{
uint8_t v___x_420_; 
v___x_420_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_390_, v_fst_405_);
v___y_411_ = v___x_420_;
goto v___jp_410_;
}
v___jp_410_:
{
if (v___y_411_ == 0)
{
lean_object* v___x_412_; 
lean_inc(v_binderName_388_);
lean_del_object(v___x_408_);
lean_del_object(v___x_403_);
lean_dec_ref(v_e_352_);
v___x_412_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__4(v_binderName_388_, v_binderInfo_391_, v_fst_395_, v_fst_405_, v_snd_406_, v_a_355_, v_snd_401_);
return v___x_412_;
}
else
{
lean_object* v___x_414_; 
lean_dec(v_fst_405_);
lean_dec(v_fst_395_);
if (v_isShared_409_ == 0)
{
lean_ctor_set(v___x_408_, 0, v_e_352_);
v___x_414_ = v___x_408_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_e_352_);
lean_ctor_set(v_reuseFailAlloc_418_, 1, v_snd_406_);
v___x_414_ = v_reuseFailAlloc_418_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
lean_object* v___x_416_; 
if (v_isShared_404_ == 0)
{
lean_ctor_set(v___x_403_, 0, v___x_414_);
v___x_416_ = v___x_403_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v___x_414_);
lean_ctor_set(v_reuseFailAlloc_417_, 1, v_snd_401_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
}
}
}
}
case 7:
{
lean_object* v_binderName_423_; lean_object* v_binderType_424_; lean_object* v_body_425_; uint8_t v_binderInfo_426_; lean_object* v___x_427_; lean_object* v_fst_428_; lean_object* v_snd_429_; lean_object* v_fst_430_; lean_object* v_snd_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v_fst_435_; lean_object* v_snd_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_457_; 
v_binderName_423_ = lean_ctor_get(v_e_352_, 0);
v_binderType_424_ = lean_ctor_get(v_e_352_, 1);
v_body_425_ = lean_ctor_get(v_e_352_, 2);
v_binderInfo_426_ = lean_ctor_get_uint8(v_e_352_, sizeof(void*)*3 + 8);
lean_inc(v_offset_353_);
lean_inc_ref(v_binderType_424_);
v___x_427_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(v_beginIdx_349_, v_n_350_, v_subst_351_, v_binderType_424_, v_offset_353_, v_a_354_, v_a_355_, v_a_356_);
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
v___x_432_ = lean_unsigned_to_nat(1u);
v___x_433_ = lean_nat_add(v_offset_353_, v___x_432_);
lean_dec(v_offset_353_);
lean_inc_ref(v_body_425_);
v___x_434_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(v_beginIdx_349_, v_n_350_, v_subst_351_, v_body_425_, v___x_433_, v_snd_431_, v_a_355_, v_snd_429_);
v_fst_435_ = lean_ctor_get(v___x_434_, 0);
v_snd_436_ = lean_ctor_get(v___x_434_, 1);
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_434_);
if (v_isSharedCheck_457_ == 0)
{
v___x_438_ = v___x_434_;
v_isShared_439_ = v_isSharedCheck_457_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_snd_436_);
lean_inc(v_fst_435_);
lean_dec(v___x_434_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_457_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v_fst_440_; lean_object* v_snd_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_456_; 
v_fst_440_ = lean_ctor_get(v_fst_435_, 0);
v_snd_441_ = lean_ctor_get(v_fst_435_, 1);
v_isSharedCheck_456_ = !lean_is_exclusive(v_fst_435_);
if (v_isSharedCheck_456_ == 0)
{
v___x_443_ = v_fst_435_;
v_isShared_444_ = v_isSharedCheck_456_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_snd_441_);
lean_inc(v_fst_440_);
lean_dec(v_fst_435_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_456_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
uint8_t v___y_446_; uint8_t v___x_454_; 
v___x_454_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_424_, v_fst_430_);
if (v___x_454_ == 0)
{
v___y_446_ = v___x_454_;
goto v___jp_445_;
}
else
{
uint8_t v___x_455_; 
v___x_455_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_425_, v_fst_440_);
v___y_446_ = v___x_455_;
goto v___jp_445_;
}
v___jp_445_:
{
if (v___y_446_ == 0)
{
lean_object* v___x_447_; 
lean_inc(v_binderName_423_);
lean_del_object(v___x_443_);
lean_del_object(v___x_438_);
lean_dec_ref(v_e_352_);
v___x_447_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__5(v_binderName_423_, v_binderInfo_426_, v_fst_430_, v_fst_440_, v_snd_441_, v_a_355_, v_snd_436_);
return v___x_447_;
}
else
{
lean_object* v___x_449_; 
lean_dec(v_fst_440_);
lean_dec(v_fst_430_);
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 0, v_e_352_);
v___x_449_ = v___x_443_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_e_352_);
lean_ctor_set(v_reuseFailAlloc_453_, 1, v_snd_441_);
v___x_449_ = v_reuseFailAlloc_453_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
lean_object* v___x_451_; 
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 0, v___x_449_);
v___x_451_ = v___x_438_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v___x_449_);
lean_ctor_set(v_reuseFailAlloc_452_, 1, v_snd_436_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
}
}
}
}
case 8:
{
lean_object* v_declName_458_; lean_object* v_type_459_; lean_object* v_value_460_; lean_object* v_body_461_; uint8_t v_nondep_462_; lean_object* v___x_463_; lean_object* v_fst_464_; lean_object* v_snd_465_; lean_object* v_fst_466_; lean_object* v_snd_467_; lean_object* v___x_468_; lean_object* v_fst_469_; lean_object* v_snd_470_; lean_object* v_fst_471_; lean_object* v_snd_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v_fst_476_; lean_object* v_snd_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_500_; 
v_declName_458_ = lean_ctor_get(v_e_352_, 0);
v_type_459_ = lean_ctor_get(v_e_352_, 1);
v_value_460_ = lean_ctor_get(v_e_352_, 2);
v_body_461_ = lean_ctor_get(v_e_352_, 3);
v_nondep_462_ = lean_ctor_get_uint8(v_e_352_, sizeof(void*)*4 + 8);
lean_inc(v_offset_353_);
lean_inc_ref(v_type_459_);
v___x_463_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(v_beginIdx_349_, v_n_350_, v_subst_351_, v_type_459_, v_offset_353_, v_a_354_, v_a_355_, v_a_356_);
v_fst_464_ = lean_ctor_get(v___x_463_, 0);
lean_inc(v_fst_464_);
v_snd_465_ = lean_ctor_get(v___x_463_, 1);
lean_inc(v_snd_465_);
lean_dec_ref(v___x_463_);
v_fst_466_ = lean_ctor_get(v_fst_464_, 0);
lean_inc(v_fst_466_);
v_snd_467_ = lean_ctor_get(v_fst_464_, 1);
lean_inc(v_snd_467_);
lean_dec(v_fst_464_);
lean_inc(v_offset_353_);
lean_inc_ref(v_value_460_);
v___x_468_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(v_beginIdx_349_, v_n_350_, v_subst_351_, v_value_460_, v_offset_353_, v_snd_467_, v_a_355_, v_snd_465_);
v_fst_469_ = lean_ctor_get(v___x_468_, 0);
lean_inc(v_fst_469_);
v_snd_470_ = lean_ctor_get(v___x_468_, 1);
lean_inc(v_snd_470_);
lean_dec_ref(v___x_468_);
v_fst_471_ = lean_ctor_get(v_fst_469_, 0);
lean_inc(v_fst_471_);
v_snd_472_ = lean_ctor_get(v_fst_469_, 1);
lean_inc(v_snd_472_);
lean_dec(v_fst_469_);
v___x_473_ = lean_unsigned_to_nat(1u);
v___x_474_ = lean_nat_add(v_offset_353_, v___x_473_);
lean_dec(v_offset_353_);
lean_inc_ref(v_body_461_);
v___x_475_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(v_beginIdx_349_, v_n_350_, v_subst_351_, v_body_461_, v___x_474_, v_snd_472_, v_a_355_, v_snd_470_);
v_fst_476_ = lean_ctor_get(v___x_475_, 0);
v_snd_477_ = lean_ctor_get(v___x_475_, 1);
v_isSharedCheck_500_ = !lean_is_exclusive(v___x_475_);
if (v_isSharedCheck_500_ == 0)
{
v___x_479_ = v___x_475_;
v_isShared_480_ = v_isSharedCheck_500_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_snd_477_);
lean_inc(v_fst_476_);
lean_dec(v___x_475_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_500_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v_fst_481_; lean_object* v_snd_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_499_; 
v_fst_481_ = lean_ctor_get(v_fst_476_, 0);
v_snd_482_ = lean_ctor_get(v_fst_476_, 1);
v_isSharedCheck_499_ = !lean_is_exclusive(v_fst_476_);
if (v_isSharedCheck_499_ == 0)
{
v___x_484_ = v_fst_476_;
v_isShared_485_ = v_isSharedCheck_499_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_snd_482_);
lean_inc(v_fst_481_);
lean_dec(v_fst_476_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_499_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
uint8_t v___y_487_; uint8_t v___x_497_; 
v___x_497_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_type_459_, v_fst_466_);
if (v___x_497_ == 0)
{
v___y_487_ = v___x_497_;
goto v___jp_486_;
}
else
{
uint8_t v___x_498_; 
v___x_498_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_value_460_, v_fst_471_);
v___y_487_ = v___x_498_;
goto v___jp_486_;
}
v___jp_486_:
{
if (v___y_487_ == 0)
{
lean_object* v___x_488_; 
lean_inc(v_declName_458_);
lean_del_object(v___x_484_);
lean_del_object(v___x_479_);
lean_dec_ref(v_e_352_);
v___x_488_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6(v_declName_458_, v_fst_466_, v_fst_471_, v_fst_481_, v_nondep_462_, v_snd_482_, v_a_355_, v_snd_477_);
return v___x_488_;
}
else
{
uint8_t v___x_489_; 
v___x_489_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_461_, v_fst_481_);
if (v___x_489_ == 0)
{
lean_object* v___x_490_; 
lean_inc(v_declName_458_);
lean_del_object(v___x_484_);
lean_del_object(v___x_479_);
lean_dec_ref(v_e_352_);
v___x_490_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6(v_declName_458_, v_fst_466_, v_fst_471_, v_fst_481_, v_nondep_462_, v_snd_482_, v_a_355_, v_snd_477_);
return v___x_490_;
}
else
{
lean_object* v___x_492_; 
lean_dec(v_fst_481_);
lean_dec(v_fst_471_);
lean_dec(v_fst_466_);
if (v_isShared_485_ == 0)
{
lean_ctor_set(v___x_484_, 0, v_e_352_);
v___x_492_ = v___x_484_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_e_352_);
lean_ctor_set(v_reuseFailAlloc_496_, 1, v_snd_482_);
v___x_492_ = v_reuseFailAlloc_496_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
lean_object* v___x_494_; 
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 0, v___x_492_);
v___x_494_ = v___x_479_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v___x_492_);
lean_ctor_set(v_reuseFailAlloc_495_, 1, v_snd_477_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
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
lean_object* v_data_501_; lean_object* v_expr_502_; lean_object* v___x_503_; lean_object* v_fst_504_; lean_object* v_snd_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_523_; 
v_data_501_ = lean_ctor_get(v_e_352_, 0);
v_expr_502_ = lean_ctor_get(v_e_352_, 1);
lean_inc_ref(v_expr_502_);
v___x_503_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(v_beginIdx_349_, v_n_350_, v_subst_351_, v_expr_502_, v_offset_353_, v_a_354_, v_a_355_, v_a_356_);
v_fst_504_ = lean_ctor_get(v___x_503_, 0);
v_snd_505_ = lean_ctor_get(v___x_503_, 1);
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_523_ == 0)
{
v___x_507_ = v___x_503_;
v_isShared_508_ = v_isSharedCheck_523_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_snd_505_);
lean_inc(v_fst_504_);
lean_dec(v___x_503_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_523_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v_fst_509_; lean_object* v_snd_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_522_; 
v_fst_509_ = lean_ctor_get(v_fst_504_, 0);
v_snd_510_ = lean_ctor_get(v_fst_504_, 1);
v_isSharedCheck_522_ = !lean_is_exclusive(v_fst_504_);
if (v_isSharedCheck_522_ == 0)
{
v___x_512_ = v_fst_504_;
v_isShared_513_ = v_isSharedCheck_522_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_snd_510_);
lean_inc(v_fst_509_);
lean_dec(v_fst_504_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_522_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
uint8_t v___x_514_; 
v___x_514_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_expr_502_, v_fst_509_);
if (v___x_514_ == 0)
{
lean_object* v___x_515_; 
lean_inc(v_data_501_);
lean_del_object(v___x_512_);
lean_del_object(v___x_507_);
lean_dec_ref(v_e_352_);
v___x_515_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__7(v_data_501_, v_fst_509_, v_snd_510_, v_a_355_, v_snd_505_);
return v___x_515_;
}
else
{
lean_object* v___x_517_; 
lean_dec(v_fst_509_);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 0, v_e_352_);
v___x_517_ = v___x_512_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v_e_352_);
lean_ctor_set(v_reuseFailAlloc_521_, 1, v_snd_510_);
v___x_517_ = v_reuseFailAlloc_521_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
lean_object* v___x_519_; 
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 0, v___x_517_);
v___x_519_ = v___x_507_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v___x_517_);
lean_ctor_set(v_reuseFailAlloc_520_, 1, v_snd_505_);
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
case 11:
{
lean_object* v_typeName_524_; lean_object* v_idx_525_; lean_object* v_struct_526_; lean_object* v___x_527_; lean_object* v_fst_528_; lean_object* v_snd_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_547_; 
v_typeName_524_ = lean_ctor_get(v_e_352_, 0);
v_idx_525_ = lean_ctor_get(v_e_352_, 1);
v_struct_526_ = lean_ctor_get(v_e_352_, 2);
lean_inc_ref(v_struct_526_);
v___x_527_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(v_beginIdx_349_, v_n_350_, v_subst_351_, v_struct_526_, v_offset_353_, v_a_354_, v_a_355_, v_a_356_);
v_fst_528_ = lean_ctor_get(v___x_527_, 0);
v_snd_529_ = lean_ctor_get(v___x_527_, 1);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_547_ == 0)
{
v___x_531_ = v___x_527_;
v_isShared_532_ = v_isSharedCheck_547_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_snd_529_);
lean_inc(v_fst_528_);
lean_dec(v___x_527_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_547_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v_fst_533_; lean_object* v_snd_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_546_; 
v_fst_533_ = lean_ctor_get(v_fst_528_, 0);
v_snd_534_ = lean_ctor_get(v_fst_528_, 1);
v_isSharedCheck_546_ = !lean_is_exclusive(v_fst_528_);
if (v_isSharedCheck_546_ == 0)
{
v___x_536_ = v_fst_528_;
v_isShared_537_ = v_isSharedCheck_546_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_snd_534_);
lean_inc(v_fst_533_);
lean_dec(v_fst_528_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_546_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
uint8_t v___x_538_; 
v___x_538_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_526_, v_fst_533_);
if (v___x_538_ == 0)
{
lean_object* v___x_539_; 
lean_inc(v_idx_525_);
lean_inc(v_typeName_524_);
lean_del_object(v___x_536_);
lean_del_object(v___x_531_);
lean_dec_ref(v_e_352_);
v___x_539_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__8(v_typeName_524_, v_idx_525_, v_fst_533_, v_snd_534_, v_a_355_, v_snd_529_);
return v___x_539_;
}
else
{
lean_object* v___x_541_; 
lean_dec(v_fst_533_);
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 0, v_e_352_);
v___x_541_ = v___x_536_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_e_352_);
lean_ctor_set(v_reuseFailAlloc_545_, 1, v_snd_534_);
v___x_541_ = v_reuseFailAlloc_545_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
lean_object* v___x_543_; 
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 0, v___x_541_);
v___x_543_ = v___x_531_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v___x_541_);
lean_ctor_set(v_reuseFailAlloc_544_, 1, v_snd_529_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_548_; lean_object* v___x_549_; 
lean_dec(v_offset_353_);
lean_dec_ref(v_e_352_);
v___x_548_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__3);
v___x_549_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9(v___x_548_, v_a_354_, v_a_355_, v_a_356_);
return v___x_549_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(lean_object* v_beginIdx_550_, lean_object* v_n_551_, lean_object* v_subst_552_, lean_object* v_e_553_, lean_object* v_offset_554_, lean_object* v_a_555_, uint8_t v_a_556_, lean_object* v_a_557_){
_start:
{
lean_object* v_key_558_; lean_object* v___x_559_; 
lean_inc(v_offset_554_);
lean_inc_ref(v_e_553_);
v_key_558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_558_, 0, v_e_553_);
lean_ctor_set(v_key_558_, 1, v_offset_554_);
v___x_559_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___redArg(v_a_555_, v_key_558_);
if (lean_obj_tag(v___x_559_) == 1)
{
lean_object* v_val_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
lean_dec_ref(v_key_558_);
lean_dec(v_offset_554_);
lean_dec_ref(v_e_553_);
v_val_560_ = lean_ctor_get(v___x_559_, 0);
lean_inc(v_val_560_);
lean_dec_ref(v___x_559_);
v___x_561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_561_, 0, v_val_560_);
lean_ctor_set(v___x_561_, 1, v_a_555_);
v___x_562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_562_, 0, v___x_561_);
lean_ctor_set(v___x_562_, 1, v_a_557_);
return v___x_562_;
}
else
{
lean_object* v_s_u2081_563_; 
lean_dec(v___x_559_);
v_s_u2081_563_ = lean_nat_add(v_beginIdx_550_, v_offset_554_);
switch(lean_obj_tag(v_e_553_))
{
case 0:
{
lean_object* v_deBruijnIndex_564_; uint8_t v___x_565_; 
v_deBruijnIndex_564_ = lean_ctor_get(v_e_553_, 0);
v___x_565_ = lean_nat_dec_le(v_s_u2081_563_, v_deBruijnIndex_564_);
lean_dec(v_s_u2081_563_);
if (v___x_565_ == 0)
{
lean_object* v___x_566_; 
lean_dec(v_offset_554_);
v___x_566_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_558_, v_e_553_, v_a_555_, v_a_556_, v_a_557_);
return v___x_566_;
}
else
{
lean_object* v___x_567_; uint8_t v___x_568_; 
lean_inc(v_deBruijnIndex_564_);
lean_dec_ref(v_e_553_);
v___x_567_ = lean_nat_add(v_offset_554_, v_n_551_);
v___x_568_ = lean_nat_dec_lt(v_deBruijnIndex_564_, v___x_567_);
lean_dec(v___x_567_);
if (v___x_568_ == 0)
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v_fst_571_; lean_object* v_snd_572_; lean_object* v___x_573_; 
lean_dec(v_offset_554_);
v___x_569_ = lean_nat_sub(v_deBruijnIndex_564_, v_n_551_);
lean_dec(v_deBruijnIndex_564_);
v___x_570_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___redArg(v___x_569_, v_a_557_);
v_fst_571_ = lean_ctor_get(v___x_570_, 0);
lean_inc(v_fst_571_);
v_snd_572_ = lean_ctor_get(v___x_570_, 1);
lean_inc(v_snd_572_);
lean_dec_ref(v___x_570_);
v___x_573_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_558_, v_fst_571_, v_a_555_, v_a_556_, v_snd_572_);
return v___x_573_;
}
else
{
lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v_v_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v_fst_581_; lean_object* v_snd_582_; lean_object* v___x_583_; 
v___x_574_ = lean_nat_sub(v_deBruijnIndex_564_, v_offset_554_);
lean_dec(v_deBruijnIndex_564_);
v___x_575_ = lean_nat_sub(v_n_551_, v___x_574_);
lean_dec(v___x_574_);
v___x_576_ = lean_unsigned_to_nat(1u);
v___x_577_ = lean_nat_sub(v___x_575_, v___x_576_);
lean_dec(v___x_575_);
v_v_578_ = lean_array_fget_borrowed(v_subst_552_, v___x_577_);
lean_dec(v___x_577_);
v___x_579_ = lean_unsigned_to_nat(0u);
lean_inc(v_v_578_);
v___x_580_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(v_v_578_, v___x_579_, v_offset_554_, v_a_556_, v_a_557_);
lean_dec(v_offset_554_);
v_fst_581_ = lean_ctor_get(v___x_580_, 0);
lean_inc(v_fst_581_);
v_snd_582_ = lean_ctor_get(v___x_580_, 1);
lean_inc(v_snd_582_);
lean_dec_ref(v___x_580_);
v___x_583_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_558_, v_fst_581_, v_a_555_, v_a_556_, v_snd_582_);
return v___x_583_;
}
}
}
case 9:
{
lean_object* v___x_584_; 
lean_dec(v_s_u2081_563_);
lean_dec(v_offset_554_);
v___x_584_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_558_, v_e_553_, v_a_555_, v_a_556_, v_a_557_);
return v___x_584_;
}
case 2:
{
lean_object* v___x_585_; 
lean_dec(v_s_u2081_563_);
lean_dec(v_offset_554_);
v___x_585_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_558_, v_e_553_, v_a_555_, v_a_556_, v_a_557_);
return v___x_585_;
}
case 1:
{
lean_object* v___x_586_; 
lean_dec(v_s_u2081_563_);
lean_dec(v_offset_554_);
v___x_586_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_558_, v_e_553_, v_a_555_, v_a_556_, v_a_557_);
return v___x_586_;
}
case 4:
{
lean_object* v___x_587_; 
lean_dec(v_s_u2081_563_);
lean_dec(v_offset_554_);
v___x_587_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_558_, v_e_553_, v_a_555_, v_a_556_, v_a_557_);
return v___x_587_;
}
case 3:
{
lean_object* v___x_588_; 
lean_dec(v_s_u2081_563_);
lean_dec(v_offset_554_);
v___x_588_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_558_, v_e_553_, v_a_555_, v_a_556_, v_a_557_);
return v___x_588_;
}
default: 
{
lean_object* v___x_589_; uint8_t v___x_590_; 
v___x_589_ = l_Lean_Expr_looseBVarRange(v_e_553_);
v___x_590_ = lean_nat_dec_le(v___x_589_, v_s_u2081_563_);
lean_dec(v_s_u2081_563_);
lean_dec(v___x_589_);
if (v___x_590_ == 0)
{
switch(lean_obj_tag(v_e_553_))
{
case 9:
{
lean_object* v___x_591_; 
lean_dec(v_offset_554_);
v___x_591_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_558_, v_e_553_, v_a_555_, v_a_556_, v_a_557_);
return v___x_591_;
}
case 2:
{
lean_object* v___x_592_; 
lean_dec(v_offset_554_);
v___x_592_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_558_, v_e_553_, v_a_555_, v_a_556_, v_a_557_);
return v___x_592_;
}
case 0:
{
lean_object* v___x_593_; 
lean_dec(v_offset_554_);
v___x_593_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_558_, v_e_553_, v_a_555_, v_a_556_, v_a_557_);
return v___x_593_;
}
case 1:
{
lean_object* v___x_594_; 
lean_dec(v_offset_554_);
v___x_594_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_558_, v_e_553_, v_a_555_, v_a_556_, v_a_557_);
return v___x_594_;
}
case 4:
{
lean_object* v___x_595_; 
lean_dec(v_offset_554_);
v___x_595_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_558_, v_e_553_, v_a_555_, v_a_556_, v_a_557_);
return v___x_595_;
}
case 3:
{
lean_object* v___x_596_; 
lean_dec(v_offset_554_);
v___x_596_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_558_, v_e_553_, v_a_555_, v_a_556_, v_a_557_);
return v___x_596_;
}
default: 
{
lean_object* v___x_597_; lean_object* v_fst_598_; lean_object* v_snd_599_; lean_object* v_fst_600_; lean_object* v_snd_601_; lean_object* v___x_602_; 
v___x_597_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(v_beginIdx_550_, v_n_551_, v_subst_552_, v_e_553_, v_offset_554_, v_a_555_, v_a_556_, v_a_557_);
v_fst_598_ = lean_ctor_get(v___x_597_, 0);
lean_inc(v_fst_598_);
v_snd_599_ = lean_ctor_get(v___x_597_, 1);
lean_inc(v_snd_599_);
lean_dec_ref(v___x_597_);
v_fst_600_ = lean_ctor_get(v_fst_598_, 0);
lean_inc(v_fst_600_);
v_snd_601_ = lean_ctor_get(v_fst_598_, 1);
lean_inc(v_snd_601_);
lean_dec(v_fst_598_);
v___x_602_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_558_, v_fst_600_, v_snd_601_, v_a_556_, v_snd_599_);
return v___x_602_;
}
}
}
else
{
lean_object* v___x_603_; 
lean_dec(v_offset_554_);
v___x_603_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_558_, v_e_553_, v_a_555_, v_a_556_, v_a_557_);
return v___x_603_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2___boxed(lean_object* v_beginIdx_604_, lean_object* v_n_605_, lean_object* v_subst_606_, lean_object* v_e_607_, lean_object* v_offset_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_){
_start:
{
uint8_t v_a_boxed_612_; lean_object* v_res_613_; 
v_a_boxed_612_ = lean_unbox(v_a_610_);
v_res_613_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(v_beginIdx_604_, v_n_605_, v_subst_606_, v_e_607_, v_offset_608_, v_a_609_, v_a_boxed_612_, v_a_611_);
lean_dec_ref(v_subst_606_);
lean_dec(v_n_605_);
lean_dec(v_beginIdx_604_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___boxed(lean_object* v_beginIdx_614_, lean_object* v_n_615_, lean_object* v_subst_616_, lean_object* v_e_617_, lean_object* v_offset_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_){
_start:
{
uint8_t v_a_boxed_622_; lean_object* v_res_623_; 
v_a_boxed_622_ = lean_unbox(v_a_620_);
v_res_623_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(v_beginIdx_614_, v_n_615_, v_subst_616_, v_e_617_, v_offset_618_, v_a_619_, v_a_boxed_622_, v_a_621_);
lean_dec_ref(v_subst_616_);
lean_dec(v_n_615_);
lean_dec(v_beginIdx_614_);
return v_res_623_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__0(void){
_start:
{
lean_object* v___x_624_; 
v___x_624_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0(lean_box(0));
return v___x_624_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__1(void){
_start:
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_625_ = lean_box(0);
v___x_626_ = lean_unsigned_to_nat(16u);
v___x_627_ = lean_mk_array(v___x_626_, v___x_625_);
return v___x_627_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__2(void){
_start:
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_628_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__1, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__1_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__1);
v___x_629_ = lean_unsigned_to_nat(0u);
v___x_630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
lean_ctor_set(v___x_630_, 1, v___x_628_);
return v___x_630_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__5(void){
_start:
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_633_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__2));
v___x_634_ = lean_unsigned_to_nat(34u);
v___x_635_ = lean_unsigned_to_nat(20u);
v___x_636_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__4));
v___x_637_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__3));
v___x_638_ = l_mkPanicMessageWithDecl(v___x_637_, v___x_636_, v___x_635_, v___x_634_, v___x_633_);
return v___x_638_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__6(void){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_639_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__2));
v___x_640_ = lean_unsigned_to_nat(32u);
v___x_641_ = lean_unsigned_to_nat(19u);
v___x_642_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__4));
v___x_643_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__3));
v___x_644_ = l_mkPanicMessageWithDecl(v___x_643_, v___x_642_, v___x_641_, v___x_640_, v___x_639_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevRangeS(lean_object* v_e_645_, lean_object* v_beginIdx_646_, lean_object* v_endIdx_647_, lean_object* v_subst_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_){
_start:
{
uint8_t v___x_656_; 
v___x_656_ = lean_nat_dec_lt(v_endIdx_647_, v_beginIdx_646_);
if (v___x_656_ == 0)
{
lean_object* v___x_657_; uint8_t v___x_658_; 
v___x_657_ = lean_array_get_size(v_subst_648_);
v___x_658_ = lean_nat_dec_lt(v___x_657_, v_endIdx_647_);
if (v___x_658_ == 0)
{
lean_object* v___x_659_; lean_object* v_share_660_; lean_object* v_maxFVar_661_; lean_object* v_proofInstInfo_662_; lean_object* v_inferType_663_; lean_object* v_getLevel_664_; lean_object* v_congrInfo_665_; lean_object* v_defEqI_666_; lean_object* v_extensions_667_; uint8_t v_debug_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_724_; 
v___x_659_ = lean_st_ref_take(v_a_650_);
v_share_660_ = lean_ctor_get(v___x_659_, 0);
v_maxFVar_661_ = lean_ctor_get(v___x_659_, 1);
v_proofInstInfo_662_ = lean_ctor_get(v___x_659_, 2);
v_inferType_663_ = lean_ctor_get(v___x_659_, 3);
v_getLevel_664_ = lean_ctor_get(v___x_659_, 4);
v_congrInfo_665_ = lean_ctor_get(v___x_659_, 5);
v_defEqI_666_ = lean_ctor_get(v___x_659_, 6);
v_extensions_667_ = lean_ctor_get(v___x_659_, 7);
v_debug_668_ = lean_ctor_get_uint8(v___x_659_, sizeof(void*)*8);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_724_ == 0)
{
v___x_670_ = v___x_659_;
v_isShared_671_ = v_isSharedCheck_724_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_extensions_667_);
lean_inc(v_defEqI_666_);
lean_inc(v_congrInfo_665_);
lean_inc(v_getLevel_664_);
lean_inc(v_inferType_663_);
lean_inc(v_proofInstInfo_662_);
lean_inc(v_maxFVar_661_);
lean_inc(v_share_660_);
lean_dec(v___x_659_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_724_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v___x_672_; lean_object* v___x_674_; 
v___x_672_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__0, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__0_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__0);
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 0, v___x_672_);
v___x_674_ = v___x_670_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___x_672_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v_maxFVar_661_);
lean_ctor_set(v_reuseFailAlloc_723_, 2, v_proofInstInfo_662_);
lean_ctor_set(v_reuseFailAlloc_723_, 3, v_inferType_663_);
lean_ctor_set(v_reuseFailAlloc_723_, 4, v_getLevel_664_);
lean_ctor_set(v_reuseFailAlloc_723_, 5, v_congrInfo_665_);
lean_ctor_set(v_reuseFailAlloc_723_, 6, v_defEqI_666_);
lean_ctor_set(v_reuseFailAlloc_723_, 7, v_extensions_667_);
lean_ctor_set_uint8(v_reuseFailAlloc_723_, sizeof(void*)*8, v_debug_668_);
v___x_674_ = v_reuseFailAlloc_723_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v_fst_678_; lean_object* v_snd_679_; uint8_t v_debug_699_; lean_object* v_n_700_; lean_object* v___x_701_; 
v___x_675_ = lean_st_ref_set(v_a_650_, v___x_674_);
v___x_676_ = lean_st_ref_get(v_a_650_);
v_debug_699_ = lean_ctor_get_uint8(v___x_676_, sizeof(void*)*8);
lean_dec(v___x_676_);
v_n_700_ = lean_nat_sub(v_endIdx_647_, v_beginIdx_646_);
v___x_701_ = lean_unsigned_to_nat(0u);
switch(lean_obj_tag(v_e_645_))
{
case 0:
{
lean_object* v_deBruijnIndex_702_; uint8_t v___x_703_; 
v_deBruijnIndex_702_ = lean_ctor_get(v_e_645_, 0);
v___x_703_ = lean_nat_dec_le(v_beginIdx_646_, v_deBruijnIndex_702_);
if (v___x_703_ == 0)
{
lean_dec(v_n_700_);
v_fst_678_ = v_e_645_;
v_snd_679_ = v_share_660_;
goto v___jp_677_;
}
else
{
uint8_t v___x_704_; 
lean_inc(v_deBruijnIndex_702_);
lean_dec_ref(v_e_645_);
v___x_704_ = lean_nat_dec_lt(v_deBruijnIndex_702_, v_n_700_);
if (v___x_704_ == 0)
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v_fst_707_; lean_object* v_snd_708_; 
v___x_705_ = lean_nat_sub(v_deBruijnIndex_702_, v_n_700_);
lean_dec(v_n_700_);
lean_dec(v_deBruijnIndex_702_);
v___x_706_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___redArg(v___x_705_, v_share_660_);
v_fst_707_ = lean_ctor_get(v___x_706_, 0);
lean_inc(v_fst_707_);
v_snd_708_ = lean_ctor_get(v___x_706_, 1);
lean_inc(v_snd_708_);
lean_dec_ref(v___x_706_);
v_fst_678_ = v_fst_707_;
v_snd_679_ = v_snd_708_;
goto v___jp_677_;
}
else
{
lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v_v_712_; lean_object* v___x_713_; lean_object* v_fst_714_; lean_object* v_snd_715_; 
v___x_709_ = lean_nat_sub(v_n_700_, v_deBruijnIndex_702_);
lean_dec(v_deBruijnIndex_702_);
lean_dec(v_n_700_);
v___x_710_ = lean_unsigned_to_nat(1u);
v___x_711_ = lean_nat_sub(v___x_709_, v___x_710_);
lean_dec(v___x_709_);
v_v_712_ = lean_array_fget_borrowed(v_subst_648_, v___x_711_);
lean_dec(v___x_711_);
lean_inc(v_v_712_);
v___x_713_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(v_v_712_, v___x_701_, v___x_701_, v_debug_699_, v_share_660_);
v_fst_714_ = lean_ctor_get(v___x_713_, 0);
lean_inc(v_fst_714_);
v_snd_715_ = lean_ctor_get(v___x_713_, 1);
lean_inc(v_snd_715_);
lean_dec_ref(v___x_713_);
v_fst_678_ = v_fst_714_;
v_snd_679_ = v_snd_715_;
goto v___jp_677_;
}
}
}
case 9:
{
lean_dec(v_n_700_);
v_fst_678_ = v_e_645_;
v_snd_679_ = v_share_660_;
goto v___jp_677_;
}
case 2:
{
lean_dec(v_n_700_);
v_fst_678_ = v_e_645_;
v_snd_679_ = v_share_660_;
goto v___jp_677_;
}
case 1:
{
lean_dec(v_n_700_);
v_fst_678_ = v_e_645_;
v_snd_679_ = v_share_660_;
goto v___jp_677_;
}
case 4:
{
lean_dec(v_n_700_);
v_fst_678_ = v_e_645_;
v_snd_679_ = v_share_660_;
goto v___jp_677_;
}
case 3:
{
lean_dec(v_n_700_);
v_fst_678_ = v_e_645_;
v_snd_679_ = v_share_660_;
goto v___jp_677_;
}
default: 
{
lean_object* v___x_716_; uint8_t v___x_717_; 
v___x_716_ = l_Lean_Expr_looseBVarRange(v_e_645_);
v___x_717_ = lean_nat_dec_le(v___x_716_, v_beginIdx_646_);
lean_dec(v___x_716_);
if (v___x_717_ == 0)
{
switch(lean_obj_tag(v_e_645_))
{
case 9:
{
lean_dec(v_n_700_);
v_fst_678_ = v_e_645_;
v_snd_679_ = v_share_660_;
goto v___jp_677_;
}
case 2:
{
lean_dec(v_n_700_);
v_fst_678_ = v_e_645_;
v_snd_679_ = v_share_660_;
goto v___jp_677_;
}
case 0:
{
lean_dec(v_n_700_);
v_fst_678_ = v_e_645_;
v_snd_679_ = v_share_660_;
goto v___jp_677_;
}
case 1:
{
lean_dec(v_n_700_);
v_fst_678_ = v_e_645_;
v_snd_679_ = v_share_660_;
goto v___jp_677_;
}
case 4:
{
lean_dec(v_n_700_);
v_fst_678_ = v_e_645_;
v_snd_679_ = v_share_660_;
goto v___jp_677_;
}
case 3:
{
lean_dec(v_n_700_);
v_fst_678_ = v_e_645_;
v_snd_679_ = v_share_660_;
goto v___jp_677_;
}
default: 
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v_fst_720_; lean_object* v_snd_721_; lean_object* v_fst_722_; 
v___x_718_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__2, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__2_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__2);
v___x_719_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(v_beginIdx_646_, v_n_700_, v_subst_648_, v_e_645_, v___x_701_, v___x_718_, v_debug_699_, v_share_660_);
lean_dec(v_n_700_);
v_fst_720_ = lean_ctor_get(v___x_719_, 0);
lean_inc(v_fst_720_);
v_snd_721_ = lean_ctor_get(v___x_719_, 1);
lean_inc(v_snd_721_);
lean_dec_ref(v___x_719_);
v_fst_722_ = lean_ctor_get(v_fst_720_, 0);
lean_inc(v_fst_722_);
lean_dec(v_fst_720_);
v_fst_678_ = v_fst_722_;
v_snd_679_ = v_snd_721_;
goto v___jp_677_;
}
}
}
else
{
lean_dec(v_n_700_);
v_fst_678_ = v_e_645_;
v_snd_679_ = v_share_660_;
goto v___jp_677_;
}
}
}
v___jp_677_:
{
lean_object* v___x_680_; lean_object* v_maxFVar_681_; lean_object* v_proofInstInfo_682_; lean_object* v_inferType_683_; lean_object* v_getLevel_684_; lean_object* v_congrInfo_685_; lean_object* v_defEqI_686_; lean_object* v_extensions_687_; uint8_t v_debug_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_697_; 
v___x_680_ = lean_st_ref_take(v_a_650_);
v_maxFVar_681_ = lean_ctor_get(v___x_680_, 1);
v_proofInstInfo_682_ = lean_ctor_get(v___x_680_, 2);
v_inferType_683_ = lean_ctor_get(v___x_680_, 3);
v_getLevel_684_ = lean_ctor_get(v___x_680_, 4);
v_congrInfo_685_ = lean_ctor_get(v___x_680_, 5);
v_defEqI_686_ = lean_ctor_get(v___x_680_, 6);
v_extensions_687_ = lean_ctor_get(v___x_680_, 7);
v_debug_688_ = lean_ctor_get_uint8(v___x_680_, sizeof(void*)*8);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_680_);
if (v_isSharedCheck_697_ == 0)
{
lean_object* v_unused_698_; 
v_unused_698_ = lean_ctor_get(v___x_680_, 0);
lean_dec(v_unused_698_);
v___x_690_ = v___x_680_;
v_isShared_691_ = v_isSharedCheck_697_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_extensions_687_);
lean_inc(v_defEqI_686_);
lean_inc(v_congrInfo_685_);
lean_inc(v_getLevel_684_);
lean_inc(v_inferType_683_);
lean_inc(v_proofInstInfo_682_);
lean_inc(v_maxFVar_681_);
lean_dec(v___x_680_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_697_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_693_; 
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 0, v_snd_679_);
v___x_693_ = v___x_690_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_snd_679_);
lean_ctor_set(v_reuseFailAlloc_696_, 1, v_maxFVar_681_);
lean_ctor_set(v_reuseFailAlloc_696_, 2, v_proofInstInfo_682_);
lean_ctor_set(v_reuseFailAlloc_696_, 3, v_inferType_683_);
lean_ctor_set(v_reuseFailAlloc_696_, 4, v_getLevel_684_);
lean_ctor_set(v_reuseFailAlloc_696_, 5, v_congrInfo_685_);
lean_ctor_set(v_reuseFailAlloc_696_, 6, v_defEqI_686_);
lean_ctor_set(v_reuseFailAlloc_696_, 7, v_extensions_687_);
lean_ctor_set_uint8(v_reuseFailAlloc_696_, sizeof(void*)*8, v_debug_688_);
v___x_693_ = v_reuseFailAlloc_696_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_694_ = lean_st_ref_set(v_a_650_, v___x_693_);
v___x_695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_695_, 0, v_fst_678_);
return v___x_695_;
}
}
}
}
}
}
else
{
lean_object* v___x_725_; lean_object* v___x_726_; 
lean_dec_ref(v_e_645_);
v___x_725_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__5, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__5_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__5);
v___x_726_ = l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3(v___x_725_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_);
return v___x_726_;
}
}
else
{
lean_object* v___x_727_; lean_object* v___x_728_; 
lean_dec_ref(v_e_645_);
v___x_727_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__6, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__6_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__6);
v___x_728_ = l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3(v___x_727_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_);
return v___x_728_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevRangeS___boxed(lean_object* v_e_729_, lean_object* v_beginIdx_730_, lean_object* v_endIdx_731_, lean_object* v_subst_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_e_729_, v_beginIdx_730_, v_endIdx_731_, v_subst_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_);
lean_dec(v_a_738_);
lean_dec_ref(v_a_737_);
lean_dec(v_a_736_);
lean_dec_ref(v_a_735_);
lean_dec(v_a_734_);
lean_dec_ref(v_a_733_);
lean_dec_ref(v_subst_732_);
lean_dec(v_endIdx_731_);
lean_dec(v_beginIdx_730_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4(lean_object* v_00_u03b2_741_, lean_object* v_m_742_, lean_object* v_a_743_){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___redArg(v_m_742_, v_a_743_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___boxed(lean_object* v_00_u03b2_745_, lean_object* v_m_746_, lean_object* v_a_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4(v_00_u03b2_745_, v_m_746_, v_a_747_);
lean_dec_ref(v_a_747_);
lean_dec_ref(v_m_746_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4_spec__12(lean_object* v_00_u03b2_749_, lean_object* v_a_750_, lean_object* v_x_751_){
_start:
{
lean_object* v___x_752_; 
v___x_752_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4_spec__12___redArg(v_a_750_, v_x_751_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4_spec__12___boxed(lean_object* v_00_u03b2_753_, lean_object* v_a_754_, lean_object* v_x_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4_spec__12(v_00_u03b2_753_, v_a_754_, v_x_755_);
lean_dec(v_x_755_);
lean_dec_ref(v_a_754_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevS(lean_object* v_e_757_, lean_object* v_subst_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_766_ = lean_unsigned_to_nat(0u);
v___x_767_ = lean_array_get_size(v_subst_758_);
v___x_768_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_e_757_, v___x_766_, v___x_767_, v_subst_758_, v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevS___boxed(lean_object* v_e_769_, lean_object* v_subst_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_Lean_Meta_Sym_instantiateRevS(v_e_769_, v_subst_770_, v_a_771_, v_a_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_);
lean_dec(v_a_776_);
lean_dec_ref(v_a_775_);
lean_dec(v_a_774_);
lean_dec_ref(v_a_773_);
lean_dec(v_a_772_);
lean_dec_ref(v_a_771_);
lean_dec_ref(v_subst_770_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1(lean_object* v_msg_779_, uint8_t v___y_780_, lean_object* v___y_781_){
_start:
{
lean_object* v___f_782_; lean_object* v___f_783_; lean_object* v___f_784_; lean_object* v___f_785_; lean_object* v___f_786_; lean_object* v___f_787_; lean_object* v___f_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___f_792_; lean_object* v___f_793_; lean_object* v___f_794_; lean_object* v___f_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___f_804_; lean_object* v___x_3111__overap_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
v___f_782_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__0));
v___f_783_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__1));
v___f_784_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__2));
v___f_785_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__3));
v___f_786_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__4));
v___f_787_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__5));
v___f_788_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__6));
v___x_789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_789_, 0, v___f_782_);
lean_ctor_set(v___x_789_, 1, v___f_783_);
v___x_790_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_790_, 0, v___x_789_);
lean_ctor_set(v___x_790_, 1, v___f_784_);
lean_ctor_set(v___x_790_, 2, v___f_785_);
lean_ctor_set(v___x_790_, 3, v___f_786_);
lean_ctor_set(v___x_790_, 4, v___f_787_);
v___x_791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_791_, 0, v___x_790_);
lean_ctor_set(v___x_791_, 1, v___f_788_);
lean_inc_ref(v___x_791_);
v___f_792_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_792_, 0, v___x_791_);
lean_inc_ref(v___x_791_);
v___f_793_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_793_, 0, v___x_791_);
lean_inc_ref(v___x_791_);
v___f_794_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_794_, 0, v___x_791_);
lean_inc_ref(v___x_791_);
v___f_795_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_795_, 0, v___x_791_);
lean_inc_ref(v___x_791_);
v___x_796_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_796_, 0, lean_box(0));
lean_closure_set(v___x_796_, 1, lean_box(0));
lean_closure_set(v___x_796_, 2, v___x_791_);
v___x_797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_797_, 0, v___x_796_);
lean_ctor_set(v___x_797_, 1, v___f_792_);
lean_inc_ref(v___x_791_);
v___x_798_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_798_, 0, lean_box(0));
lean_closure_set(v___x_798_, 1, lean_box(0));
lean_closure_set(v___x_798_, 2, v___x_791_);
v___x_799_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_799_, 0, v___x_797_);
lean_ctor_set(v___x_799_, 1, v___x_798_);
lean_ctor_set(v___x_799_, 2, v___f_793_);
lean_ctor_set(v___x_799_, 3, v___f_794_);
lean_ctor_set(v___x_799_, 4, v___f_795_);
v___x_800_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_800_, 0, lean_box(0));
lean_closure_set(v___x_800_, 1, lean_box(0));
lean_closure_set(v___x_800_, 2, v___x_791_);
v___x_801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_801_, 0, v___x_799_);
lean_ctor_set(v___x_801_, 1, v___x_800_);
v___x_802_ = l_Lean_instInhabitedExpr;
v___x_803_ = l_instInhabitedOfMonad___redArg(v___x_801_, v___x_802_);
v___f_804_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_804_, 0, v___x_803_);
v___x_3111__overap_805_ = lean_panic_fn(v___f_804_, v_msg_779_);
v___x_806_ = lean_box(v___y_780_);
v___x_807_ = lean_apply_2(v___x_3111__overap_805_, v___x_806_, v___y_781_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1___boxed(lean_object* v_msg_808_, lean_object* v___y_809_, lean_object* v___y_810_){
_start:
{
uint8_t v___y_3548__boxed_811_; lean_object* v_res_812_; 
v___y_3548__boxed_811_ = lean_unbox(v___y_809_);
v_res_812_ = l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1(v_msg_808_, v___y_3548__boxed_811_, v___y_810_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0(lean_object* v_n_813_, lean_object* v_beginIdx_814_, lean_object* v_subst_815_, lean_object* v_e_816_, lean_object* v_offset_817_, lean_object* v_a_818_, uint8_t v_a_819_, lean_object* v_a_820_){
_start:
{
switch(lean_obj_tag(v_e_816_))
{
case 5:
{
lean_object* v_fn_821_; lean_object* v_arg_822_; lean_object* v___x_823_; lean_object* v_fst_824_; lean_object* v_snd_825_; lean_object* v_fst_826_; lean_object* v_snd_827_; lean_object* v___x_828_; lean_object* v_fst_829_; lean_object* v_snd_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_851_; 
v_fn_821_ = lean_ctor_get(v_e_816_, 0);
v_arg_822_ = lean_ctor_get(v_e_816_, 1);
lean_inc(v_offset_817_);
lean_inc_ref(v_fn_821_);
v___x_823_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_813_, v_beginIdx_814_, v_subst_815_, v_fn_821_, v_offset_817_, v_a_818_, v_a_819_, v_a_820_);
v_fst_824_ = lean_ctor_get(v___x_823_, 0);
lean_inc(v_fst_824_);
v_snd_825_ = lean_ctor_get(v___x_823_, 1);
lean_inc(v_snd_825_);
lean_dec_ref(v___x_823_);
v_fst_826_ = lean_ctor_get(v_fst_824_, 0);
lean_inc(v_fst_826_);
v_snd_827_ = lean_ctor_get(v_fst_824_, 1);
lean_inc(v_snd_827_);
lean_dec(v_fst_824_);
lean_inc_ref(v_arg_822_);
v___x_828_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_813_, v_beginIdx_814_, v_subst_815_, v_arg_822_, v_offset_817_, v_snd_827_, v_a_819_, v_snd_825_);
v_fst_829_ = lean_ctor_get(v___x_828_, 0);
v_snd_830_ = lean_ctor_get(v___x_828_, 1);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_851_ == 0)
{
v___x_832_ = v___x_828_;
v_isShared_833_ = v_isSharedCheck_851_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_snd_830_);
lean_inc(v_fst_829_);
lean_dec(v___x_828_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_851_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v_fst_834_; lean_object* v_snd_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_850_; 
v_fst_834_ = lean_ctor_get(v_fst_829_, 0);
v_snd_835_ = lean_ctor_get(v_fst_829_, 1);
v_isSharedCheck_850_ = !lean_is_exclusive(v_fst_829_);
if (v_isSharedCheck_850_ == 0)
{
v___x_837_ = v_fst_829_;
v_isShared_838_ = v_isSharedCheck_850_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_snd_835_);
lean_inc(v_fst_834_);
lean_dec(v_fst_829_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_850_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
uint8_t v___y_840_; uint8_t v___x_848_; 
v___x_848_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_821_, v_fst_826_);
if (v___x_848_ == 0)
{
v___y_840_ = v___x_848_;
goto v___jp_839_;
}
else
{
uint8_t v___x_849_; 
v___x_849_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_822_, v_fst_834_);
v___y_840_ = v___x_849_;
goto v___jp_839_;
}
v___jp_839_:
{
if (v___y_840_ == 0)
{
lean_object* v___x_841_; 
lean_del_object(v___x_837_);
lean_del_object(v___x_832_);
lean_dec_ref(v_e_816_);
v___x_841_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__3(v_fst_826_, v_fst_834_, v_snd_835_, v_a_819_, v_snd_830_);
return v___x_841_;
}
else
{
lean_object* v___x_843_; 
lean_dec(v_fst_834_);
lean_dec(v_fst_826_);
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 0, v_e_816_);
v___x_843_ = v___x_837_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_e_816_);
lean_ctor_set(v_reuseFailAlloc_847_, 1, v_snd_835_);
v___x_843_ = v_reuseFailAlloc_847_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
lean_object* v___x_845_; 
if (v_isShared_833_ == 0)
{
lean_ctor_set(v___x_832_, 0, v___x_843_);
v___x_845_ = v___x_832_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v___x_843_);
lean_ctor_set(v_reuseFailAlloc_846_, 1, v_snd_830_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
}
}
}
}
case 6:
{
lean_object* v_binderName_852_; lean_object* v_binderType_853_; lean_object* v_body_854_; uint8_t v_binderInfo_855_; lean_object* v___x_856_; lean_object* v_fst_857_; lean_object* v_snd_858_; lean_object* v_fst_859_; lean_object* v_snd_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v_fst_864_; lean_object* v_snd_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_886_; 
v_binderName_852_ = lean_ctor_get(v_e_816_, 0);
v_binderType_853_ = lean_ctor_get(v_e_816_, 1);
v_body_854_ = lean_ctor_get(v_e_816_, 2);
v_binderInfo_855_ = lean_ctor_get_uint8(v_e_816_, sizeof(void*)*3 + 8);
lean_inc(v_offset_817_);
lean_inc_ref(v_binderType_853_);
v___x_856_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_813_, v_beginIdx_814_, v_subst_815_, v_binderType_853_, v_offset_817_, v_a_818_, v_a_819_, v_a_820_);
v_fst_857_ = lean_ctor_get(v___x_856_, 0);
lean_inc(v_fst_857_);
v_snd_858_ = lean_ctor_get(v___x_856_, 1);
lean_inc(v_snd_858_);
lean_dec_ref(v___x_856_);
v_fst_859_ = lean_ctor_get(v_fst_857_, 0);
lean_inc(v_fst_859_);
v_snd_860_ = lean_ctor_get(v_fst_857_, 1);
lean_inc(v_snd_860_);
lean_dec(v_fst_857_);
v___x_861_ = lean_unsigned_to_nat(1u);
v___x_862_ = lean_nat_add(v_offset_817_, v___x_861_);
lean_dec(v_offset_817_);
lean_inc_ref(v_body_854_);
v___x_863_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_813_, v_beginIdx_814_, v_subst_815_, v_body_854_, v___x_862_, v_snd_860_, v_a_819_, v_snd_858_);
v_fst_864_ = lean_ctor_get(v___x_863_, 0);
v_snd_865_ = lean_ctor_get(v___x_863_, 1);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_886_ == 0)
{
v___x_867_ = v___x_863_;
v_isShared_868_ = v_isSharedCheck_886_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_snd_865_);
lean_inc(v_fst_864_);
lean_dec(v___x_863_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_886_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v_fst_869_; lean_object* v_snd_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_885_; 
v_fst_869_ = lean_ctor_get(v_fst_864_, 0);
v_snd_870_ = lean_ctor_get(v_fst_864_, 1);
v_isSharedCheck_885_ = !lean_is_exclusive(v_fst_864_);
if (v_isSharedCheck_885_ == 0)
{
v___x_872_ = v_fst_864_;
v_isShared_873_ = v_isSharedCheck_885_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_snd_870_);
lean_inc(v_fst_869_);
lean_dec(v_fst_864_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_885_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
uint8_t v___y_875_; uint8_t v___x_883_; 
v___x_883_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_853_, v_fst_859_);
if (v___x_883_ == 0)
{
v___y_875_ = v___x_883_;
goto v___jp_874_;
}
else
{
uint8_t v___x_884_; 
v___x_884_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_854_, v_fst_869_);
v___y_875_ = v___x_884_;
goto v___jp_874_;
}
v___jp_874_:
{
if (v___y_875_ == 0)
{
lean_object* v___x_876_; 
lean_inc(v_binderName_852_);
lean_del_object(v___x_872_);
lean_del_object(v___x_867_);
lean_dec_ref(v_e_816_);
v___x_876_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__4(v_binderName_852_, v_binderInfo_855_, v_fst_859_, v_fst_869_, v_snd_870_, v_a_819_, v_snd_865_);
return v___x_876_;
}
else
{
lean_object* v___x_878_; 
lean_dec(v_fst_869_);
lean_dec(v_fst_859_);
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 0, v_e_816_);
v___x_878_ = v___x_872_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_e_816_);
lean_ctor_set(v_reuseFailAlloc_882_, 1, v_snd_870_);
v___x_878_ = v_reuseFailAlloc_882_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
lean_object* v___x_880_; 
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 0, v___x_878_);
v___x_880_ = v___x_867_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v___x_878_);
lean_ctor_set(v_reuseFailAlloc_881_, 1, v_snd_865_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
}
}
}
}
case 7:
{
lean_object* v_binderName_887_; lean_object* v_binderType_888_; lean_object* v_body_889_; uint8_t v_binderInfo_890_; lean_object* v___x_891_; lean_object* v_fst_892_; lean_object* v_snd_893_; lean_object* v_fst_894_; lean_object* v_snd_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v_fst_899_; lean_object* v_snd_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_921_; 
v_binderName_887_ = lean_ctor_get(v_e_816_, 0);
v_binderType_888_ = lean_ctor_get(v_e_816_, 1);
v_body_889_ = lean_ctor_get(v_e_816_, 2);
v_binderInfo_890_ = lean_ctor_get_uint8(v_e_816_, sizeof(void*)*3 + 8);
lean_inc(v_offset_817_);
lean_inc_ref(v_binderType_888_);
v___x_891_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_813_, v_beginIdx_814_, v_subst_815_, v_binderType_888_, v_offset_817_, v_a_818_, v_a_819_, v_a_820_);
v_fst_892_ = lean_ctor_get(v___x_891_, 0);
lean_inc(v_fst_892_);
v_snd_893_ = lean_ctor_get(v___x_891_, 1);
lean_inc(v_snd_893_);
lean_dec_ref(v___x_891_);
v_fst_894_ = lean_ctor_get(v_fst_892_, 0);
lean_inc(v_fst_894_);
v_snd_895_ = lean_ctor_get(v_fst_892_, 1);
lean_inc(v_snd_895_);
lean_dec(v_fst_892_);
v___x_896_ = lean_unsigned_to_nat(1u);
v___x_897_ = lean_nat_add(v_offset_817_, v___x_896_);
lean_dec(v_offset_817_);
lean_inc_ref(v_body_889_);
v___x_898_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_813_, v_beginIdx_814_, v_subst_815_, v_body_889_, v___x_897_, v_snd_895_, v_a_819_, v_snd_893_);
v_fst_899_ = lean_ctor_get(v___x_898_, 0);
v_snd_900_ = lean_ctor_get(v___x_898_, 1);
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_898_);
if (v_isSharedCheck_921_ == 0)
{
v___x_902_ = v___x_898_;
v_isShared_903_ = v_isSharedCheck_921_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_snd_900_);
lean_inc(v_fst_899_);
lean_dec(v___x_898_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_921_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v_fst_904_; lean_object* v_snd_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_920_; 
v_fst_904_ = lean_ctor_get(v_fst_899_, 0);
v_snd_905_ = lean_ctor_get(v_fst_899_, 1);
v_isSharedCheck_920_ = !lean_is_exclusive(v_fst_899_);
if (v_isSharedCheck_920_ == 0)
{
v___x_907_ = v_fst_899_;
v_isShared_908_ = v_isSharedCheck_920_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_snd_905_);
lean_inc(v_fst_904_);
lean_dec(v_fst_899_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_920_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
uint8_t v___y_910_; uint8_t v___x_918_; 
v___x_918_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_888_, v_fst_894_);
if (v___x_918_ == 0)
{
v___y_910_ = v___x_918_;
goto v___jp_909_;
}
else
{
uint8_t v___x_919_; 
v___x_919_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_889_, v_fst_904_);
v___y_910_ = v___x_919_;
goto v___jp_909_;
}
v___jp_909_:
{
if (v___y_910_ == 0)
{
lean_object* v___x_911_; 
lean_inc(v_binderName_887_);
lean_del_object(v___x_907_);
lean_del_object(v___x_902_);
lean_dec_ref(v_e_816_);
v___x_911_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__5(v_binderName_887_, v_binderInfo_890_, v_fst_894_, v_fst_904_, v_snd_905_, v_a_819_, v_snd_900_);
return v___x_911_;
}
else
{
lean_object* v___x_913_; 
lean_dec(v_fst_904_);
lean_dec(v_fst_894_);
if (v_isShared_908_ == 0)
{
lean_ctor_set(v___x_907_, 0, v_e_816_);
v___x_913_ = v___x_907_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_e_816_);
lean_ctor_set(v_reuseFailAlloc_917_, 1, v_snd_905_);
v___x_913_ = v_reuseFailAlloc_917_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
lean_object* v___x_915_; 
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 0, v___x_913_);
v___x_915_ = v___x_902_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v___x_913_);
lean_ctor_set(v_reuseFailAlloc_916_, 1, v_snd_900_);
v___x_915_ = v_reuseFailAlloc_916_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
return v___x_915_;
}
}
}
}
}
}
}
case 8:
{
lean_object* v_declName_922_; lean_object* v_type_923_; lean_object* v_value_924_; lean_object* v_body_925_; uint8_t v_nondep_926_; lean_object* v___x_927_; lean_object* v_fst_928_; lean_object* v_snd_929_; lean_object* v_fst_930_; lean_object* v_snd_931_; lean_object* v___x_932_; lean_object* v_fst_933_; lean_object* v_snd_934_; lean_object* v_fst_935_; lean_object* v_snd_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v_fst_940_; lean_object* v_snd_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_964_; 
v_declName_922_ = lean_ctor_get(v_e_816_, 0);
v_type_923_ = lean_ctor_get(v_e_816_, 1);
v_value_924_ = lean_ctor_get(v_e_816_, 2);
v_body_925_ = lean_ctor_get(v_e_816_, 3);
v_nondep_926_ = lean_ctor_get_uint8(v_e_816_, sizeof(void*)*4 + 8);
lean_inc(v_offset_817_);
lean_inc_ref(v_type_923_);
v___x_927_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_813_, v_beginIdx_814_, v_subst_815_, v_type_923_, v_offset_817_, v_a_818_, v_a_819_, v_a_820_);
v_fst_928_ = lean_ctor_get(v___x_927_, 0);
lean_inc(v_fst_928_);
v_snd_929_ = lean_ctor_get(v___x_927_, 1);
lean_inc(v_snd_929_);
lean_dec_ref(v___x_927_);
v_fst_930_ = lean_ctor_get(v_fst_928_, 0);
lean_inc(v_fst_930_);
v_snd_931_ = lean_ctor_get(v_fst_928_, 1);
lean_inc(v_snd_931_);
lean_dec(v_fst_928_);
lean_inc(v_offset_817_);
lean_inc_ref(v_value_924_);
v___x_932_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_813_, v_beginIdx_814_, v_subst_815_, v_value_924_, v_offset_817_, v_snd_931_, v_a_819_, v_snd_929_);
v_fst_933_ = lean_ctor_get(v___x_932_, 0);
lean_inc(v_fst_933_);
v_snd_934_ = lean_ctor_get(v___x_932_, 1);
lean_inc(v_snd_934_);
lean_dec_ref(v___x_932_);
v_fst_935_ = lean_ctor_get(v_fst_933_, 0);
lean_inc(v_fst_935_);
v_snd_936_ = lean_ctor_get(v_fst_933_, 1);
lean_inc(v_snd_936_);
lean_dec(v_fst_933_);
v___x_937_ = lean_unsigned_to_nat(1u);
v___x_938_ = lean_nat_add(v_offset_817_, v___x_937_);
lean_dec(v_offset_817_);
lean_inc_ref(v_body_925_);
v___x_939_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_813_, v_beginIdx_814_, v_subst_815_, v_body_925_, v___x_938_, v_snd_936_, v_a_819_, v_snd_934_);
v_fst_940_ = lean_ctor_get(v___x_939_, 0);
v_snd_941_ = lean_ctor_get(v___x_939_, 1);
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_939_);
if (v_isSharedCheck_964_ == 0)
{
v___x_943_ = v___x_939_;
v_isShared_944_ = v_isSharedCheck_964_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_snd_941_);
lean_inc(v_fst_940_);
lean_dec(v___x_939_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_964_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v_fst_945_; lean_object* v_snd_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_963_; 
v_fst_945_ = lean_ctor_get(v_fst_940_, 0);
v_snd_946_ = lean_ctor_get(v_fst_940_, 1);
v_isSharedCheck_963_ = !lean_is_exclusive(v_fst_940_);
if (v_isSharedCheck_963_ == 0)
{
v___x_948_ = v_fst_940_;
v_isShared_949_ = v_isSharedCheck_963_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_snd_946_);
lean_inc(v_fst_945_);
lean_dec(v_fst_940_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_963_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
uint8_t v___y_951_; uint8_t v___x_961_; 
v___x_961_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_type_923_, v_fst_930_);
if (v___x_961_ == 0)
{
v___y_951_ = v___x_961_;
goto v___jp_950_;
}
else
{
uint8_t v___x_962_; 
v___x_962_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_value_924_, v_fst_935_);
v___y_951_ = v___x_962_;
goto v___jp_950_;
}
v___jp_950_:
{
if (v___y_951_ == 0)
{
lean_object* v___x_952_; 
lean_inc(v_declName_922_);
lean_del_object(v___x_948_);
lean_del_object(v___x_943_);
lean_dec_ref(v_e_816_);
v___x_952_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6(v_declName_922_, v_fst_930_, v_fst_935_, v_fst_945_, v_nondep_926_, v_snd_946_, v_a_819_, v_snd_941_);
return v___x_952_;
}
else
{
uint8_t v___x_953_; 
v___x_953_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_925_, v_fst_945_);
if (v___x_953_ == 0)
{
lean_object* v___x_954_; 
lean_inc(v_declName_922_);
lean_del_object(v___x_948_);
lean_del_object(v___x_943_);
lean_dec_ref(v_e_816_);
v___x_954_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6(v_declName_922_, v_fst_930_, v_fst_935_, v_fst_945_, v_nondep_926_, v_snd_946_, v_a_819_, v_snd_941_);
return v___x_954_;
}
else
{
lean_object* v___x_956_; 
lean_dec(v_fst_945_);
lean_dec(v_fst_935_);
lean_dec(v_fst_930_);
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 0, v_e_816_);
v___x_956_ = v___x_948_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_e_816_);
lean_ctor_set(v_reuseFailAlloc_960_, 1, v_snd_946_);
v___x_956_ = v_reuseFailAlloc_960_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
lean_object* v___x_958_; 
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 0, v___x_956_);
v___x_958_ = v___x_943_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v___x_956_);
lean_ctor_set(v_reuseFailAlloc_959_, 1, v_snd_941_);
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
}
}
case 10:
{
lean_object* v_data_965_; lean_object* v_expr_966_; lean_object* v___x_967_; lean_object* v_fst_968_; lean_object* v_snd_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_987_; 
v_data_965_ = lean_ctor_get(v_e_816_, 0);
v_expr_966_ = lean_ctor_get(v_e_816_, 1);
lean_inc_ref(v_expr_966_);
v___x_967_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_813_, v_beginIdx_814_, v_subst_815_, v_expr_966_, v_offset_817_, v_a_818_, v_a_819_, v_a_820_);
v_fst_968_ = lean_ctor_get(v___x_967_, 0);
v_snd_969_ = lean_ctor_get(v___x_967_, 1);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_987_ == 0)
{
v___x_971_ = v___x_967_;
v_isShared_972_ = v_isSharedCheck_987_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_snd_969_);
lean_inc(v_fst_968_);
lean_dec(v___x_967_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_987_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v_fst_973_; lean_object* v_snd_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_986_; 
v_fst_973_ = lean_ctor_get(v_fst_968_, 0);
v_snd_974_ = lean_ctor_get(v_fst_968_, 1);
v_isSharedCheck_986_ = !lean_is_exclusive(v_fst_968_);
if (v_isSharedCheck_986_ == 0)
{
v___x_976_ = v_fst_968_;
v_isShared_977_ = v_isSharedCheck_986_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_snd_974_);
lean_inc(v_fst_973_);
lean_dec(v_fst_968_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_986_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
uint8_t v___x_978_; 
v___x_978_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_expr_966_, v_fst_973_);
if (v___x_978_ == 0)
{
lean_object* v___x_979_; 
lean_inc(v_data_965_);
lean_del_object(v___x_976_);
lean_del_object(v___x_971_);
lean_dec_ref(v_e_816_);
v___x_979_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__7(v_data_965_, v_fst_973_, v_snd_974_, v_a_819_, v_snd_969_);
return v___x_979_;
}
else
{
lean_object* v___x_981_; 
lean_dec(v_fst_973_);
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 0, v_e_816_);
v___x_981_ = v___x_976_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_e_816_);
lean_ctor_set(v_reuseFailAlloc_985_, 1, v_snd_974_);
v___x_981_ = v_reuseFailAlloc_985_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
lean_object* v___x_983_; 
if (v_isShared_972_ == 0)
{
lean_ctor_set(v___x_971_, 0, v___x_981_);
v___x_983_ = v___x_971_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v___x_981_);
lean_ctor_set(v_reuseFailAlloc_984_, 1, v_snd_969_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
}
}
}
}
case 11:
{
lean_object* v_typeName_988_; lean_object* v_idx_989_; lean_object* v_struct_990_; lean_object* v___x_991_; lean_object* v_fst_992_; lean_object* v_snd_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1011_; 
v_typeName_988_ = lean_ctor_get(v_e_816_, 0);
v_idx_989_ = lean_ctor_get(v_e_816_, 1);
v_struct_990_ = lean_ctor_get(v_e_816_, 2);
lean_inc_ref(v_struct_990_);
v___x_991_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_813_, v_beginIdx_814_, v_subst_815_, v_struct_990_, v_offset_817_, v_a_818_, v_a_819_, v_a_820_);
v_fst_992_ = lean_ctor_get(v___x_991_, 0);
v_snd_993_ = lean_ctor_get(v___x_991_, 1);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_995_ = v___x_991_;
v_isShared_996_ = v_isSharedCheck_1011_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_snd_993_);
lean_inc(v_fst_992_);
lean_dec(v___x_991_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1011_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v_fst_997_; lean_object* v_snd_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1010_; 
v_fst_997_ = lean_ctor_get(v_fst_992_, 0);
v_snd_998_ = lean_ctor_get(v_fst_992_, 1);
v_isSharedCheck_1010_ = !lean_is_exclusive(v_fst_992_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1000_ = v_fst_992_;
v_isShared_1001_ = v_isSharedCheck_1010_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_snd_998_);
lean_inc(v_fst_997_);
lean_dec(v_fst_992_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1010_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
uint8_t v___x_1002_; 
v___x_1002_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_990_, v_fst_997_);
if (v___x_1002_ == 0)
{
lean_object* v___x_1003_; 
lean_inc(v_idx_989_);
lean_inc(v_typeName_988_);
lean_del_object(v___x_1000_);
lean_del_object(v___x_995_);
lean_dec_ref(v_e_816_);
v___x_1003_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__8(v_typeName_988_, v_idx_989_, v_fst_997_, v_snd_998_, v_a_819_, v_snd_993_);
return v___x_1003_;
}
else
{
lean_object* v___x_1005_; 
lean_dec(v_fst_997_);
if (v_isShared_1001_ == 0)
{
lean_ctor_set(v___x_1000_, 0, v_e_816_);
v___x_1005_ = v___x_1000_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_e_816_);
lean_ctor_set(v_reuseFailAlloc_1009_, 1, v_snd_998_);
v___x_1005_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
lean_object* v___x_1007_; 
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 0, v___x_1005_);
v___x_1007_ = v___x_995_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v___x_1005_);
lean_ctor_set(v_reuseFailAlloc_1008_, 1, v_snd_993_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_1012_; lean_object* v___x_1013_; 
lean_dec(v_offset_817_);
lean_dec_ref(v_e_816_);
v___x_1012_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__3);
v___x_1013_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9(v___x_1012_, v_a_818_, v_a_819_, v_a_820_);
return v___x_1013_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(lean_object* v_n_1014_, lean_object* v_beginIdx_1015_, lean_object* v_subst_1016_, lean_object* v_e_1017_, lean_object* v_offset_1018_, lean_object* v_a_1019_, uint8_t v_a_1020_, lean_object* v_a_1021_){
_start:
{
lean_object* v_key_1022_; lean_object* v___x_1023_; 
lean_inc(v_offset_1018_);
lean_inc_ref(v_e_1017_);
v_key_1022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1022_, 0, v_e_1017_);
lean_ctor_set(v_key_1022_, 1, v_offset_1018_);
v___x_1023_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___redArg(v_a_1019_, v_key_1022_);
if (lean_obj_tag(v___x_1023_) == 1)
{
lean_object* v_val_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
lean_dec_ref(v_key_1022_);
lean_dec(v_offset_1018_);
lean_dec_ref(v_e_1017_);
v_val_1024_ = lean_ctor_get(v___x_1023_, 0);
lean_inc(v_val_1024_);
lean_dec_ref(v___x_1023_);
v___x_1025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1025_, 0, v_val_1024_);
lean_ctor_set(v___x_1025_, 1, v_a_1019_);
v___x_1026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1025_);
lean_ctor_set(v___x_1026_, 1, v_a_1021_);
return v___x_1026_;
}
else
{
lean_dec(v___x_1023_);
switch(lean_obj_tag(v_e_1017_))
{
case 0:
{
lean_object* v_deBruijnIndex_1027_; uint8_t v___x_1028_; 
v_deBruijnIndex_1027_ = lean_ctor_get(v_e_1017_, 0);
v___x_1028_ = lean_nat_dec_le(v_offset_1018_, v_deBruijnIndex_1027_);
if (v___x_1028_ == 0)
{
lean_object* v___x_1029_; 
lean_dec(v_offset_1018_);
v___x_1029_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1022_, v_e_1017_, v_a_1019_, v_a_1020_, v_a_1021_);
return v___x_1029_;
}
else
{
lean_object* v___x_1030_; uint8_t v___x_1031_; 
lean_inc(v_deBruijnIndex_1027_);
lean_dec_ref(v_e_1017_);
v___x_1030_ = lean_nat_add(v_offset_1018_, v_n_1014_);
v___x_1031_ = lean_nat_dec_lt(v_deBruijnIndex_1027_, v___x_1030_);
lean_dec(v___x_1030_);
if (v___x_1031_ == 0)
{
lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v_fst_1034_; lean_object* v_snd_1035_; lean_object* v___x_1036_; 
lean_dec(v_offset_1018_);
v___x_1032_ = lean_nat_sub(v_deBruijnIndex_1027_, v_n_1014_);
lean_dec(v_deBruijnIndex_1027_);
v___x_1033_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___redArg(v___x_1032_, v_a_1021_);
v_fst_1034_ = lean_ctor_get(v___x_1033_, 0);
lean_inc(v_fst_1034_);
v_snd_1035_ = lean_ctor_get(v___x_1033_, 1);
lean_inc(v_snd_1035_);
lean_dec_ref(v___x_1033_);
v___x_1036_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1022_, v_fst_1034_, v_a_1019_, v_a_1020_, v_snd_1035_);
return v___x_1036_;
}
else
{
lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v_v_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v_fst_1042_; lean_object* v_snd_1043_; lean_object* v___x_1044_; 
v___x_1037_ = lean_nat_add(v_beginIdx_1015_, v_deBruijnIndex_1027_);
lean_dec(v_deBruijnIndex_1027_);
v___x_1038_ = lean_nat_sub(v___x_1037_, v_offset_1018_);
lean_dec(v___x_1037_);
v_v_1039_ = lean_array_fget_borrowed(v_subst_1016_, v___x_1038_);
lean_dec(v___x_1038_);
v___x_1040_ = lean_unsigned_to_nat(0u);
lean_inc(v_v_1039_);
v___x_1041_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(v_v_1039_, v___x_1040_, v_offset_1018_, v_a_1020_, v_a_1021_);
lean_dec(v_offset_1018_);
v_fst_1042_ = lean_ctor_get(v___x_1041_, 0);
lean_inc(v_fst_1042_);
v_snd_1043_ = lean_ctor_get(v___x_1041_, 1);
lean_inc(v_snd_1043_);
lean_dec_ref(v___x_1041_);
v___x_1044_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1022_, v_fst_1042_, v_a_1019_, v_a_1020_, v_snd_1043_);
return v___x_1044_;
}
}
}
case 9:
{
lean_object* v___x_1045_; 
lean_dec(v_offset_1018_);
v___x_1045_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1022_, v_e_1017_, v_a_1019_, v_a_1020_, v_a_1021_);
return v___x_1045_;
}
case 2:
{
lean_object* v___x_1046_; 
lean_dec(v_offset_1018_);
v___x_1046_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1022_, v_e_1017_, v_a_1019_, v_a_1020_, v_a_1021_);
return v___x_1046_;
}
case 1:
{
lean_object* v___x_1047_; 
lean_dec(v_offset_1018_);
v___x_1047_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1022_, v_e_1017_, v_a_1019_, v_a_1020_, v_a_1021_);
return v___x_1047_;
}
case 4:
{
lean_object* v___x_1048_; 
lean_dec(v_offset_1018_);
v___x_1048_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1022_, v_e_1017_, v_a_1019_, v_a_1020_, v_a_1021_);
return v___x_1048_;
}
case 3:
{
lean_object* v___x_1049_; 
lean_dec(v_offset_1018_);
v___x_1049_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1022_, v_e_1017_, v_a_1019_, v_a_1020_, v_a_1021_);
return v___x_1049_;
}
default: 
{
lean_object* v___x_1050_; uint8_t v___x_1051_; 
v___x_1050_ = l_Lean_Expr_looseBVarRange(v_e_1017_);
v___x_1051_ = lean_nat_dec_le(v___x_1050_, v_offset_1018_);
lean_dec(v___x_1050_);
if (v___x_1051_ == 0)
{
switch(lean_obj_tag(v_e_1017_))
{
case 9:
{
lean_object* v___x_1052_; 
lean_dec(v_offset_1018_);
v___x_1052_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1022_, v_e_1017_, v_a_1019_, v_a_1020_, v_a_1021_);
return v___x_1052_;
}
case 2:
{
lean_object* v___x_1053_; 
lean_dec(v_offset_1018_);
v___x_1053_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1022_, v_e_1017_, v_a_1019_, v_a_1020_, v_a_1021_);
return v___x_1053_;
}
case 0:
{
lean_object* v___x_1054_; 
lean_dec(v_offset_1018_);
v___x_1054_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1022_, v_e_1017_, v_a_1019_, v_a_1020_, v_a_1021_);
return v___x_1054_;
}
case 1:
{
lean_object* v___x_1055_; 
lean_dec(v_offset_1018_);
v___x_1055_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1022_, v_e_1017_, v_a_1019_, v_a_1020_, v_a_1021_);
return v___x_1055_;
}
case 4:
{
lean_object* v___x_1056_; 
lean_dec(v_offset_1018_);
v___x_1056_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1022_, v_e_1017_, v_a_1019_, v_a_1020_, v_a_1021_);
return v___x_1056_;
}
case 3:
{
lean_object* v___x_1057_; 
lean_dec(v_offset_1018_);
v___x_1057_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1022_, v_e_1017_, v_a_1019_, v_a_1020_, v_a_1021_);
return v___x_1057_;
}
default: 
{
lean_object* v___x_1058_; lean_object* v_fst_1059_; lean_object* v_snd_1060_; lean_object* v_fst_1061_; lean_object* v_snd_1062_; lean_object* v___x_1063_; 
v___x_1058_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0(v_n_1014_, v_beginIdx_1015_, v_subst_1016_, v_e_1017_, v_offset_1018_, v_a_1019_, v_a_1020_, v_a_1021_);
v_fst_1059_ = lean_ctor_get(v___x_1058_, 0);
lean_inc(v_fst_1059_);
v_snd_1060_ = lean_ctor_get(v___x_1058_, 1);
lean_inc(v_snd_1060_);
lean_dec_ref(v___x_1058_);
v_fst_1061_ = lean_ctor_get(v_fst_1059_, 0);
lean_inc(v_fst_1061_);
v_snd_1062_ = lean_ctor_get(v_fst_1059_, 1);
lean_inc(v_snd_1062_);
lean_dec(v_fst_1059_);
v___x_1063_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1022_, v_fst_1061_, v_snd_1062_, v_a_1020_, v_snd_1060_);
return v___x_1063_;
}
}
}
else
{
lean_object* v___x_1064_; 
lean_dec(v_offset_1018_);
v___x_1064_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1022_, v_e_1017_, v_a_1019_, v_a_1020_, v_a_1021_);
return v___x_1064_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0___boxed(lean_object* v_n_1065_, lean_object* v_beginIdx_1066_, lean_object* v_subst_1067_, lean_object* v_e_1068_, lean_object* v_offset_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_){
_start:
{
uint8_t v_a_boxed_1073_; lean_object* v_res_1074_; 
v_a_boxed_1073_ = lean_unbox(v_a_1071_);
v_res_1074_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1065_, v_beginIdx_1066_, v_subst_1067_, v_e_1068_, v_offset_1069_, v_a_1070_, v_a_boxed_1073_, v_a_1072_);
lean_dec_ref(v_subst_1067_);
lean_dec(v_beginIdx_1066_);
lean_dec(v_n_1065_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0___boxed(lean_object* v_n_1075_, lean_object* v_beginIdx_1076_, lean_object* v_subst_1077_, lean_object* v_e_1078_, lean_object* v_offset_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_){
_start:
{
uint8_t v_a_boxed_1083_; lean_object* v_res_1084_; 
v_a_boxed_1083_ = lean_unbox(v_a_1081_);
v_res_1084_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0(v_n_1075_, v_beginIdx_1076_, v_subst_1077_, v_e_1078_, v_offset_1079_, v_a_1080_, v_a_boxed_1083_, v_a_1082_);
lean_dec_ref(v_subst_1077_);
lean_dec(v_beginIdx_1076_);
lean_dec(v_n_1075_);
return v_res_1084_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__1(void){
_start:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1086_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__2));
v___x_1087_ = lean_unsigned_to_nat(34u);
v___x_1088_ = lean_unsigned_to_nat(57u);
v___x_1089_ = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__0));
v___x_1090_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__3));
v___x_1091_ = l_mkPanicMessageWithDecl(v___x_1090_, v___x_1089_, v___x_1088_, v___x_1087_, v___x_1086_);
return v___x_1091_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__2(void){
_start:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1092_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__2));
v___x_1093_ = lean_unsigned_to_nat(32u);
v___x_1094_ = lean_unsigned_to_nat(56u);
v___x_1095_ = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__0));
v___x_1096_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__3));
v___x_1097_ = l_mkPanicMessageWithDecl(v___x_1096_, v___x_1095_, v___x_1094_, v___x_1093_, v___x_1092_);
return v___x_1097_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27(lean_object* v_e_1098_, lean_object* v_beginIdx_1099_, lean_object* v_endIdx_1100_, lean_object* v_subst_1101_, uint8_t v_a_1102_, lean_object* v_a_1103_){
_start:
{
uint8_t v___x_1104_; 
v___x_1104_ = lean_nat_dec_lt(v_endIdx_1100_, v_beginIdx_1099_);
if (v___x_1104_ == 0)
{
lean_object* v___x_1105_; uint8_t v___x_1106_; 
v___x_1105_ = lean_array_get_size(v_subst_1101_);
v___x_1106_ = lean_nat_dec_lt(v___x_1105_, v_endIdx_1100_);
if (v___x_1106_ == 0)
{
lean_object* v_n_1107_; lean_object* v___x_1108_; 
v_n_1107_ = lean_nat_sub(v_endIdx_1100_, v_beginIdx_1099_);
v___x_1108_ = lean_unsigned_to_nat(0u);
switch(lean_obj_tag(v_e_1098_))
{
case 0:
{
lean_object* v_deBruijnIndex_1109_; uint8_t v___x_1110_; 
v_deBruijnIndex_1109_ = lean_ctor_get(v_e_1098_, 0);
v___x_1110_ = lean_nat_dec_le(v___x_1108_, v_deBruijnIndex_1109_);
if (v___x_1110_ == 0)
{
lean_object* v___x_1111_; 
lean_dec(v_n_1107_);
v___x_1111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1111_, 0, v_e_1098_);
lean_ctor_set(v___x_1111_, 1, v_a_1103_);
return v___x_1111_;
}
else
{
uint8_t v___x_1112_; 
lean_inc(v_deBruijnIndex_1109_);
lean_dec_ref(v_e_1098_);
v___x_1112_ = lean_nat_dec_lt(v_deBruijnIndex_1109_, v_n_1107_);
if (v___x_1112_ == 0)
{
lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1113_ = lean_nat_sub(v_deBruijnIndex_1109_, v_n_1107_);
lean_dec(v_n_1107_);
lean_dec(v_deBruijnIndex_1109_);
v___x_1114_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___redArg(v___x_1113_, v_a_1103_);
return v___x_1114_;
}
else
{
lean_object* v___x_1115_; lean_object* v_v_1116_; lean_object* v___x_1117_; 
lean_dec(v_n_1107_);
v___x_1115_ = lean_nat_add(v_beginIdx_1099_, v_deBruijnIndex_1109_);
lean_dec(v_deBruijnIndex_1109_);
v_v_1116_ = lean_array_fget_borrowed(v_subst_1101_, v___x_1115_);
lean_dec(v___x_1115_);
lean_inc(v_v_1116_);
v___x_1117_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(v_v_1116_, v___x_1108_, v___x_1108_, v_a_1102_, v_a_1103_);
return v___x_1117_;
}
}
}
case 9:
{
lean_object* v___x_1118_; 
lean_dec(v_n_1107_);
v___x_1118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1118_, 0, v_e_1098_);
lean_ctor_set(v___x_1118_, 1, v_a_1103_);
return v___x_1118_;
}
case 2:
{
lean_object* v___x_1119_; 
lean_dec(v_n_1107_);
v___x_1119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1119_, 0, v_e_1098_);
lean_ctor_set(v___x_1119_, 1, v_a_1103_);
return v___x_1119_;
}
case 1:
{
lean_object* v___x_1120_; 
lean_dec(v_n_1107_);
v___x_1120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1120_, 0, v_e_1098_);
lean_ctor_set(v___x_1120_, 1, v_a_1103_);
return v___x_1120_;
}
case 4:
{
lean_object* v___x_1121_; 
lean_dec(v_n_1107_);
v___x_1121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1121_, 0, v_e_1098_);
lean_ctor_set(v___x_1121_, 1, v_a_1103_);
return v___x_1121_;
}
case 3:
{
lean_object* v___x_1122_; 
lean_dec(v_n_1107_);
v___x_1122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1122_, 0, v_e_1098_);
lean_ctor_set(v___x_1122_, 1, v_a_1103_);
return v___x_1122_;
}
default: 
{
lean_object* v___x_1123_; uint8_t v___x_1124_; 
v___x_1123_ = l_Lean_Expr_looseBVarRange(v_e_1098_);
v___x_1124_ = lean_nat_dec_le(v___x_1123_, v___x_1108_);
lean_dec(v___x_1123_);
if (v___x_1124_ == 0)
{
switch(lean_obj_tag(v_e_1098_))
{
case 9:
{
lean_object* v___x_1125_; 
lean_dec(v_n_1107_);
v___x_1125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1125_, 0, v_e_1098_);
lean_ctor_set(v___x_1125_, 1, v_a_1103_);
return v___x_1125_;
}
case 2:
{
lean_object* v___x_1126_; 
lean_dec(v_n_1107_);
v___x_1126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1126_, 0, v_e_1098_);
lean_ctor_set(v___x_1126_, 1, v_a_1103_);
return v___x_1126_;
}
case 0:
{
lean_object* v___x_1127_; 
lean_dec(v_n_1107_);
v___x_1127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1127_, 0, v_e_1098_);
lean_ctor_set(v___x_1127_, 1, v_a_1103_);
return v___x_1127_;
}
case 1:
{
lean_object* v___x_1128_; 
lean_dec(v_n_1107_);
v___x_1128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1128_, 0, v_e_1098_);
lean_ctor_set(v___x_1128_, 1, v_a_1103_);
return v___x_1128_;
}
case 4:
{
lean_object* v___x_1129_; 
lean_dec(v_n_1107_);
v___x_1129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1129_, 0, v_e_1098_);
lean_ctor_set(v___x_1129_, 1, v_a_1103_);
return v___x_1129_;
}
case 3:
{
lean_object* v___x_1130_; 
lean_dec(v_n_1107_);
v___x_1130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1130_, 0, v_e_1098_);
lean_ctor_set(v___x_1130_, 1, v_a_1103_);
return v___x_1130_;
}
default: 
{
lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v_fst_1133_; lean_object* v_snd_1134_; lean_object* v_fst_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1142_; 
v___x_1131_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__2, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__2_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__2);
v___x_1132_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0(v_n_1107_, v_beginIdx_1099_, v_subst_1101_, v_e_1098_, v___x_1108_, v___x_1131_, v_a_1102_, v_a_1103_);
lean_dec(v_n_1107_);
v_fst_1133_ = lean_ctor_get(v___x_1132_, 0);
lean_inc(v_fst_1133_);
v_snd_1134_ = lean_ctor_get(v___x_1132_, 1);
lean_inc(v_snd_1134_);
lean_dec_ref(v___x_1132_);
v_fst_1135_ = lean_ctor_get(v_fst_1133_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v_fst_1133_);
if (v_isSharedCheck_1142_ == 0)
{
lean_object* v_unused_1143_; 
v_unused_1143_ = lean_ctor_get(v_fst_1133_, 1);
lean_dec(v_unused_1143_);
v___x_1137_ = v_fst_1133_;
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_fst_1135_);
lean_dec(v_fst_1133_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1140_; 
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 1, v_snd_1134_);
v___x_1140_ = v___x_1137_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_fst_1135_);
lean_ctor_set(v_reuseFailAlloc_1141_, 1, v_snd_1134_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
}
}
else
{
lean_object* v___x_1144_; 
lean_dec(v_n_1107_);
v___x_1144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1144_, 0, v_e_1098_);
lean_ctor_set(v___x_1144_, 1, v_a_1103_);
return v___x_1144_;
}
}
}
}
else
{
lean_object* v___x_1145_; lean_object* v___x_1146_; 
lean_dec_ref(v_e_1098_);
v___x_1145_ = lean_obj_once(&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__1, &l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__1_once, _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__1);
v___x_1146_ = l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1(v___x_1145_, v_a_1102_, v_a_1103_);
return v___x_1146_;
}
}
else
{
lean_object* v___x_1147_; lean_object* v___x_1148_; 
lean_dec_ref(v_e_1098_);
v___x_1147_ = lean_obj_once(&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__2, &l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__2_once, _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__2);
v___x_1148_ = l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1(v___x_1147_, v_a_1102_, v_a_1103_);
return v___x_1148_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___boxed(lean_object* v_e_1149_, lean_object* v_beginIdx_1150_, lean_object* v_endIdx_1151_, lean_object* v_subst_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_){
_start:
{
uint8_t v_a_boxed_1155_; lean_object* v_res_1156_; 
v_a_boxed_1155_ = lean_unbox(v_a_1153_);
v_res_1156_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27(v_e_1149_, v_beginIdx_1150_, v_endIdx_1151_, v_subst_1152_, v_a_boxed_1155_, v_a_1154_);
lean_dec_ref(v_subst_1152_);
lean_dec(v_endIdx_1151_);
lean_dec(v_beginIdx_1150_);
return v_res_1156_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27(lean_object* v_e_1157_, lean_object* v_subst_1158_, uint8_t v_a_1159_, lean_object* v_a_1160_){
_start:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1161_ = lean_unsigned_to_nat(0u);
v___x_1162_ = lean_array_get_size(v_subst_1158_);
v___x_1163_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27(v_e_1157_, v___x_1161_, v___x_1162_, v_subst_1158_, v_a_1159_, v_a_1160_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27___boxed(lean_object* v_e_1164_, lean_object* v_subst_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_){
_start:
{
uint8_t v_a_boxed_1168_; lean_object* v_res_1169_; 
v_a_boxed_1168_ = lean_unbox(v_a_1166_);
v_res_1169_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27(v_e_1164_, v_subst_1165_, v_a_boxed_1168_, v_a_1167_);
lean_dec_ref(v_subst_1165_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateS___redArg(lean_object* v_e_1170_, lean_object* v_subst_1171_, lean_object* v_a_1172_){
_start:
{
lean_object* v___x_1174_; lean_object* v_share_1175_; lean_object* v_maxFVar_1176_; lean_object* v_proofInstInfo_1177_; lean_object* v_inferType_1178_; lean_object* v_getLevel_1179_; lean_object* v_congrInfo_1180_; lean_object* v_defEqI_1181_; lean_object* v_extensions_1182_; uint8_t v_debug_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1216_; 
v___x_1174_ = lean_st_ref_take(v_a_1172_);
v_share_1175_ = lean_ctor_get(v___x_1174_, 0);
v_maxFVar_1176_ = lean_ctor_get(v___x_1174_, 1);
v_proofInstInfo_1177_ = lean_ctor_get(v___x_1174_, 2);
v_inferType_1178_ = lean_ctor_get(v___x_1174_, 3);
v_getLevel_1179_ = lean_ctor_get(v___x_1174_, 4);
v_congrInfo_1180_ = lean_ctor_get(v___x_1174_, 5);
v_defEqI_1181_ = lean_ctor_get(v___x_1174_, 6);
v_extensions_1182_ = lean_ctor_get(v___x_1174_, 7);
v_debug_1183_ = lean_ctor_get_uint8(v___x_1174_, sizeof(void*)*8);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1174_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1185_ = v___x_1174_;
v_isShared_1186_ = v_isSharedCheck_1216_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_extensions_1182_);
lean_inc(v_defEqI_1181_);
lean_inc(v_congrInfo_1180_);
lean_inc(v_getLevel_1179_);
lean_inc(v_inferType_1178_);
lean_inc(v_proofInstInfo_1177_);
lean_inc(v_maxFVar_1176_);
lean_inc(v_share_1175_);
lean_dec(v___x_1174_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1216_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1187_; lean_object* v___x_1189_; 
v___x_1187_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__0, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__0_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__0);
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 0, v___x_1187_);
v___x_1189_ = v___x_1185_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v___x_1187_);
lean_ctor_set(v_reuseFailAlloc_1215_, 1, v_maxFVar_1176_);
lean_ctor_set(v_reuseFailAlloc_1215_, 2, v_proofInstInfo_1177_);
lean_ctor_set(v_reuseFailAlloc_1215_, 3, v_inferType_1178_);
lean_ctor_set(v_reuseFailAlloc_1215_, 4, v_getLevel_1179_);
lean_ctor_set(v_reuseFailAlloc_1215_, 5, v_congrInfo_1180_);
lean_ctor_set(v_reuseFailAlloc_1215_, 6, v_defEqI_1181_);
lean_ctor_set(v_reuseFailAlloc_1215_, 7, v_extensions_1182_);
lean_ctor_set_uint8(v_reuseFailAlloc_1215_, sizeof(void*)*8, v_debug_1183_);
v___x_1189_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; uint8_t v_debug_1192_; lean_object* v___x_1193_; lean_object* v_fst_1194_; lean_object* v_snd_1195_; lean_object* v___x_1196_; lean_object* v_maxFVar_1197_; lean_object* v_proofInstInfo_1198_; lean_object* v_inferType_1199_; lean_object* v_getLevel_1200_; lean_object* v_congrInfo_1201_; lean_object* v_defEqI_1202_; lean_object* v_extensions_1203_; uint8_t v_debug_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1213_; 
v___x_1190_ = lean_st_ref_set(v_a_1172_, v___x_1189_);
v___x_1191_ = lean_st_ref_get(v_a_1172_);
v_debug_1192_ = lean_ctor_get_uint8(v___x_1191_, sizeof(void*)*8);
lean_dec(v___x_1191_);
v___x_1193_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27(v_e_1170_, v_subst_1171_, v_debug_1192_, v_share_1175_);
v_fst_1194_ = lean_ctor_get(v___x_1193_, 0);
lean_inc(v_fst_1194_);
v_snd_1195_ = lean_ctor_get(v___x_1193_, 1);
lean_inc(v_snd_1195_);
lean_dec_ref(v___x_1193_);
v___x_1196_ = lean_st_ref_take(v_a_1172_);
v_maxFVar_1197_ = lean_ctor_get(v___x_1196_, 1);
v_proofInstInfo_1198_ = lean_ctor_get(v___x_1196_, 2);
v_inferType_1199_ = lean_ctor_get(v___x_1196_, 3);
v_getLevel_1200_ = lean_ctor_get(v___x_1196_, 4);
v_congrInfo_1201_ = lean_ctor_get(v___x_1196_, 5);
v_defEqI_1202_ = lean_ctor_get(v___x_1196_, 6);
v_extensions_1203_ = lean_ctor_get(v___x_1196_, 7);
v_debug_1204_ = lean_ctor_get_uint8(v___x_1196_, sizeof(void*)*8);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1196_);
if (v_isSharedCheck_1213_ == 0)
{
lean_object* v_unused_1214_; 
v_unused_1214_ = lean_ctor_get(v___x_1196_, 0);
lean_dec(v_unused_1214_);
v___x_1206_ = v___x_1196_;
v_isShared_1207_ = v_isSharedCheck_1213_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_extensions_1203_);
lean_inc(v_defEqI_1202_);
lean_inc(v_congrInfo_1201_);
lean_inc(v_getLevel_1200_);
lean_inc(v_inferType_1199_);
lean_inc(v_proofInstInfo_1198_);
lean_inc(v_maxFVar_1197_);
lean_dec(v___x_1196_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1213_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___x_1209_; 
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 0, v_snd_1195_);
v___x_1209_ = v___x_1206_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_snd_1195_);
lean_ctor_set(v_reuseFailAlloc_1212_, 1, v_maxFVar_1197_);
lean_ctor_set(v_reuseFailAlloc_1212_, 2, v_proofInstInfo_1198_);
lean_ctor_set(v_reuseFailAlloc_1212_, 3, v_inferType_1199_);
lean_ctor_set(v_reuseFailAlloc_1212_, 4, v_getLevel_1200_);
lean_ctor_set(v_reuseFailAlloc_1212_, 5, v_congrInfo_1201_);
lean_ctor_set(v_reuseFailAlloc_1212_, 6, v_defEqI_1202_);
lean_ctor_set(v_reuseFailAlloc_1212_, 7, v_extensions_1203_);
lean_ctor_set_uint8(v_reuseFailAlloc_1212_, sizeof(void*)*8, v_debug_1204_);
v___x_1209_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1210_ = lean_st_ref_set(v_a_1172_, v___x_1209_);
v___x_1211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1211_, 0, v_fst_1194_);
return v___x_1211_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateS___redArg___boxed(lean_object* v_e_1217_, lean_object* v_subst_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_){
_start:
{
lean_object* v_res_1221_; 
v_res_1221_ = l_Lean_Meta_Sym_instantiateS___redArg(v_e_1217_, v_subst_1218_, v_a_1219_);
lean_dec(v_a_1219_);
lean_dec_ref(v_subst_1218_);
return v_res_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateS(lean_object* v_e_1222_, lean_object* v_subst_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_){
_start:
{
lean_object* v___x_1231_; 
v___x_1231_ = l_Lean_Meta_Sym_instantiateS___redArg(v_e_1222_, v_subst_1223_, v_a_1225_);
return v___x_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateS___boxed(lean_object* v_e_1232_, lean_object* v_subst_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_){
_start:
{
lean_object* v_res_1241_; 
v_res_1241_ = l_Lean_Meta_Sym_instantiateS(v_e_1232_, v_subst_1233_, v_a_1234_, v_a_1235_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_);
lean_dec(v_a_1239_);
lean_dec_ref(v_a_1238_);
lean_dec(v_a_1237_);
lean_dec_ref(v_a_1236_);
lean_dec(v_a_1235_);
lean_dec_ref(v_a_1234_);
lean_dec_ref(v_subst_1233_);
return v_res_1241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS_loop_spec__0(lean_object* v_f_1242_, lean_object* v_a_1243_, uint8_t v___y_1244_, lean_object* v___y_1245_){
_start:
{
lean_object* v___y_1247_; 
if (v___y_1244_ == 0)
{
v___y_1247_ = v___y_1245_;
goto v___jp_1246_;
}
else
{
lean_object* v___x_1250_; lean_object* v_snd_1251_; lean_object* v___x_1252_; lean_object* v_snd_1253_; 
lean_inc_ref(v_f_1242_);
v___x_1250_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_f_1242_, v___y_1244_, v___y_1245_);
v_snd_1251_ = lean_ctor_get(v___x_1250_, 1);
lean_inc(v_snd_1251_);
lean_dec_ref(v___x_1250_);
lean_inc_ref(v_a_1243_);
v___x_1252_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_a_1243_, v___y_1244_, v_snd_1251_);
v_snd_1253_ = lean_ctor_get(v___x_1252_, 1);
lean_inc(v_snd_1253_);
lean_dec_ref(v___x_1252_);
v___y_1247_ = v_snd_1253_;
goto v___jp_1246_;
}
v___jp_1246_:
{
lean_object* v___x_1248_; lean_object* v___x_1249_; 
v___x_1248_ = l_Lean_Expr_app___override(v_f_1242_, v_a_1243_);
v___x_1249_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1248_, v___y_1247_);
return v___x_1249_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS_loop_spec__0___boxed(lean_object* v_f_1254_, lean_object* v_a_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_){
_start:
{
uint8_t v___y_1244__boxed_1258_; lean_object* v_res_1259_; 
v___y_1244__boxed_1258_ = lean_unbox(v___y_1256_);
v_res_1259_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS_loop_spec__0(v_f_1254_, v_a_1255_, v___y_1244__boxed_1258_, v___y_1257_);
return v_res_1259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS_loop(lean_object* v_revArgs_1260_, lean_object* v_start_1261_, lean_object* v_b_1262_, lean_object* v_i_1263_, uint8_t v_a_1264_, lean_object* v_a_1265_){
_start:
{
uint8_t v___x_1266_; 
v___x_1266_ = lean_nat_dec_le(v_i_1263_, v_start_1261_);
if (v___x_1266_ == 0)
{
lean_object* v___x_1267_; lean_object* v_i_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v_fst_1272_; lean_object* v_snd_1273_; 
v___x_1267_ = lean_unsigned_to_nat(1u);
v_i_1268_ = lean_nat_sub(v_i_1263_, v___x_1267_);
lean_dec(v_i_1263_);
v___x_1269_ = l_Lean_instInhabitedExpr;
v___x_1270_ = lean_array_get_borrowed(v___x_1269_, v_revArgs_1260_, v_i_1268_);
lean_inc(v___x_1270_);
v___x_1271_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS_loop_spec__0(v_b_1262_, v___x_1270_, v_a_1264_, v_a_1265_);
v_fst_1272_ = lean_ctor_get(v___x_1271_, 0);
lean_inc(v_fst_1272_);
v_snd_1273_ = lean_ctor_get(v___x_1271_, 1);
lean_inc(v_snd_1273_);
lean_dec_ref(v___x_1271_);
v_b_1262_ = v_fst_1272_;
v_i_1263_ = v_i_1268_;
v_a_1265_ = v_snd_1273_;
goto _start;
}
else
{
lean_object* v___x_1275_; 
lean_dec(v_i_1263_);
v___x_1275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1275_, 0, v_b_1262_);
lean_ctor_set(v___x_1275_, 1, v_a_1265_);
return v___x_1275_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS_loop___boxed(lean_object* v_revArgs_1276_, lean_object* v_start_1277_, lean_object* v_b_1278_, lean_object* v_i_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_){
_start:
{
uint8_t v_a_boxed_1282_; lean_object* v_res_1283_; 
v_a_boxed_1282_ = lean_unbox(v_a_1280_);
v_res_1283_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS_loop(v_revArgs_1276_, v_start_1277_, v_b_1278_, v_i_1279_, v_a_boxed_1282_, v_a_1281_);
lean_dec(v_start_1277_);
lean_dec_ref(v_revArgs_1276_);
return v_res_1283_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS(lean_object* v_f_1284_, lean_object* v_beginIdx_1285_, lean_object* v_endIdx_1286_, lean_object* v_revArgs_1287_, uint8_t v_a_1288_, lean_object* v_a_1289_){
_start:
{
lean_object* v___x_1290_; 
v___x_1290_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS_loop(v_revArgs_1287_, v_beginIdx_1285_, v_f_1284_, v_endIdx_1286_, v_a_1288_, v_a_1289_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS___boxed(lean_object* v_f_1291_, lean_object* v_beginIdx_1292_, lean_object* v_endIdx_1293_, lean_object* v_revArgs_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_){
_start:
{
uint8_t v_a_boxed_1297_; lean_object* v_res_1298_; 
v_a_boxed_1297_ = lean_unbox(v_a_1295_);
v_res_1298_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS(v_f_1291_, v_beginIdx_1292_, v_endIdx_1293_, v_revArgs_1294_, v_a_boxed_1297_, v_a_1296_);
lean_dec_ref(v_revArgs_1294_);
lean_dec(v_beginIdx_1292_);
return v_res_1298_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_go(lean_object* v_revArgs_1299_, lean_object* v_sz_1300_, lean_object* v_e_1301_, lean_object* v_i_1302_, uint8_t v_a_1303_, lean_object* v_a_1304_){
_start:
{
switch(lean_obj_tag(v_e_1301_))
{
case 6:
{
lean_object* v_body_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; uint8_t v___x_1308_; 
v_body_1305_ = lean_ctor_get(v_e_1301_, 2);
lean_inc_ref(v_body_1305_);
lean_dec_ref(v_e_1301_);
v___x_1306_ = lean_unsigned_to_nat(1u);
v___x_1307_ = lean_nat_add(v_i_1302_, v___x_1306_);
lean_dec(v_i_1302_);
v___x_1308_ = lean_nat_dec_lt(v___x_1307_, v_sz_1300_);
if (v___x_1308_ == 0)
{
lean_object* v___x_1309_; 
lean_dec(v___x_1307_);
v___x_1309_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27(v_body_1305_, v_revArgs_1299_, v_a_1303_, v_a_1304_);
return v___x_1309_;
}
else
{
v_e_1301_ = v_body_1305_;
v_i_1302_ = v___x_1307_;
goto _start;
}
}
case 10:
{
lean_object* v_expr_1311_; 
v_expr_1311_ = lean_ctor_get(v_e_1301_, 1);
lean_inc_ref(v_expr_1311_);
lean_dec_ref(v_e_1301_);
v_e_1301_ = v_expr_1311_;
goto _start;
}
default: 
{
lean_object* v_n_1313_; lean_object* v___x_1314_; lean_object* v_fst_1315_; lean_object* v_snd_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; 
v_n_1313_ = lean_nat_sub(v_sz_1300_, v_i_1302_);
lean_dec(v_i_1302_);
v___x_1314_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27(v_e_1301_, v_n_1313_, v_sz_1300_, v_revArgs_1299_, v_a_1303_, v_a_1304_);
v_fst_1315_ = lean_ctor_get(v___x_1314_, 0);
lean_inc(v_fst_1315_);
v_snd_1316_ = lean_ctor_get(v___x_1314_, 1);
lean_inc(v_snd_1316_);
lean_dec_ref(v___x_1314_);
v___x_1317_ = lean_unsigned_to_nat(0u);
v___x_1318_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS_loop(v_revArgs_1299_, v___x_1317_, v_fst_1315_, v_n_1313_, v_a_1303_, v_snd_1316_);
return v___x_1318_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_go___boxed(lean_object* v_revArgs_1319_, lean_object* v_sz_1320_, lean_object* v_e_1321_, lean_object* v_i_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_){
_start:
{
uint8_t v_a_boxed_1325_; lean_object* v_res_1326_; 
v_a_boxed_1325_ = lean_unbox(v_a_1323_);
v_res_1326_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_go(v_revArgs_1319_, v_sz_1320_, v_e_1321_, v_i_1322_, v_a_boxed_1325_, v_a_1324_);
lean_dec(v_sz_1320_);
lean_dec_ref(v_revArgs_1319_);
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS(lean_object* v_f_1327_, lean_object* v_revArgs_1328_, uint8_t v_a_1329_, lean_object* v_a_1330_){
_start:
{
lean_object* v_sz_1331_; lean_object* v___x_1332_; uint8_t v___x_1333_; 
v_sz_1331_ = lean_array_get_size(v_revArgs_1328_);
v___x_1332_ = lean_unsigned_to_nat(0u);
v___x_1333_ = lean_nat_dec_eq(v_sz_1331_, v___x_1332_);
if (v___x_1333_ == 0)
{
lean_object* v___x_1334_; 
v___x_1334_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_go(v_revArgs_1328_, v_sz_1331_, v_f_1327_, v___x_1332_, v_a_1329_, v_a_1330_);
return v___x_1334_;
}
else
{
lean_object* v___x_1335_; 
v___x_1335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1335_, 0, v_f_1327_);
lean_ctor_set(v___x_1335_, 1, v_a_1330_);
return v___x_1335_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS___boxed(lean_object* v_f_1336_, lean_object* v_revArgs_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_){
_start:
{
uint8_t v_a_boxed_1340_; lean_object* v_res_1341_; 
v_a_boxed_1340_ = lean_unbox(v_a_1338_);
v_res_1341_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS(v_f_1336_, v_revArgs_1337_, v_a_boxed_1340_, v_a_1339_);
lean_dec_ref(v_revArgs_1337_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_1342_, lean_object* v_x_1343_){
_start:
{
if (lean_obj_tag(v_x_1343_) == 0)
{
return v_x_1342_;
}
else
{
lean_object* v_key_1344_; lean_object* v_value_1345_; lean_object* v_tail_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1373_; 
v_key_1344_ = lean_ctor_get(v_x_1343_, 0);
v_value_1345_ = lean_ctor_get(v_x_1343_, 1);
v_tail_1346_ = lean_ctor_get(v_x_1343_, 2);
v_isSharedCheck_1373_ = !lean_is_exclusive(v_x_1343_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1348_ = v_x_1343_;
v_isShared_1349_ = v_isSharedCheck_1373_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_tail_1346_);
lean_inc(v_value_1345_);
lean_inc(v_key_1344_);
lean_dec(v_x_1343_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1373_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v_fst_1350_; lean_object* v_snd_1351_; lean_object* v___x_1352_; uint64_t v___x_1353_; uint64_t v___x_1354_; uint64_t v___x_1355_; uint64_t v___x_1356_; uint64_t v___x_1357_; uint64_t v_fold_1358_; uint64_t v___x_1359_; uint64_t v___x_1360_; uint64_t v___x_1361_; size_t v___x_1362_; size_t v___x_1363_; size_t v___x_1364_; size_t v___x_1365_; size_t v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1369_; 
v_fst_1350_ = lean_ctor_get(v_key_1344_, 0);
v_snd_1351_ = lean_ctor_get(v_key_1344_, 1);
v___x_1352_ = lean_array_get_size(v_x_1342_);
v___x_1353_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_1350_);
v___x_1354_ = lean_uint64_of_nat(v_snd_1351_);
v___x_1355_ = lean_uint64_mix_hash(v___x_1353_, v___x_1354_);
v___x_1356_ = 32ULL;
v___x_1357_ = lean_uint64_shift_right(v___x_1355_, v___x_1356_);
v_fold_1358_ = lean_uint64_xor(v___x_1355_, v___x_1357_);
v___x_1359_ = 16ULL;
v___x_1360_ = lean_uint64_shift_right(v_fold_1358_, v___x_1359_);
v___x_1361_ = lean_uint64_xor(v_fold_1358_, v___x_1360_);
v___x_1362_ = lean_uint64_to_usize(v___x_1361_);
v___x_1363_ = lean_usize_of_nat(v___x_1352_);
v___x_1364_ = ((size_t)1ULL);
v___x_1365_ = lean_usize_sub(v___x_1363_, v___x_1364_);
v___x_1366_ = lean_usize_land(v___x_1362_, v___x_1365_);
v___x_1367_ = lean_array_uget_borrowed(v_x_1342_, v___x_1366_);
lean_inc(v___x_1367_);
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 2, v___x_1367_);
v___x_1369_ = v___x_1348_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_key_1344_);
lean_ctor_set(v_reuseFailAlloc_1372_, 1, v_value_1345_);
lean_ctor_set(v_reuseFailAlloc_1372_, 2, v___x_1367_);
v___x_1369_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
lean_object* v___x_1370_; 
v___x_1370_ = lean_array_uset(v_x_1342_, v___x_1366_, v___x_1369_);
v_x_1342_ = v___x_1370_;
v_x_1343_ = v_tail_1346_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2___redArg(lean_object* v_i_1374_, lean_object* v_source_1375_, lean_object* v_target_1376_){
_start:
{
lean_object* v___x_1377_; uint8_t v___x_1378_; 
v___x_1377_ = lean_array_get_size(v_source_1375_);
v___x_1378_ = lean_nat_dec_lt(v_i_1374_, v___x_1377_);
if (v___x_1378_ == 0)
{
lean_dec_ref(v_source_1375_);
lean_dec(v_i_1374_);
return v_target_1376_;
}
else
{
lean_object* v_es_1379_; lean_object* v___x_1380_; lean_object* v_source_1381_; lean_object* v_target_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
v_es_1379_ = lean_array_fget(v_source_1375_, v_i_1374_);
v___x_1380_ = lean_box(0);
v_source_1381_ = lean_array_fset(v_source_1375_, v_i_1374_, v___x_1380_);
v_target_1382_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3___redArg(v_target_1376_, v_es_1379_);
v___x_1383_ = lean_unsigned_to_nat(1u);
v___x_1384_ = lean_nat_add(v_i_1374_, v___x_1383_);
lean_dec(v_i_1374_);
v_i_1374_ = v___x_1384_;
v_source_1375_ = v_source_1381_;
v_target_1376_ = v_target_1382_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1___redArg(lean_object* v_data_1386_){
_start:
{
lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v_nbuckets_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; 
v___x_1387_ = lean_array_get_size(v_data_1386_);
v___x_1388_ = lean_unsigned_to_nat(2u);
v_nbuckets_1389_ = lean_nat_mul(v___x_1387_, v___x_1388_);
v___x_1390_ = lean_unsigned_to_nat(0u);
v___x_1391_ = lean_box(0);
v___x_1392_ = lean_mk_array(v_nbuckets_1389_, v___x_1391_);
v___x_1393_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2___redArg(v___x_1390_, v_data_1386_, v___x_1392_);
return v___x_1393_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(lean_object* v_a_1394_, lean_object* v_b_1395_, lean_object* v_x_1396_){
_start:
{
if (lean_obj_tag(v_x_1396_) == 0)
{
lean_dec(v_b_1395_);
lean_dec_ref(v_a_1394_);
return v_x_1396_;
}
else
{
lean_object* v_key_1397_; lean_object* v_value_1398_; lean_object* v_tail_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1418_; 
v_key_1397_ = lean_ctor_get(v_x_1396_, 0);
v_value_1398_ = lean_ctor_get(v_x_1396_, 1);
v_tail_1399_ = lean_ctor_get(v_x_1396_, 2);
v_isSharedCheck_1418_ = !lean_is_exclusive(v_x_1396_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1401_ = v_x_1396_;
v_isShared_1402_ = v_isSharedCheck_1418_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_tail_1399_);
lean_inc(v_value_1398_);
lean_inc(v_key_1397_);
lean_dec(v_x_1396_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1418_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
uint8_t v___y_1404_; lean_object* v_fst_1412_; lean_object* v_snd_1413_; lean_object* v_fst_1414_; lean_object* v_snd_1415_; uint8_t v___x_1416_; 
v_fst_1412_ = lean_ctor_get(v_key_1397_, 0);
v_snd_1413_ = lean_ctor_get(v_key_1397_, 1);
v_fst_1414_ = lean_ctor_get(v_a_1394_, 0);
v_snd_1415_ = lean_ctor_get(v_a_1394_, 1);
v___x_1416_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_1412_, v_fst_1414_);
if (v___x_1416_ == 0)
{
v___y_1404_ = v___x_1416_;
goto v___jp_1403_;
}
else
{
uint8_t v___x_1417_; 
v___x_1417_ = lean_nat_dec_eq(v_snd_1413_, v_snd_1415_);
v___y_1404_ = v___x_1417_;
goto v___jp_1403_;
}
v___jp_1403_:
{
if (v___y_1404_ == 0)
{
lean_object* v___x_1405_; lean_object* v___x_1407_; 
v___x_1405_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(v_a_1394_, v_b_1395_, v_tail_1399_);
if (v_isShared_1402_ == 0)
{
lean_ctor_set(v___x_1401_, 2, v___x_1405_);
v___x_1407_ = v___x_1401_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v_key_1397_);
lean_ctor_set(v_reuseFailAlloc_1408_, 1, v_value_1398_);
lean_ctor_set(v_reuseFailAlloc_1408_, 2, v___x_1405_);
v___x_1407_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
return v___x_1407_;
}
}
else
{
lean_object* v___x_1410_; 
lean_dec(v_value_1398_);
lean_dec(v_key_1397_);
if (v_isShared_1402_ == 0)
{
lean_ctor_set(v___x_1401_, 1, v_b_1395_);
lean_ctor_set(v___x_1401_, 0, v_a_1394_);
v___x_1410_ = v___x_1401_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_a_1394_);
lean_ctor_set(v_reuseFailAlloc_1411_, 1, v_b_1395_);
lean_ctor_set(v_reuseFailAlloc_1411_, 2, v_tail_1399_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(lean_object* v_a_1419_, lean_object* v_x_1420_){
_start:
{
if (lean_obj_tag(v_x_1420_) == 0)
{
uint8_t v___x_1421_; 
v___x_1421_ = 0;
return v___x_1421_;
}
else
{
lean_object* v_key_1422_; lean_object* v_tail_1423_; uint8_t v___y_1425_; lean_object* v_fst_1427_; lean_object* v_snd_1428_; lean_object* v_fst_1429_; lean_object* v_snd_1430_; uint8_t v___x_1431_; 
v_key_1422_ = lean_ctor_get(v_x_1420_, 0);
v_tail_1423_ = lean_ctor_get(v_x_1420_, 2);
v_fst_1427_ = lean_ctor_get(v_key_1422_, 0);
v_snd_1428_ = lean_ctor_get(v_key_1422_, 1);
v_fst_1429_ = lean_ctor_get(v_a_1419_, 0);
v_snd_1430_ = lean_ctor_get(v_a_1419_, 1);
v___x_1431_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_1427_, v_fst_1429_);
if (v___x_1431_ == 0)
{
v___y_1425_ = v___x_1431_;
goto v___jp_1424_;
}
else
{
uint8_t v___x_1432_; 
v___x_1432_ = lean_nat_dec_eq(v_snd_1428_, v_snd_1430_);
v___y_1425_ = v___x_1432_;
goto v___jp_1424_;
}
v___jp_1424_:
{
if (v___y_1425_ == 0)
{
v_x_1420_ = v_tail_1423_;
goto _start;
}
else
{
return v___y_1425_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg___boxed(lean_object* v_a_1433_, lean_object* v_x_1434_){
_start:
{
uint8_t v_res_1435_; lean_object* v_r_1436_; 
v_res_1435_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_a_1433_, v_x_1434_);
lean_dec(v_x_1434_);
lean_dec_ref(v_a_1433_);
v_r_1436_ = lean_box(v_res_1435_);
return v_r_1436_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0___redArg(lean_object* v_m_1437_, lean_object* v_a_1438_, lean_object* v_b_1439_){
_start:
{
lean_object* v_size_1440_; lean_object* v_buckets_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1488_; 
v_size_1440_ = lean_ctor_get(v_m_1437_, 0);
v_buckets_1441_ = lean_ctor_get(v_m_1437_, 1);
v_isSharedCheck_1488_ = !lean_is_exclusive(v_m_1437_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1443_ = v_m_1437_;
v_isShared_1444_ = v_isSharedCheck_1488_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_buckets_1441_);
lean_inc(v_size_1440_);
lean_dec(v_m_1437_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1488_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v_fst_1445_; lean_object* v_snd_1446_; lean_object* v___x_1447_; uint64_t v___x_1448_; uint64_t v___x_1449_; uint64_t v___x_1450_; uint64_t v___x_1451_; uint64_t v___x_1452_; uint64_t v_fold_1453_; uint64_t v___x_1454_; uint64_t v___x_1455_; uint64_t v___x_1456_; size_t v___x_1457_; size_t v___x_1458_; size_t v___x_1459_; size_t v___x_1460_; size_t v___x_1461_; lean_object* v_bkt_1462_; uint8_t v___x_1463_; 
v_fst_1445_ = lean_ctor_get(v_a_1438_, 0);
v_snd_1446_ = lean_ctor_get(v_a_1438_, 1);
v___x_1447_ = lean_array_get_size(v_buckets_1441_);
v___x_1448_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_1445_);
v___x_1449_ = lean_uint64_of_nat(v_snd_1446_);
v___x_1450_ = lean_uint64_mix_hash(v___x_1448_, v___x_1449_);
v___x_1451_ = 32ULL;
v___x_1452_ = lean_uint64_shift_right(v___x_1450_, v___x_1451_);
v_fold_1453_ = lean_uint64_xor(v___x_1450_, v___x_1452_);
v___x_1454_ = 16ULL;
v___x_1455_ = lean_uint64_shift_right(v_fold_1453_, v___x_1454_);
v___x_1456_ = lean_uint64_xor(v_fold_1453_, v___x_1455_);
v___x_1457_ = lean_uint64_to_usize(v___x_1456_);
v___x_1458_ = lean_usize_of_nat(v___x_1447_);
v___x_1459_ = ((size_t)1ULL);
v___x_1460_ = lean_usize_sub(v___x_1458_, v___x_1459_);
v___x_1461_ = lean_usize_land(v___x_1457_, v___x_1460_);
v_bkt_1462_ = lean_array_uget_borrowed(v_buckets_1441_, v___x_1461_);
v___x_1463_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_a_1438_, v_bkt_1462_);
if (v___x_1463_ == 0)
{
lean_object* v___x_1464_; lean_object* v_size_x27_1465_; lean_object* v___x_1466_; lean_object* v_buckets_x27_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; uint8_t v___x_1473_; 
v___x_1464_ = lean_unsigned_to_nat(1u);
v_size_x27_1465_ = lean_nat_add(v_size_1440_, v___x_1464_);
lean_dec(v_size_1440_);
lean_inc(v_bkt_1462_);
v___x_1466_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1466_, 0, v_a_1438_);
lean_ctor_set(v___x_1466_, 1, v_b_1439_);
lean_ctor_set(v___x_1466_, 2, v_bkt_1462_);
v_buckets_x27_1467_ = lean_array_uset(v_buckets_1441_, v___x_1461_, v___x_1466_);
v___x_1468_ = lean_unsigned_to_nat(4u);
v___x_1469_ = lean_nat_mul(v_size_x27_1465_, v___x_1468_);
v___x_1470_ = lean_unsigned_to_nat(3u);
v___x_1471_ = lean_nat_div(v___x_1469_, v___x_1470_);
lean_dec(v___x_1469_);
v___x_1472_ = lean_array_get_size(v_buckets_x27_1467_);
v___x_1473_ = lean_nat_dec_le(v___x_1471_, v___x_1472_);
lean_dec(v___x_1471_);
if (v___x_1473_ == 0)
{
lean_object* v_val_1474_; lean_object* v___x_1476_; 
v_val_1474_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1___redArg(v_buckets_x27_1467_);
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 1, v_val_1474_);
lean_ctor_set(v___x_1443_, 0, v_size_x27_1465_);
v___x_1476_ = v___x_1443_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_size_x27_1465_);
lean_ctor_set(v_reuseFailAlloc_1477_, 1, v_val_1474_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
else
{
lean_object* v___x_1479_; 
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 1, v_buckets_x27_1467_);
lean_ctor_set(v___x_1443_, 0, v_size_x27_1465_);
v___x_1479_ = v___x_1443_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v_size_x27_1465_);
lean_ctor_set(v_reuseFailAlloc_1480_, 1, v_buckets_x27_1467_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
return v___x_1479_;
}
}
}
else
{
lean_object* v___x_1481_; lean_object* v_buckets_x27_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1486_; 
lean_inc(v_bkt_1462_);
v___x_1481_ = lean_box(0);
v_buckets_x27_1482_ = lean_array_uset(v_buckets_1441_, v___x_1461_, v___x_1481_);
v___x_1483_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(v_a_1438_, v_b_1439_, v_bkt_1462_);
v___x_1484_ = lean_array_uset(v_buckets_x27_1482_, v___x_1461_, v___x_1483_);
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 1, v___x_1484_);
v___x_1486_ = v___x_1443_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_size_1440_);
lean_ctor_set(v_reuseFailAlloc_1487_, 1, v___x_1484_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(lean_object* v_key_1489_, lean_object* v_r_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_){
_start:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; 
lean_inc_ref(v_r_1490_);
v___x_1493_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1491_, v_key_1489_, v_r_1490_);
v___x_1494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1494_, 0, v_r_1490_);
lean_ctor_set(v___x_1494_, 1, v___x_1493_);
v___x_1495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1495_, 0, v___x_1494_);
lean_ctor_set(v___x_1495_, 1, v_a_1492_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save(lean_object* v_key_1496_, lean_object* v_r_1497_, lean_object* v_a_1498_, uint8_t v_a_1499_, lean_object* v_a_1500_){
_start:
{
lean_object* v___x_1501_; 
v___x_1501_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_1496_, v_r_1497_, v_a_1498_, v_a_1500_);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___boxed(lean_object* v_key_1502_, lean_object* v_r_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_){
_start:
{
uint8_t v_a_boxed_1507_; lean_object* v_res_1508_; 
v_a_boxed_1507_ = lean_unbox(v_a_1505_);
v_res_1508_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save(v_key_1502_, v_r_1503_, v_a_1504_, v_a_boxed_1507_, v_a_1506_);
return v_res_1508_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0(lean_object* v_00_u03b2_1509_, lean_object* v_m_1510_, lean_object* v_a_1511_, lean_object* v_b_1512_){
_start:
{
lean_object* v___x_1513_; 
v___x_1513_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0___redArg(v_m_1510_, v_a_1511_, v_b_1512_);
return v___x_1513_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0(lean_object* v_00_u03b2_1514_, lean_object* v_a_1515_, lean_object* v_x_1516_){
_start:
{
uint8_t v___x_1517_; 
v___x_1517_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_a_1515_, v_x_1516_);
return v___x_1517_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1518_, lean_object* v_a_1519_, lean_object* v_x_1520_){
_start:
{
uint8_t v_res_1521_; lean_object* v_r_1522_; 
v_res_1521_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0(v_00_u03b2_1518_, v_a_1519_, v_x_1520_);
lean_dec(v_x_1520_);
lean_dec_ref(v_a_1519_);
v_r_1522_ = lean_box(v_res_1521_);
return v_r_1522_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1(lean_object* v_00_u03b2_1523_, lean_object* v_data_1524_){
_start:
{
lean_object* v___x_1525_; 
v___x_1525_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1___redArg(v_data_1524_);
return v___x_1525_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2(lean_object* v_00_u03b2_1526_, lean_object* v_a_1527_, lean_object* v_b_1528_, lean_object* v_x_1529_){
_start:
{
lean_object* v___x_1530_; 
v___x_1530_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(v_a_1527_, v_b_1528_, v_x_1529_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1531_, lean_object* v_i_1532_, lean_object* v_source_1533_, lean_object* v_target_1534_){
_start:
{
lean_object* v___x_1535_; 
v___x_1535_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2___redArg(v_i_1532_, v_source_1533_, v_target_1534_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1536_, lean_object* v_x_1537_, lean_object* v_x_1538_){
_start:
{
lean_object* v___x_1539_; 
v___x_1539_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1537_, v_x_1538_);
return v___x_1539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0___redArg(lean_object* v_idx_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_){
_start:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v_fst_1545_; lean_object* v_snd_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1554_; 
v___x_1543_ = l_Lean_Expr_bvar___override(v_idx_1540_);
v___x_1544_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1543_, v___y_1542_);
v_fst_1545_ = lean_ctor_get(v___x_1544_, 0);
v_snd_1546_ = lean_ctor_get(v___x_1544_, 1);
v_isSharedCheck_1554_ = !lean_is_exclusive(v___x_1544_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1548_ = v___x_1544_;
v_isShared_1549_ = v_isSharedCheck_1554_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_snd_1546_);
lean_inc(v_fst_1545_);
lean_dec(v___x_1544_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1554_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v___x_1551_; 
if (v_isShared_1549_ == 0)
{
lean_ctor_set(v___x_1548_, 1, v___y_1541_);
v___x_1551_ = v___x_1548_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v_fst_1545_);
lean_ctor_set(v_reuseFailAlloc_1553_, 1, v___y_1541_);
v___x_1551_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
lean_object* v___x_1552_; 
v___x_1552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1551_);
lean_ctor_set(v___x_1552_, 1, v_snd_1546_);
return v___x_1552_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0(lean_object* v_idx_1555_, lean_object* v___y_1556_, uint8_t v___y_1557_, lean_object* v___y_1558_){
_start:
{
lean_object* v___x_1559_; 
v___x_1559_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0___redArg(v_idx_1555_, v___y_1556_, v___y_1558_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0___boxed(lean_object* v_idx_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_){
_start:
{
uint8_t v___y_1291__boxed_1564_; lean_object* v_res_1565_; 
v___y_1291__boxed_1564_ = lean_unbox(v___y_1562_);
v_res_1565_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0(v_idx_1560_, v___y_1561_, v___y_1291__boxed_1564_, v___y_1563_);
return v_res_1565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(lean_object* v_subst_1566_, lean_object* v_e_1567_, lean_object* v_bidx_1568_, lean_object* v_offset_1569_, lean_object* v_a_1570_, uint8_t v_a_1571_, lean_object* v_a_1572_){
_start:
{
uint8_t v___x_1573_; 
v___x_1573_ = lean_nat_dec_le(v_offset_1569_, v_bidx_1568_);
if (v___x_1573_ == 0)
{
lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1574_, 0, v_e_1567_);
lean_ctor_set(v___x_1574_, 1, v_a_1570_);
v___x_1575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1574_);
lean_ctor_set(v___x_1575_, 1, v_a_1572_);
return v___x_1575_;
}
else
{
lean_object* v_n_1576_; lean_object* v___x_1577_; uint8_t v___x_1578_; 
lean_dec_ref(v_e_1567_);
v_n_1576_ = lean_array_get_size(v_subst_1566_);
v___x_1577_ = lean_nat_add(v_offset_1569_, v_n_1576_);
v___x_1578_ = lean_nat_dec_lt(v_bidx_1568_, v___x_1577_);
lean_dec(v___x_1577_);
if (v___x_1578_ == 0)
{
lean_object* v___x_1579_; lean_object* v___x_1580_; 
v___x_1579_ = lean_nat_sub(v_bidx_1568_, v_n_1576_);
v___x_1580_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0___redArg(v___x_1579_, v_a_1570_, v_a_1572_);
return v___x_1580_;
}
else
{
lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v_v_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v_fst_1588_; lean_object* v_snd_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1597_; 
v___x_1581_ = lean_nat_sub(v_bidx_1568_, v_offset_1569_);
v___x_1582_ = lean_nat_sub(v_n_1576_, v___x_1581_);
lean_dec(v___x_1581_);
v___x_1583_ = lean_unsigned_to_nat(1u);
v___x_1584_ = lean_nat_sub(v___x_1582_, v___x_1583_);
lean_dec(v___x_1582_);
v_v_1585_ = lean_array_fget_borrowed(v_subst_1566_, v___x_1584_);
lean_dec(v___x_1584_);
v___x_1586_ = lean_unsigned_to_nat(0u);
lean_inc(v_v_1585_);
v___x_1587_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(v_v_1585_, v___x_1586_, v_offset_1569_, v_a_1571_, v_a_1572_);
v_fst_1588_ = lean_ctor_get(v___x_1587_, 0);
v_snd_1589_ = lean_ctor_get(v___x_1587_, 1);
v_isSharedCheck_1597_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1591_ = v___x_1587_;
v_isShared_1592_ = v_isSharedCheck_1597_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_snd_1589_);
lean_inc(v_fst_1588_);
lean_dec(v___x_1587_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1597_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v___x_1594_; 
if (v_isShared_1592_ == 0)
{
lean_ctor_set(v___x_1591_, 1, v_a_1570_);
v___x_1594_ = v___x_1591_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_fst_1588_);
lean_ctor_set(v_reuseFailAlloc_1596_, 1, v_a_1570_);
v___x_1594_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
lean_object* v___x_1595_; 
v___x_1595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1595_, 0, v___x_1594_);
lean_ctor_set(v___x_1595_, 1, v_snd_1589_);
return v___x_1595_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar___boxed(lean_object* v_subst_1598_, lean_object* v_e_1599_, lean_object* v_bidx_1600_, lean_object* v_offset_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_){
_start:
{
uint8_t v_a_boxed_1605_; lean_object* v_res_1606_; 
v_a_boxed_1605_ = lean_unbox(v_a_1603_);
v_res_1606_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(v_subst_1598_, v_e_1599_, v_bidx_1600_, v_offset_1601_, v_a_1602_, v_a_boxed_1605_, v_a_1604_);
lean_dec(v_offset_1601_);
lean_dec(v_bidx_1600_);
lean_dec_ref(v_subst_1598_);
return v_res_1606_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__3(void){
_start:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1610_ = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__2));
v___x_1611_ = lean_unsigned_to_nat(25u);
v___x_1612_ = lean_unsigned_to_nat(148u);
v___x_1613_ = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__1));
v___x_1614_ = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__0));
v___x_1615_ = l_mkPanicMessageWithDecl(v___x_1614_, v___x_1613_, v___x_1612_, v___x_1611_, v___x_1610_);
return v___x_1615_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__1(void){
_start:
{
lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1617_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__2));
v___x_1618_ = lean_unsigned_to_nat(11u);
v___x_1619_ = lean_unsigned_to_nat(179u);
v___x_1620_ = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__0));
v___x_1621_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__3));
v___x_1622_ = l_mkPanicMessageWithDecl(v___x_1621_, v___x_1620_, v___x_1619_, v___x_1618_, v___x_1617_);
return v___x_1622_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta(lean_object* v_subst_1623_, lean_object* v_e_1624_, lean_object* v_f_1625_, lean_object* v_argsRev_1626_, lean_object* v_offset_1627_, uint8_t v_modified_1628_, lean_object* v_a_1629_, uint8_t v_a_1630_, lean_object* v_a_1631_){
_start:
{
switch(lean_obj_tag(v_f_1625_))
{
case 5:
{
lean_object* v_fn_1632_; lean_object* v_arg_1633_; lean_object* v___x_1634_; lean_object* v_fst_1635_; lean_object* v_snd_1636_; lean_object* v_fst_1637_; lean_object* v_snd_1638_; lean_object* v___x_1639_; 
v_fn_1632_ = lean_ctor_get(v_f_1625_, 0);
lean_inc_ref(v_fn_1632_);
v_arg_1633_ = lean_ctor_get(v_f_1625_, 1);
lean_inc_ref(v_arg_1633_);
lean_dec_ref(v_f_1625_);
lean_inc(v_offset_1627_);
lean_inc_ref(v_arg_1633_);
v___x_1634_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1623_, v_arg_1633_, v_offset_1627_, v_a_1629_, v_a_1630_, v_a_1631_);
v_fst_1635_ = lean_ctor_get(v___x_1634_, 0);
lean_inc(v_fst_1635_);
v_snd_1636_ = lean_ctor_get(v___x_1634_, 1);
lean_inc(v_snd_1636_);
lean_dec_ref(v___x_1634_);
v_fst_1637_ = lean_ctor_get(v_fst_1635_, 0);
lean_inc(v_fst_1637_);
v_snd_1638_ = lean_ctor_get(v_fst_1635_, 1);
lean_inc(v_snd_1638_);
lean_dec(v_fst_1635_);
lean_inc(v_fst_1637_);
v___x_1639_ = lean_array_push(v_argsRev_1626_, v_fst_1637_);
if (v_modified_1628_ == 0)
{
uint8_t v___x_1640_; 
v___x_1640_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_1633_, v_fst_1637_);
lean_dec(v_fst_1637_);
lean_dec_ref(v_arg_1633_);
if (v___x_1640_ == 0)
{
uint8_t v___x_1641_; 
v___x_1641_ = 1;
v_f_1625_ = v_fn_1632_;
v_argsRev_1626_ = v___x_1639_;
v_modified_1628_ = v___x_1641_;
v_a_1629_ = v_snd_1638_;
v_a_1631_ = v_snd_1636_;
goto _start;
}
else
{
v_f_1625_ = v_fn_1632_;
v_argsRev_1626_ = v___x_1639_;
v_a_1629_ = v_snd_1638_;
v_a_1631_ = v_snd_1636_;
goto _start;
}
}
else
{
lean_dec(v_fst_1637_);
lean_dec_ref(v_arg_1633_);
v_f_1625_ = v_fn_1632_;
v_argsRev_1626_ = v___x_1639_;
v_a_1629_ = v_snd_1638_;
v_a_1631_ = v_snd_1636_;
goto _start;
}
}
case 0:
{
lean_object* v_deBruijnIndex_1645_; lean_object* v___x_1646_; lean_object* v_fst_1647_; lean_object* v_snd_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1677_; 
v_deBruijnIndex_1645_ = lean_ctor_get(v_f_1625_, 0);
lean_inc_ref(v_f_1625_);
v___x_1646_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(v_subst_1623_, v_f_1625_, v_deBruijnIndex_1645_, v_offset_1627_, v_a_1629_, v_a_1630_, v_a_1631_);
lean_dec(v_offset_1627_);
v_fst_1647_ = lean_ctor_get(v___x_1646_, 0);
v_snd_1648_ = lean_ctor_get(v___x_1646_, 1);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1646_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1650_ = v___x_1646_;
v_isShared_1651_ = v_isSharedCheck_1677_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_snd_1648_);
lean_inc(v_fst_1647_);
lean_dec(v___x_1646_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1677_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v_fst_1652_; lean_object* v_snd_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1676_; 
v_fst_1652_ = lean_ctor_get(v_fst_1647_, 0);
v_snd_1653_ = lean_ctor_get(v_fst_1647_, 1);
v_isSharedCheck_1676_ = !lean_is_exclusive(v_fst_1647_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1655_ = v_fst_1647_;
v_isShared_1656_ = v_isSharedCheck_1676_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_snd_1653_);
lean_inc(v_fst_1652_);
lean_dec(v_fst_1647_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1676_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
if (v_modified_1628_ == 0)
{
uint8_t v___x_1671_; 
v___x_1671_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_f_1625_, v_fst_1652_);
lean_dec_ref(v_f_1625_);
if (v___x_1671_ == 0)
{
lean_del_object(v___x_1650_);
lean_dec_ref(v_e_1624_);
goto v___jp_1657_;
}
else
{
lean_object* v___x_1673_; 
lean_del_object(v___x_1655_);
lean_dec(v_fst_1652_);
lean_dec_ref(v_argsRev_1626_);
if (v_isShared_1651_ == 0)
{
lean_ctor_set(v___x_1650_, 1, v_snd_1653_);
lean_ctor_set(v___x_1650_, 0, v_e_1624_);
v___x_1673_ = v___x_1650_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_e_1624_);
lean_ctor_set(v_reuseFailAlloc_1675_, 1, v_snd_1653_);
v___x_1673_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
lean_object* v___x_1674_; 
v___x_1674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1674_, 0, v___x_1673_);
lean_ctor_set(v___x_1674_, 1, v_snd_1648_);
return v___x_1674_;
}
}
}
else
{
lean_del_object(v___x_1650_);
lean_dec_ref(v_f_1625_);
lean_dec_ref(v_e_1624_);
goto v___jp_1657_;
}
v___jp_1657_:
{
lean_object* v___x_1658_; lean_object* v_fst_1659_; lean_object* v_snd_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1670_; 
v___x_1658_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS(v_fst_1652_, v_argsRev_1626_, v_a_1630_, v_snd_1648_);
lean_dec_ref(v_argsRev_1626_);
v_fst_1659_ = lean_ctor_get(v___x_1658_, 0);
v_snd_1660_ = lean_ctor_get(v___x_1658_, 1);
v_isSharedCheck_1670_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1670_ == 0)
{
v___x_1662_ = v___x_1658_;
v_isShared_1663_ = v_isSharedCheck_1670_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_snd_1660_);
lean_inc(v_fst_1659_);
lean_dec(v___x_1658_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1670_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1665_; 
if (v_isShared_1663_ == 0)
{
lean_ctor_set(v___x_1662_, 1, v_snd_1653_);
v___x_1665_ = v___x_1662_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v_fst_1659_);
lean_ctor_set(v_reuseFailAlloc_1669_, 1, v_snd_1653_);
v___x_1665_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
lean_object* v___x_1667_; 
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 1, v_snd_1660_);
lean_ctor_set(v___x_1655_, 0, v___x_1665_);
v___x_1667_ = v___x_1655_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v___x_1665_);
lean_ctor_set(v_reuseFailAlloc_1668_, 1, v_snd_1660_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
}
}
}
}
default: 
{
lean_object* v___x_1678_; lean_object* v___x_1679_; 
lean_dec(v_offset_1627_);
lean_dec_ref(v_argsRev_1626_);
lean_dec_ref(v_f_1625_);
lean_dec_ref(v_e_1624_);
v___x_1678_ = lean_obj_once(&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__1, &l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__1_once, _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__1);
v___x_1679_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9(v___x_1678_, v_a_1629_, v_a_1630_, v_a_1631_);
return v___x_1679_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg(lean_object* v_subst_1680_, lean_object* v_e_1681_, lean_object* v_f_1682_, lean_object* v_arg_1683_, lean_object* v_offset_1684_, lean_object* v_a_1685_, uint8_t v_a_1686_, lean_object* v_a_1687_){
_start:
{
lean_object* v___x_1688_; lean_object* v_fst_1689_; lean_object* v_snd_1690_; lean_object* v_fst_1691_; lean_object* v_snd_1692_; lean_object* v___x_1693_; uint8_t v___x_1694_; 
lean_inc(v_offset_1684_);
lean_inc_ref(v_arg_1683_);
v___x_1688_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1680_, v_arg_1683_, v_offset_1684_, v_a_1685_, v_a_1686_, v_a_1687_);
v_fst_1689_ = lean_ctor_get(v___x_1688_, 0);
lean_inc(v_fst_1689_);
v_snd_1690_ = lean_ctor_get(v___x_1688_, 1);
lean_inc(v_snd_1690_);
lean_dec_ref(v___x_1688_);
v_fst_1691_ = lean_ctor_get(v_fst_1689_, 0);
lean_inc(v_fst_1691_);
v_snd_1692_ = lean_ctor_get(v_fst_1689_, 1);
lean_inc(v_snd_1692_);
lean_dec(v_fst_1689_);
v___x_1693_ = l_Lean_Expr_getAppFn(v_f_1682_);
v___x_1694_ = l_Lean_Expr_isBVar(v___x_1693_);
lean_dec_ref(v___x_1693_);
if (v___x_1694_ == 0)
{
lean_object* v___x_1695_; lean_object* v_fst_1696_; lean_object* v_snd_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1722_; 
lean_dec_ref(v_arg_1683_);
v___x_1695_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault(v_subst_1680_, v_f_1682_, v_offset_1684_, v_snd_1692_, v_a_1686_, v_snd_1690_);
v_fst_1696_ = lean_ctor_get(v___x_1695_, 0);
v_snd_1697_ = lean_ctor_get(v___x_1695_, 1);
v_isSharedCheck_1722_ = !lean_is_exclusive(v___x_1695_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1699_ = v___x_1695_;
v_isShared_1700_ = v_isSharedCheck_1722_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_snd_1697_);
lean_inc(v_fst_1696_);
lean_dec(v___x_1695_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1722_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v_fst_1701_; lean_object* v_snd_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1721_; 
v_fst_1701_ = lean_ctor_get(v_fst_1696_, 0);
v_snd_1702_ = lean_ctor_get(v_fst_1696_, 1);
v_isSharedCheck_1721_ = !lean_is_exclusive(v_fst_1696_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1704_ = v_fst_1696_;
v_isShared_1705_ = v_isSharedCheck_1721_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_snd_1702_);
lean_inc(v_fst_1701_);
lean_dec(v_fst_1696_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1721_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
uint8_t v___y_1707_; 
if (lean_obj_tag(v_e_1681_) == 5)
{
lean_object* v_fn_1715_; lean_object* v_arg_1716_; uint8_t v___x_1717_; 
v_fn_1715_ = lean_ctor_get(v_e_1681_, 0);
v_arg_1716_ = lean_ctor_get(v_e_1681_, 1);
v___x_1717_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_1715_, v_fst_1701_);
if (v___x_1717_ == 0)
{
v___y_1707_ = v___x_1717_;
goto v___jp_1706_;
}
else
{
uint8_t v___x_1718_; 
v___x_1718_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_1716_, v_fst_1691_);
v___y_1707_ = v___x_1718_;
goto v___jp_1706_;
}
}
else
{
lean_object* v___x_1719_; lean_object* v___x_1720_; 
lean_del_object(v___x_1704_);
lean_dec(v_fst_1701_);
lean_del_object(v___x_1699_);
lean_dec(v_fst_1691_);
lean_dec_ref(v_e_1681_);
v___x_1719_ = lean_obj_once(&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__3, &l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__3_once, _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__3);
v___x_1720_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9(v___x_1719_, v_snd_1702_, v_a_1686_, v_snd_1697_);
return v___x_1720_;
}
v___jp_1706_:
{
if (v___y_1707_ == 0)
{
lean_object* v___x_1708_; 
lean_del_object(v___x_1704_);
lean_del_object(v___x_1699_);
lean_dec_ref(v_e_1681_);
v___x_1708_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__3(v_fst_1701_, v_fst_1691_, v_snd_1702_, v_a_1686_, v_snd_1697_);
return v___x_1708_;
}
else
{
lean_object* v___x_1710_; 
lean_dec(v_fst_1701_);
lean_dec(v_fst_1691_);
if (v_isShared_1705_ == 0)
{
lean_ctor_set(v___x_1704_, 0, v_e_1681_);
v___x_1710_ = v___x_1704_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_e_1681_);
lean_ctor_set(v_reuseFailAlloc_1714_, 1, v_snd_1702_);
v___x_1710_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
lean_object* v___x_1712_; 
if (v_isShared_1700_ == 0)
{
lean_ctor_set(v___x_1699_, 0, v___x_1710_);
v___x_1712_ = v___x_1699_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v___x_1710_);
lean_ctor_set(v_reuseFailAlloc_1713_, 1, v_snd_1697_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
return v___x_1712_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; uint8_t v___x_1726_; 
v___x_1723_ = lean_unsigned_to_nat(1u);
v___x_1724_ = lean_mk_empty_array_with_capacity(v___x_1723_);
lean_inc(v_fst_1691_);
v___x_1725_ = lean_array_push(v___x_1724_, v_fst_1691_);
v___x_1726_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_1683_, v_fst_1691_);
lean_dec(v_fst_1691_);
lean_dec_ref(v_arg_1683_);
if (v___x_1726_ == 0)
{
lean_object* v___x_1727_; 
v___x_1727_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta(v_subst_1680_, v_e_1681_, v_f_1682_, v___x_1725_, v_offset_1684_, v___x_1694_, v_snd_1692_, v_a_1686_, v_snd_1690_);
return v___x_1727_;
}
else
{
uint8_t v___x_1728_; lean_object* v___x_1729_; 
v___x_1728_ = 0;
v___x_1729_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta(v_subst_1680_, v_e_1681_, v_f_1682_, v___x_1725_, v_offset_1684_, v___x_1728_, v_snd_1692_, v_a_1686_, v_snd_1690_);
return v___x_1729_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__1(void){
_start:
{
lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; 
v___x_1731_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__2));
v___x_1732_ = lean_unsigned_to_nat(59u);
v___x_1733_ = lean_unsigned_to_nat(190u);
v___x_1734_ = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__0));
v___x_1735_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__3));
v___x_1736_ = l_mkPanicMessageWithDecl(v___x_1735_, v___x_1734_, v___x_1733_, v___x_1732_, v___x_1731_);
return v___x_1736_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit(lean_object* v_subst_1737_, lean_object* v_e_1738_, lean_object* v_offset_1739_, lean_object* v_a_1740_, uint8_t v_a_1741_, lean_object* v_a_1742_){
_start:
{
switch(lean_obj_tag(v_e_1738_))
{
case 0:
{
lean_object* v_deBruijnIndex_1743_; lean_object* v___x_1744_; 
v_deBruijnIndex_1743_ = lean_ctor_get(v_e_1738_, 0);
lean_inc(v_deBruijnIndex_1743_);
v___x_1744_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(v_subst_1737_, v_e_1738_, v_deBruijnIndex_1743_, v_offset_1739_, v_a_1740_, v_a_1741_, v_a_1742_);
lean_dec(v_offset_1739_);
lean_dec(v_deBruijnIndex_1743_);
return v___x_1744_;
}
case 5:
{
lean_object* v_fn_1745_; lean_object* v_arg_1746_; lean_object* v___x_1747_; 
v_fn_1745_ = lean_ctor_get(v_e_1738_, 0);
lean_inc_ref(v_fn_1745_);
v_arg_1746_ = lean_ctor_get(v_e_1738_, 1);
lean_inc_ref(v_arg_1746_);
v___x_1747_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg(v_subst_1737_, v_e_1738_, v_fn_1745_, v_arg_1746_, v_offset_1739_, v_a_1740_, v_a_1741_, v_a_1742_);
return v___x_1747_;
}
case 6:
{
lean_object* v_binderName_1748_; lean_object* v_binderType_1749_; lean_object* v_body_1750_; uint8_t v_binderInfo_1751_; lean_object* v___x_1752_; lean_object* v_fst_1753_; lean_object* v_snd_1754_; lean_object* v_fst_1755_; lean_object* v_snd_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v_fst_1760_; lean_object* v_snd_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1782_; 
v_binderName_1748_ = lean_ctor_get(v_e_1738_, 0);
v_binderType_1749_ = lean_ctor_get(v_e_1738_, 1);
v_body_1750_ = lean_ctor_get(v_e_1738_, 2);
v_binderInfo_1751_ = lean_ctor_get_uint8(v_e_1738_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1739_);
lean_inc_ref(v_binderType_1749_);
v___x_1752_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1737_, v_binderType_1749_, v_offset_1739_, v_a_1740_, v_a_1741_, v_a_1742_);
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
v___x_1757_ = lean_unsigned_to_nat(1u);
v___x_1758_ = lean_nat_add(v_offset_1739_, v___x_1757_);
lean_dec(v_offset_1739_);
lean_inc_ref(v_body_1750_);
v___x_1759_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1737_, v_body_1750_, v___x_1758_, v_snd_1756_, v_a_1741_, v_snd_1754_);
v_fst_1760_ = lean_ctor_get(v___x_1759_, 0);
v_snd_1761_ = lean_ctor_get(v___x_1759_, 1);
v_isSharedCheck_1782_ = !lean_is_exclusive(v___x_1759_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1763_ = v___x_1759_;
v_isShared_1764_ = v_isSharedCheck_1782_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_snd_1761_);
lean_inc(v_fst_1760_);
lean_dec(v___x_1759_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1782_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v_fst_1765_; lean_object* v_snd_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1781_; 
v_fst_1765_ = lean_ctor_get(v_fst_1760_, 0);
v_snd_1766_ = lean_ctor_get(v_fst_1760_, 1);
v_isSharedCheck_1781_ = !lean_is_exclusive(v_fst_1760_);
if (v_isSharedCheck_1781_ == 0)
{
v___x_1768_ = v_fst_1760_;
v_isShared_1769_ = v_isSharedCheck_1781_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_snd_1766_);
lean_inc(v_fst_1765_);
lean_dec(v_fst_1760_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1781_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
uint8_t v___y_1771_; uint8_t v___x_1779_; 
v___x_1779_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_1749_, v_fst_1755_);
if (v___x_1779_ == 0)
{
v___y_1771_ = v___x_1779_;
goto v___jp_1770_;
}
else
{
uint8_t v___x_1780_; 
v___x_1780_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1750_, v_fst_1765_);
v___y_1771_ = v___x_1780_;
goto v___jp_1770_;
}
v___jp_1770_:
{
if (v___y_1771_ == 0)
{
lean_object* v___x_1772_; 
lean_inc(v_binderName_1748_);
lean_del_object(v___x_1768_);
lean_del_object(v___x_1763_);
lean_dec_ref(v_e_1738_);
v___x_1772_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__4(v_binderName_1748_, v_binderInfo_1751_, v_fst_1755_, v_fst_1765_, v_snd_1766_, v_a_1741_, v_snd_1761_);
return v___x_1772_;
}
else
{
lean_object* v___x_1774_; 
lean_dec(v_fst_1765_);
lean_dec(v_fst_1755_);
if (v_isShared_1769_ == 0)
{
lean_ctor_set(v___x_1768_, 0, v_e_1738_);
v___x_1774_ = v___x_1768_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_e_1738_);
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
case 7:
{
lean_object* v_binderName_1783_; lean_object* v_binderType_1784_; lean_object* v_body_1785_; uint8_t v_binderInfo_1786_; lean_object* v___x_1787_; lean_object* v_fst_1788_; lean_object* v_snd_1789_; lean_object* v_fst_1790_; lean_object* v_snd_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v_fst_1795_; lean_object* v_snd_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1817_; 
v_binderName_1783_ = lean_ctor_get(v_e_1738_, 0);
v_binderType_1784_ = lean_ctor_get(v_e_1738_, 1);
v_body_1785_ = lean_ctor_get(v_e_1738_, 2);
v_binderInfo_1786_ = lean_ctor_get_uint8(v_e_1738_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1739_);
lean_inc_ref(v_binderType_1784_);
v___x_1787_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1737_, v_binderType_1784_, v_offset_1739_, v_a_1740_, v_a_1741_, v_a_1742_);
v_fst_1788_ = lean_ctor_get(v___x_1787_, 0);
lean_inc(v_fst_1788_);
v_snd_1789_ = lean_ctor_get(v___x_1787_, 1);
lean_inc(v_snd_1789_);
lean_dec_ref(v___x_1787_);
v_fst_1790_ = lean_ctor_get(v_fst_1788_, 0);
lean_inc(v_fst_1790_);
v_snd_1791_ = lean_ctor_get(v_fst_1788_, 1);
lean_inc(v_snd_1791_);
lean_dec(v_fst_1788_);
v___x_1792_ = lean_unsigned_to_nat(1u);
v___x_1793_ = lean_nat_add(v_offset_1739_, v___x_1792_);
lean_dec(v_offset_1739_);
lean_inc_ref(v_body_1785_);
v___x_1794_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1737_, v_body_1785_, v___x_1793_, v_snd_1791_, v_a_1741_, v_snd_1789_);
v_fst_1795_ = lean_ctor_get(v___x_1794_, 0);
v_snd_1796_ = lean_ctor_get(v___x_1794_, 1);
v_isSharedCheck_1817_ = !lean_is_exclusive(v___x_1794_);
if (v_isSharedCheck_1817_ == 0)
{
v___x_1798_ = v___x_1794_;
v_isShared_1799_ = v_isSharedCheck_1817_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_snd_1796_);
lean_inc(v_fst_1795_);
lean_dec(v___x_1794_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1817_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v_fst_1800_; lean_object* v_snd_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1816_; 
v_fst_1800_ = lean_ctor_get(v_fst_1795_, 0);
v_snd_1801_ = lean_ctor_get(v_fst_1795_, 1);
v_isSharedCheck_1816_ = !lean_is_exclusive(v_fst_1795_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1803_ = v_fst_1795_;
v_isShared_1804_ = v_isSharedCheck_1816_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_snd_1801_);
lean_inc(v_fst_1800_);
lean_dec(v_fst_1795_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1816_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
uint8_t v___y_1806_; uint8_t v___x_1814_; 
v___x_1814_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_1784_, v_fst_1790_);
if (v___x_1814_ == 0)
{
v___y_1806_ = v___x_1814_;
goto v___jp_1805_;
}
else
{
uint8_t v___x_1815_; 
v___x_1815_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1785_, v_fst_1800_);
v___y_1806_ = v___x_1815_;
goto v___jp_1805_;
}
v___jp_1805_:
{
if (v___y_1806_ == 0)
{
lean_object* v___x_1807_; 
lean_inc(v_binderName_1783_);
lean_del_object(v___x_1803_);
lean_del_object(v___x_1798_);
lean_dec_ref(v_e_1738_);
v___x_1807_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__5(v_binderName_1783_, v_binderInfo_1786_, v_fst_1790_, v_fst_1800_, v_snd_1801_, v_a_1741_, v_snd_1796_);
return v___x_1807_;
}
else
{
lean_object* v___x_1809_; 
lean_dec(v_fst_1800_);
lean_dec(v_fst_1790_);
if (v_isShared_1804_ == 0)
{
lean_ctor_set(v___x_1803_, 0, v_e_1738_);
v___x_1809_ = v___x_1803_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v_e_1738_);
lean_ctor_set(v_reuseFailAlloc_1813_, 1, v_snd_1801_);
v___x_1809_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
lean_object* v___x_1811_; 
if (v_isShared_1799_ == 0)
{
lean_ctor_set(v___x_1798_, 0, v___x_1809_);
v___x_1811_ = v___x_1798_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v___x_1809_);
lean_ctor_set(v_reuseFailAlloc_1812_, 1, v_snd_1796_);
v___x_1811_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
return v___x_1811_;
}
}
}
}
}
}
}
case 8:
{
lean_object* v_declName_1818_; lean_object* v_type_1819_; lean_object* v_value_1820_; lean_object* v_body_1821_; uint8_t v_nondep_1822_; lean_object* v___x_1823_; lean_object* v_fst_1824_; lean_object* v_snd_1825_; lean_object* v_fst_1826_; lean_object* v_snd_1827_; lean_object* v___x_1828_; lean_object* v_fst_1829_; lean_object* v_snd_1830_; lean_object* v_fst_1831_; lean_object* v_snd_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v_fst_1836_; lean_object* v_snd_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1860_; 
v_declName_1818_ = lean_ctor_get(v_e_1738_, 0);
v_type_1819_ = lean_ctor_get(v_e_1738_, 1);
v_value_1820_ = lean_ctor_get(v_e_1738_, 2);
v_body_1821_ = lean_ctor_get(v_e_1738_, 3);
v_nondep_1822_ = lean_ctor_get_uint8(v_e_1738_, sizeof(void*)*4 + 8);
lean_inc(v_offset_1739_);
lean_inc_ref(v_type_1819_);
v___x_1823_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1737_, v_type_1819_, v_offset_1739_, v_a_1740_, v_a_1741_, v_a_1742_);
v_fst_1824_ = lean_ctor_get(v___x_1823_, 0);
lean_inc(v_fst_1824_);
v_snd_1825_ = lean_ctor_get(v___x_1823_, 1);
lean_inc(v_snd_1825_);
lean_dec_ref(v___x_1823_);
v_fst_1826_ = lean_ctor_get(v_fst_1824_, 0);
lean_inc(v_fst_1826_);
v_snd_1827_ = lean_ctor_get(v_fst_1824_, 1);
lean_inc(v_snd_1827_);
lean_dec(v_fst_1824_);
lean_inc(v_offset_1739_);
lean_inc_ref(v_value_1820_);
v___x_1828_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1737_, v_value_1820_, v_offset_1739_, v_snd_1827_, v_a_1741_, v_snd_1825_);
v_fst_1829_ = lean_ctor_get(v___x_1828_, 0);
lean_inc(v_fst_1829_);
v_snd_1830_ = lean_ctor_get(v___x_1828_, 1);
lean_inc(v_snd_1830_);
lean_dec_ref(v___x_1828_);
v_fst_1831_ = lean_ctor_get(v_fst_1829_, 0);
lean_inc(v_fst_1831_);
v_snd_1832_ = lean_ctor_get(v_fst_1829_, 1);
lean_inc(v_snd_1832_);
lean_dec(v_fst_1829_);
v___x_1833_ = lean_unsigned_to_nat(1u);
v___x_1834_ = lean_nat_add(v_offset_1739_, v___x_1833_);
lean_dec(v_offset_1739_);
lean_inc_ref(v_body_1821_);
v___x_1835_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1737_, v_body_1821_, v___x_1834_, v_snd_1832_, v_a_1741_, v_snd_1830_);
v_fst_1836_ = lean_ctor_get(v___x_1835_, 0);
v_snd_1837_ = lean_ctor_get(v___x_1835_, 1);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1839_ = v___x_1835_;
v_isShared_1840_ = v_isSharedCheck_1860_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_snd_1837_);
lean_inc(v_fst_1836_);
lean_dec(v___x_1835_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1860_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v_fst_1841_; lean_object* v_snd_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1859_; 
v_fst_1841_ = lean_ctor_get(v_fst_1836_, 0);
v_snd_1842_ = lean_ctor_get(v_fst_1836_, 1);
v_isSharedCheck_1859_ = !lean_is_exclusive(v_fst_1836_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1844_ = v_fst_1836_;
v_isShared_1845_ = v_isSharedCheck_1859_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_snd_1842_);
lean_inc(v_fst_1841_);
lean_dec(v_fst_1836_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1859_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
uint8_t v___y_1847_; uint8_t v___x_1857_; 
v___x_1857_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_type_1819_, v_fst_1826_);
if (v___x_1857_ == 0)
{
v___y_1847_ = v___x_1857_;
goto v___jp_1846_;
}
else
{
uint8_t v___x_1858_; 
v___x_1858_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_value_1820_, v_fst_1831_);
v___y_1847_ = v___x_1858_;
goto v___jp_1846_;
}
v___jp_1846_:
{
if (v___y_1847_ == 0)
{
lean_object* v___x_1848_; 
lean_inc(v_declName_1818_);
lean_del_object(v___x_1844_);
lean_del_object(v___x_1839_);
lean_dec_ref(v_e_1738_);
v___x_1848_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6(v_declName_1818_, v_fst_1826_, v_fst_1831_, v_fst_1841_, v_nondep_1822_, v_snd_1842_, v_a_1741_, v_snd_1837_);
return v___x_1848_;
}
else
{
uint8_t v___x_1849_; 
v___x_1849_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1821_, v_fst_1841_);
if (v___x_1849_ == 0)
{
lean_object* v___x_1850_; 
lean_inc(v_declName_1818_);
lean_del_object(v___x_1844_);
lean_del_object(v___x_1839_);
lean_dec_ref(v_e_1738_);
v___x_1850_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6(v_declName_1818_, v_fst_1826_, v_fst_1831_, v_fst_1841_, v_nondep_1822_, v_snd_1842_, v_a_1741_, v_snd_1837_);
return v___x_1850_;
}
else
{
lean_object* v___x_1852_; 
lean_dec(v_fst_1841_);
lean_dec(v_fst_1831_);
lean_dec(v_fst_1826_);
if (v_isShared_1845_ == 0)
{
lean_ctor_set(v___x_1844_, 0, v_e_1738_);
v___x_1852_ = v___x_1844_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v_e_1738_);
lean_ctor_set(v_reuseFailAlloc_1856_, 1, v_snd_1842_);
v___x_1852_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
lean_object* v___x_1854_; 
if (v_isShared_1840_ == 0)
{
lean_ctor_set(v___x_1839_, 0, v___x_1852_);
v___x_1854_ = v___x_1839_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v___x_1852_);
lean_ctor_set(v_reuseFailAlloc_1855_, 1, v_snd_1837_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
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
lean_object* v_data_1861_; lean_object* v_expr_1862_; lean_object* v___x_1863_; lean_object* v_fst_1864_; lean_object* v_snd_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1883_; 
v_data_1861_ = lean_ctor_get(v_e_1738_, 0);
v_expr_1862_ = lean_ctor_get(v_e_1738_, 1);
lean_inc_ref(v_expr_1862_);
v___x_1863_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1737_, v_expr_1862_, v_offset_1739_, v_a_1740_, v_a_1741_, v_a_1742_);
v_fst_1864_ = lean_ctor_get(v___x_1863_, 0);
v_snd_1865_ = lean_ctor_get(v___x_1863_, 1);
v_isSharedCheck_1883_ = !lean_is_exclusive(v___x_1863_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1867_ = v___x_1863_;
v_isShared_1868_ = v_isSharedCheck_1883_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_snd_1865_);
lean_inc(v_fst_1864_);
lean_dec(v___x_1863_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1883_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
lean_object* v_fst_1869_; lean_object* v_snd_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1882_; 
v_fst_1869_ = lean_ctor_get(v_fst_1864_, 0);
v_snd_1870_ = lean_ctor_get(v_fst_1864_, 1);
v_isSharedCheck_1882_ = !lean_is_exclusive(v_fst_1864_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1872_ = v_fst_1864_;
v_isShared_1873_ = v_isSharedCheck_1882_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_snd_1870_);
lean_inc(v_fst_1869_);
lean_dec(v_fst_1864_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1882_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
uint8_t v___x_1874_; 
v___x_1874_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_expr_1862_, v_fst_1869_);
if (v___x_1874_ == 0)
{
lean_object* v___x_1875_; 
lean_inc(v_data_1861_);
lean_del_object(v___x_1872_);
lean_del_object(v___x_1867_);
lean_dec_ref(v_e_1738_);
v___x_1875_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__7(v_data_1861_, v_fst_1869_, v_snd_1870_, v_a_1741_, v_snd_1865_);
return v___x_1875_;
}
else
{
lean_object* v___x_1877_; 
lean_dec(v_fst_1869_);
if (v_isShared_1873_ == 0)
{
lean_ctor_set(v___x_1872_, 0, v_e_1738_);
v___x_1877_ = v___x_1872_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v_e_1738_);
lean_ctor_set(v_reuseFailAlloc_1881_, 1, v_snd_1870_);
v___x_1877_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
lean_object* v___x_1879_; 
if (v_isShared_1868_ == 0)
{
lean_ctor_set(v___x_1867_, 0, v___x_1877_);
v___x_1879_ = v___x_1867_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v___x_1877_);
lean_ctor_set(v_reuseFailAlloc_1880_, 1, v_snd_1865_);
v___x_1879_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
return v___x_1879_;
}
}
}
}
}
}
case 11:
{
lean_object* v_typeName_1884_; lean_object* v_idx_1885_; lean_object* v_struct_1886_; lean_object* v___x_1887_; lean_object* v_fst_1888_; lean_object* v_snd_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1907_; 
v_typeName_1884_ = lean_ctor_get(v_e_1738_, 0);
v_idx_1885_ = lean_ctor_get(v_e_1738_, 1);
v_struct_1886_ = lean_ctor_get(v_e_1738_, 2);
lean_inc_ref(v_struct_1886_);
v___x_1887_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1737_, v_struct_1886_, v_offset_1739_, v_a_1740_, v_a_1741_, v_a_1742_);
v_fst_1888_ = lean_ctor_get(v___x_1887_, 0);
v_snd_1889_ = lean_ctor_get(v___x_1887_, 1);
v_isSharedCheck_1907_ = !lean_is_exclusive(v___x_1887_);
if (v_isSharedCheck_1907_ == 0)
{
v___x_1891_ = v___x_1887_;
v_isShared_1892_ = v_isSharedCheck_1907_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_snd_1889_);
lean_inc(v_fst_1888_);
lean_dec(v___x_1887_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1907_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v_fst_1893_; lean_object* v_snd_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1906_; 
v_fst_1893_ = lean_ctor_get(v_fst_1888_, 0);
v_snd_1894_ = lean_ctor_get(v_fst_1888_, 1);
v_isSharedCheck_1906_ = !lean_is_exclusive(v_fst_1888_);
if (v_isSharedCheck_1906_ == 0)
{
v___x_1896_ = v_fst_1888_;
v_isShared_1897_ = v_isSharedCheck_1906_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_snd_1894_);
lean_inc(v_fst_1893_);
lean_dec(v_fst_1888_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1906_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
uint8_t v___x_1898_; 
v___x_1898_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_1886_, v_fst_1893_);
if (v___x_1898_ == 0)
{
lean_object* v___x_1899_; 
lean_inc(v_idx_1885_);
lean_inc(v_typeName_1884_);
lean_del_object(v___x_1896_);
lean_del_object(v___x_1891_);
lean_dec_ref(v_e_1738_);
v___x_1899_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__8(v_typeName_1884_, v_idx_1885_, v_fst_1893_, v_snd_1894_, v_a_1741_, v_snd_1889_);
return v___x_1899_;
}
else
{
lean_object* v___x_1901_; 
lean_dec(v_fst_1893_);
if (v_isShared_1897_ == 0)
{
lean_ctor_set(v___x_1896_, 0, v_e_1738_);
v___x_1901_ = v___x_1896_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v_e_1738_);
lean_ctor_set(v_reuseFailAlloc_1905_, 1, v_snd_1894_);
v___x_1901_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
lean_object* v___x_1903_; 
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 0, v___x_1901_);
v___x_1903_ = v___x_1891_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v___x_1901_);
lean_ctor_set(v_reuseFailAlloc_1904_, 1, v_snd_1889_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_1908_; lean_object* v___x_1909_; 
lean_dec(v_offset_1739_);
lean_dec_ref(v_e_1738_);
v___x_1908_ = lean_obj_once(&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__1, &l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__1_once, _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__1);
v___x_1909_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9(v___x_1908_, v_a_1740_, v_a_1741_, v_a_1742_);
return v___x_1909_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(lean_object* v_subst_1910_, lean_object* v_e_1911_, lean_object* v_offset_1912_, lean_object* v_a_1913_, uint8_t v_a_1914_, lean_object* v_a_1915_){
_start:
{
lean_object* v___x_1916_; uint8_t v___x_1917_; 
v___x_1916_ = l_Lean_Expr_looseBVarRange(v_e_1911_);
v___x_1917_ = lean_nat_dec_le(v___x_1916_, v_offset_1912_);
lean_dec(v___x_1916_);
if (v___x_1917_ == 0)
{
lean_object* v_key_1918_; lean_object* v___x_1919_; 
lean_inc(v_offset_1912_);
lean_inc_ref(v_e_1911_);
v_key_1918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1918_, 0, v_e_1911_);
lean_ctor_set(v_key_1918_, 1, v_offset_1912_);
v___x_1919_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___redArg(v_a_1913_, v_key_1918_);
if (lean_obj_tag(v___x_1919_) == 1)
{
lean_object* v_val_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; 
lean_dec_ref(v_key_1918_);
lean_dec(v_offset_1912_);
lean_dec_ref(v_e_1911_);
v_val_1920_ = lean_ctor_get(v___x_1919_, 0);
lean_inc(v_val_1920_);
lean_dec_ref(v___x_1919_);
v___x_1921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1921_, 0, v_val_1920_);
lean_ctor_set(v___x_1921_, 1, v_a_1913_);
v___x_1922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1921_);
lean_ctor_set(v___x_1922_, 1, v_a_1915_);
return v___x_1922_;
}
else
{
lean_dec(v___x_1919_);
switch(lean_obj_tag(v_e_1911_))
{
case 0:
{
lean_object* v_deBruijnIndex_1923_; lean_object* v___x_1924_; lean_object* v_fst_1925_; lean_object* v_snd_1926_; lean_object* v_fst_1927_; lean_object* v_snd_1928_; lean_object* v___x_1929_; 
v_deBruijnIndex_1923_ = lean_ctor_get(v_e_1911_, 0);
lean_inc(v_deBruijnIndex_1923_);
v___x_1924_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(v_subst_1910_, v_e_1911_, v_deBruijnIndex_1923_, v_offset_1912_, v_a_1913_, v_a_1914_, v_a_1915_);
lean_dec(v_offset_1912_);
lean_dec(v_deBruijnIndex_1923_);
v_fst_1925_ = lean_ctor_get(v___x_1924_, 0);
lean_inc(v_fst_1925_);
v_snd_1926_ = lean_ctor_get(v___x_1924_, 1);
lean_inc(v_snd_1926_);
lean_dec_ref(v___x_1924_);
v_fst_1927_ = lean_ctor_get(v_fst_1925_, 0);
lean_inc(v_fst_1927_);
v_snd_1928_ = lean_ctor_get(v_fst_1925_, 1);
lean_inc(v_snd_1928_);
lean_dec(v_fst_1925_);
v___x_1929_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_1918_, v_fst_1927_, v_snd_1928_, v_snd_1926_);
return v___x_1929_;
}
case 9:
{
lean_object* v___x_1930_; 
lean_dec(v_offset_1912_);
v___x_1930_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_1918_, v_e_1911_, v_a_1913_, v_a_1915_);
return v___x_1930_;
}
case 2:
{
lean_object* v___x_1931_; 
lean_dec(v_offset_1912_);
v___x_1931_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_1918_, v_e_1911_, v_a_1913_, v_a_1915_);
return v___x_1931_;
}
case 1:
{
lean_object* v___x_1932_; 
lean_dec(v_offset_1912_);
v___x_1932_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_1918_, v_e_1911_, v_a_1913_, v_a_1915_);
return v___x_1932_;
}
case 4:
{
lean_object* v___x_1933_; 
lean_dec(v_offset_1912_);
v___x_1933_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_1918_, v_e_1911_, v_a_1913_, v_a_1915_);
return v___x_1933_;
}
case 3:
{
lean_object* v___x_1934_; 
lean_dec(v_offset_1912_);
v___x_1934_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_1918_, v_e_1911_, v_a_1913_, v_a_1915_);
return v___x_1934_;
}
default: 
{
lean_object* v___x_1935_; lean_object* v_fst_1936_; lean_object* v_snd_1937_; lean_object* v_fst_1938_; lean_object* v_snd_1939_; lean_object* v___x_1940_; 
v___x_1935_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit(v_subst_1910_, v_e_1911_, v_offset_1912_, v_a_1913_, v_a_1914_, v_a_1915_);
v_fst_1936_ = lean_ctor_get(v___x_1935_, 0);
lean_inc(v_fst_1936_);
v_snd_1937_ = lean_ctor_get(v___x_1935_, 1);
lean_inc(v_snd_1937_);
lean_dec_ref(v___x_1935_);
v_fst_1938_ = lean_ctor_get(v_fst_1936_, 0);
lean_inc(v_fst_1938_);
v_snd_1939_ = lean_ctor_get(v_fst_1936_, 1);
lean_inc(v_snd_1939_);
lean_dec(v_fst_1936_);
v___x_1940_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_1918_, v_fst_1938_, v_snd_1939_, v_snd_1937_);
return v___x_1940_;
}
}
}
}
else
{
lean_object* v___x_1941_; lean_object* v___x_1942_; 
lean_dec(v_offset_1912_);
v___x_1941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1941_, 0, v_e_1911_);
lean_ctor_set(v___x_1941_, 1, v_a_1913_);
v___x_1942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1942_, 0, v___x_1941_);
lean_ctor_set(v___x_1942_, 1, v_a_1915_);
return v___x_1942_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault(lean_object* v_subst_1943_, lean_object* v_e_1944_, lean_object* v_offset_1945_, lean_object* v_a_1946_, uint8_t v_a_1947_, lean_object* v_a_1948_){
_start:
{
if (lean_obj_tag(v_e_1944_) == 5)
{
lean_object* v_fn_1949_; lean_object* v_arg_1950_; lean_object* v_key_1951_; lean_object* v___x_1952_; 
v_fn_1949_ = lean_ctor_get(v_e_1944_, 0);
v_arg_1950_ = lean_ctor_get(v_e_1944_, 1);
lean_inc(v_offset_1945_);
lean_inc_ref(v_e_1944_);
v_key_1951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1951_, 0, v_e_1944_);
lean_ctor_set(v_key_1951_, 1, v_offset_1945_);
v___x_1952_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___redArg(v_a_1946_, v_key_1951_);
if (lean_obj_tag(v___x_1952_) == 1)
{
lean_object* v_val_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; 
lean_dec_ref(v_key_1951_);
lean_dec_ref(v_e_1944_);
lean_dec(v_offset_1945_);
v_val_1953_ = lean_ctor_get(v___x_1952_, 0);
lean_inc(v_val_1953_);
lean_dec_ref(v___x_1952_);
v___x_1954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1954_, 0, v_val_1953_);
lean_ctor_set(v___x_1954_, 1, v_a_1946_);
v___x_1955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1955_, 0, v___x_1954_);
lean_ctor_set(v___x_1955_, 1, v_a_1948_);
return v___x_1955_;
}
else
{
lean_object* v___x_1956_; lean_object* v_fst_1957_; lean_object* v_snd_1958_; lean_object* v_fst_1959_; lean_object* v_snd_1960_; lean_object* v___x_1961_; lean_object* v_fst_1962_; lean_object* v_snd_1963_; lean_object* v_fst_1964_; lean_object* v_snd_1965_; uint8_t v___y_1967_; uint8_t v___x_1975_; 
lean_dec(v___x_1952_);
lean_inc(v_offset_1945_);
lean_inc_ref(v_fn_1949_);
v___x_1956_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault(v_subst_1943_, v_fn_1949_, v_offset_1945_, v_a_1946_, v_a_1947_, v_a_1948_);
v_fst_1957_ = lean_ctor_get(v___x_1956_, 0);
lean_inc(v_fst_1957_);
v_snd_1958_ = lean_ctor_get(v___x_1956_, 1);
lean_inc(v_snd_1958_);
lean_dec_ref(v___x_1956_);
v_fst_1959_ = lean_ctor_get(v_fst_1957_, 0);
lean_inc(v_fst_1959_);
v_snd_1960_ = lean_ctor_get(v_fst_1957_, 1);
lean_inc(v_snd_1960_);
lean_dec(v_fst_1957_);
lean_inc_ref(v_arg_1950_);
v___x_1961_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1943_, v_arg_1950_, v_offset_1945_, v_snd_1960_, v_a_1947_, v_snd_1958_);
v_fst_1962_ = lean_ctor_get(v___x_1961_, 0);
lean_inc(v_fst_1962_);
v_snd_1963_ = lean_ctor_get(v___x_1961_, 1);
lean_inc(v_snd_1963_);
lean_dec_ref(v___x_1961_);
v_fst_1964_ = lean_ctor_get(v_fst_1962_, 0);
lean_inc(v_fst_1964_);
v_snd_1965_ = lean_ctor_get(v_fst_1962_, 1);
lean_inc(v_snd_1965_);
lean_dec(v_fst_1962_);
v___x_1975_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_1949_, v_fst_1959_);
if (v___x_1975_ == 0)
{
v___y_1967_ = v___x_1975_;
goto v___jp_1966_;
}
else
{
uint8_t v___x_1976_; 
v___x_1976_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_1950_, v_fst_1964_);
v___y_1967_ = v___x_1976_;
goto v___jp_1966_;
}
v___jp_1966_:
{
if (v___y_1967_ == 0)
{
lean_object* v___x_1968_; lean_object* v_fst_1969_; lean_object* v_snd_1970_; lean_object* v_fst_1971_; lean_object* v_snd_1972_; lean_object* v___x_1973_; 
lean_dec_ref(v_e_1944_);
v___x_1968_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__3(v_fst_1959_, v_fst_1964_, v_snd_1965_, v_a_1947_, v_snd_1963_);
v_fst_1969_ = lean_ctor_get(v___x_1968_, 0);
lean_inc(v_fst_1969_);
v_snd_1970_ = lean_ctor_get(v___x_1968_, 1);
lean_inc(v_snd_1970_);
lean_dec_ref(v___x_1968_);
v_fst_1971_ = lean_ctor_get(v_fst_1969_, 0);
lean_inc(v_fst_1971_);
v_snd_1972_ = lean_ctor_get(v_fst_1969_, 1);
lean_inc(v_snd_1972_);
lean_dec(v_fst_1969_);
v___x_1973_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_1951_, v_fst_1971_, v_snd_1972_, v_snd_1970_);
return v___x_1973_;
}
else
{
lean_object* v___x_1974_; 
lean_dec(v_fst_1964_);
lean_dec(v_fst_1959_);
v___x_1974_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_1951_, v_e_1944_, v_snd_1965_, v_snd_1963_);
return v___x_1974_;
}
}
}
}
else
{
lean_object* v___x_1977_; 
v___x_1977_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1943_, v_e_1944_, v_offset_1945_, v_a_1946_, v_a_1947_, v_a_1948_);
return v___x_1977_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault___boxed(lean_object* v_subst_1978_, lean_object* v_e_1979_, lean_object* v_offset_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_){
_start:
{
uint8_t v_a_boxed_1984_; lean_object* v_res_1985_; 
v_a_boxed_1984_ = lean_unbox(v_a_1982_);
v_res_1985_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault(v_subst_1978_, v_e_1979_, v_offset_1980_, v_a_1981_, v_a_boxed_1984_, v_a_1983_);
lean_dec_ref(v_subst_1978_);
return v_res_1985_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild___boxed(lean_object* v_subst_1986_, lean_object* v_e_1987_, lean_object* v_offset_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_){
_start:
{
uint8_t v_a_boxed_1992_; lean_object* v_res_1993_; 
v_a_boxed_1992_ = lean_unbox(v_a_1990_);
v_res_1993_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1986_, v_e_1987_, v_offset_1988_, v_a_1989_, v_a_boxed_1992_, v_a_1991_);
lean_dec_ref(v_subst_1986_);
return v_res_1993_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___boxed(lean_object* v_subst_1994_, lean_object* v_e_1995_, lean_object* v_f_1996_, lean_object* v_arg_1997_, lean_object* v_offset_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_){
_start:
{
uint8_t v_a_boxed_2002_; lean_object* v_res_2003_; 
v_a_boxed_2002_ = lean_unbox(v_a_2000_);
v_res_2003_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg(v_subst_1994_, v_e_1995_, v_f_1996_, v_arg_1997_, v_offset_1998_, v_a_1999_, v_a_boxed_2002_, v_a_2001_);
lean_dec_ref(v_subst_1994_);
return v_res_2003_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___boxed(lean_object* v_subst_2004_, lean_object* v_e_2005_, lean_object* v_f_2006_, lean_object* v_argsRev_2007_, lean_object* v_offset_2008_, lean_object* v_modified_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_){
_start:
{
uint8_t v_modified_boxed_2013_; uint8_t v_a_boxed_2014_; lean_object* v_res_2015_; 
v_modified_boxed_2013_ = lean_unbox(v_modified_2009_);
v_a_boxed_2014_ = lean_unbox(v_a_2011_);
v_res_2015_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta(v_subst_2004_, v_e_2005_, v_f_2006_, v_argsRev_2007_, v_offset_2008_, v_modified_boxed_2013_, v_a_2010_, v_a_boxed_2014_, v_a_2012_);
lean_dec_ref(v_subst_2004_);
return v_res_2015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___boxed(lean_object* v_subst_2016_, lean_object* v_e_2017_, lean_object* v_offset_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_){
_start:
{
uint8_t v_a_boxed_2022_; lean_object* v_res_2023_; 
v_a_boxed_2022_ = lean_unbox(v_a_2020_);
v_res_2023_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit(v_subst_2016_, v_e_2017_, v_offset_2018_, v_a_2019_, v_a_boxed_2022_, v_a_2021_);
lean_dec_ref(v_subst_2016_);
return v_res_2023_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp(lean_object* v_subst_2024_, lean_object* v_e_2025_, lean_object* v_f_2026_, lean_object* v_arg_2027_, lean_object* v_offset_2028_, lean_object* v_x_2029_, lean_object* v_a_2030_, uint8_t v_a_2031_, lean_object* v_a_2032_){
_start:
{
lean_object* v___x_2033_; 
v___x_2033_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg(v_subst_2024_, v_e_2025_, v_f_2026_, v_arg_2027_, v_offset_2028_, v_a_2030_, v_a_2031_, v_a_2032_);
return v___x_2033_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___boxed(lean_object* v_subst_2034_, lean_object* v_e_2035_, lean_object* v_f_2036_, lean_object* v_arg_2037_, lean_object* v_offset_2038_, lean_object* v_x_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_){
_start:
{
uint8_t v_a_boxed_2043_; lean_object* v_res_2044_; 
v_a_boxed_2043_ = lean_unbox(v_a_2041_);
v_res_2044_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp(v_subst_2034_, v_e_2035_, v_f_2036_, v_arg_2037_, v_offset_2038_, v_x_2039_, v_a_2040_, v_a_boxed_2043_, v_a_2042_);
lean_dec_ref(v_subst_2034_);
return v_res_2044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27(lean_object* v_e_2045_, lean_object* v_subst_2046_, uint8_t v_a_2047_, lean_object* v_a_2048_){
_start:
{
uint8_t v___y_2050_; lean_object* v___x_2066_; lean_object* v___x_2067_; uint8_t v___x_2068_; 
v___x_2066_ = lean_array_get_size(v_subst_2046_);
v___x_2067_ = lean_unsigned_to_nat(0u);
v___x_2068_ = lean_nat_dec_eq(v___x_2066_, v___x_2067_);
if (v___x_2068_ == 0)
{
uint8_t v___x_2069_; 
v___x_2069_ = l_Lean_Expr_hasLooseBVars(v_e_2045_);
if (v___x_2069_ == 0)
{
lean_object* v___x_2070_; 
v___x_2070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2070_, 0, v_e_2045_);
lean_ctor_set(v___x_2070_, 1, v_a_2048_);
return v___x_2070_;
}
else
{
v___y_2050_ = v___x_2068_;
goto v___jp_2049_;
}
}
else
{
v___y_2050_ = v___x_2068_;
goto v___jp_2049_;
}
v___jp_2049_:
{
if (v___y_2050_ == 0)
{
lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v_fst_2054_; lean_object* v_snd_2055_; lean_object* v_fst_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2063_; 
v___x_2051_ = lean_unsigned_to_nat(0u);
v___x_2052_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__2, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__2_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__2);
v___x_2053_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit(v_subst_2046_, v_e_2045_, v___x_2051_, v___x_2052_, v_a_2047_, v_a_2048_);
v_fst_2054_ = lean_ctor_get(v___x_2053_, 0);
lean_inc(v_fst_2054_);
v_snd_2055_ = lean_ctor_get(v___x_2053_, 1);
lean_inc(v_snd_2055_);
lean_dec_ref(v___x_2053_);
v_fst_2056_ = lean_ctor_get(v_fst_2054_, 0);
v_isSharedCheck_2063_ = !lean_is_exclusive(v_fst_2054_);
if (v_isSharedCheck_2063_ == 0)
{
lean_object* v_unused_2064_; 
v_unused_2064_ = lean_ctor_get(v_fst_2054_, 1);
lean_dec(v_unused_2064_);
v___x_2058_ = v_fst_2054_;
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_fst_2056_);
lean_dec(v_fst_2054_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2061_; 
if (v_isShared_2059_ == 0)
{
lean_ctor_set(v___x_2058_, 1, v_snd_2055_);
v___x_2061_ = v___x_2058_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_fst_2056_);
lean_ctor_set(v_reuseFailAlloc_2062_, 1, v_snd_2055_);
v___x_2061_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
return v___x_2061_;
}
}
}
else
{
lean_object* v___x_2065_; 
v___x_2065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2065_, 0, v_e_2045_);
lean_ctor_set(v___x_2065_, 1, v_a_2048_);
return v___x_2065_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27___boxed(lean_object* v_e_2071_, lean_object* v_subst_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_){
_start:
{
uint8_t v_a_boxed_2075_; lean_object* v_res_2076_; 
v_a_boxed_2075_ = lean_unbox(v_a_2073_);
v_res_2076_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27(v_e_2071_, v_subst_2072_, v_a_boxed_2075_, v_a_2074_);
lean_dec_ref(v_subst_2072_);
return v_res_2076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevBetaS___redArg(lean_object* v_e_2077_, lean_object* v_subst_2078_, lean_object* v_a_2079_){
_start:
{
uint8_t v___x_2081_; 
v___x_2081_ = l_Lean_Expr_hasLooseBVars(v_e_2077_);
if (v___x_2081_ == 0)
{
lean_object* v___x_2082_; 
v___x_2082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2082_, 0, v_e_2077_);
return v___x_2082_;
}
else
{
lean_object* v___x_2083_; lean_object* v___x_2084_; uint8_t v___x_2085_; 
v___x_2083_ = lean_array_get_size(v_subst_2078_);
v___x_2084_ = lean_unsigned_to_nat(0u);
v___x_2085_ = lean_nat_dec_eq(v___x_2083_, v___x_2084_);
if (v___x_2085_ == 0)
{
lean_object* v___x_2086_; lean_object* v_share_2087_; lean_object* v_maxFVar_2088_; lean_object* v_proofInstInfo_2089_; lean_object* v_inferType_2090_; lean_object* v_getLevel_2091_; lean_object* v_congrInfo_2092_; lean_object* v_defEqI_2093_; lean_object* v_extensions_2094_; uint8_t v_debug_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2128_; 
v___x_2086_ = lean_st_ref_take(v_a_2079_);
v_share_2087_ = lean_ctor_get(v___x_2086_, 0);
v_maxFVar_2088_ = lean_ctor_get(v___x_2086_, 1);
v_proofInstInfo_2089_ = lean_ctor_get(v___x_2086_, 2);
v_inferType_2090_ = lean_ctor_get(v___x_2086_, 3);
v_getLevel_2091_ = lean_ctor_get(v___x_2086_, 4);
v_congrInfo_2092_ = lean_ctor_get(v___x_2086_, 5);
v_defEqI_2093_ = lean_ctor_get(v___x_2086_, 6);
v_extensions_2094_ = lean_ctor_get(v___x_2086_, 7);
v_debug_2095_ = lean_ctor_get_uint8(v___x_2086_, sizeof(void*)*8);
v_isSharedCheck_2128_ = !lean_is_exclusive(v___x_2086_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2097_ = v___x_2086_;
v_isShared_2098_ = v_isSharedCheck_2128_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_extensions_2094_);
lean_inc(v_defEqI_2093_);
lean_inc(v_congrInfo_2092_);
lean_inc(v_getLevel_2091_);
lean_inc(v_inferType_2090_);
lean_inc(v_proofInstInfo_2089_);
lean_inc(v_maxFVar_2088_);
lean_inc(v_share_2087_);
lean_dec(v___x_2086_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2128_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2099_; lean_object* v___x_2101_; 
v___x_2099_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__0, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__0_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__0);
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 0, v___x_2099_);
v___x_2101_ = v___x_2097_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v___x_2099_);
lean_ctor_set(v_reuseFailAlloc_2127_, 1, v_maxFVar_2088_);
lean_ctor_set(v_reuseFailAlloc_2127_, 2, v_proofInstInfo_2089_);
lean_ctor_set(v_reuseFailAlloc_2127_, 3, v_inferType_2090_);
lean_ctor_set(v_reuseFailAlloc_2127_, 4, v_getLevel_2091_);
lean_ctor_set(v_reuseFailAlloc_2127_, 5, v_congrInfo_2092_);
lean_ctor_set(v_reuseFailAlloc_2127_, 6, v_defEqI_2093_);
lean_ctor_set(v_reuseFailAlloc_2127_, 7, v_extensions_2094_);
lean_ctor_set_uint8(v_reuseFailAlloc_2127_, sizeof(void*)*8, v_debug_2095_);
v___x_2101_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; uint8_t v_debug_2104_; lean_object* v___x_2105_; lean_object* v_fst_2106_; lean_object* v_snd_2107_; lean_object* v___x_2108_; lean_object* v_maxFVar_2109_; lean_object* v_proofInstInfo_2110_; lean_object* v_inferType_2111_; lean_object* v_getLevel_2112_; lean_object* v_congrInfo_2113_; lean_object* v_defEqI_2114_; lean_object* v_extensions_2115_; uint8_t v_debug_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2125_; 
v___x_2102_ = lean_st_ref_set(v_a_2079_, v___x_2101_);
v___x_2103_ = lean_st_ref_get(v_a_2079_);
v_debug_2104_ = lean_ctor_get_uint8(v___x_2103_, sizeof(void*)*8);
lean_dec(v___x_2103_);
v___x_2105_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27(v_e_2077_, v_subst_2078_, v_debug_2104_, v_share_2087_);
v_fst_2106_ = lean_ctor_get(v___x_2105_, 0);
lean_inc(v_fst_2106_);
v_snd_2107_ = lean_ctor_get(v___x_2105_, 1);
lean_inc(v_snd_2107_);
lean_dec_ref(v___x_2105_);
v___x_2108_ = lean_st_ref_take(v_a_2079_);
v_maxFVar_2109_ = lean_ctor_get(v___x_2108_, 1);
v_proofInstInfo_2110_ = lean_ctor_get(v___x_2108_, 2);
v_inferType_2111_ = lean_ctor_get(v___x_2108_, 3);
v_getLevel_2112_ = lean_ctor_get(v___x_2108_, 4);
v_congrInfo_2113_ = lean_ctor_get(v___x_2108_, 5);
v_defEqI_2114_ = lean_ctor_get(v___x_2108_, 6);
v_extensions_2115_ = lean_ctor_get(v___x_2108_, 7);
v_debug_2116_ = lean_ctor_get_uint8(v___x_2108_, sizeof(void*)*8);
v_isSharedCheck_2125_ = !lean_is_exclusive(v___x_2108_);
if (v_isSharedCheck_2125_ == 0)
{
lean_object* v_unused_2126_; 
v_unused_2126_ = lean_ctor_get(v___x_2108_, 0);
lean_dec(v_unused_2126_);
v___x_2118_ = v___x_2108_;
v_isShared_2119_ = v_isSharedCheck_2125_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_extensions_2115_);
lean_inc(v_defEqI_2114_);
lean_inc(v_congrInfo_2113_);
lean_inc(v_getLevel_2112_);
lean_inc(v_inferType_2111_);
lean_inc(v_proofInstInfo_2110_);
lean_inc(v_maxFVar_2109_);
lean_dec(v___x_2108_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2125_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v___x_2121_; 
if (v_isShared_2119_ == 0)
{
lean_ctor_set(v___x_2118_, 0, v_snd_2107_);
v___x_2121_ = v___x_2118_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v_snd_2107_);
lean_ctor_set(v_reuseFailAlloc_2124_, 1, v_maxFVar_2109_);
lean_ctor_set(v_reuseFailAlloc_2124_, 2, v_proofInstInfo_2110_);
lean_ctor_set(v_reuseFailAlloc_2124_, 3, v_inferType_2111_);
lean_ctor_set(v_reuseFailAlloc_2124_, 4, v_getLevel_2112_);
lean_ctor_set(v_reuseFailAlloc_2124_, 5, v_congrInfo_2113_);
lean_ctor_set(v_reuseFailAlloc_2124_, 6, v_defEqI_2114_);
lean_ctor_set(v_reuseFailAlloc_2124_, 7, v_extensions_2115_);
lean_ctor_set_uint8(v_reuseFailAlloc_2124_, sizeof(void*)*8, v_debug_2116_);
v___x_2121_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
lean_object* v___x_2122_; lean_object* v___x_2123_; 
v___x_2122_ = lean_st_ref_set(v_a_2079_, v___x_2121_);
v___x_2123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2123_, 0, v_fst_2106_);
return v___x_2123_;
}
}
}
}
}
else
{
lean_object* v___x_2129_; 
v___x_2129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2129_, 0, v_e_2077_);
return v___x_2129_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevBetaS___redArg___boxed(lean_object* v_e_2130_, lean_object* v_subst_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_){
_start:
{
lean_object* v_res_2134_; 
v_res_2134_ = l_Lean_Meta_Sym_instantiateRevBetaS___redArg(v_e_2130_, v_subst_2131_, v_a_2132_);
lean_dec(v_a_2132_);
lean_dec_ref(v_subst_2131_);
return v_res_2134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevBetaS(lean_object* v_e_2135_, lean_object* v_subst_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_){
_start:
{
lean_object* v___x_2144_; 
v___x_2144_ = l_Lean_Meta_Sym_instantiateRevBetaS___redArg(v_e_2135_, v_subst_2136_, v_a_2138_);
return v___x_2144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevBetaS___boxed(lean_object* v_e_2145_, lean_object* v_subst_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_){
_start:
{
lean_object* v_res_2154_; 
v_res_2154_ = l_Lean_Meta_Sym_instantiateRevBetaS(v_e_2145_, v_subst_2146_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_);
lean_dec(v_a_2152_);
lean_dec_ref(v_a_2151_);
lean_dec(v_a_2150_);
lean_dec_ref(v_a_2149_);
lean_dec(v_a_2148_);
lean_dec_ref(v_a_2147_);
lean_dec_ref(v_subst_2146_);
return v_res_2154_;
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
