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
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
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
uint8_t v___y_22951__boxed_17_; lean_object* v_res_18_; 
v___y_22951__boxed_17_ = lean_unbox(v___y_15_);
v_res_18_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1(v_idx_14_, v___y_22951__boxed_17_, v___y_16_);
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
lean_object* v___x_28_; lean_object* v___x_3191__overap_29_; lean_object* v___x_30_; 
v___x_28_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__0, &l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__0);
v___x_3191__overap_29_ = lean_panic_fn_borrowed(v___x_28_, v_msg_20_);
lean_inc(v___y_26_);
lean_inc_ref(v___y_25_);
lean_inc(v___y_24_);
lean_inc_ref(v___y_23_);
lean_inc(v___y_22_);
lean_inc_ref(v___y_21_);
v___x_30_ = lean_apply_7(v___x_3191__overap_29_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_, lean_box(0));
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
uint8_t v_bi_boxed_73_; uint8_t v___y_22988__boxed_74_; lean_object* v_res_75_; 
v_bi_boxed_73_ = lean_unbox(v_bi_67_);
v___y_22988__boxed_74_ = lean_unbox(v___y_71_);
v_res_75_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__5(v_x_66_, v_bi_boxed_73_, v_t_68_, v_b_69_, v___y_70_, v___y_22988__boxed_74_, v___y_72_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9(lean_object* v_msg_83_, lean_object* v___y_84_, uint8_t v___y_85_, lean_object* v___y_86_){
_start:
{
lean_object* v___f_87_; lean_object* v___f_88_; lean_object* v___f_89_; lean_object* v___f_90_; lean_object* v___f_91_; lean_object* v___f_92_; lean_object* v___f_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___f_97_; lean_object* v___f_98_; lean_object* v___f_99_; lean_object* v___f_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___f_108_; lean_object* v___f_109_; lean_object* v___f_110_; lean_object* v___f_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_22617__overap_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
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
lean_inc_ref_n(v___x_96_, 6);
v___f_97_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_97_, 0, v___x_96_);
v___f_98_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_98_, 0, v___x_96_);
v___f_99_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_99_, 0, v___x_96_);
v___f_100_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_100_, 0, v___x_96_);
v___x_101_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_101_, 0, lean_box(0));
lean_closure_set(v___x_101_, 1, lean_box(0));
lean_closure_set(v___x_101_, 2, v___x_96_);
v___x_102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
lean_ctor_set(v___x_102_, 1, v___f_97_);
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
lean_inc_ref_n(v___x_107_, 6);
v___f_108_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_108_, 0, v___x_107_);
v___f_109_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_109_, 0, v___x_107_);
v___f_110_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_110_, 0, v___x_107_);
v___f_111_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_111_, 0, v___x_107_);
v___x_112_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_112_, 0, lean_box(0));
lean_closure_set(v___x_112_, 1, lean_box(0));
lean_closure_set(v___x_112_, 2, v___x_107_);
v___x_113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_113_, 0, v___x_112_);
lean_ctor_set(v___x_113_, 1, v___f_108_);
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
v___x_22617__overap_120_ = lean_panic_fn_borrowed(v___x_119_, v_msg_83_);
lean_dec(v___x_119_);
v___x_121_ = lean_box(v___y_85_);
v___x_122_ = lean_apply_3(v___x_22617__overap_120_, v___y_84_, v___x_121_, v___y_86_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___boxed(lean_object* v_msg_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_){
_start:
{
uint8_t v___y_23051__boxed_127_; lean_object* v_res_128_; 
v___y_23051__boxed_127_ = lean_unbox(v___y_125_);
v_res_128_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9(v_msg_123_, v___y_124_, v___y_23051__boxed_127_, v___y_126_);
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
uint8_t v___y_23137__boxed_158_; lean_object* v_res_159_; 
v___y_23137__boxed_158_ = lean_unbox(v___y_156_);
v_res_159_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__8(v_structName_152_, v_idx_153_, v_struct_154_, v___y_155_, v___y_23137__boxed_158_, v___y_157_);
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
uint8_t v_bi_boxed_193_; uint8_t v___y_23181__boxed_194_; lean_object* v_res_195_; 
v_bi_boxed_193_ = lean_unbox(v_bi_187_);
v___y_23181__boxed_194_ = lean_unbox(v___y_191_);
v_res_195_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__4(v_x_186_, v_bi_boxed_193_, v_t_188_, v_b_189_, v___y_190_, v___y_23181__boxed_194_, v___y_192_);
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
uint8_t v___y_23230__boxed_223_; lean_object* v_res_224_; 
v___y_23230__boxed_223_ = lean_unbox(v___y_221_);
v_res_224_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__7(v_d_218_, v_e_219_, v___y_220_, v___y_23230__boxed_223_, v___y_222_);
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
uint8_t v___y_23343__boxed_298_; lean_object* v_res_299_; 
v___y_23343__boxed_298_ = lean_unbox(v___y_296_);
v_res_299_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__3(v_f_293_, v_a_294_, v___y_295_, v___y_23343__boxed_298_, v___y_297_);
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
uint8_t v_nondep_boxed_337_; uint8_t v___y_23392__boxed_338_; lean_object* v_res_339_; 
v_nondep_boxed_337_ = lean_unbox(v_nondep_333_);
v___y_23392__boxed_338_ = lean_unbox(v___y_335_);
v_res_339_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6(v_x_329_, v_t_330_, v_v_331_, v_b_332_, v_nondep_boxed_337_, v___y_334_, v___y_23392__boxed_338_, v___y_336_);
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
lean_inc_n(v_offset_353_, 2);
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
lean_object* v___x_659_; lean_object* v_share_660_; lean_object* v_maxFVar_661_; lean_object* v_proofInstInfo_662_; lean_object* v_inferType_663_; lean_object* v_getLevel_664_; lean_object* v_congrInfo_665_; lean_object* v_defEqI_666_; lean_object* v_extensions_667_; lean_object* v_issues_668_; lean_object* v_canon_669_; uint8_t v_debug_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_728_; 
v___x_659_ = lean_st_ref_take(v_a_650_);
v_share_660_ = lean_ctor_get(v___x_659_, 0);
v_maxFVar_661_ = lean_ctor_get(v___x_659_, 1);
v_proofInstInfo_662_ = lean_ctor_get(v___x_659_, 2);
v_inferType_663_ = lean_ctor_get(v___x_659_, 3);
v_getLevel_664_ = lean_ctor_get(v___x_659_, 4);
v_congrInfo_665_ = lean_ctor_get(v___x_659_, 5);
v_defEqI_666_ = lean_ctor_get(v___x_659_, 6);
v_extensions_667_ = lean_ctor_get(v___x_659_, 7);
v_issues_668_ = lean_ctor_get(v___x_659_, 8);
v_canon_669_ = lean_ctor_get(v___x_659_, 9);
v_debug_670_ = lean_ctor_get_uint8(v___x_659_, sizeof(void*)*10);
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_728_ == 0)
{
v___x_672_ = v___x_659_;
v_isShared_673_ = v_isSharedCheck_728_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_canon_669_);
lean_inc(v_issues_668_);
lean_inc(v_extensions_667_);
lean_inc(v_defEqI_666_);
lean_inc(v_congrInfo_665_);
lean_inc(v_getLevel_664_);
lean_inc(v_inferType_663_);
lean_inc(v_proofInstInfo_662_);
lean_inc(v_maxFVar_661_);
lean_inc(v_share_660_);
lean_dec(v___x_659_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_728_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_674_; lean_object* v___x_676_; 
v___x_674_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__0, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__0_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__0);
if (v_isShared_673_ == 0)
{
lean_ctor_set(v___x_672_, 0, v___x_674_);
v___x_676_ = v___x_672_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v___x_674_);
lean_ctor_set(v_reuseFailAlloc_727_, 1, v_maxFVar_661_);
lean_ctor_set(v_reuseFailAlloc_727_, 2, v_proofInstInfo_662_);
lean_ctor_set(v_reuseFailAlloc_727_, 3, v_inferType_663_);
lean_ctor_set(v_reuseFailAlloc_727_, 4, v_getLevel_664_);
lean_ctor_set(v_reuseFailAlloc_727_, 5, v_congrInfo_665_);
lean_ctor_set(v_reuseFailAlloc_727_, 6, v_defEqI_666_);
lean_ctor_set(v_reuseFailAlloc_727_, 7, v_extensions_667_);
lean_ctor_set(v_reuseFailAlloc_727_, 8, v_issues_668_);
lean_ctor_set(v_reuseFailAlloc_727_, 9, v_canon_669_);
lean_ctor_set_uint8(v_reuseFailAlloc_727_, sizeof(void*)*10, v_debug_670_);
v___x_676_ = v_reuseFailAlloc_727_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v_fst_680_; lean_object* v_snd_681_; uint8_t v_debug_703_; lean_object* v_n_704_; lean_object* v___x_705_; 
v___x_677_ = lean_st_ref_set(v_a_650_, v___x_676_);
v___x_678_ = lean_st_ref_get(v_a_650_);
v_debug_703_ = lean_ctor_get_uint8(v___x_678_, sizeof(void*)*10);
lean_dec(v___x_678_);
v_n_704_ = lean_nat_sub(v_endIdx_647_, v_beginIdx_646_);
v___x_705_ = lean_unsigned_to_nat(0u);
switch(lean_obj_tag(v_e_645_))
{
case 0:
{
lean_object* v_deBruijnIndex_706_; uint8_t v___x_707_; 
v_deBruijnIndex_706_ = lean_ctor_get(v_e_645_, 0);
v___x_707_ = lean_nat_dec_le(v_beginIdx_646_, v_deBruijnIndex_706_);
if (v___x_707_ == 0)
{
lean_dec(v_n_704_);
v_fst_680_ = v_e_645_;
v_snd_681_ = v_share_660_;
goto v___jp_679_;
}
else
{
uint8_t v___x_708_; 
lean_inc(v_deBruijnIndex_706_);
lean_dec_ref(v_e_645_);
v___x_708_ = lean_nat_dec_lt(v_deBruijnIndex_706_, v_n_704_);
if (v___x_708_ == 0)
{
lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v_fst_711_; lean_object* v_snd_712_; 
v___x_709_ = lean_nat_sub(v_deBruijnIndex_706_, v_n_704_);
lean_dec(v_n_704_);
lean_dec(v_deBruijnIndex_706_);
v___x_710_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___redArg(v___x_709_, v_share_660_);
v_fst_711_ = lean_ctor_get(v___x_710_, 0);
lean_inc(v_fst_711_);
v_snd_712_ = lean_ctor_get(v___x_710_, 1);
lean_inc(v_snd_712_);
lean_dec_ref(v___x_710_);
v_fst_680_ = v_fst_711_;
v_snd_681_ = v_snd_712_;
goto v___jp_679_;
}
else
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v_v_716_; lean_object* v___x_717_; lean_object* v_fst_718_; lean_object* v_snd_719_; 
v___x_713_ = lean_nat_sub(v_n_704_, v_deBruijnIndex_706_);
lean_dec(v_deBruijnIndex_706_);
lean_dec(v_n_704_);
v___x_714_ = lean_unsigned_to_nat(1u);
v___x_715_ = lean_nat_sub(v___x_713_, v___x_714_);
lean_dec(v___x_713_);
v_v_716_ = lean_array_fget_borrowed(v_subst_648_, v___x_715_);
lean_dec(v___x_715_);
lean_inc(v_v_716_);
v___x_717_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(v_v_716_, v___x_705_, v___x_705_, v_debug_703_, v_share_660_);
v_fst_718_ = lean_ctor_get(v___x_717_, 0);
lean_inc(v_fst_718_);
v_snd_719_ = lean_ctor_get(v___x_717_, 1);
lean_inc(v_snd_719_);
lean_dec_ref(v___x_717_);
v_fst_680_ = v_fst_718_;
v_snd_681_ = v_snd_719_;
goto v___jp_679_;
}
}
}
case 9:
{
lean_dec(v_n_704_);
v_fst_680_ = v_e_645_;
v_snd_681_ = v_share_660_;
goto v___jp_679_;
}
case 2:
{
lean_dec(v_n_704_);
v_fst_680_ = v_e_645_;
v_snd_681_ = v_share_660_;
goto v___jp_679_;
}
case 1:
{
lean_dec(v_n_704_);
v_fst_680_ = v_e_645_;
v_snd_681_ = v_share_660_;
goto v___jp_679_;
}
case 4:
{
lean_dec(v_n_704_);
v_fst_680_ = v_e_645_;
v_snd_681_ = v_share_660_;
goto v___jp_679_;
}
case 3:
{
lean_dec(v_n_704_);
v_fst_680_ = v_e_645_;
v_snd_681_ = v_share_660_;
goto v___jp_679_;
}
default: 
{
lean_object* v___x_720_; uint8_t v___x_721_; 
v___x_720_ = l_Lean_Expr_looseBVarRange(v_e_645_);
v___x_721_ = lean_nat_dec_le(v___x_720_, v_beginIdx_646_);
lean_dec(v___x_720_);
if (v___x_721_ == 0)
{
switch(lean_obj_tag(v_e_645_))
{
case 9:
{
lean_dec(v_n_704_);
v_fst_680_ = v_e_645_;
v_snd_681_ = v_share_660_;
goto v___jp_679_;
}
case 2:
{
lean_dec(v_n_704_);
v_fst_680_ = v_e_645_;
v_snd_681_ = v_share_660_;
goto v___jp_679_;
}
case 0:
{
lean_dec(v_n_704_);
v_fst_680_ = v_e_645_;
v_snd_681_ = v_share_660_;
goto v___jp_679_;
}
case 1:
{
lean_dec(v_n_704_);
v_fst_680_ = v_e_645_;
v_snd_681_ = v_share_660_;
goto v___jp_679_;
}
case 4:
{
lean_dec(v_n_704_);
v_fst_680_ = v_e_645_;
v_snd_681_ = v_share_660_;
goto v___jp_679_;
}
case 3:
{
lean_dec(v_n_704_);
v_fst_680_ = v_e_645_;
v_snd_681_ = v_share_660_;
goto v___jp_679_;
}
default: 
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v_fst_724_; lean_object* v_snd_725_; lean_object* v_fst_726_; 
v___x_722_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__2, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__2_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__2);
v___x_723_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(v_beginIdx_646_, v_n_704_, v_subst_648_, v_e_645_, v___x_705_, v___x_722_, v_debug_703_, v_share_660_);
lean_dec(v_n_704_);
v_fst_724_ = lean_ctor_get(v___x_723_, 0);
lean_inc(v_fst_724_);
v_snd_725_ = lean_ctor_get(v___x_723_, 1);
lean_inc(v_snd_725_);
lean_dec_ref(v___x_723_);
v_fst_726_ = lean_ctor_get(v_fst_724_, 0);
lean_inc(v_fst_726_);
lean_dec(v_fst_724_);
v_fst_680_ = v_fst_726_;
v_snd_681_ = v_snd_725_;
goto v___jp_679_;
}
}
}
else
{
lean_dec(v_n_704_);
v_fst_680_ = v_e_645_;
v_snd_681_ = v_share_660_;
goto v___jp_679_;
}
}
}
v___jp_679_:
{
lean_object* v___x_682_; lean_object* v_maxFVar_683_; lean_object* v_proofInstInfo_684_; lean_object* v_inferType_685_; lean_object* v_getLevel_686_; lean_object* v_congrInfo_687_; lean_object* v_defEqI_688_; lean_object* v_extensions_689_; lean_object* v_issues_690_; lean_object* v_canon_691_; uint8_t v_debug_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_701_; 
v___x_682_ = lean_st_ref_take(v_a_650_);
v_maxFVar_683_ = lean_ctor_get(v___x_682_, 1);
v_proofInstInfo_684_ = lean_ctor_get(v___x_682_, 2);
v_inferType_685_ = lean_ctor_get(v___x_682_, 3);
v_getLevel_686_ = lean_ctor_get(v___x_682_, 4);
v_congrInfo_687_ = lean_ctor_get(v___x_682_, 5);
v_defEqI_688_ = lean_ctor_get(v___x_682_, 6);
v_extensions_689_ = lean_ctor_get(v___x_682_, 7);
v_issues_690_ = lean_ctor_get(v___x_682_, 8);
v_canon_691_ = lean_ctor_get(v___x_682_, 9);
v_debug_692_ = lean_ctor_get_uint8(v___x_682_, sizeof(void*)*10);
v_isSharedCheck_701_ = !lean_is_exclusive(v___x_682_);
if (v_isSharedCheck_701_ == 0)
{
lean_object* v_unused_702_; 
v_unused_702_ = lean_ctor_get(v___x_682_, 0);
lean_dec(v_unused_702_);
v___x_694_ = v___x_682_;
v_isShared_695_ = v_isSharedCheck_701_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_canon_691_);
lean_inc(v_issues_690_);
lean_inc(v_extensions_689_);
lean_inc(v_defEqI_688_);
lean_inc(v_congrInfo_687_);
lean_inc(v_getLevel_686_);
lean_inc(v_inferType_685_);
lean_inc(v_proofInstInfo_684_);
lean_inc(v_maxFVar_683_);
lean_dec(v___x_682_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_701_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_697_; 
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 0, v_snd_681_);
v___x_697_ = v___x_694_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_snd_681_);
lean_ctor_set(v_reuseFailAlloc_700_, 1, v_maxFVar_683_);
lean_ctor_set(v_reuseFailAlloc_700_, 2, v_proofInstInfo_684_);
lean_ctor_set(v_reuseFailAlloc_700_, 3, v_inferType_685_);
lean_ctor_set(v_reuseFailAlloc_700_, 4, v_getLevel_686_);
lean_ctor_set(v_reuseFailAlloc_700_, 5, v_congrInfo_687_);
lean_ctor_set(v_reuseFailAlloc_700_, 6, v_defEqI_688_);
lean_ctor_set(v_reuseFailAlloc_700_, 7, v_extensions_689_);
lean_ctor_set(v_reuseFailAlloc_700_, 8, v_issues_690_);
lean_ctor_set(v_reuseFailAlloc_700_, 9, v_canon_691_);
lean_ctor_set_uint8(v_reuseFailAlloc_700_, sizeof(void*)*10, v_debug_692_);
v___x_697_ = v_reuseFailAlloc_700_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_698_ = lean_st_ref_set(v_a_650_, v___x_697_);
v___x_699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_699_, 0, v_fst_680_);
return v___x_699_;
}
}
}
}
}
}
else
{
lean_object* v___x_729_; lean_object* v___x_730_; 
lean_dec_ref(v_e_645_);
v___x_729_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__5, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__5_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__5);
v___x_730_ = l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3(v___x_729_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_);
return v___x_730_;
}
}
else
{
lean_object* v___x_731_; lean_object* v___x_732_; 
lean_dec_ref(v_e_645_);
v___x_731_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__6, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__6_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__6);
v___x_732_ = l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3(v___x_731_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_);
return v___x_732_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevRangeS___boxed(lean_object* v_e_733_, lean_object* v_beginIdx_734_, lean_object* v_endIdx_735_, lean_object* v_subst_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_e_733_, v_beginIdx_734_, v_endIdx_735_, v_subst_736_, v_a_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_, v_a_742_);
lean_dec(v_a_742_);
lean_dec_ref(v_a_741_);
lean_dec(v_a_740_);
lean_dec_ref(v_a_739_);
lean_dec(v_a_738_);
lean_dec_ref(v_a_737_);
lean_dec_ref(v_subst_736_);
lean_dec(v_endIdx_735_);
lean_dec(v_beginIdx_734_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4(lean_object* v_00_u03b2_745_, lean_object* v_m_746_, lean_object* v_a_747_){
_start:
{
lean_object* v___x_748_; 
v___x_748_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___redArg(v_m_746_, v_a_747_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___boxed(lean_object* v_00_u03b2_749_, lean_object* v_m_750_, lean_object* v_a_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4(v_00_u03b2_749_, v_m_750_, v_a_751_);
lean_dec_ref(v_a_751_);
lean_dec_ref(v_m_750_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4_spec__12(lean_object* v_00_u03b2_753_, lean_object* v_a_754_, lean_object* v_x_755_){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4_spec__12___redArg(v_a_754_, v_x_755_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4_spec__12___boxed(lean_object* v_00_u03b2_757_, lean_object* v_a_758_, lean_object* v_x_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4_spec__12(v_00_u03b2_757_, v_a_758_, v_x_759_);
lean_dec(v_x_759_);
lean_dec_ref(v_a_758_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevS(lean_object* v_e_761_, lean_object* v_subst_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_){
_start:
{
lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_770_ = lean_unsigned_to_nat(0u);
v___x_771_ = lean_array_get_size(v_subst_762_);
v___x_772_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_e_761_, v___x_770_, v___x_771_, v_subst_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevS___boxed(lean_object* v_e_773_, lean_object* v_subst_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_Lean_Meta_Sym_instantiateRevS(v_e_773_, v_subst_774_, v_a_775_, v_a_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_);
lean_dec(v_a_780_);
lean_dec_ref(v_a_779_);
lean_dec(v_a_778_);
lean_dec_ref(v_a_777_);
lean_dec(v_a_776_);
lean_dec_ref(v_a_775_);
lean_dec_ref(v_subst_774_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1(lean_object* v_msg_783_, uint8_t v___y_784_, lean_object* v___y_785_){
_start:
{
lean_object* v___f_786_; lean_object* v___f_787_; lean_object* v___f_788_; lean_object* v___f_789_; lean_object* v___f_790_; lean_object* v___f_791_; lean_object* v___f_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___f_796_; lean_object* v___f_797_; lean_object* v___f_798_; lean_object* v___f_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___f_808_; lean_object* v___x_3111__overap_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
v___f_786_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__0));
v___f_787_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__1));
v___f_788_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__2));
v___f_789_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__3));
v___f_790_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__4));
v___f_791_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__5));
v___f_792_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__6));
v___x_793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_793_, 0, v___f_786_);
lean_ctor_set(v___x_793_, 1, v___f_787_);
v___x_794_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_794_, 0, v___x_793_);
lean_ctor_set(v___x_794_, 1, v___f_788_);
lean_ctor_set(v___x_794_, 2, v___f_789_);
lean_ctor_set(v___x_794_, 3, v___f_790_);
lean_ctor_set(v___x_794_, 4, v___f_791_);
v___x_795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_795_, 0, v___x_794_);
lean_ctor_set(v___x_795_, 1, v___f_792_);
lean_inc_ref_n(v___x_795_, 6);
v___f_796_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_796_, 0, v___x_795_);
v___f_797_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_797_, 0, v___x_795_);
v___f_798_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_798_, 0, v___x_795_);
v___f_799_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_799_, 0, v___x_795_);
v___x_800_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_800_, 0, lean_box(0));
lean_closure_set(v___x_800_, 1, lean_box(0));
lean_closure_set(v___x_800_, 2, v___x_795_);
v___x_801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_801_, 0, v___x_800_);
lean_ctor_set(v___x_801_, 1, v___f_796_);
v___x_802_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_802_, 0, lean_box(0));
lean_closure_set(v___x_802_, 1, lean_box(0));
lean_closure_set(v___x_802_, 2, v___x_795_);
v___x_803_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_803_, 0, v___x_801_);
lean_ctor_set(v___x_803_, 1, v___x_802_);
lean_ctor_set(v___x_803_, 2, v___f_797_);
lean_ctor_set(v___x_803_, 3, v___f_798_);
lean_ctor_set(v___x_803_, 4, v___f_799_);
v___x_804_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_804_, 0, lean_box(0));
lean_closure_set(v___x_804_, 1, lean_box(0));
lean_closure_set(v___x_804_, 2, v___x_795_);
v___x_805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_805_, 0, v___x_803_);
lean_ctor_set(v___x_805_, 1, v___x_804_);
v___x_806_ = l_Lean_instInhabitedExpr;
v___x_807_ = l_instInhabitedOfMonad___redArg(v___x_805_, v___x_806_);
v___f_808_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_808_, 0, v___x_807_);
v___x_3111__overap_809_ = lean_panic_fn_borrowed(v___f_808_, v_msg_783_);
lean_dec_ref(v___f_808_);
v___x_810_ = lean_box(v___y_784_);
v___x_811_ = lean_apply_2(v___x_3111__overap_809_, v___x_810_, v___y_785_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1___boxed(lean_object* v_msg_812_, lean_object* v___y_813_, lean_object* v___y_814_){
_start:
{
uint8_t v___y_3548__boxed_815_; lean_object* v_res_816_; 
v___y_3548__boxed_815_ = lean_unbox(v___y_813_);
v_res_816_ = l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1(v_msg_812_, v___y_3548__boxed_815_, v___y_814_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0(lean_object* v_n_817_, lean_object* v_beginIdx_818_, lean_object* v_subst_819_, lean_object* v_e_820_, lean_object* v_offset_821_, lean_object* v_a_822_, uint8_t v_a_823_, lean_object* v_a_824_){
_start:
{
switch(lean_obj_tag(v_e_820_))
{
case 5:
{
lean_object* v_fn_825_; lean_object* v_arg_826_; lean_object* v___x_827_; lean_object* v_fst_828_; lean_object* v_snd_829_; lean_object* v_fst_830_; lean_object* v_snd_831_; lean_object* v___x_832_; lean_object* v_fst_833_; lean_object* v_snd_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_855_; 
v_fn_825_ = lean_ctor_get(v_e_820_, 0);
v_arg_826_ = lean_ctor_get(v_e_820_, 1);
lean_inc(v_offset_821_);
lean_inc_ref(v_fn_825_);
v___x_827_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_817_, v_beginIdx_818_, v_subst_819_, v_fn_825_, v_offset_821_, v_a_822_, v_a_823_, v_a_824_);
v_fst_828_ = lean_ctor_get(v___x_827_, 0);
lean_inc(v_fst_828_);
v_snd_829_ = lean_ctor_get(v___x_827_, 1);
lean_inc(v_snd_829_);
lean_dec_ref(v___x_827_);
v_fst_830_ = lean_ctor_get(v_fst_828_, 0);
lean_inc(v_fst_830_);
v_snd_831_ = lean_ctor_get(v_fst_828_, 1);
lean_inc(v_snd_831_);
lean_dec(v_fst_828_);
lean_inc_ref(v_arg_826_);
v___x_832_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_817_, v_beginIdx_818_, v_subst_819_, v_arg_826_, v_offset_821_, v_snd_831_, v_a_823_, v_snd_829_);
v_fst_833_ = lean_ctor_get(v___x_832_, 0);
v_snd_834_ = lean_ctor_get(v___x_832_, 1);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_832_);
if (v_isSharedCheck_855_ == 0)
{
v___x_836_ = v___x_832_;
v_isShared_837_ = v_isSharedCheck_855_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_snd_834_);
lean_inc(v_fst_833_);
lean_dec(v___x_832_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_855_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v_fst_838_; lean_object* v_snd_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_854_; 
v_fst_838_ = lean_ctor_get(v_fst_833_, 0);
v_snd_839_ = lean_ctor_get(v_fst_833_, 1);
v_isSharedCheck_854_ = !lean_is_exclusive(v_fst_833_);
if (v_isSharedCheck_854_ == 0)
{
v___x_841_ = v_fst_833_;
v_isShared_842_ = v_isSharedCheck_854_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_snd_839_);
lean_inc(v_fst_838_);
lean_dec(v_fst_833_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_854_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
uint8_t v___y_844_; uint8_t v___x_852_; 
v___x_852_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_825_, v_fst_830_);
if (v___x_852_ == 0)
{
v___y_844_ = v___x_852_;
goto v___jp_843_;
}
else
{
uint8_t v___x_853_; 
v___x_853_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_826_, v_fst_838_);
v___y_844_ = v___x_853_;
goto v___jp_843_;
}
v___jp_843_:
{
if (v___y_844_ == 0)
{
lean_object* v___x_845_; 
lean_del_object(v___x_841_);
lean_del_object(v___x_836_);
lean_dec_ref(v_e_820_);
v___x_845_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__3(v_fst_830_, v_fst_838_, v_snd_839_, v_a_823_, v_snd_834_);
return v___x_845_;
}
else
{
lean_object* v___x_847_; 
lean_dec(v_fst_838_);
lean_dec(v_fst_830_);
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 0, v_e_820_);
v___x_847_ = v___x_841_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_e_820_);
lean_ctor_set(v_reuseFailAlloc_851_, 1, v_snd_839_);
v___x_847_ = v_reuseFailAlloc_851_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
lean_object* v___x_849_; 
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 0, v___x_847_);
v___x_849_ = v___x_836_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v___x_847_);
lean_ctor_set(v_reuseFailAlloc_850_, 1, v_snd_834_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
}
}
}
}
case 6:
{
lean_object* v_binderName_856_; lean_object* v_binderType_857_; lean_object* v_body_858_; uint8_t v_binderInfo_859_; lean_object* v___x_860_; lean_object* v_fst_861_; lean_object* v_snd_862_; lean_object* v_fst_863_; lean_object* v_snd_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v_fst_868_; lean_object* v_snd_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_890_; 
v_binderName_856_ = lean_ctor_get(v_e_820_, 0);
v_binderType_857_ = lean_ctor_get(v_e_820_, 1);
v_body_858_ = lean_ctor_get(v_e_820_, 2);
v_binderInfo_859_ = lean_ctor_get_uint8(v_e_820_, sizeof(void*)*3 + 8);
lean_inc(v_offset_821_);
lean_inc_ref(v_binderType_857_);
v___x_860_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_817_, v_beginIdx_818_, v_subst_819_, v_binderType_857_, v_offset_821_, v_a_822_, v_a_823_, v_a_824_);
v_fst_861_ = lean_ctor_get(v___x_860_, 0);
lean_inc(v_fst_861_);
v_snd_862_ = lean_ctor_get(v___x_860_, 1);
lean_inc(v_snd_862_);
lean_dec_ref(v___x_860_);
v_fst_863_ = lean_ctor_get(v_fst_861_, 0);
lean_inc(v_fst_863_);
v_snd_864_ = lean_ctor_get(v_fst_861_, 1);
lean_inc(v_snd_864_);
lean_dec(v_fst_861_);
v___x_865_ = lean_unsigned_to_nat(1u);
v___x_866_ = lean_nat_add(v_offset_821_, v___x_865_);
lean_dec(v_offset_821_);
lean_inc_ref(v_body_858_);
v___x_867_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_817_, v_beginIdx_818_, v_subst_819_, v_body_858_, v___x_866_, v_snd_864_, v_a_823_, v_snd_862_);
v_fst_868_ = lean_ctor_get(v___x_867_, 0);
v_snd_869_ = lean_ctor_get(v___x_867_, 1);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_890_ == 0)
{
v___x_871_ = v___x_867_;
v_isShared_872_ = v_isSharedCheck_890_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_snd_869_);
lean_inc(v_fst_868_);
lean_dec(v___x_867_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_890_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v_fst_873_; lean_object* v_snd_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_889_; 
v_fst_873_ = lean_ctor_get(v_fst_868_, 0);
v_snd_874_ = lean_ctor_get(v_fst_868_, 1);
v_isSharedCheck_889_ = !lean_is_exclusive(v_fst_868_);
if (v_isSharedCheck_889_ == 0)
{
v___x_876_ = v_fst_868_;
v_isShared_877_ = v_isSharedCheck_889_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_snd_874_);
lean_inc(v_fst_873_);
lean_dec(v_fst_868_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_889_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
uint8_t v___y_879_; uint8_t v___x_887_; 
v___x_887_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_857_, v_fst_863_);
if (v___x_887_ == 0)
{
v___y_879_ = v___x_887_;
goto v___jp_878_;
}
else
{
uint8_t v___x_888_; 
v___x_888_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_858_, v_fst_873_);
v___y_879_ = v___x_888_;
goto v___jp_878_;
}
v___jp_878_:
{
if (v___y_879_ == 0)
{
lean_object* v___x_880_; 
lean_inc(v_binderName_856_);
lean_del_object(v___x_876_);
lean_del_object(v___x_871_);
lean_dec_ref(v_e_820_);
v___x_880_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__4(v_binderName_856_, v_binderInfo_859_, v_fst_863_, v_fst_873_, v_snd_874_, v_a_823_, v_snd_869_);
return v___x_880_;
}
else
{
lean_object* v___x_882_; 
lean_dec(v_fst_873_);
lean_dec(v_fst_863_);
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 0, v_e_820_);
v___x_882_ = v___x_876_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_e_820_);
lean_ctor_set(v_reuseFailAlloc_886_, 1, v_snd_874_);
v___x_882_ = v_reuseFailAlloc_886_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
lean_object* v___x_884_; 
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 0, v___x_882_);
v___x_884_ = v___x_871_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_882_);
lean_ctor_set(v_reuseFailAlloc_885_, 1, v_snd_869_);
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
}
case 7:
{
lean_object* v_binderName_891_; lean_object* v_binderType_892_; lean_object* v_body_893_; uint8_t v_binderInfo_894_; lean_object* v___x_895_; lean_object* v_fst_896_; lean_object* v_snd_897_; lean_object* v_fst_898_; lean_object* v_snd_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v_fst_903_; lean_object* v_snd_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_925_; 
v_binderName_891_ = lean_ctor_get(v_e_820_, 0);
v_binderType_892_ = lean_ctor_get(v_e_820_, 1);
v_body_893_ = lean_ctor_get(v_e_820_, 2);
v_binderInfo_894_ = lean_ctor_get_uint8(v_e_820_, sizeof(void*)*3 + 8);
lean_inc(v_offset_821_);
lean_inc_ref(v_binderType_892_);
v___x_895_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_817_, v_beginIdx_818_, v_subst_819_, v_binderType_892_, v_offset_821_, v_a_822_, v_a_823_, v_a_824_);
v_fst_896_ = lean_ctor_get(v___x_895_, 0);
lean_inc(v_fst_896_);
v_snd_897_ = lean_ctor_get(v___x_895_, 1);
lean_inc(v_snd_897_);
lean_dec_ref(v___x_895_);
v_fst_898_ = lean_ctor_get(v_fst_896_, 0);
lean_inc(v_fst_898_);
v_snd_899_ = lean_ctor_get(v_fst_896_, 1);
lean_inc(v_snd_899_);
lean_dec(v_fst_896_);
v___x_900_ = lean_unsigned_to_nat(1u);
v___x_901_ = lean_nat_add(v_offset_821_, v___x_900_);
lean_dec(v_offset_821_);
lean_inc_ref(v_body_893_);
v___x_902_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_817_, v_beginIdx_818_, v_subst_819_, v_body_893_, v___x_901_, v_snd_899_, v_a_823_, v_snd_897_);
v_fst_903_ = lean_ctor_get(v___x_902_, 0);
v_snd_904_ = lean_ctor_get(v___x_902_, 1);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_925_ == 0)
{
v___x_906_ = v___x_902_;
v_isShared_907_ = v_isSharedCheck_925_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_snd_904_);
lean_inc(v_fst_903_);
lean_dec(v___x_902_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_925_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v_fst_908_; lean_object* v_snd_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_924_; 
v_fst_908_ = lean_ctor_get(v_fst_903_, 0);
v_snd_909_ = lean_ctor_get(v_fst_903_, 1);
v_isSharedCheck_924_ = !lean_is_exclusive(v_fst_903_);
if (v_isSharedCheck_924_ == 0)
{
v___x_911_ = v_fst_903_;
v_isShared_912_ = v_isSharedCheck_924_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_snd_909_);
lean_inc(v_fst_908_);
lean_dec(v_fst_903_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_924_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
uint8_t v___y_914_; uint8_t v___x_922_; 
v___x_922_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_892_, v_fst_898_);
if (v___x_922_ == 0)
{
v___y_914_ = v___x_922_;
goto v___jp_913_;
}
else
{
uint8_t v___x_923_; 
v___x_923_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_893_, v_fst_908_);
v___y_914_ = v___x_923_;
goto v___jp_913_;
}
v___jp_913_:
{
if (v___y_914_ == 0)
{
lean_object* v___x_915_; 
lean_inc(v_binderName_891_);
lean_del_object(v___x_911_);
lean_del_object(v___x_906_);
lean_dec_ref(v_e_820_);
v___x_915_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__5(v_binderName_891_, v_binderInfo_894_, v_fst_898_, v_fst_908_, v_snd_909_, v_a_823_, v_snd_904_);
return v___x_915_;
}
else
{
lean_object* v___x_917_; 
lean_dec(v_fst_908_);
lean_dec(v_fst_898_);
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 0, v_e_820_);
v___x_917_ = v___x_911_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_e_820_);
lean_ctor_set(v_reuseFailAlloc_921_, 1, v_snd_909_);
v___x_917_ = v_reuseFailAlloc_921_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
lean_object* v___x_919_; 
if (v_isShared_907_ == 0)
{
lean_ctor_set(v___x_906_, 0, v___x_917_);
v___x_919_ = v___x_906_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v___x_917_);
lean_ctor_set(v_reuseFailAlloc_920_, 1, v_snd_904_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
}
}
}
}
}
case 8:
{
lean_object* v_declName_926_; lean_object* v_type_927_; lean_object* v_value_928_; lean_object* v_body_929_; uint8_t v_nondep_930_; lean_object* v___x_931_; lean_object* v_fst_932_; lean_object* v_snd_933_; lean_object* v_fst_934_; lean_object* v_snd_935_; lean_object* v___x_936_; lean_object* v_fst_937_; lean_object* v_snd_938_; lean_object* v_fst_939_; lean_object* v_snd_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v_fst_944_; lean_object* v_snd_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_968_; 
v_declName_926_ = lean_ctor_get(v_e_820_, 0);
v_type_927_ = lean_ctor_get(v_e_820_, 1);
v_value_928_ = lean_ctor_get(v_e_820_, 2);
v_body_929_ = lean_ctor_get(v_e_820_, 3);
v_nondep_930_ = lean_ctor_get_uint8(v_e_820_, sizeof(void*)*4 + 8);
lean_inc_n(v_offset_821_, 2);
lean_inc_ref(v_type_927_);
v___x_931_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_817_, v_beginIdx_818_, v_subst_819_, v_type_927_, v_offset_821_, v_a_822_, v_a_823_, v_a_824_);
v_fst_932_ = lean_ctor_get(v___x_931_, 0);
lean_inc(v_fst_932_);
v_snd_933_ = lean_ctor_get(v___x_931_, 1);
lean_inc(v_snd_933_);
lean_dec_ref(v___x_931_);
v_fst_934_ = lean_ctor_get(v_fst_932_, 0);
lean_inc(v_fst_934_);
v_snd_935_ = lean_ctor_get(v_fst_932_, 1);
lean_inc(v_snd_935_);
lean_dec(v_fst_932_);
lean_inc_ref(v_value_928_);
v___x_936_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_817_, v_beginIdx_818_, v_subst_819_, v_value_928_, v_offset_821_, v_snd_935_, v_a_823_, v_snd_933_);
v_fst_937_ = lean_ctor_get(v___x_936_, 0);
lean_inc(v_fst_937_);
v_snd_938_ = lean_ctor_get(v___x_936_, 1);
lean_inc(v_snd_938_);
lean_dec_ref(v___x_936_);
v_fst_939_ = lean_ctor_get(v_fst_937_, 0);
lean_inc(v_fst_939_);
v_snd_940_ = lean_ctor_get(v_fst_937_, 1);
lean_inc(v_snd_940_);
lean_dec(v_fst_937_);
v___x_941_ = lean_unsigned_to_nat(1u);
v___x_942_ = lean_nat_add(v_offset_821_, v___x_941_);
lean_dec(v_offset_821_);
lean_inc_ref(v_body_929_);
v___x_943_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_817_, v_beginIdx_818_, v_subst_819_, v_body_929_, v___x_942_, v_snd_940_, v_a_823_, v_snd_938_);
v_fst_944_ = lean_ctor_get(v___x_943_, 0);
v_snd_945_ = lean_ctor_get(v___x_943_, 1);
v_isSharedCheck_968_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_968_ == 0)
{
v___x_947_ = v___x_943_;
v_isShared_948_ = v_isSharedCheck_968_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_snd_945_);
lean_inc(v_fst_944_);
lean_dec(v___x_943_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_968_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v_fst_949_; lean_object* v_snd_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_967_; 
v_fst_949_ = lean_ctor_get(v_fst_944_, 0);
v_snd_950_ = lean_ctor_get(v_fst_944_, 1);
v_isSharedCheck_967_ = !lean_is_exclusive(v_fst_944_);
if (v_isSharedCheck_967_ == 0)
{
v___x_952_ = v_fst_944_;
v_isShared_953_ = v_isSharedCheck_967_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_snd_950_);
lean_inc(v_fst_949_);
lean_dec(v_fst_944_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_967_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
uint8_t v___y_955_; uint8_t v___x_965_; 
v___x_965_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_type_927_, v_fst_934_);
if (v___x_965_ == 0)
{
v___y_955_ = v___x_965_;
goto v___jp_954_;
}
else
{
uint8_t v___x_966_; 
v___x_966_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_value_928_, v_fst_939_);
v___y_955_ = v___x_966_;
goto v___jp_954_;
}
v___jp_954_:
{
if (v___y_955_ == 0)
{
lean_object* v___x_956_; 
lean_inc(v_declName_926_);
lean_del_object(v___x_952_);
lean_del_object(v___x_947_);
lean_dec_ref(v_e_820_);
v___x_956_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6(v_declName_926_, v_fst_934_, v_fst_939_, v_fst_949_, v_nondep_930_, v_snd_950_, v_a_823_, v_snd_945_);
return v___x_956_;
}
else
{
uint8_t v___x_957_; 
v___x_957_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_929_, v_fst_949_);
if (v___x_957_ == 0)
{
lean_object* v___x_958_; 
lean_inc(v_declName_926_);
lean_del_object(v___x_952_);
lean_del_object(v___x_947_);
lean_dec_ref(v_e_820_);
v___x_958_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6(v_declName_926_, v_fst_934_, v_fst_939_, v_fst_949_, v_nondep_930_, v_snd_950_, v_a_823_, v_snd_945_);
return v___x_958_;
}
else
{
lean_object* v___x_960_; 
lean_dec(v_fst_949_);
lean_dec(v_fst_939_);
lean_dec(v_fst_934_);
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 0, v_e_820_);
v___x_960_ = v___x_952_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_e_820_);
lean_ctor_set(v_reuseFailAlloc_964_, 1, v_snd_950_);
v___x_960_ = v_reuseFailAlloc_964_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
lean_object* v___x_962_; 
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 0, v___x_960_);
v___x_962_ = v___x_947_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v___x_960_);
lean_ctor_set(v_reuseFailAlloc_963_, 1, v_snd_945_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
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
lean_object* v_data_969_; lean_object* v_expr_970_; lean_object* v___x_971_; lean_object* v_fst_972_; lean_object* v_snd_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_991_; 
v_data_969_ = lean_ctor_get(v_e_820_, 0);
v_expr_970_ = lean_ctor_get(v_e_820_, 1);
lean_inc_ref(v_expr_970_);
v___x_971_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_817_, v_beginIdx_818_, v_subst_819_, v_expr_970_, v_offset_821_, v_a_822_, v_a_823_, v_a_824_);
v_fst_972_ = lean_ctor_get(v___x_971_, 0);
v_snd_973_ = lean_ctor_get(v___x_971_, 1);
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_971_);
if (v_isSharedCheck_991_ == 0)
{
v___x_975_ = v___x_971_;
v_isShared_976_ = v_isSharedCheck_991_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_snd_973_);
lean_inc(v_fst_972_);
lean_dec(v___x_971_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_991_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v_fst_977_; lean_object* v_snd_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_990_; 
v_fst_977_ = lean_ctor_get(v_fst_972_, 0);
v_snd_978_ = lean_ctor_get(v_fst_972_, 1);
v_isSharedCheck_990_ = !lean_is_exclusive(v_fst_972_);
if (v_isSharedCheck_990_ == 0)
{
v___x_980_ = v_fst_972_;
v_isShared_981_ = v_isSharedCheck_990_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_snd_978_);
lean_inc(v_fst_977_);
lean_dec(v_fst_972_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_990_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
uint8_t v___x_982_; 
v___x_982_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_expr_970_, v_fst_977_);
if (v___x_982_ == 0)
{
lean_object* v___x_983_; 
lean_inc(v_data_969_);
lean_del_object(v___x_980_);
lean_del_object(v___x_975_);
lean_dec_ref(v_e_820_);
v___x_983_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__7(v_data_969_, v_fst_977_, v_snd_978_, v_a_823_, v_snd_973_);
return v___x_983_;
}
else
{
lean_object* v___x_985_; 
lean_dec(v_fst_977_);
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 0, v_e_820_);
v___x_985_ = v___x_980_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_e_820_);
lean_ctor_set(v_reuseFailAlloc_989_, 1, v_snd_978_);
v___x_985_ = v_reuseFailAlloc_989_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
lean_object* v___x_987_; 
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 0, v___x_985_);
v___x_987_ = v___x_975_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v___x_985_);
lean_ctor_set(v_reuseFailAlloc_988_, 1, v_snd_973_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
}
}
}
}
case 11:
{
lean_object* v_typeName_992_; lean_object* v_idx_993_; lean_object* v_struct_994_; lean_object* v___x_995_; lean_object* v_fst_996_; lean_object* v_snd_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1015_; 
v_typeName_992_ = lean_ctor_get(v_e_820_, 0);
v_idx_993_ = lean_ctor_get(v_e_820_, 1);
v_struct_994_ = lean_ctor_get(v_e_820_, 2);
lean_inc_ref(v_struct_994_);
v___x_995_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_817_, v_beginIdx_818_, v_subst_819_, v_struct_994_, v_offset_821_, v_a_822_, v_a_823_, v_a_824_);
v_fst_996_ = lean_ctor_get(v___x_995_, 0);
v_snd_997_ = lean_ctor_get(v___x_995_, 1);
v_isSharedCheck_1015_ = !lean_is_exclusive(v___x_995_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_999_ = v___x_995_;
v_isShared_1000_ = v_isSharedCheck_1015_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_snd_997_);
lean_inc(v_fst_996_);
lean_dec(v___x_995_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1015_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v_fst_1001_; lean_object* v_snd_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1014_; 
v_fst_1001_ = lean_ctor_get(v_fst_996_, 0);
v_snd_1002_ = lean_ctor_get(v_fst_996_, 1);
v_isSharedCheck_1014_ = !lean_is_exclusive(v_fst_996_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1004_ = v_fst_996_;
v_isShared_1005_ = v_isSharedCheck_1014_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_snd_1002_);
lean_inc(v_fst_1001_);
lean_dec(v_fst_996_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1014_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
uint8_t v___x_1006_; 
v___x_1006_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_994_, v_fst_1001_);
if (v___x_1006_ == 0)
{
lean_object* v___x_1007_; 
lean_inc(v_idx_993_);
lean_inc(v_typeName_992_);
lean_del_object(v___x_1004_);
lean_del_object(v___x_999_);
lean_dec_ref(v_e_820_);
v___x_1007_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__8(v_typeName_992_, v_idx_993_, v_fst_1001_, v_snd_1002_, v_a_823_, v_snd_997_);
return v___x_1007_;
}
else
{
lean_object* v___x_1009_; 
lean_dec(v_fst_1001_);
if (v_isShared_1005_ == 0)
{
lean_ctor_set(v___x_1004_, 0, v_e_820_);
v___x_1009_ = v___x_1004_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_e_820_);
lean_ctor_set(v_reuseFailAlloc_1013_, 1, v_snd_1002_);
v___x_1009_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
lean_object* v___x_1011_; 
if (v_isShared_1000_ == 0)
{
lean_ctor_set(v___x_999_, 0, v___x_1009_);
v___x_1011_ = v___x_999_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v___x_1009_);
lean_ctor_set(v_reuseFailAlloc_1012_, 1, v_snd_997_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
lean_dec(v_offset_821_);
lean_dec_ref(v_e_820_);
v___x_1016_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__3);
v___x_1017_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9(v___x_1016_, v_a_822_, v_a_823_, v_a_824_);
return v___x_1017_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(lean_object* v_n_1018_, lean_object* v_beginIdx_1019_, lean_object* v_subst_1020_, lean_object* v_e_1021_, lean_object* v_offset_1022_, lean_object* v_a_1023_, uint8_t v_a_1024_, lean_object* v_a_1025_){
_start:
{
lean_object* v_key_1026_; lean_object* v___x_1027_; 
lean_inc(v_offset_1022_);
lean_inc_ref(v_e_1021_);
v_key_1026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1026_, 0, v_e_1021_);
lean_ctor_set(v_key_1026_, 1, v_offset_1022_);
v___x_1027_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___redArg(v_a_1023_, v_key_1026_);
if (lean_obj_tag(v___x_1027_) == 1)
{
lean_object* v_val_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
lean_dec_ref(v_key_1026_);
lean_dec(v_offset_1022_);
lean_dec_ref(v_e_1021_);
v_val_1028_ = lean_ctor_get(v___x_1027_, 0);
lean_inc(v_val_1028_);
lean_dec_ref(v___x_1027_);
v___x_1029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1029_, 0, v_val_1028_);
lean_ctor_set(v___x_1029_, 1, v_a_1023_);
v___x_1030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1029_);
lean_ctor_set(v___x_1030_, 1, v_a_1025_);
return v___x_1030_;
}
else
{
lean_dec(v___x_1027_);
switch(lean_obj_tag(v_e_1021_))
{
case 0:
{
lean_object* v_deBruijnIndex_1031_; uint8_t v___x_1032_; 
v_deBruijnIndex_1031_ = lean_ctor_get(v_e_1021_, 0);
v___x_1032_ = lean_nat_dec_le(v_offset_1022_, v_deBruijnIndex_1031_);
if (v___x_1032_ == 0)
{
lean_object* v___x_1033_; 
lean_dec(v_offset_1022_);
v___x_1033_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1026_, v_e_1021_, v_a_1023_, v_a_1024_, v_a_1025_);
return v___x_1033_;
}
else
{
lean_object* v___x_1034_; uint8_t v___x_1035_; 
lean_inc(v_deBruijnIndex_1031_);
lean_dec_ref(v_e_1021_);
v___x_1034_ = lean_nat_add(v_offset_1022_, v_n_1018_);
v___x_1035_ = lean_nat_dec_lt(v_deBruijnIndex_1031_, v___x_1034_);
lean_dec(v___x_1034_);
if (v___x_1035_ == 0)
{
lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v_fst_1038_; lean_object* v_snd_1039_; lean_object* v___x_1040_; 
lean_dec(v_offset_1022_);
v___x_1036_ = lean_nat_sub(v_deBruijnIndex_1031_, v_n_1018_);
lean_dec(v_deBruijnIndex_1031_);
v___x_1037_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___redArg(v___x_1036_, v_a_1025_);
v_fst_1038_ = lean_ctor_get(v___x_1037_, 0);
lean_inc(v_fst_1038_);
v_snd_1039_ = lean_ctor_get(v___x_1037_, 1);
lean_inc(v_snd_1039_);
lean_dec_ref(v___x_1037_);
v___x_1040_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1026_, v_fst_1038_, v_a_1023_, v_a_1024_, v_snd_1039_);
return v___x_1040_;
}
else
{
lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v_v_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v_fst_1046_; lean_object* v_snd_1047_; lean_object* v___x_1048_; 
v___x_1041_ = lean_nat_add(v_beginIdx_1019_, v_deBruijnIndex_1031_);
lean_dec(v_deBruijnIndex_1031_);
v___x_1042_ = lean_nat_sub(v___x_1041_, v_offset_1022_);
lean_dec(v___x_1041_);
v_v_1043_ = lean_array_fget_borrowed(v_subst_1020_, v___x_1042_);
lean_dec(v___x_1042_);
v___x_1044_ = lean_unsigned_to_nat(0u);
lean_inc(v_v_1043_);
v___x_1045_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(v_v_1043_, v___x_1044_, v_offset_1022_, v_a_1024_, v_a_1025_);
lean_dec(v_offset_1022_);
v_fst_1046_ = lean_ctor_get(v___x_1045_, 0);
lean_inc(v_fst_1046_);
v_snd_1047_ = lean_ctor_get(v___x_1045_, 1);
lean_inc(v_snd_1047_);
lean_dec_ref(v___x_1045_);
v___x_1048_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1026_, v_fst_1046_, v_a_1023_, v_a_1024_, v_snd_1047_);
return v___x_1048_;
}
}
}
case 9:
{
lean_object* v___x_1049_; 
lean_dec(v_offset_1022_);
v___x_1049_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1026_, v_e_1021_, v_a_1023_, v_a_1024_, v_a_1025_);
return v___x_1049_;
}
case 2:
{
lean_object* v___x_1050_; 
lean_dec(v_offset_1022_);
v___x_1050_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1026_, v_e_1021_, v_a_1023_, v_a_1024_, v_a_1025_);
return v___x_1050_;
}
case 1:
{
lean_object* v___x_1051_; 
lean_dec(v_offset_1022_);
v___x_1051_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1026_, v_e_1021_, v_a_1023_, v_a_1024_, v_a_1025_);
return v___x_1051_;
}
case 4:
{
lean_object* v___x_1052_; 
lean_dec(v_offset_1022_);
v___x_1052_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1026_, v_e_1021_, v_a_1023_, v_a_1024_, v_a_1025_);
return v___x_1052_;
}
case 3:
{
lean_object* v___x_1053_; 
lean_dec(v_offset_1022_);
v___x_1053_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1026_, v_e_1021_, v_a_1023_, v_a_1024_, v_a_1025_);
return v___x_1053_;
}
default: 
{
lean_object* v___x_1054_; uint8_t v___x_1055_; 
v___x_1054_ = l_Lean_Expr_looseBVarRange(v_e_1021_);
v___x_1055_ = lean_nat_dec_le(v___x_1054_, v_offset_1022_);
lean_dec(v___x_1054_);
if (v___x_1055_ == 0)
{
switch(lean_obj_tag(v_e_1021_))
{
case 9:
{
lean_object* v___x_1056_; 
lean_dec(v_offset_1022_);
v___x_1056_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1026_, v_e_1021_, v_a_1023_, v_a_1024_, v_a_1025_);
return v___x_1056_;
}
case 2:
{
lean_object* v___x_1057_; 
lean_dec(v_offset_1022_);
v___x_1057_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1026_, v_e_1021_, v_a_1023_, v_a_1024_, v_a_1025_);
return v___x_1057_;
}
case 0:
{
lean_object* v___x_1058_; 
lean_dec(v_offset_1022_);
v___x_1058_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1026_, v_e_1021_, v_a_1023_, v_a_1024_, v_a_1025_);
return v___x_1058_;
}
case 1:
{
lean_object* v___x_1059_; 
lean_dec(v_offset_1022_);
v___x_1059_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1026_, v_e_1021_, v_a_1023_, v_a_1024_, v_a_1025_);
return v___x_1059_;
}
case 4:
{
lean_object* v___x_1060_; 
lean_dec(v_offset_1022_);
v___x_1060_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1026_, v_e_1021_, v_a_1023_, v_a_1024_, v_a_1025_);
return v___x_1060_;
}
case 3:
{
lean_object* v___x_1061_; 
lean_dec(v_offset_1022_);
v___x_1061_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1026_, v_e_1021_, v_a_1023_, v_a_1024_, v_a_1025_);
return v___x_1061_;
}
default: 
{
lean_object* v___x_1062_; lean_object* v_fst_1063_; lean_object* v_snd_1064_; lean_object* v_fst_1065_; lean_object* v_snd_1066_; lean_object* v___x_1067_; 
v___x_1062_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0(v_n_1018_, v_beginIdx_1019_, v_subst_1020_, v_e_1021_, v_offset_1022_, v_a_1023_, v_a_1024_, v_a_1025_);
v_fst_1063_ = lean_ctor_get(v___x_1062_, 0);
lean_inc(v_fst_1063_);
v_snd_1064_ = lean_ctor_get(v___x_1062_, 1);
lean_inc(v_snd_1064_);
lean_dec_ref(v___x_1062_);
v_fst_1065_ = lean_ctor_get(v_fst_1063_, 0);
lean_inc(v_fst_1065_);
v_snd_1066_ = lean_ctor_get(v_fst_1063_, 1);
lean_inc(v_snd_1066_);
lean_dec(v_fst_1063_);
v___x_1067_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1026_, v_fst_1065_, v_snd_1066_, v_a_1024_, v_snd_1064_);
return v___x_1067_;
}
}
}
else
{
lean_object* v___x_1068_; 
lean_dec(v_offset_1022_);
v___x_1068_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1026_, v_e_1021_, v_a_1023_, v_a_1024_, v_a_1025_);
return v___x_1068_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0___boxed(lean_object* v_n_1069_, lean_object* v_beginIdx_1070_, lean_object* v_subst_1071_, lean_object* v_e_1072_, lean_object* v_offset_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_){
_start:
{
uint8_t v_a_boxed_1077_; lean_object* v_res_1078_; 
v_a_boxed_1077_ = lean_unbox(v_a_1075_);
v_res_1078_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1069_, v_beginIdx_1070_, v_subst_1071_, v_e_1072_, v_offset_1073_, v_a_1074_, v_a_boxed_1077_, v_a_1076_);
lean_dec_ref(v_subst_1071_);
lean_dec(v_beginIdx_1070_);
lean_dec(v_n_1069_);
return v_res_1078_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0___boxed(lean_object* v_n_1079_, lean_object* v_beginIdx_1080_, lean_object* v_subst_1081_, lean_object* v_e_1082_, lean_object* v_offset_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_){
_start:
{
uint8_t v_a_boxed_1087_; lean_object* v_res_1088_; 
v_a_boxed_1087_ = lean_unbox(v_a_1085_);
v_res_1088_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0(v_n_1079_, v_beginIdx_1080_, v_subst_1081_, v_e_1082_, v_offset_1083_, v_a_1084_, v_a_boxed_1087_, v_a_1086_);
lean_dec_ref(v_subst_1081_);
lean_dec(v_beginIdx_1080_);
lean_dec(v_n_1079_);
return v_res_1088_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__1(void){
_start:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1090_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__2));
v___x_1091_ = lean_unsigned_to_nat(34u);
v___x_1092_ = lean_unsigned_to_nat(57u);
v___x_1093_ = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__0));
v___x_1094_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__3));
v___x_1095_ = l_mkPanicMessageWithDecl(v___x_1094_, v___x_1093_, v___x_1092_, v___x_1091_, v___x_1090_);
return v___x_1095_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__2(void){
_start:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1096_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__2));
v___x_1097_ = lean_unsigned_to_nat(32u);
v___x_1098_ = lean_unsigned_to_nat(56u);
v___x_1099_ = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__0));
v___x_1100_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__3));
v___x_1101_ = l_mkPanicMessageWithDecl(v___x_1100_, v___x_1099_, v___x_1098_, v___x_1097_, v___x_1096_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27(lean_object* v_e_1102_, lean_object* v_beginIdx_1103_, lean_object* v_endIdx_1104_, lean_object* v_subst_1105_, uint8_t v_a_1106_, lean_object* v_a_1107_){
_start:
{
uint8_t v___x_1108_; 
v___x_1108_ = lean_nat_dec_lt(v_endIdx_1104_, v_beginIdx_1103_);
if (v___x_1108_ == 0)
{
lean_object* v___x_1109_; uint8_t v___x_1110_; 
v___x_1109_ = lean_array_get_size(v_subst_1105_);
v___x_1110_ = lean_nat_dec_lt(v___x_1109_, v_endIdx_1104_);
if (v___x_1110_ == 0)
{
lean_object* v_n_1111_; lean_object* v___x_1112_; 
v_n_1111_ = lean_nat_sub(v_endIdx_1104_, v_beginIdx_1103_);
v___x_1112_ = lean_unsigned_to_nat(0u);
switch(lean_obj_tag(v_e_1102_))
{
case 0:
{
lean_object* v_deBruijnIndex_1113_; uint8_t v___x_1114_; 
v_deBruijnIndex_1113_ = lean_ctor_get(v_e_1102_, 0);
v___x_1114_ = lean_nat_dec_le(v___x_1112_, v_deBruijnIndex_1113_);
if (v___x_1114_ == 0)
{
lean_object* v___x_1115_; 
lean_dec(v_n_1111_);
v___x_1115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1115_, 0, v_e_1102_);
lean_ctor_set(v___x_1115_, 1, v_a_1107_);
return v___x_1115_;
}
else
{
uint8_t v___x_1116_; 
lean_inc(v_deBruijnIndex_1113_);
lean_dec_ref(v_e_1102_);
v___x_1116_ = lean_nat_dec_lt(v_deBruijnIndex_1113_, v_n_1111_);
if (v___x_1116_ == 0)
{
lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1117_ = lean_nat_sub(v_deBruijnIndex_1113_, v_n_1111_);
lean_dec(v_n_1111_);
lean_dec(v_deBruijnIndex_1113_);
v___x_1118_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___redArg(v___x_1117_, v_a_1107_);
return v___x_1118_;
}
else
{
lean_object* v___x_1119_; lean_object* v_v_1120_; lean_object* v___x_1121_; 
lean_dec(v_n_1111_);
v___x_1119_ = lean_nat_add(v_beginIdx_1103_, v_deBruijnIndex_1113_);
lean_dec(v_deBruijnIndex_1113_);
v_v_1120_ = lean_array_fget_borrowed(v_subst_1105_, v___x_1119_);
lean_dec(v___x_1119_);
lean_inc(v_v_1120_);
v___x_1121_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(v_v_1120_, v___x_1112_, v___x_1112_, v_a_1106_, v_a_1107_);
return v___x_1121_;
}
}
}
case 9:
{
lean_object* v___x_1122_; 
lean_dec(v_n_1111_);
v___x_1122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1122_, 0, v_e_1102_);
lean_ctor_set(v___x_1122_, 1, v_a_1107_);
return v___x_1122_;
}
case 2:
{
lean_object* v___x_1123_; 
lean_dec(v_n_1111_);
v___x_1123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1123_, 0, v_e_1102_);
lean_ctor_set(v___x_1123_, 1, v_a_1107_);
return v___x_1123_;
}
case 1:
{
lean_object* v___x_1124_; 
lean_dec(v_n_1111_);
v___x_1124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1124_, 0, v_e_1102_);
lean_ctor_set(v___x_1124_, 1, v_a_1107_);
return v___x_1124_;
}
case 4:
{
lean_object* v___x_1125_; 
lean_dec(v_n_1111_);
v___x_1125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1125_, 0, v_e_1102_);
lean_ctor_set(v___x_1125_, 1, v_a_1107_);
return v___x_1125_;
}
case 3:
{
lean_object* v___x_1126_; 
lean_dec(v_n_1111_);
v___x_1126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1126_, 0, v_e_1102_);
lean_ctor_set(v___x_1126_, 1, v_a_1107_);
return v___x_1126_;
}
default: 
{
lean_object* v___x_1127_; uint8_t v___x_1128_; 
v___x_1127_ = l_Lean_Expr_looseBVarRange(v_e_1102_);
v___x_1128_ = lean_nat_dec_le(v___x_1127_, v___x_1112_);
lean_dec(v___x_1127_);
if (v___x_1128_ == 0)
{
switch(lean_obj_tag(v_e_1102_))
{
case 9:
{
lean_object* v___x_1129_; 
lean_dec(v_n_1111_);
v___x_1129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1129_, 0, v_e_1102_);
lean_ctor_set(v___x_1129_, 1, v_a_1107_);
return v___x_1129_;
}
case 2:
{
lean_object* v___x_1130_; 
lean_dec(v_n_1111_);
v___x_1130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1130_, 0, v_e_1102_);
lean_ctor_set(v___x_1130_, 1, v_a_1107_);
return v___x_1130_;
}
case 0:
{
lean_object* v___x_1131_; 
lean_dec(v_n_1111_);
v___x_1131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1131_, 0, v_e_1102_);
lean_ctor_set(v___x_1131_, 1, v_a_1107_);
return v___x_1131_;
}
case 1:
{
lean_object* v___x_1132_; 
lean_dec(v_n_1111_);
v___x_1132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1132_, 0, v_e_1102_);
lean_ctor_set(v___x_1132_, 1, v_a_1107_);
return v___x_1132_;
}
case 4:
{
lean_object* v___x_1133_; 
lean_dec(v_n_1111_);
v___x_1133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1133_, 0, v_e_1102_);
lean_ctor_set(v___x_1133_, 1, v_a_1107_);
return v___x_1133_;
}
case 3:
{
lean_object* v___x_1134_; 
lean_dec(v_n_1111_);
v___x_1134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1134_, 0, v_e_1102_);
lean_ctor_set(v___x_1134_, 1, v_a_1107_);
return v___x_1134_;
}
default: 
{
lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v_fst_1137_; lean_object* v_snd_1138_; lean_object* v_fst_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1146_; 
v___x_1135_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__2, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__2_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__2);
v___x_1136_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0(v_n_1111_, v_beginIdx_1103_, v_subst_1105_, v_e_1102_, v___x_1112_, v___x_1135_, v_a_1106_, v_a_1107_);
lean_dec(v_n_1111_);
v_fst_1137_ = lean_ctor_get(v___x_1136_, 0);
lean_inc(v_fst_1137_);
v_snd_1138_ = lean_ctor_get(v___x_1136_, 1);
lean_inc(v_snd_1138_);
lean_dec_ref(v___x_1136_);
v_fst_1139_ = lean_ctor_get(v_fst_1137_, 0);
v_isSharedCheck_1146_ = !lean_is_exclusive(v_fst_1137_);
if (v_isSharedCheck_1146_ == 0)
{
lean_object* v_unused_1147_; 
v_unused_1147_ = lean_ctor_get(v_fst_1137_, 1);
lean_dec(v_unused_1147_);
v___x_1141_ = v_fst_1137_;
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_fst_1139_);
lean_dec(v_fst_1137_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1144_; 
if (v_isShared_1142_ == 0)
{
lean_ctor_set(v___x_1141_, 1, v_snd_1138_);
v___x_1144_ = v___x_1141_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v_fst_1139_);
lean_ctor_set(v_reuseFailAlloc_1145_, 1, v_snd_1138_);
v___x_1144_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
return v___x_1144_;
}
}
}
}
}
else
{
lean_object* v___x_1148_; 
lean_dec(v_n_1111_);
v___x_1148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1148_, 0, v_e_1102_);
lean_ctor_set(v___x_1148_, 1, v_a_1107_);
return v___x_1148_;
}
}
}
}
else
{
lean_object* v___x_1149_; lean_object* v___x_1150_; 
lean_dec_ref(v_e_1102_);
v___x_1149_ = lean_obj_once(&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__1, &l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__1_once, _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__1);
v___x_1150_ = l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1(v___x_1149_, v_a_1106_, v_a_1107_);
return v___x_1150_;
}
}
else
{
lean_object* v___x_1151_; lean_object* v___x_1152_; 
lean_dec_ref(v_e_1102_);
v___x_1151_ = lean_obj_once(&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__2, &l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__2_once, _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__2);
v___x_1152_ = l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1(v___x_1151_, v_a_1106_, v_a_1107_);
return v___x_1152_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___boxed(lean_object* v_e_1153_, lean_object* v_beginIdx_1154_, lean_object* v_endIdx_1155_, lean_object* v_subst_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_){
_start:
{
uint8_t v_a_boxed_1159_; lean_object* v_res_1160_; 
v_a_boxed_1159_ = lean_unbox(v_a_1157_);
v_res_1160_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27(v_e_1153_, v_beginIdx_1154_, v_endIdx_1155_, v_subst_1156_, v_a_boxed_1159_, v_a_1158_);
lean_dec_ref(v_subst_1156_);
lean_dec(v_endIdx_1155_);
lean_dec(v_beginIdx_1154_);
return v_res_1160_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27(lean_object* v_e_1161_, lean_object* v_subst_1162_, uint8_t v_a_1163_, lean_object* v_a_1164_){
_start:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1165_ = lean_unsigned_to_nat(0u);
v___x_1166_ = lean_array_get_size(v_subst_1162_);
v___x_1167_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27(v_e_1161_, v___x_1165_, v___x_1166_, v_subst_1162_, v_a_1163_, v_a_1164_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27___boxed(lean_object* v_e_1168_, lean_object* v_subst_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_){
_start:
{
uint8_t v_a_boxed_1172_; lean_object* v_res_1173_; 
v_a_boxed_1172_ = lean_unbox(v_a_1170_);
v_res_1173_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27(v_e_1168_, v_subst_1169_, v_a_boxed_1172_, v_a_1171_);
lean_dec_ref(v_subst_1169_);
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateS___redArg(lean_object* v_e_1174_, lean_object* v_subst_1175_, lean_object* v_a_1176_){
_start:
{
lean_object* v___x_1178_; lean_object* v_share_1179_; lean_object* v_maxFVar_1180_; lean_object* v_proofInstInfo_1181_; lean_object* v_inferType_1182_; lean_object* v_getLevel_1183_; lean_object* v_congrInfo_1184_; lean_object* v_defEqI_1185_; lean_object* v_extensions_1186_; lean_object* v_issues_1187_; lean_object* v_canon_1188_; uint8_t v_debug_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1224_; 
v___x_1178_ = lean_st_ref_take(v_a_1176_);
v_share_1179_ = lean_ctor_get(v___x_1178_, 0);
v_maxFVar_1180_ = lean_ctor_get(v___x_1178_, 1);
v_proofInstInfo_1181_ = lean_ctor_get(v___x_1178_, 2);
v_inferType_1182_ = lean_ctor_get(v___x_1178_, 3);
v_getLevel_1183_ = lean_ctor_get(v___x_1178_, 4);
v_congrInfo_1184_ = lean_ctor_get(v___x_1178_, 5);
v_defEqI_1185_ = lean_ctor_get(v___x_1178_, 6);
v_extensions_1186_ = lean_ctor_get(v___x_1178_, 7);
v_issues_1187_ = lean_ctor_get(v___x_1178_, 8);
v_canon_1188_ = lean_ctor_get(v___x_1178_, 9);
v_debug_1189_ = lean_ctor_get_uint8(v___x_1178_, sizeof(void*)*10);
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1178_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1191_ = v___x_1178_;
v_isShared_1192_ = v_isSharedCheck_1224_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_canon_1188_);
lean_inc(v_issues_1187_);
lean_inc(v_extensions_1186_);
lean_inc(v_defEqI_1185_);
lean_inc(v_congrInfo_1184_);
lean_inc(v_getLevel_1183_);
lean_inc(v_inferType_1182_);
lean_inc(v_proofInstInfo_1181_);
lean_inc(v_maxFVar_1180_);
lean_inc(v_share_1179_);
lean_dec(v___x_1178_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1224_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
lean_object* v___x_1193_; lean_object* v___x_1195_; 
v___x_1193_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__0, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__0_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__0);
if (v_isShared_1192_ == 0)
{
lean_ctor_set(v___x_1191_, 0, v___x_1193_);
v___x_1195_ = v___x_1191_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v___x_1193_);
lean_ctor_set(v_reuseFailAlloc_1223_, 1, v_maxFVar_1180_);
lean_ctor_set(v_reuseFailAlloc_1223_, 2, v_proofInstInfo_1181_);
lean_ctor_set(v_reuseFailAlloc_1223_, 3, v_inferType_1182_);
lean_ctor_set(v_reuseFailAlloc_1223_, 4, v_getLevel_1183_);
lean_ctor_set(v_reuseFailAlloc_1223_, 5, v_congrInfo_1184_);
lean_ctor_set(v_reuseFailAlloc_1223_, 6, v_defEqI_1185_);
lean_ctor_set(v_reuseFailAlloc_1223_, 7, v_extensions_1186_);
lean_ctor_set(v_reuseFailAlloc_1223_, 8, v_issues_1187_);
lean_ctor_set(v_reuseFailAlloc_1223_, 9, v_canon_1188_);
lean_ctor_set_uint8(v_reuseFailAlloc_1223_, sizeof(void*)*10, v_debug_1189_);
v___x_1195_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; uint8_t v_debug_1198_; lean_object* v___x_1199_; lean_object* v_fst_1200_; lean_object* v_snd_1201_; lean_object* v___x_1202_; lean_object* v_maxFVar_1203_; lean_object* v_proofInstInfo_1204_; lean_object* v_inferType_1205_; lean_object* v_getLevel_1206_; lean_object* v_congrInfo_1207_; lean_object* v_defEqI_1208_; lean_object* v_extensions_1209_; lean_object* v_issues_1210_; lean_object* v_canon_1211_; uint8_t v_debug_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1221_; 
v___x_1196_ = lean_st_ref_set(v_a_1176_, v___x_1195_);
v___x_1197_ = lean_st_ref_get(v_a_1176_);
v_debug_1198_ = lean_ctor_get_uint8(v___x_1197_, sizeof(void*)*10);
lean_dec(v___x_1197_);
v___x_1199_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27(v_e_1174_, v_subst_1175_, v_debug_1198_, v_share_1179_);
v_fst_1200_ = lean_ctor_get(v___x_1199_, 0);
lean_inc(v_fst_1200_);
v_snd_1201_ = lean_ctor_get(v___x_1199_, 1);
lean_inc(v_snd_1201_);
lean_dec_ref(v___x_1199_);
v___x_1202_ = lean_st_ref_take(v_a_1176_);
v_maxFVar_1203_ = lean_ctor_get(v___x_1202_, 1);
v_proofInstInfo_1204_ = lean_ctor_get(v___x_1202_, 2);
v_inferType_1205_ = lean_ctor_get(v___x_1202_, 3);
v_getLevel_1206_ = lean_ctor_get(v___x_1202_, 4);
v_congrInfo_1207_ = lean_ctor_get(v___x_1202_, 5);
v_defEqI_1208_ = lean_ctor_get(v___x_1202_, 6);
v_extensions_1209_ = lean_ctor_get(v___x_1202_, 7);
v_issues_1210_ = lean_ctor_get(v___x_1202_, 8);
v_canon_1211_ = lean_ctor_get(v___x_1202_, 9);
v_debug_1212_ = lean_ctor_get_uint8(v___x_1202_, sizeof(void*)*10);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1202_);
if (v_isSharedCheck_1221_ == 0)
{
lean_object* v_unused_1222_; 
v_unused_1222_ = lean_ctor_get(v___x_1202_, 0);
lean_dec(v_unused_1222_);
v___x_1214_ = v___x_1202_;
v_isShared_1215_ = v_isSharedCheck_1221_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_canon_1211_);
lean_inc(v_issues_1210_);
lean_inc(v_extensions_1209_);
lean_inc(v_defEqI_1208_);
lean_inc(v_congrInfo_1207_);
lean_inc(v_getLevel_1206_);
lean_inc(v_inferType_1205_);
lean_inc(v_proofInstInfo_1204_);
lean_inc(v_maxFVar_1203_);
lean_dec(v___x_1202_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1221_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1217_; 
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 0, v_snd_1201_);
v___x_1217_ = v___x_1214_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_snd_1201_);
lean_ctor_set(v_reuseFailAlloc_1220_, 1, v_maxFVar_1203_);
lean_ctor_set(v_reuseFailAlloc_1220_, 2, v_proofInstInfo_1204_);
lean_ctor_set(v_reuseFailAlloc_1220_, 3, v_inferType_1205_);
lean_ctor_set(v_reuseFailAlloc_1220_, 4, v_getLevel_1206_);
lean_ctor_set(v_reuseFailAlloc_1220_, 5, v_congrInfo_1207_);
lean_ctor_set(v_reuseFailAlloc_1220_, 6, v_defEqI_1208_);
lean_ctor_set(v_reuseFailAlloc_1220_, 7, v_extensions_1209_);
lean_ctor_set(v_reuseFailAlloc_1220_, 8, v_issues_1210_);
lean_ctor_set(v_reuseFailAlloc_1220_, 9, v_canon_1211_);
lean_ctor_set_uint8(v_reuseFailAlloc_1220_, sizeof(void*)*10, v_debug_1212_);
v___x_1217_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1218_ = lean_st_ref_set(v_a_1176_, v___x_1217_);
v___x_1219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1219_, 0, v_fst_1200_);
return v___x_1219_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateS___redArg___boxed(lean_object* v_e_1225_, lean_object* v_subst_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_){
_start:
{
lean_object* v_res_1229_; 
v_res_1229_ = l_Lean_Meta_Sym_instantiateS___redArg(v_e_1225_, v_subst_1226_, v_a_1227_);
lean_dec(v_a_1227_);
lean_dec_ref(v_subst_1226_);
return v_res_1229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateS(lean_object* v_e_1230_, lean_object* v_subst_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_){
_start:
{
lean_object* v___x_1239_; 
v___x_1239_ = l_Lean_Meta_Sym_instantiateS___redArg(v_e_1230_, v_subst_1231_, v_a_1233_);
return v___x_1239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateS___boxed(lean_object* v_e_1240_, lean_object* v_subst_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l_Lean_Meta_Sym_instantiateS(v_e_1240_, v_subst_1241_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_, v_a_1246_, v_a_1247_);
lean_dec(v_a_1247_);
lean_dec_ref(v_a_1246_);
lean_dec(v_a_1245_);
lean_dec_ref(v_a_1244_);
lean_dec(v_a_1243_);
lean_dec_ref(v_a_1242_);
lean_dec_ref(v_subst_1241_);
return v_res_1249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS_loop_spec__0(lean_object* v_f_1250_, lean_object* v_a_1251_, uint8_t v___y_1252_, lean_object* v___y_1253_){
_start:
{
lean_object* v___y_1255_; 
if (v___y_1252_ == 0)
{
v___y_1255_ = v___y_1253_;
goto v___jp_1254_;
}
else
{
lean_object* v___x_1258_; lean_object* v_snd_1259_; lean_object* v___x_1260_; lean_object* v_snd_1261_; 
lean_inc_ref(v_f_1250_);
v___x_1258_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_f_1250_, v___y_1252_, v___y_1253_);
v_snd_1259_ = lean_ctor_get(v___x_1258_, 1);
lean_inc(v_snd_1259_);
lean_dec_ref(v___x_1258_);
lean_inc_ref(v_a_1251_);
v___x_1260_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_a_1251_, v___y_1252_, v_snd_1259_);
v_snd_1261_ = lean_ctor_get(v___x_1260_, 1);
lean_inc(v_snd_1261_);
lean_dec_ref(v___x_1260_);
v___y_1255_ = v_snd_1261_;
goto v___jp_1254_;
}
v___jp_1254_:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1256_ = l_Lean_Expr_app___override(v_f_1250_, v_a_1251_);
v___x_1257_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1256_, v___y_1255_);
return v___x_1257_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS_loop_spec__0___boxed(lean_object* v_f_1262_, lean_object* v_a_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_){
_start:
{
uint8_t v___y_1244__boxed_1266_; lean_object* v_res_1267_; 
v___y_1244__boxed_1266_ = lean_unbox(v___y_1264_);
v_res_1267_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS_loop_spec__0(v_f_1262_, v_a_1263_, v___y_1244__boxed_1266_, v___y_1265_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS_loop(lean_object* v_revArgs_1268_, lean_object* v_start_1269_, lean_object* v_b_1270_, lean_object* v_i_1271_, uint8_t v_a_1272_, lean_object* v_a_1273_){
_start:
{
uint8_t v___x_1274_; 
v___x_1274_ = lean_nat_dec_le(v_i_1271_, v_start_1269_);
if (v___x_1274_ == 0)
{
lean_object* v___x_1275_; lean_object* v_i_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v_fst_1280_; lean_object* v_snd_1281_; 
v___x_1275_ = lean_unsigned_to_nat(1u);
v_i_1276_ = lean_nat_sub(v_i_1271_, v___x_1275_);
lean_dec(v_i_1271_);
v___x_1277_ = l_Lean_instInhabitedExpr;
v___x_1278_ = lean_array_get_borrowed(v___x_1277_, v_revArgs_1268_, v_i_1276_);
lean_inc(v___x_1278_);
v___x_1279_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS_loop_spec__0(v_b_1270_, v___x_1278_, v_a_1272_, v_a_1273_);
v_fst_1280_ = lean_ctor_get(v___x_1279_, 0);
lean_inc(v_fst_1280_);
v_snd_1281_ = lean_ctor_get(v___x_1279_, 1);
lean_inc(v_snd_1281_);
lean_dec_ref(v___x_1279_);
v_b_1270_ = v_fst_1280_;
v_i_1271_ = v_i_1276_;
v_a_1273_ = v_snd_1281_;
goto _start;
}
else
{
lean_object* v___x_1283_; 
lean_dec(v_i_1271_);
v___x_1283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1283_, 0, v_b_1270_);
lean_ctor_set(v___x_1283_, 1, v_a_1273_);
return v___x_1283_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS_loop___boxed(lean_object* v_revArgs_1284_, lean_object* v_start_1285_, lean_object* v_b_1286_, lean_object* v_i_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_){
_start:
{
uint8_t v_a_boxed_1290_; lean_object* v_res_1291_; 
v_a_boxed_1290_ = lean_unbox(v_a_1288_);
v_res_1291_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS_loop(v_revArgs_1284_, v_start_1285_, v_b_1286_, v_i_1287_, v_a_boxed_1290_, v_a_1289_);
lean_dec(v_start_1285_);
lean_dec_ref(v_revArgs_1284_);
return v_res_1291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS(lean_object* v_f_1292_, lean_object* v_beginIdx_1293_, lean_object* v_endIdx_1294_, lean_object* v_revArgs_1295_, uint8_t v_a_1296_, lean_object* v_a_1297_){
_start:
{
lean_object* v___x_1298_; 
v___x_1298_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS_loop(v_revArgs_1295_, v_beginIdx_1293_, v_f_1292_, v_endIdx_1294_, v_a_1296_, v_a_1297_);
return v___x_1298_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS___boxed(lean_object* v_f_1299_, lean_object* v_beginIdx_1300_, lean_object* v_endIdx_1301_, lean_object* v_revArgs_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_){
_start:
{
uint8_t v_a_boxed_1305_; lean_object* v_res_1306_; 
v_a_boxed_1305_ = lean_unbox(v_a_1303_);
v_res_1306_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS(v_f_1299_, v_beginIdx_1300_, v_endIdx_1301_, v_revArgs_1302_, v_a_boxed_1305_, v_a_1304_);
lean_dec_ref(v_revArgs_1302_);
lean_dec(v_beginIdx_1300_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_go(lean_object* v_revArgs_1307_, lean_object* v_sz_1308_, lean_object* v_e_1309_, lean_object* v_i_1310_, uint8_t v_a_1311_, lean_object* v_a_1312_){
_start:
{
switch(lean_obj_tag(v_e_1309_))
{
case 6:
{
lean_object* v_body_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; uint8_t v___x_1316_; 
v_body_1313_ = lean_ctor_get(v_e_1309_, 2);
lean_inc_ref(v_body_1313_);
lean_dec_ref(v_e_1309_);
v___x_1314_ = lean_unsigned_to_nat(1u);
v___x_1315_ = lean_nat_add(v_i_1310_, v___x_1314_);
lean_dec(v_i_1310_);
v___x_1316_ = lean_nat_dec_lt(v___x_1315_, v_sz_1308_);
if (v___x_1316_ == 0)
{
lean_object* v___x_1317_; 
lean_dec(v___x_1315_);
v___x_1317_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27(v_body_1313_, v_revArgs_1307_, v_a_1311_, v_a_1312_);
return v___x_1317_;
}
else
{
v_e_1309_ = v_body_1313_;
v_i_1310_ = v___x_1315_;
goto _start;
}
}
case 10:
{
lean_object* v_expr_1319_; 
v_expr_1319_ = lean_ctor_get(v_e_1309_, 1);
lean_inc_ref(v_expr_1319_);
lean_dec_ref(v_e_1309_);
v_e_1309_ = v_expr_1319_;
goto _start;
}
default: 
{
lean_object* v_n_1321_; lean_object* v___x_1322_; lean_object* v_fst_1323_; lean_object* v_snd_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; 
v_n_1321_ = lean_nat_sub(v_sz_1308_, v_i_1310_);
lean_dec(v_i_1310_);
v___x_1322_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27(v_e_1309_, v_n_1321_, v_sz_1308_, v_revArgs_1307_, v_a_1311_, v_a_1312_);
v_fst_1323_ = lean_ctor_get(v___x_1322_, 0);
lean_inc(v_fst_1323_);
v_snd_1324_ = lean_ctor_get(v___x_1322_, 1);
lean_inc(v_snd_1324_);
lean_dec_ref(v___x_1322_);
v___x_1325_ = lean_unsigned_to_nat(0u);
v___x_1326_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS_loop(v_revArgs_1307_, v___x_1325_, v_fst_1323_, v_n_1321_, v_a_1311_, v_snd_1324_);
return v___x_1326_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_go___boxed(lean_object* v_revArgs_1327_, lean_object* v_sz_1328_, lean_object* v_e_1329_, lean_object* v_i_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_){
_start:
{
uint8_t v_a_boxed_1333_; lean_object* v_res_1334_; 
v_a_boxed_1333_ = lean_unbox(v_a_1331_);
v_res_1334_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_go(v_revArgs_1327_, v_sz_1328_, v_e_1329_, v_i_1330_, v_a_boxed_1333_, v_a_1332_);
lean_dec(v_sz_1328_);
lean_dec_ref(v_revArgs_1327_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS(lean_object* v_f_1335_, lean_object* v_revArgs_1336_, uint8_t v_a_1337_, lean_object* v_a_1338_){
_start:
{
lean_object* v_sz_1339_; lean_object* v___x_1340_; uint8_t v___x_1341_; 
v_sz_1339_ = lean_array_get_size(v_revArgs_1336_);
v___x_1340_ = lean_unsigned_to_nat(0u);
v___x_1341_ = lean_nat_dec_eq(v_sz_1339_, v___x_1340_);
if (v___x_1341_ == 0)
{
lean_object* v___x_1342_; 
v___x_1342_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_go(v_revArgs_1336_, v_sz_1339_, v_f_1335_, v___x_1340_, v_a_1337_, v_a_1338_);
return v___x_1342_;
}
else
{
lean_object* v___x_1343_; 
v___x_1343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1343_, 0, v_f_1335_);
lean_ctor_set(v___x_1343_, 1, v_a_1338_);
return v___x_1343_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS___boxed(lean_object* v_f_1344_, lean_object* v_revArgs_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_){
_start:
{
uint8_t v_a_boxed_1348_; lean_object* v_res_1349_; 
v_a_boxed_1348_ = lean_unbox(v_a_1346_);
v_res_1349_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS(v_f_1344_, v_revArgs_1345_, v_a_boxed_1348_, v_a_1347_);
lean_dec_ref(v_revArgs_1345_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_1350_, lean_object* v_x_1351_){
_start:
{
if (lean_obj_tag(v_x_1351_) == 0)
{
return v_x_1350_;
}
else
{
lean_object* v_key_1352_; lean_object* v_value_1353_; lean_object* v_tail_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1381_; 
v_key_1352_ = lean_ctor_get(v_x_1351_, 0);
v_value_1353_ = lean_ctor_get(v_x_1351_, 1);
v_tail_1354_ = lean_ctor_get(v_x_1351_, 2);
v_isSharedCheck_1381_ = !lean_is_exclusive(v_x_1351_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1356_ = v_x_1351_;
v_isShared_1357_ = v_isSharedCheck_1381_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_tail_1354_);
lean_inc(v_value_1353_);
lean_inc(v_key_1352_);
lean_dec(v_x_1351_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1381_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v_fst_1358_; lean_object* v_snd_1359_; lean_object* v___x_1360_; uint64_t v___x_1361_; uint64_t v___x_1362_; uint64_t v___x_1363_; uint64_t v___x_1364_; uint64_t v___x_1365_; uint64_t v_fold_1366_; uint64_t v___x_1367_; uint64_t v___x_1368_; uint64_t v___x_1369_; size_t v___x_1370_; size_t v___x_1371_; size_t v___x_1372_; size_t v___x_1373_; size_t v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1377_; 
v_fst_1358_ = lean_ctor_get(v_key_1352_, 0);
v_snd_1359_ = lean_ctor_get(v_key_1352_, 1);
v___x_1360_ = lean_array_get_size(v_x_1350_);
v___x_1361_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_1358_);
v___x_1362_ = lean_uint64_of_nat(v_snd_1359_);
v___x_1363_ = lean_uint64_mix_hash(v___x_1361_, v___x_1362_);
v___x_1364_ = 32ULL;
v___x_1365_ = lean_uint64_shift_right(v___x_1363_, v___x_1364_);
v_fold_1366_ = lean_uint64_xor(v___x_1363_, v___x_1365_);
v___x_1367_ = 16ULL;
v___x_1368_ = lean_uint64_shift_right(v_fold_1366_, v___x_1367_);
v___x_1369_ = lean_uint64_xor(v_fold_1366_, v___x_1368_);
v___x_1370_ = lean_uint64_to_usize(v___x_1369_);
v___x_1371_ = lean_usize_of_nat(v___x_1360_);
v___x_1372_ = ((size_t)1ULL);
v___x_1373_ = lean_usize_sub(v___x_1371_, v___x_1372_);
v___x_1374_ = lean_usize_land(v___x_1370_, v___x_1373_);
v___x_1375_ = lean_array_uget_borrowed(v_x_1350_, v___x_1374_);
lean_inc(v___x_1375_);
if (v_isShared_1357_ == 0)
{
lean_ctor_set(v___x_1356_, 2, v___x_1375_);
v___x_1377_ = v___x_1356_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_key_1352_);
lean_ctor_set(v_reuseFailAlloc_1380_, 1, v_value_1353_);
lean_ctor_set(v_reuseFailAlloc_1380_, 2, v___x_1375_);
v___x_1377_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
lean_object* v___x_1378_; 
v___x_1378_ = lean_array_uset(v_x_1350_, v___x_1374_, v___x_1377_);
v_x_1350_ = v___x_1378_;
v_x_1351_ = v_tail_1354_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2___redArg(lean_object* v_i_1382_, lean_object* v_source_1383_, lean_object* v_target_1384_){
_start:
{
lean_object* v___x_1385_; uint8_t v___x_1386_; 
v___x_1385_ = lean_array_get_size(v_source_1383_);
v___x_1386_ = lean_nat_dec_lt(v_i_1382_, v___x_1385_);
if (v___x_1386_ == 0)
{
lean_dec_ref(v_source_1383_);
lean_dec(v_i_1382_);
return v_target_1384_;
}
else
{
lean_object* v_es_1387_; lean_object* v___x_1388_; lean_object* v_source_1389_; lean_object* v_target_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; 
v_es_1387_ = lean_array_fget(v_source_1383_, v_i_1382_);
v___x_1388_ = lean_box(0);
v_source_1389_ = lean_array_fset(v_source_1383_, v_i_1382_, v___x_1388_);
v_target_1390_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3___redArg(v_target_1384_, v_es_1387_);
v___x_1391_ = lean_unsigned_to_nat(1u);
v___x_1392_ = lean_nat_add(v_i_1382_, v___x_1391_);
lean_dec(v_i_1382_);
v_i_1382_ = v___x_1392_;
v_source_1383_ = v_source_1389_;
v_target_1384_ = v_target_1390_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1___redArg(lean_object* v_data_1394_){
_start:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v_nbuckets_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; 
v___x_1395_ = lean_array_get_size(v_data_1394_);
v___x_1396_ = lean_unsigned_to_nat(2u);
v_nbuckets_1397_ = lean_nat_mul(v___x_1395_, v___x_1396_);
v___x_1398_ = lean_unsigned_to_nat(0u);
v___x_1399_ = lean_box(0);
v___x_1400_ = lean_mk_array(v_nbuckets_1397_, v___x_1399_);
v___x_1401_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2___redArg(v___x_1398_, v_data_1394_, v___x_1400_);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(lean_object* v_a_1402_, lean_object* v_b_1403_, lean_object* v_x_1404_){
_start:
{
if (lean_obj_tag(v_x_1404_) == 0)
{
lean_dec(v_b_1403_);
lean_dec_ref(v_a_1402_);
return v_x_1404_;
}
else
{
lean_object* v_key_1405_; lean_object* v_value_1406_; lean_object* v_tail_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1426_; 
v_key_1405_ = lean_ctor_get(v_x_1404_, 0);
v_value_1406_ = lean_ctor_get(v_x_1404_, 1);
v_tail_1407_ = lean_ctor_get(v_x_1404_, 2);
v_isSharedCheck_1426_ = !lean_is_exclusive(v_x_1404_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1409_ = v_x_1404_;
v_isShared_1410_ = v_isSharedCheck_1426_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_tail_1407_);
lean_inc(v_value_1406_);
lean_inc(v_key_1405_);
lean_dec(v_x_1404_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1426_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
uint8_t v___y_1412_; lean_object* v_fst_1420_; lean_object* v_snd_1421_; lean_object* v_fst_1422_; lean_object* v_snd_1423_; uint8_t v___x_1424_; 
v_fst_1420_ = lean_ctor_get(v_key_1405_, 0);
v_snd_1421_ = lean_ctor_get(v_key_1405_, 1);
v_fst_1422_ = lean_ctor_get(v_a_1402_, 0);
v_snd_1423_ = lean_ctor_get(v_a_1402_, 1);
v___x_1424_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_1420_, v_fst_1422_);
if (v___x_1424_ == 0)
{
v___y_1412_ = v___x_1424_;
goto v___jp_1411_;
}
else
{
uint8_t v___x_1425_; 
v___x_1425_ = lean_nat_dec_eq(v_snd_1421_, v_snd_1423_);
v___y_1412_ = v___x_1425_;
goto v___jp_1411_;
}
v___jp_1411_:
{
if (v___y_1412_ == 0)
{
lean_object* v___x_1413_; lean_object* v___x_1415_; 
v___x_1413_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(v_a_1402_, v_b_1403_, v_tail_1407_);
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 2, v___x_1413_);
v___x_1415_ = v___x_1409_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_key_1405_);
lean_ctor_set(v_reuseFailAlloc_1416_, 1, v_value_1406_);
lean_ctor_set(v_reuseFailAlloc_1416_, 2, v___x_1413_);
v___x_1415_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
return v___x_1415_;
}
}
else
{
lean_object* v___x_1418_; 
lean_dec(v_value_1406_);
lean_dec(v_key_1405_);
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 1, v_b_1403_);
lean_ctor_set(v___x_1409_, 0, v_a_1402_);
v___x_1418_ = v___x_1409_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_a_1402_);
lean_ctor_set(v_reuseFailAlloc_1419_, 1, v_b_1403_);
lean_ctor_set(v_reuseFailAlloc_1419_, 2, v_tail_1407_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(lean_object* v_a_1427_, lean_object* v_x_1428_){
_start:
{
if (lean_obj_tag(v_x_1428_) == 0)
{
uint8_t v___x_1429_; 
v___x_1429_ = 0;
return v___x_1429_;
}
else
{
lean_object* v_key_1430_; lean_object* v_tail_1431_; uint8_t v___y_1433_; lean_object* v_fst_1435_; lean_object* v_snd_1436_; lean_object* v_fst_1437_; lean_object* v_snd_1438_; uint8_t v___x_1439_; 
v_key_1430_ = lean_ctor_get(v_x_1428_, 0);
v_tail_1431_ = lean_ctor_get(v_x_1428_, 2);
v_fst_1435_ = lean_ctor_get(v_key_1430_, 0);
v_snd_1436_ = lean_ctor_get(v_key_1430_, 1);
v_fst_1437_ = lean_ctor_get(v_a_1427_, 0);
v_snd_1438_ = lean_ctor_get(v_a_1427_, 1);
v___x_1439_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_1435_, v_fst_1437_);
if (v___x_1439_ == 0)
{
v___y_1433_ = v___x_1439_;
goto v___jp_1432_;
}
else
{
uint8_t v___x_1440_; 
v___x_1440_ = lean_nat_dec_eq(v_snd_1436_, v_snd_1438_);
v___y_1433_ = v___x_1440_;
goto v___jp_1432_;
}
v___jp_1432_:
{
if (v___y_1433_ == 0)
{
v_x_1428_ = v_tail_1431_;
goto _start;
}
else
{
return v___y_1433_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg___boxed(lean_object* v_a_1441_, lean_object* v_x_1442_){
_start:
{
uint8_t v_res_1443_; lean_object* v_r_1444_; 
v_res_1443_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_a_1441_, v_x_1442_);
lean_dec(v_x_1442_);
lean_dec_ref(v_a_1441_);
v_r_1444_ = lean_box(v_res_1443_);
return v_r_1444_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0___redArg(lean_object* v_m_1445_, lean_object* v_a_1446_, lean_object* v_b_1447_){
_start:
{
lean_object* v_size_1448_; lean_object* v_buckets_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1496_; 
v_size_1448_ = lean_ctor_get(v_m_1445_, 0);
v_buckets_1449_ = lean_ctor_get(v_m_1445_, 1);
v_isSharedCheck_1496_ = !lean_is_exclusive(v_m_1445_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1451_ = v_m_1445_;
v_isShared_1452_ = v_isSharedCheck_1496_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_buckets_1449_);
lean_inc(v_size_1448_);
lean_dec(v_m_1445_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1496_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v_fst_1453_; lean_object* v_snd_1454_; lean_object* v___x_1455_; uint64_t v___x_1456_; uint64_t v___x_1457_; uint64_t v___x_1458_; uint64_t v___x_1459_; uint64_t v___x_1460_; uint64_t v_fold_1461_; uint64_t v___x_1462_; uint64_t v___x_1463_; uint64_t v___x_1464_; size_t v___x_1465_; size_t v___x_1466_; size_t v___x_1467_; size_t v___x_1468_; size_t v___x_1469_; lean_object* v_bkt_1470_; uint8_t v___x_1471_; 
v_fst_1453_ = lean_ctor_get(v_a_1446_, 0);
v_snd_1454_ = lean_ctor_get(v_a_1446_, 1);
v___x_1455_ = lean_array_get_size(v_buckets_1449_);
v___x_1456_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_1453_);
v___x_1457_ = lean_uint64_of_nat(v_snd_1454_);
v___x_1458_ = lean_uint64_mix_hash(v___x_1456_, v___x_1457_);
v___x_1459_ = 32ULL;
v___x_1460_ = lean_uint64_shift_right(v___x_1458_, v___x_1459_);
v_fold_1461_ = lean_uint64_xor(v___x_1458_, v___x_1460_);
v___x_1462_ = 16ULL;
v___x_1463_ = lean_uint64_shift_right(v_fold_1461_, v___x_1462_);
v___x_1464_ = lean_uint64_xor(v_fold_1461_, v___x_1463_);
v___x_1465_ = lean_uint64_to_usize(v___x_1464_);
v___x_1466_ = lean_usize_of_nat(v___x_1455_);
v___x_1467_ = ((size_t)1ULL);
v___x_1468_ = lean_usize_sub(v___x_1466_, v___x_1467_);
v___x_1469_ = lean_usize_land(v___x_1465_, v___x_1468_);
v_bkt_1470_ = lean_array_uget_borrowed(v_buckets_1449_, v___x_1469_);
v___x_1471_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_a_1446_, v_bkt_1470_);
if (v___x_1471_ == 0)
{
lean_object* v___x_1472_; lean_object* v_size_x27_1473_; lean_object* v___x_1474_; lean_object* v_buckets_x27_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; uint8_t v___x_1481_; 
v___x_1472_ = lean_unsigned_to_nat(1u);
v_size_x27_1473_ = lean_nat_add(v_size_1448_, v___x_1472_);
lean_dec(v_size_1448_);
lean_inc(v_bkt_1470_);
v___x_1474_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1474_, 0, v_a_1446_);
lean_ctor_set(v___x_1474_, 1, v_b_1447_);
lean_ctor_set(v___x_1474_, 2, v_bkt_1470_);
v_buckets_x27_1475_ = lean_array_uset(v_buckets_1449_, v___x_1469_, v___x_1474_);
v___x_1476_ = lean_unsigned_to_nat(4u);
v___x_1477_ = lean_nat_mul(v_size_x27_1473_, v___x_1476_);
v___x_1478_ = lean_unsigned_to_nat(3u);
v___x_1479_ = lean_nat_div(v___x_1477_, v___x_1478_);
lean_dec(v___x_1477_);
v___x_1480_ = lean_array_get_size(v_buckets_x27_1475_);
v___x_1481_ = lean_nat_dec_le(v___x_1479_, v___x_1480_);
lean_dec(v___x_1479_);
if (v___x_1481_ == 0)
{
lean_object* v_val_1482_; lean_object* v___x_1484_; 
v_val_1482_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1___redArg(v_buckets_x27_1475_);
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 1, v_val_1482_);
lean_ctor_set(v___x_1451_, 0, v_size_x27_1473_);
v___x_1484_ = v___x_1451_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_size_x27_1473_);
lean_ctor_set(v_reuseFailAlloc_1485_, 1, v_val_1482_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
else
{
lean_object* v___x_1487_; 
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 1, v_buckets_x27_1475_);
lean_ctor_set(v___x_1451_, 0, v_size_x27_1473_);
v___x_1487_ = v___x_1451_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_size_x27_1473_);
lean_ctor_set(v_reuseFailAlloc_1488_, 1, v_buckets_x27_1475_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
return v___x_1487_;
}
}
}
else
{
lean_object* v___x_1489_; lean_object* v_buckets_x27_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1494_; 
lean_inc(v_bkt_1470_);
v___x_1489_ = lean_box(0);
v_buckets_x27_1490_ = lean_array_uset(v_buckets_1449_, v___x_1469_, v___x_1489_);
v___x_1491_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(v_a_1446_, v_b_1447_, v_bkt_1470_);
v___x_1492_ = lean_array_uset(v_buckets_x27_1490_, v___x_1469_, v___x_1491_);
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 1, v___x_1492_);
v___x_1494_ = v___x_1451_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_size_1448_);
lean_ctor_set(v_reuseFailAlloc_1495_, 1, v___x_1492_);
v___x_1494_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
return v___x_1494_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(lean_object* v_key_1497_, lean_object* v_r_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_){
_start:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; 
lean_inc_ref(v_r_1498_);
v___x_1501_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1499_, v_key_1497_, v_r_1498_);
v___x_1502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1502_, 0, v_r_1498_);
lean_ctor_set(v___x_1502_, 1, v___x_1501_);
v___x_1503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1503_, 0, v___x_1502_);
lean_ctor_set(v___x_1503_, 1, v_a_1500_);
return v___x_1503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save(lean_object* v_key_1504_, lean_object* v_r_1505_, lean_object* v_a_1506_, uint8_t v_a_1507_, lean_object* v_a_1508_){
_start:
{
lean_object* v___x_1509_; 
v___x_1509_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_1504_, v_r_1505_, v_a_1506_, v_a_1508_);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___boxed(lean_object* v_key_1510_, lean_object* v_r_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_){
_start:
{
uint8_t v_a_boxed_1515_; lean_object* v_res_1516_; 
v_a_boxed_1515_ = lean_unbox(v_a_1513_);
v_res_1516_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save(v_key_1510_, v_r_1511_, v_a_1512_, v_a_boxed_1515_, v_a_1514_);
return v_res_1516_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0(lean_object* v_00_u03b2_1517_, lean_object* v_m_1518_, lean_object* v_a_1519_, lean_object* v_b_1520_){
_start:
{
lean_object* v___x_1521_; 
v___x_1521_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0___redArg(v_m_1518_, v_a_1519_, v_b_1520_);
return v___x_1521_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0(lean_object* v_00_u03b2_1522_, lean_object* v_a_1523_, lean_object* v_x_1524_){
_start:
{
uint8_t v___x_1525_; 
v___x_1525_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_a_1523_, v_x_1524_);
return v___x_1525_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1526_, lean_object* v_a_1527_, lean_object* v_x_1528_){
_start:
{
uint8_t v_res_1529_; lean_object* v_r_1530_; 
v_res_1529_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0(v_00_u03b2_1526_, v_a_1527_, v_x_1528_);
lean_dec(v_x_1528_);
lean_dec_ref(v_a_1527_);
v_r_1530_ = lean_box(v_res_1529_);
return v_r_1530_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1(lean_object* v_00_u03b2_1531_, lean_object* v_data_1532_){
_start:
{
lean_object* v___x_1533_; 
v___x_1533_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1___redArg(v_data_1532_);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2(lean_object* v_00_u03b2_1534_, lean_object* v_a_1535_, lean_object* v_b_1536_, lean_object* v_x_1537_){
_start:
{
lean_object* v___x_1538_; 
v___x_1538_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(v_a_1535_, v_b_1536_, v_x_1537_);
return v___x_1538_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1539_, lean_object* v_i_1540_, lean_object* v_source_1541_, lean_object* v_target_1542_){
_start:
{
lean_object* v___x_1543_; 
v___x_1543_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2___redArg(v_i_1540_, v_source_1541_, v_target_1542_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1544_, lean_object* v_x_1545_, lean_object* v_x_1546_){
_start:
{
lean_object* v___x_1547_; 
v___x_1547_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1545_, v_x_1546_);
return v___x_1547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0___redArg(lean_object* v_idx_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_){
_start:
{
lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v_fst_1553_; lean_object* v_snd_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1562_; 
v___x_1551_ = l_Lean_Expr_bvar___override(v_idx_1548_);
v___x_1552_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1551_, v___y_1550_);
v_fst_1553_ = lean_ctor_get(v___x_1552_, 0);
v_snd_1554_ = lean_ctor_get(v___x_1552_, 1);
v_isSharedCheck_1562_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1562_ == 0)
{
v___x_1556_ = v___x_1552_;
v_isShared_1557_ = v_isSharedCheck_1562_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_snd_1554_);
lean_inc(v_fst_1553_);
lean_dec(v___x_1552_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1562_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v___x_1559_; 
if (v_isShared_1557_ == 0)
{
lean_ctor_set(v___x_1556_, 1, v___y_1549_);
v___x_1559_ = v___x_1556_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_fst_1553_);
lean_ctor_set(v_reuseFailAlloc_1561_, 1, v___y_1549_);
v___x_1559_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
lean_object* v___x_1560_; 
v___x_1560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1560_, 0, v___x_1559_);
lean_ctor_set(v___x_1560_, 1, v_snd_1554_);
return v___x_1560_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0(lean_object* v_idx_1563_, lean_object* v___y_1564_, uint8_t v___y_1565_, lean_object* v___y_1566_){
_start:
{
lean_object* v___x_1567_; 
v___x_1567_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0___redArg(v_idx_1563_, v___y_1564_, v___y_1566_);
return v___x_1567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0___boxed(lean_object* v_idx_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_){
_start:
{
uint8_t v___y_1291__boxed_1572_; lean_object* v_res_1573_; 
v___y_1291__boxed_1572_ = lean_unbox(v___y_1570_);
v_res_1573_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0(v_idx_1568_, v___y_1569_, v___y_1291__boxed_1572_, v___y_1571_);
return v_res_1573_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(lean_object* v_subst_1574_, lean_object* v_e_1575_, lean_object* v_bidx_1576_, lean_object* v_offset_1577_, lean_object* v_a_1578_, uint8_t v_a_1579_, lean_object* v_a_1580_){
_start:
{
uint8_t v___x_1581_; 
v___x_1581_ = lean_nat_dec_le(v_offset_1577_, v_bidx_1576_);
if (v___x_1581_ == 0)
{
lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___x_1582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1582_, 0, v_e_1575_);
lean_ctor_set(v___x_1582_, 1, v_a_1578_);
v___x_1583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1583_, 0, v___x_1582_);
lean_ctor_set(v___x_1583_, 1, v_a_1580_);
return v___x_1583_;
}
else
{
lean_object* v_n_1584_; lean_object* v___x_1585_; uint8_t v___x_1586_; 
lean_dec_ref(v_e_1575_);
v_n_1584_ = lean_array_get_size(v_subst_1574_);
v___x_1585_ = lean_nat_add(v_offset_1577_, v_n_1584_);
v___x_1586_ = lean_nat_dec_lt(v_bidx_1576_, v___x_1585_);
lean_dec(v___x_1585_);
if (v___x_1586_ == 0)
{
lean_object* v___x_1587_; lean_object* v___x_1588_; 
v___x_1587_ = lean_nat_sub(v_bidx_1576_, v_n_1584_);
v___x_1588_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0___redArg(v___x_1587_, v_a_1578_, v_a_1580_);
return v___x_1588_;
}
else
{
lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v_v_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v_fst_1596_; lean_object* v_snd_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1605_; 
v___x_1589_ = lean_nat_sub(v_bidx_1576_, v_offset_1577_);
v___x_1590_ = lean_nat_sub(v_n_1584_, v___x_1589_);
lean_dec(v___x_1589_);
v___x_1591_ = lean_unsigned_to_nat(1u);
v___x_1592_ = lean_nat_sub(v___x_1590_, v___x_1591_);
lean_dec(v___x_1590_);
v_v_1593_ = lean_array_fget_borrowed(v_subst_1574_, v___x_1592_);
lean_dec(v___x_1592_);
v___x_1594_ = lean_unsigned_to_nat(0u);
lean_inc(v_v_1593_);
v___x_1595_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(v_v_1593_, v___x_1594_, v_offset_1577_, v_a_1579_, v_a_1580_);
v_fst_1596_ = lean_ctor_get(v___x_1595_, 0);
v_snd_1597_ = lean_ctor_get(v___x_1595_, 1);
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1599_ = v___x_1595_;
v_isShared_1600_ = v_isSharedCheck_1605_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_snd_1597_);
lean_inc(v_fst_1596_);
lean_dec(v___x_1595_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1605_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___x_1602_; 
if (v_isShared_1600_ == 0)
{
lean_ctor_set(v___x_1599_, 1, v_a_1578_);
v___x_1602_ = v___x_1599_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v_fst_1596_);
lean_ctor_set(v_reuseFailAlloc_1604_, 1, v_a_1578_);
v___x_1602_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
lean_object* v___x_1603_; 
v___x_1603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1603_, 0, v___x_1602_);
lean_ctor_set(v___x_1603_, 1, v_snd_1597_);
return v___x_1603_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar___boxed(lean_object* v_subst_1606_, lean_object* v_e_1607_, lean_object* v_bidx_1608_, lean_object* v_offset_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_){
_start:
{
uint8_t v_a_boxed_1613_; lean_object* v_res_1614_; 
v_a_boxed_1613_ = lean_unbox(v_a_1611_);
v_res_1614_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(v_subst_1606_, v_e_1607_, v_bidx_1608_, v_offset_1609_, v_a_1610_, v_a_boxed_1613_, v_a_1612_);
lean_dec(v_offset_1609_);
lean_dec(v_bidx_1608_);
lean_dec_ref(v_subst_1606_);
return v_res_1614_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__3(void){
_start:
{
lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1618_ = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__2));
v___x_1619_ = lean_unsigned_to_nat(25u);
v___x_1620_ = lean_unsigned_to_nat(148u);
v___x_1621_ = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__1));
v___x_1622_ = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__0));
v___x_1623_ = l_mkPanicMessageWithDecl(v___x_1622_, v___x_1621_, v___x_1620_, v___x_1619_, v___x_1618_);
return v___x_1623_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__1(void){
_start:
{
lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1625_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__2));
v___x_1626_ = lean_unsigned_to_nat(11u);
v___x_1627_ = lean_unsigned_to_nat(179u);
v___x_1628_ = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__0));
v___x_1629_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__3));
v___x_1630_ = l_mkPanicMessageWithDecl(v___x_1629_, v___x_1628_, v___x_1627_, v___x_1626_, v___x_1625_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta(lean_object* v_subst_1631_, lean_object* v_e_1632_, lean_object* v_f_1633_, lean_object* v_argsRev_1634_, lean_object* v_offset_1635_, uint8_t v_modified_1636_, lean_object* v_a_1637_, uint8_t v_a_1638_, lean_object* v_a_1639_){
_start:
{
switch(lean_obj_tag(v_f_1633_))
{
case 5:
{
lean_object* v_fn_1640_; lean_object* v_arg_1641_; lean_object* v___x_1642_; lean_object* v_fst_1643_; lean_object* v_snd_1644_; lean_object* v_fst_1645_; lean_object* v_snd_1646_; lean_object* v___x_1647_; 
v_fn_1640_ = lean_ctor_get(v_f_1633_, 0);
lean_inc_ref(v_fn_1640_);
v_arg_1641_ = lean_ctor_get(v_f_1633_, 1);
lean_inc_ref_n(v_arg_1641_, 2);
lean_dec_ref(v_f_1633_);
lean_inc(v_offset_1635_);
v___x_1642_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1631_, v_arg_1641_, v_offset_1635_, v_a_1637_, v_a_1638_, v_a_1639_);
v_fst_1643_ = lean_ctor_get(v___x_1642_, 0);
lean_inc(v_fst_1643_);
v_snd_1644_ = lean_ctor_get(v___x_1642_, 1);
lean_inc(v_snd_1644_);
lean_dec_ref(v___x_1642_);
v_fst_1645_ = lean_ctor_get(v_fst_1643_, 0);
lean_inc_n(v_fst_1645_, 2);
v_snd_1646_ = lean_ctor_get(v_fst_1643_, 1);
lean_inc(v_snd_1646_);
lean_dec(v_fst_1643_);
v___x_1647_ = lean_array_push(v_argsRev_1634_, v_fst_1645_);
if (v_modified_1636_ == 0)
{
uint8_t v___x_1648_; 
v___x_1648_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_1641_, v_fst_1645_);
lean_dec(v_fst_1645_);
lean_dec_ref(v_arg_1641_);
if (v___x_1648_ == 0)
{
uint8_t v___x_1649_; 
v___x_1649_ = 1;
v_f_1633_ = v_fn_1640_;
v_argsRev_1634_ = v___x_1647_;
v_modified_1636_ = v___x_1649_;
v_a_1637_ = v_snd_1646_;
v_a_1639_ = v_snd_1644_;
goto _start;
}
else
{
v_f_1633_ = v_fn_1640_;
v_argsRev_1634_ = v___x_1647_;
v_a_1637_ = v_snd_1646_;
v_a_1639_ = v_snd_1644_;
goto _start;
}
}
else
{
lean_dec(v_fst_1645_);
lean_dec_ref(v_arg_1641_);
v_f_1633_ = v_fn_1640_;
v_argsRev_1634_ = v___x_1647_;
v_a_1637_ = v_snd_1646_;
v_a_1639_ = v_snd_1644_;
goto _start;
}
}
case 0:
{
lean_object* v_deBruijnIndex_1653_; lean_object* v___x_1654_; lean_object* v_fst_1655_; lean_object* v_snd_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1685_; 
v_deBruijnIndex_1653_ = lean_ctor_get(v_f_1633_, 0);
lean_inc_ref(v_f_1633_);
v___x_1654_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(v_subst_1631_, v_f_1633_, v_deBruijnIndex_1653_, v_offset_1635_, v_a_1637_, v_a_1638_, v_a_1639_);
lean_dec(v_offset_1635_);
v_fst_1655_ = lean_ctor_get(v___x_1654_, 0);
v_snd_1656_ = lean_ctor_get(v___x_1654_, 1);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___x_1654_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1658_ = v___x_1654_;
v_isShared_1659_ = v_isSharedCheck_1685_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_snd_1656_);
lean_inc(v_fst_1655_);
lean_dec(v___x_1654_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1685_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v_fst_1660_; lean_object* v_snd_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1684_; 
v_fst_1660_ = lean_ctor_get(v_fst_1655_, 0);
v_snd_1661_ = lean_ctor_get(v_fst_1655_, 1);
v_isSharedCheck_1684_ = !lean_is_exclusive(v_fst_1655_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_1663_ = v_fst_1655_;
v_isShared_1664_ = v_isSharedCheck_1684_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_snd_1661_);
lean_inc(v_fst_1660_);
lean_dec(v_fst_1655_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1684_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
if (v_modified_1636_ == 0)
{
uint8_t v___x_1679_; 
v___x_1679_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_f_1633_, v_fst_1660_);
lean_dec_ref(v_f_1633_);
if (v___x_1679_ == 0)
{
lean_del_object(v___x_1658_);
lean_dec_ref(v_e_1632_);
goto v___jp_1665_;
}
else
{
lean_object* v___x_1681_; 
lean_del_object(v___x_1663_);
lean_dec(v_fst_1660_);
lean_dec_ref(v_argsRev_1634_);
if (v_isShared_1659_ == 0)
{
lean_ctor_set(v___x_1658_, 1, v_snd_1661_);
lean_ctor_set(v___x_1658_, 0, v_e_1632_);
v___x_1681_ = v___x_1658_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_e_1632_);
lean_ctor_set(v_reuseFailAlloc_1683_, 1, v_snd_1661_);
v___x_1681_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
lean_object* v___x_1682_; 
v___x_1682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1682_, 0, v___x_1681_);
lean_ctor_set(v___x_1682_, 1, v_snd_1656_);
return v___x_1682_;
}
}
}
else
{
lean_del_object(v___x_1658_);
lean_dec_ref(v_f_1633_);
lean_dec_ref(v_e_1632_);
goto v___jp_1665_;
}
v___jp_1665_:
{
lean_object* v___x_1666_; lean_object* v_fst_1667_; lean_object* v_snd_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1678_; 
v___x_1666_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS(v_fst_1660_, v_argsRev_1634_, v_a_1638_, v_snd_1656_);
lean_dec_ref(v_argsRev_1634_);
v_fst_1667_ = lean_ctor_get(v___x_1666_, 0);
v_snd_1668_ = lean_ctor_get(v___x_1666_, 1);
v_isSharedCheck_1678_ = !lean_is_exclusive(v___x_1666_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1670_ = v___x_1666_;
v_isShared_1671_ = v_isSharedCheck_1678_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_snd_1668_);
lean_inc(v_fst_1667_);
lean_dec(v___x_1666_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1678_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1673_; 
if (v_isShared_1671_ == 0)
{
lean_ctor_set(v___x_1670_, 1, v_snd_1661_);
v___x_1673_ = v___x_1670_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v_fst_1667_);
lean_ctor_set(v_reuseFailAlloc_1677_, 1, v_snd_1661_);
v___x_1673_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
lean_object* v___x_1675_; 
if (v_isShared_1664_ == 0)
{
lean_ctor_set(v___x_1663_, 1, v_snd_1668_);
lean_ctor_set(v___x_1663_, 0, v___x_1673_);
v___x_1675_ = v___x_1663_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v___x_1673_);
lean_ctor_set(v_reuseFailAlloc_1676_, 1, v_snd_1668_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
}
}
}
}
default: 
{
lean_object* v___x_1686_; lean_object* v___x_1687_; 
lean_dec(v_offset_1635_);
lean_dec_ref(v_argsRev_1634_);
lean_dec_ref(v_f_1633_);
lean_dec_ref(v_e_1632_);
v___x_1686_ = lean_obj_once(&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__1, &l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__1_once, _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__1);
v___x_1687_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9(v___x_1686_, v_a_1637_, v_a_1638_, v_a_1639_);
return v___x_1687_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg(lean_object* v_subst_1688_, lean_object* v_e_1689_, lean_object* v_f_1690_, lean_object* v_arg_1691_, lean_object* v_offset_1692_, lean_object* v_a_1693_, uint8_t v_a_1694_, lean_object* v_a_1695_){
_start:
{
lean_object* v___x_1696_; lean_object* v_fst_1697_; lean_object* v_snd_1698_; lean_object* v_fst_1699_; lean_object* v_snd_1700_; lean_object* v___x_1701_; uint8_t v___x_1702_; 
lean_inc(v_offset_1692_);
lean_inc_ref(v_arg_1691_);
v___x_1696_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1688_, v_arg_1691_, v_offset_1692_, v_a_1693_, v_a_1694_, v_a_1695_);
v_fst_1697_ = lean_ctor_get(v___x_1696_, 0);
lean_inc(v_fst_1697_);
v_snd_1698_ = lean_ctor_get(v___x_1696_, 1);
lean_inc(v_snd_1698_);
lean_dec_ref(v___x_1696_);
v_fst_1699_ = lean_ctor_get(v_fst_1697_, 0);
lean_inc(v_fst_1699_);
v_snd_1700_ = lean_ctor_get(v_fst_1697_, 1);
lean_inc(v_snd_1700_);
lean_dec(v_fst_1697_);
v___x_1701_ = l_Lean_Expr_getAppFn(v_f_1690_);
v___x_1702_ = l_Lean_Expr_isBVar(v___x_1701_);
lean_dec_ref(v___x_1701_);
if (v___x_1702_ == 0)
{
lean_object* v___x_1703_; lean_object* v_fst_1704_; lean_object* v_snd_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1730_; 
lean_dec_ref(v_arg_1691_);
v___x_1703_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault(v_subst_1688_, v_f_1690_, v_offset_1692_, v_snd_1700_, v_a_1694_, v_snd_1698_);
v_fst_1704_ = lean_ctor_get(v___x_1703_, 0);
v_snd_1705_ = lean_ctor_get(v___x_1703_, 1);
v_isSharedCheck_1730_ = !lean_is_exclusive(v___x_1703_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1707_ = v___x_1703_;
v_isShared_1708_ = v_isSharedCheck_1730_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_snd_1705_);
lean_inc(v_fst_1704_);
lean_dec(v___x_1703_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1730_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v_fst_1709_; lean_object* v_snd_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1729_; 
v_fst_1709_ = lean_ctor_get(v_fst_1704_, 0);
v_snd_1710_ = lean_ctor_get(v_fst_1704_, 1);
v_isSharedCheck_1729_ = !lean_is_exclusive(v_fst_1704_);
if (v_isSharedCheck_1729_ == 0)
{
v___x_1712_ = v_fst_1704_;
v_isShared_1713_ = v_isSharedCheck_1729_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_snd_1710_);
lean_inc(v_fst_1709_);
lean_dec(v_fst_1704_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1729_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
uint8_t v___y_1715_; 
if (lean_obj_tag(v_e_1689_) == 5)
{
lean_object* v_fn_1723_; lean_object* v_arg_1724_; uint8_t v___x_1725_; 
v_fn_1723_ = lean_ctor_get(v_e_1689_, 0);
v_arg_1724_ = lean_ctor_get(v_e_1689_, 1);
v___x_1725_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_1723_, v_fst_1709_);
if (v___x_1725_ == 0)
{
v___y_1715_ = v___x_1725_;
goto v___jp_1714_;
}
else
{
uint8_t v___x_1726_; 
v___x_1726_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_1724_, v_fst_1699_);
v___y_1715_ = v___x_1726_;
goto v___jp_1714_;
}
}
else
{
lean_object* v___x_1727_; lean_object* v___x_1728_; 
lean_del_object(v___x_1712_);
lean_dec(v_fst_1709_);
lean_del_object(v___x_1707_);
lean_dec(v_fst_1699_);
lean_dec_ref(v_e_1689_);
v___x_1727_ = lean_obj_once(&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__3, &l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__3_once, _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__3);
v___x_1728_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9(v___x_1727_, v_snd_1710_, v_a_1694_, v_snd_1705_);
return v___x_1728_;
}
v___jp_1714_:
{
if (v___y_1715_ == 0)
{
lean_object* v___x_1716_; 
lean_del_object(v___x_1712_);
lean_del_object(v___x_1707_);
lean_dec_ref(v_e_1689_);
v___x_1716_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__3(v_fst_1709_, v_fst_1699_, v_snd_1710_, v_a_1694_, v_snd_1705_);
return v___x_1716_;
}
else
{
lean_object* v___x_1718_; 
lean_dec(v_fst_1709_);
lean_dec(v_fst_1699_);
if (v_isShared_1713_ == 0)
{
lean_ctor_set(v___x_1712_, 0, v_e_1689_);
v___x_1718_ = v___x_1712_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_e_1689_);
lean_ctor_set(v_reuseFailAlloc_1722_, 1, v_snd_1710_);
v___x_1718_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
lean_object* v___x_1720_; 
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 0, v___x_1718_);
v___x_1720_ = v___x_1707_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v___x_1718_);
lean_ctor_set(v_reuseFailAlloc_1721_, 1, v_snd_1705_);
v___x_1720_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
return v___x_1720_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; uint8_t v___x_1734_; 
v___x_1731_ = lean_unsigned_to_nat(1u);
v___x_1732_ = lean_mk_empty_array_with_capacity(v___x_1731_);
lean_inc(v_fst_1699_);
v___x_1733_ = lean_array_push(v___x_1732_, v_fst_1699_);
v___x_1734_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_1691_, v_fst_1699_);
lean_dec(v_fst_1699_);
lean_dec_ref(v_arg_1691_);
if (v___x_1734_ == 0)
{
lean_object* v___x_1735_; 
v___x_1735_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta(v_subst_1688_, v_e_1689_, v_f_1690_, v___x_1733_, v_offset_1692_, v___x_1702_, v_snd_1700_, v_a_1694_, v_snd_1698_);
return v___x_1735_;
}
else
{
uint8_t v___x_1736_; lean_object* v___x_1737_; 
v___x_1736_ = 0;
v___x_1737_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta(v_subst_1688_, v_e_1689_, v_f_1690_, v___x_1733_, v_offset_1692_, v___x_1736_, v_snd_1700_, v_a_1694_, v_snd_1698_);
return v___x_1737_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__1(void){
_start:
{
lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
v___x_1739_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__2));
v___x_1740_ = lean_unsigned_to_nat(59u);
v___x_1741_ = lean_unsigned_to_nat(190u);
v___x_1742_ = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__0));
v___x_1743_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__3));
v___x_1744_ = l_mkPanicMessageWithDecl(v___x_1743_, v___x_1742_, v___x_1741_, v___x_1740_, v___x_1739_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit(lean_object* v_subst_1745_, lean_object* v_e_1746_, lean_object* v_offset_1747_, lean_object* v_a_1748_, uint8_t v_a_1749_, lean_object* v_a_1750_){
_start:
{
switch(lean_obj_tag(v_e_1746_))
{
case 0:
{
lean_object* v_deBruijnIndex_1751_; lean_object* v___x_1752_; 
v_deBruijnIndex_1751_ = lean_ctor_get(v_e_1746_, 0);
lean_inc(v_deBruijnIndex_1751_);
v___x_1752_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(v_subst_1745_, v_e_1746_, v_deBruijnIndex_1751_, v_offset_1747_, v_a_1748_, v_a_1749_, v_a_1750_);
lean_dec(v_offset_1747_);
lean_dec(v_deBruijnIndex_1751_);
return v___x_1752_;
}
case 5:
{
lean_object* v_fn_1753_; lean_object* v_arg_1754_; lean_object* v___x_1755_; 
v_fn_1753_ = lean_ctor_get(v_e_1746_, 0);
lean_inc_ref(v_fn_1753_);
v_arg_1754_ = lean_ctor_get(v_e_1746_, 1);
lean_inc_ref(v_arg_1754_);
v___x_1755_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg(v_subst_1745_, v_e_1746_, v_fn_1753_, v_arg_1754_, v_offset_1747_, v_a_1748_, v_a_1749_, v_a_1750_);
return v___x_1755_;
}
case 6:
{
lean_object* v_binderName_1756_; lean_object* v_binderType_1757_; lean_object* v_body_1758_; uint8_t v_binderInfo_1759_; lean_object* v___x_1760_; lean_object* v_fst_1761_; lean_object* v_snd_1762_; lean_object* v_fst_1763_; lean_object* v_snd_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v_fst_1768_; lean_object* v_snd_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1790_; 
v_binderName_1756_ = lean_ctor_get(v_e_1746_, 0);
v_binderType_1757_ = lean_ctor_get(v_e_1746_, 1);
v_body_1758_ = lean_ctor_get(v_e_1746_, 2);
v_binderInfo_1759_ = lean_ctor_get_uint8(v_e_1746_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1747_);
lean_inc_ref(v_binderType_1757_);
v___x_1760_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1745_, v_binderType_1757_, v_offset_1747_, v_a_1748_, v_a_1749_, v_a_1750_);
v_fst_1761_ = lean_ctor_get(v___x_1760_, 0);
lean_inc(v_fst_1761_);
v_snd_1762_ = lean_ctor_get(v___x_1760_, 1);
lean_inc(v_snd_1762_);
lean_dec_ref(v___x_1760_);
v_fst_1763_ = lean_ctor_get(v_fst_1761_, 0);
lean_inc(v_fst_1763_);
v_snd_1764_ = lean_ctor_get(v_fst_1761_, 1);
lean_inc(v_snd_1764_);
lean_dec(v_fst_1761_);
v___x_1765_ = lean_unsigned_to_nat(1u);
v___x_1766_ = lean_nat_add(v_offset_1747_, v___x_1765_);
lean_dec(v_offset_1747_);
lean_inc_ref(v_body_1758_);
v___x_1767_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1745_, v_body_1758_, v___x_1766_, v_snd_1764_, v_a_1749_, v_snd_1762_);
v_fst_1768_ = lean_ctor_get(v___x_1767_, 0);
v_snd_1769_ = lean_ctor_get(v___x_1767_, 1);
v_isSharedCheck_1790_ = !lean_is_exclusive(v___x_1767_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1771_ = v___x_1767_;
v_isShared_1772_ = v_isSharedCheck_1790_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_snd_1769_);
lean_inc(v_fst_1768_);
lean_dec(v___x_1767_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1790_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v_fst_1773_; lean_object* v_snd_1774_; lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1789_; 
v_fst_1773_ = lean_ctor_get(v_fst_1768_, 0);
v_snd_1774_ = lean_ctor_get(v_fst_1768_, 1);
v_isSharedCheck_1789_ = !lean_is_exclusive(v_fst_1768_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1776_ = v_fst_1768_;
v_isShared_1777_ = v_isSharedCheck_1789_;
goto v_resetjp_1775_;
}
else
{
lean_inc(v_snd_1774_);
lean_inc(v_fst_1773_);
lean_dec(v_fst_1768_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1789_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
uint8_t v___y_1779_; uint8_t v___x_1787_; 
v___x_1787_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_1757_, v_fst_1763_);
if (v___x_1787_ == 0)
{
v___y_1779_ = v___x_1787_;
goto v___jp_1778_;
}
else
{
uint8_t v___x_1788_; 
v___x_1788_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1758_, v_fst_1773_);
v___y_1779_ = v___x_1788_;
goto v___jp_1778_;
}
v___jp_1778_:
{
if (v___y_1779_ == 0)
{
lean_object* v___x_1780_; 
lean_inc(v_binderName_1756_);
lean_del_object(v___x_1776_);
lean_del_object(v___x_1771_);
lean_dec_ref(v_e_1746_);
v___x_1780_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__4(v_binderName_1756_, v_binderInfo_1759_, v_fst_1763_, v_fst_1773_, v_snd_1774_, v_a_1749_, v_snd_1769_);
return v___x_1780_;
}
else
{
lean_object* v___x_1782_; 
lean_dec(v_fst_1773_);
lean_dec(v_fst_1763_);
if (v_isShared_1777_ == 0)
{
lean_ctor_set(v___x_1776_, 0, v_e_1746_);
v___x_1782_ = v___x_1776_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_e_1746_);
lean_ctor_set(v_reuseFailAlloc_1786_, 1, v_snd_1774_);
v___x_1782_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
lean_object* v___x_1784_; 
if (v_isShared_1772_ == 0)
{
lean_ctor_set(v___x_1771_, 0, v___x_1782_);
v___x_1784_ = v___x_1771_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v___x_1782_);
lean_ctor_set(v_reuseFailAlloc_1785_, 1, v_snd_1769_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
}
}
}
}
case 7:
{
lean_object* v_binderName_1791_; lean_object* v_binderType_1792_; lean_object* v_body_1793_; uint8_t v_binderInfo_1794_; lean_object* v___x_1795_; lean_object* v_fst_1796_; lean_object* v_snd_1797_; lean_object* v_fst_1798_; lean_object* v_snd_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v_fst_1803_; lean_object* v_snd_1804_; lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1825_; 
v_binderName_1791_ = lean_ctor_get(v_e_1746_, 0);
v_binderType_1792_ = lean_ctor_get(v_e_1746_, 1);
v_body_1793_ = lean_ctor_get(v_e_1746_, 2);
v_binderInfo_1794_ = lean_ctor_get_uint8(v_e_1746_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1747_);
lean_inc_ref(v_binderType_1792_);
v___x_1795_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1745_, v_binderType_1792_, v_offset_1747_, v_a_1748_, v_a_1749_, v_a_1750_);
v_fst_1796_ = lean_ctor_get(v___x_1795_, 0);
lean_inc(v_fst_1796_);
v_snd_1797_ = lean_ctor_get(v___x_1795_, 1);
lean_inc(v_snd_1797_);
lean_dec_ref(v___x_1795_);
v_fst_1798_ = lean_ctor_get(v_fst_1796_, 0);
lean_inc(v_fst_1798_);
v_snd_1799_ = lean_ctor_get(v_fst_1796_, 1);
lean_inc(v_snd_1799_);
lean_dec(v_fst_1796_);
v___x_1800_ = lean_unsigned_to_nat(1u);
v___x_1801_ = lean_nat_add(v_offset_1747_, v___x_1800_);
lean_dec(v_offset_1747_);
lean_inc_ref(v_body_1793_);
v___x_1802_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1745_, v_body_1793_, v___x_1801_, v_snd_1799_, v_a_1749_, v_snd_1797_);
v_fst_1803_ = lean_ctor_get(v___x_1802_, 0);
v_snd_1804_ = lean_ctor_get(v___x_1802_, 1);
v_isSharedCheck_1825_ = !lean_is_exclusive(v___x_1802_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1806_ = v___x_1802_;
v_isShared_1807_ = v_isSharedCheck_1825_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_snd_1804_);
lean_inc(v_fst_1803_);
lean_dec(v___x_1802_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1825_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
lean_object* v_fst_1808_; lean_object* v_snd_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1824_; 
v_fst_1808_ = lean_ctor_get(v_fst_1803_, 0);
v_snd_1809_ = lean_ctor_get(v_fst_1803_, 1);
v_isSharedCheck_1824_ = !lean_is_exclusive(v_fst_1803_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1811_ = v_fst_1803_;
v_isShared_1812_ = v_isSharedCheck_1824_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_snd_1809_);
lean_inc(v_fst_1808_);
lean_dec(v_fst_1803_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1824_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
uint8_t v___y_1814_; uint8_t v___x_1822_; 
v___x_1822_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_1792_, v_fst_1798_);
if (v___x_1822_ == 0)
{
v___y_1814_ = v___x_1822_;
goto v___jp_1813_;
}
else
{
uint8_t v___x_1823_; 
v___x_1823_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1793_, v_fst_1808_);
v___y_1814_ = v___x_1823_;
goto v___jp_1813_;
}
v___jp_1813_:
{
if (v___y_1814_ == 0)
{
lean_object* v___x_1815_; 
lean_inc(v_binderName_1791_);
lean_del_object(v___x_1811_);
lean_del_object(v___x_1806_);
lean_dec_ref(v_e_1746_);
v___x_1815_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__5(v_binderName_1791_, v_binderInfo_1794_, v_fst_1798_, v_fst_1808_, v_snd_1809_, v_a_1749_, v_snd_1804_);
return v___x_1815_;
}
else
{
lean_object* v___x_1817_; 
lean_dec(v_fst_1808_);
lean_dec(v_fst_1798_);
if (v_isShared_1812_ == 0)
{
lean_ctor_set(v___x_1811_, 0, v_e_1746_);
v___x_1817_ = v___x_1811_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v_e_1746_);
lean_ctor_set(v_reuseFailAlloc_1821_, 1, v_snd_1809_);
v___x_1817_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
lean_object* v___x_1819_; 
if (v_isShared_1807_ == 0)
{
lean_ctor_set(v___x_1806_, 0, v___x_1817_);
v___x_1819_ = v___x_1806_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v___x_1817_);
lean_ctor_set(v_reuseFailAlloc_1820_, 1, v_snd_1804_);
v___x_1819_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
return v___x_1819_;
}
}
}
}
}
}
}
case 8:
{
lean_object* v_declName_1826_; lean_object* v_type_1827_; lean_object* v_value_1828_; lean_object* v_body_1829_; uint8_t v_nondep_1830_; lean_object* v___x_1831_; lean_object* v_fst_1832_; lean_object* v_snd_1833_; lean_object* v_fst_1834_; lean_object* v_snd_1835_; lean_object* v___x_1836_; lean_object* v_fst_1837_; lean_object* v_snd_1838_; lean_object* v_fst_1839_; lean_object* v_snd_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v_fst_1844_; lean_object* v_snd_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1868_; 
v_declName_1826_ = lean_ctor_get(v_e_1746_, 0);
v_type_1827_ = lean_ctor_get(v_e_1746_, 1);
v_value_1828_ = lean_ctor_get(v_e_1746_, 2);
v_body_1829_ = lean_ctor_get(v_e_1746_, 3);
v_nondep_1830_ = lean_ctor_get_uint8(v_e_1746_, sizeof(void*)*4 + 8);
lean_inc_n(v_offset_1747_, 2);
lean_inc_ref(v_type_1827_);
v___x_1831_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1745_, v_type_1827_, v_offset_1747_, v_a_1748_, v_a_1749_, v_a_1750_);
v_fst_1832_ = lean_ctor_get(v___x_1831_, 0);
lean_inc(v_fst_1832_);
v_snd_1833_ = lean_ctor_get(v___x_1831_, 1);
lean_inc(v_snd_1833_);
lean_dec_ref(v___x_1831_);
v_fst_1834_ = lean_ctor_get(v_fst_1832_, 0);
lean_inc(v_fst_1834_);
v_snd_1835_ = lean_ctor_get(v_fst_1832_, 1);
lean_inc(v_snd_1835_);
lean_dec(v_fst_1832_);
lean_inc_ref(v_value_1828_);
v___x_1836_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1745_, v_value_1828_, v_offset_1747_, v_snd_1835_, v_a_1749_, v_snd_1833_);
v_fst_1837_ = lean_ctor_get(v___x_1836_, 0);
lean_inc(v_fst_1837_);
v_snd_1838_ = lean_ctor_get(v___x_1836_, 1);
lean_inc(v_snd_1838_);
lean_dec_ref(v___x_1836_);
v_fst_1839_ = lean_ctor_get(v_fst_1837_, 0);
lean_inc(v_fst_1839_);
v_snd_1840_ = lean_ctor_get(v_fst_1837_, 1);
lean_inc(v_snd_1840_);
lean_dec(v_fst_1837_);
v___x_1841_ = lean_unsigned_to_nat(1u);
v___x_1842_ = lean_nat_add(v_offset_1747_, v___x_1841_);
lean_dec(v_offset_1747_);
lean_inc_ref(v_body_1829_);
v___x_1843_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1745_, v_body_1829_, v___x_1842_, v_snd_1840_, v_a_1749_, v_snd_1838_);
v_fst_1844_ = lean_ctor_get(v___x_1843_, 0);
v_snd_1845_ = lean_ctor_get(v___x_1843_, 1);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1847_ = v___x_1843_;
v_isShared_1848_ = v_isSharedCheck_1868_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_snd_1845_);
lean_inc(v_fst_1844_);
lean_dec(v___x_1843_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1868_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
lean_object* v_fst_1849_; lean_object* v_snd_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1867_; 
v_fst_1849_ = lean_ctor_get(v_fst_1844_, 0);
v_snd_1850_ = lean_ctor_get(v_fst_1844_, 1);
v_isSharedCheck_1867_ = !lean_is_exclusive(v_fst_1844_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1852_ = v_fst_1844_;
v_isShared_1853_ = v_isSharedCheck_1867_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_snd_1850_);
lean_inc(v_fst_1849_);
lean_dec(v_fst_1844_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1867_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
uint8_t v___y_1855_; uint8_t v___x_1865_; 
v___x_1865_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_type_1827_, v_fst_1834_);
if (v___x_1865_ == 0)
{
v___y_1855_ = v___x_1865_;
goto v___jp_1854_;
}
else
{
uint8_t v___x_1866_; 
v___x_1866_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_value_1828_, v_fst_1839_);
v___y_1855_ = v___x_1866_;
goto v___jp_1854_;
}
v___jp_1854_:
{
if (v___y_1855_ == 0)
{
lean_object* v___x_1856_; 
lean_inc(v_declName_1826_);
lean_del_object(v___x_1852_);
lean_del_object(v___x_1847_);
lean_dec_ref(v_e_1746_);
v___x_1856_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6(v_declName_1826_, v_fst_1834_, v_fst_1839_, v_fst_1849_, v_nondep_1830_, v_snd_1850_, v_a_1749_, v_snd_1845_);
return v___x_1856_;
}
else
{
uint8_t v___x_1857_; 
v___x_1857_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1829_, v_fst_1849_);
if (v___x_1857_ == 0)
{
lean_object* v___x_1858_; 
lean_inc(v_declName_1826_);
lean_del_object(v___x_1852_);
lean_del_object(v___x_1847_);
lean_dec_ref(v_e_1746_);
v___x_1858_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6(v_declName_1826_, v_fst_1834_, v_fst_1839_, v_fst_1849_, v_nondep_1830_, v_snd_1850_, v_a_1749_, v_snd_1845_);
return v___x_1858_;
}
else
{
lean_object* v___x_1860_; 
lean_dec(v_fst_1849_);
lean_dec(v_fst_1839_);
lean_dec(v_fst_1834_);
if (v_isShared_1853_ == 0)
{
lean_ctor_set(v___x_1852_, 0, v_e_1746_);
v___x_1860_ = v___x_1852_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v_e_1746_);
lean_ctor_set(v_reuseFailAlloc_1864_, 1, v_snd_1850_);
v___x_1860_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
lean_object* v___x_1862_; 
if (v_isShared_1848_ == 0)
{
lean_ctor_set(v___x_1847_, 0, v___x_1860_);
v___x_1862_ = v___x_1847_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v___x_1860_);
lean_ctor_set(v_reuseFailAlloc_1863_, 1, v_snd_1845_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
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
lean_object* v_data_1869_; lean_object* v_expr_1870_; lean_object* v___x_1871_; lean_object* v_fst_1872_; lean_object* v_snd_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1891_; 
v_data_1869_ = lean_ctor_get(v_e_1746_, 0);
v_expr_1870_ = lean_ctor_get(v_e_1746_, 1);
lean_inc_ref(v_expr_1870_);
v___x_1871_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1745_, v_expr_1870_, v_offset_1747_, v_a_1748_, v_a_1749_, v_a_1750_);
v_fst_1872_ = lean_ctor_get(v___x_1871_, 0);
v_snd_1873_ = lean_ctor_get(v___x_1871_, 1);
v_isSharedCheck_1891_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1875_ = v___x_1871_;
v_isShared_1876_ = v_isSharedCheck_1891_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_snd_1873_);
lean_inc(v_fst_1872_);
lean_dec(v___x_1871_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1891_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v_fst_1877_; lean_object* v_snd_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1890_; 
v_fst_1877_ = lean_ctor_get(v_fst_1872_, 0);
v_snd_1878_ = lean_ctor_get(v_fst_1872_, 1);
v_isSharedCheck_1890_ = !lean_is_exclusive(v_fst_1872_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1880_ = v_fst_1872_;
v_isShared_1881_ = v_isSharedCheck_1890_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_snd_1878_);
lean_inc(v_fst_1877_);
lean_dec(v_fst_1872_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1890_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
uint8_t v___x_1882_; 
v___x_1882_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_expr_1870_, v_fst_1877_);
if (v___x_1882_ == 0)
{
lean_object* v___x_1883_; 
lean_inc(v_data_1869_);
lean_del_object(v___x_1880_);
lean_del_object(v___x_1875_);
lean_dec_ref(v_e_1746_);
v___x_1883_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__7(v_data_1869_, v_fst_1877_, v_snd_1878_, v_a_1749_, v_snd_1873_);
return v___x_1883_;
}
else
{
lean_object* v___x_1885_; 
lean_dec(v_fst_1877_);
if (v_isShared_1881_ == 0)
{
lean_ctor_set(v___x_1880_, 0, v_e_1746_);
v___x_1885_ = v___x_1880_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_e_1746_);
lean_ctor_set(v_reuseFailAlloc_1889_, 1, v_snd_1878_);
v___x_1885_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
lean_object* v___x_1887_; 
if (v_isShared_1876_ == 0)
{
lean_ctor_set(v___x_1875_, 0, v___x_1885_);
v___x_1887_ = v___x_1875_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v___x_1885_);
lean_ctor_set(v_reuseFailAlloc_1888_, 1, v_snd_1873_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
return v___x_1887_;
}
}
}
}
}
}
case 11:
{
lean_object* v_typeName_1892_; lean_object* v_idx_1893_; lean_object* v_struct_1894_; lean_object* v___x_1895_; lean_object* v_fst_1896_; lean_object* v_snd_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1915_; 
v_typeName_1892_ = lean_ctor_get(v_e_1746_, 0);
v_idx_1893_ = lean_ctor_get(v_e_1746_, 1);
v_struct_1894_ = lean_ctor_get(v_e_1746_, 2);
lean_inc_ref(v_struct_1894_);
v___x_1895_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1745_, v_struct_1894_, v_offset_1747_, v_a_1748_, v_a_1749_, v_a_1750_);
v_fst_1896_ = lean_ctor_get(v___x_1895_, 0);
v_snd_1897_ = lean_ctor_get(v___x_1895_, 1);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1895_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1899_ = v___x_1895_;
v_isShared_1900_ = v_isSharedCheck_1915_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_snd_1897_);
lean_inc(v_fst_1896_);
lean_dec(v___x_1895_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1915_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v_fst_1901_; lean_object* v_snd_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1914_; 
v_fst_1901_ = lean_ctor_get(v_fst_1896_, 0);
v_snd_1902_ = lean_ctor_get(v_fst_1896_, 1);
v_isSharedCheck_1914_ = !lean_is_exclusive(v_fst_1896_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1904_ = v_fst_1896_;
v_isShared_1905_ = v_isSharedCheck_1914_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_snd_1902_);
lean_inc(v_fst_1901_);
lean_dec(v_fst_1896_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1914_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
uint8_t v___x_1906_; 
v___x_1906_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_1894_, v_fst_1901_);
if (v___x_1906_ == 0)
{
lean_object* v___x_1907_; 
lean_inc(v_idx_1893_);
lean_inc(v_typeName_1892_);
lean_del_object(v___x_1904_);
lean_del_object(v___x_1899_);
lean_dec_ref(v_e_1746_);
v___x_1907_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__8(v_typeName_1892_, v_idx_1893_, v_fst_1901_, v_snd_1902_, v_a_1749_, v_snd_1897_);
return v___x_1907_;
}
else
{
lean_object* v___x_1909_; 
lean_dec(v_fst_1901_);
if (v_isShared_1905_ == 0)
{
lean_ctor_set(v___x_1904_, 0, v_e_1746_);
v___x_1909_ = v___x_1904_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_e_1746_);
lean_ctor_set(v_reuseFailAlloc_1913_, 1, v_snd_1902_);
v___x_1909_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
lean_object* v___x_1911_; 
if (v_isShared_1900_ == 0)
{
lean_ctor_set(v___x_1899_, 0, v___x_1909_);
v___x_1911_ = v___x_1899_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v___x_1909_);
lean_ctor_set(v_reuseFailAlloc_1912_, 1, v_snd_1897_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_1916_; lean_object* v___x_1917_; 
lean_dec(v_offset_1747_);
lean_dec_ref(v_e_1746_);
v___x_1916_ = lean_obj_once(&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__1, &l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__1_once, _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__1);
v___x_1917_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9(v___x_1916_, v_a_1748_, v_a_1749_, v_a_1750_);
return v___x_1917_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(lean_object* v_subst_1918_, lean_object* v_e_1919_, lean_object* v_offset_1920_, lean_object* v_a_1921_, uint8_t v_a_1922_, lean_object* v_a_1923_){
_start:
{
lean_object* v___x_1924_; uint8_t v___x_1925_; 
v___x_1924_ = l_Lean_Expr_looseBVarRange(v_e_1919_);
v___x_1925_ = lean_nat_dec_le(v___x_1924_, v_offset_1920_);
lean_dec(v___x_1924_);
if (v___x_1925_ == 0)
{
lean_object* v_key_1926_; lean_object* v___x_1927_; 
lean_inc(v_offset_1920_);
lean_inc_ref(v_e_1919_);
v_key_1926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1926_, 0, v_e_1919_);
lean_ctor_set(v_key_1926_, 1, v_offset_1920_);
v___x_1927_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___redArg(v_a_1921_, v_key_1926_);
if (lean_obj_tag(v___x_1927_) == 1)
{
lean_object* v_val_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; 
lean_dec_ref(v_key_1926_);
lean_dec(v_offset_1920_);
lean_dec_ref(v_e_1919_);
v_val_1928_ = lean_ctor_get(v___x_1927_, 0);
lean_inc(v_val_1928_);
lean_dec_ref(v___x_1927_);
v___x_1929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1929_, 0, v_val_1928_);
lean_ctor_set(v___x_1929_, 1, v_a_1921_);
v___x_1930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1930_, 0, v___x_1929_);
lean_ctor_set(v___x_1930_, 1, v_a_1923_);
return v___x_1930_;
}
else
{
lean_dec(v___x_1927_);
switch(lean_obj_tag(v_e_1919_))
{
case 0:
{
lean_object* v_deBruijnIndex_1931_; lean_object* v___x_1932_; lean_object* v_fst_1933_; lean_object* v_snd_1934_; lean_object* v_fst_1935_; lean_object* v_snd_1936_; lean_object* v___x_1937_; 
v_deBruijnIndex_1931_ = lean_ctor_get(v_e_1919_, 0);
lean_inc(v_deBruijnIndex_1931_);
v___x_1932_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(v_subst_1918_, v_e_1919_, v_deBruijnIndex_1931_, v_offset_1920_, v_a_1921_, v_a_1922_, v_a_1923_);
lean_dec(v_offset_1920_);
lean_dec(v_deBruijnIndex_1931_);
v_fst_1933_ = lean_ctor_get(v___x_1932_, 0);
lean_inc(v_fst_1933_);
v_snd_1934_ = lean_ctor_get(v___x_1932_, 1);
lean_inc(v_snd_1934_);
lean_dec_ref(v___x_1932_);
v_fst_1935_ = lean_ctor_get(v_fst_1933_, 0);
lean_inc(v_fst_1935_);
v_snd_1936_ = lean_ctor_get(v_fst_1933_, 1);
lean_inc(v_snd_1936_);
lean_dec(v_fst_1933_);
v___x_1937_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_1926_, v_fst_1935_, v_snd_1936_, v_snd_1934_);
return v___x_1937_;
}
case 9:
{
lean_object* v___x_1938_; 
lean_dec(v_offset_1920_);
v___x_1938_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_1926_, v_e_1919_, v_a_1921_, v_a_1923_);
return v___x_1938_;
}
case 2:
{
lean_object* v___x_1939_; 
lean_dec(v_offset_1920_);
v___x_1939_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_1926_, v_e_1919_, v_a_1921_, v_a_1923_);
return v___x_1939_;
}
case 1:
{
lean_object* v___x_1940_; 
lean_dec(v_offset_1920_);
v___x_1940_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_1926_, v_e_1919_, v_a_1921_, v_a_1923_);
return v___x_1940_;
}
case 4:
{
lean_object* v___x_1941_; 
lean_dec(v_offset_1920_);
v___x_1941_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_1926_, v_e_1919_, v_a_1921_, v_a_1923_);
return v___x_1941_;
}
case 3:
{
lean_object* v___x_1942_; 
lean_dec(v_offset_1920_);
v___x_1942_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_1926_, v_e_1919_, v_a_1921_, v_a_1923_);
return v___x_1942_;
}
default: 
{
lean_object* v___x_1943_; lean_object* v_fst_1944_; lean_object* v_snd_1945_; lean_object* v_fst_1946_; lean_object* v_snd_1947_; lean_object* v___x_1948_; 
v___x_1943_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit(v_subst_1918_, v_e_1919_, v_offset_1920_, v_a_1921_, v_a_1922_, v_a_1923_);
v_fst_1944_ = lean_ctor_get(v___x_1943_, 0);
lean_inc(v_fst_1944_);
v_snd_1945_ = lean_ctor_get(v___x_1943_, 1);
lean_inc(v_snd_1945_);
lean_dec_ref(v___x_1943_);
v_fst_1946_ = lean_ctor_get(v_fst_1944_, 0);
lean_inc(v_fst_1946_);
v_snd_1947_ = lean_ctor_get(v_fst_1944_, 1);
lean_inc(v_snd_1947_);
lean_dec(v_fst_1944_);
v___x_1948_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_1926_, v_fst_1946_, v_snd_1947_, v_snd_1945_);
return v___x_1948_;
}
}
}
}
else
{
lean_object* v___x_1949_; lean_object* v___x_1950_; 
lean_dec(v_offset_1920_);
v___x_1949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1949_, 0, v_e_1919_);
lean_ctor_set(v___x_1949_, 1, v_a_1921_);
v___x_1950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1950_, 0, v___x_1949_);
lean_ctor_set(v___x_1950_, 1, v_a_1923_);
return v___x_1950_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault(lean_object* v_subst_1951_, lean_object* v_e_1952_, lean_object* v_offset_1953_, lean_object* v_a_1954_, uint8_t v_a_1955_, lean_object* v_a_1956_){
_start:
{
if (lean_obj_tag(v_e_1952_) == 5)
{
lean_object* v_fn_1957_; lean_object* v_arg_1958_; lean_object* v_key_1959_; lean_object* v___x_1960_; 
v_fn_1957_ = lean_ctor_get(v_e_1952_, 0);
v_arg_1958_ = lean_ctor_get(v_e_1952_, 1);
lean_inc(v_offset_1953_);
lean_inc_ref(v_e_1952_);
v_key_1959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1959_, 0, v_e_1952_);
lean_ctor_set(v_key_1959_, 1, v_offset_1953_);
v___x_1960_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___redArg(v_a_1954_, v_key_1959_);
if (lean_obj_tag(v___x_1960_) == 1)
{
lean_object* v_val_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; 
lean_dec_ref(v_key_1959_);
lean_dec_ref(v_e_1952_);
lean_dec(v_offset_1953_);
v_val_1961_ = lean_ctor_get(v___x_1960_, 0);
lean_inc(v_val_1961_);
lean_dec_ref(v___x_1960_);
v___x_1962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1962_, 0, v_val_1961_);
lean_ctor_set(v___x_1962_, 1, v_a_1954_);
v___x_1963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1963_, 0, v___x_1962_);
lean_ctor_set(v___x_1963_, 1, v_a_1956_);
return v___x_1963_;
}
else
{
lean_object* v___x_1964_; lean_object* v_fst_1965_; lean_object* v_snd_1966_; lean_object* v_fst_1967_; lean_object* v_snd_1968_; lean_object* v___x_1969_; lean_object* v_fst_1970_; lean_object* v_snd_1971_; lean_object* v_fst_1972_; lean_object* v_snd_1973_; uint8_t v___y_1975_; uint8_t v___x_1983_; 
lean_dec(v___x_1960_);
lean_inc(v_offset_1953_);
lean_inc_ref(v_fn_1957_);
v___x_1964_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault(v_subst_1951_, v_fn_1957_, v_offset_1953_, v_a_1954_, v_a_1955_, v_a_1956_);
v_fst_1965_ = lean_ctor_get(v___x_1964_, 0);
lean_inc(v_fst_1965_);
v_snd_1966_ = lean_ctor_get(v___x_1964_, 1);
lean_inc(v_snd_1966_);
lean_dec_ref(v___x_1964_);
v_fst_1967_ = lean_ctor_get(v_fst_1965_, 0);
lean_inc(v_fst_1967_);
v_snd_1968_ = lean_ctor_get(v_fst_1965_, 1);
lean_inc(v_snd_1968_);
lean_dec(v_fst_1965_);
lean_inc_ref(v_arg_1958_);
v___x_1969_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1951_, v_arg_1958_, v_offset_1953_, v_snd_1968_, v_a_1955_, v_snd_1966_);
v_fst_1970_ = lean_ctor_get(v___x_1969_, 0);
lean_inc(v_fst_1970_);
v_snd_1971_ = lean_ctor_get(v___x_1969_, 1);
lean_inc(v_snd_1971_);
lean_dec_ref(v___x_1969_);
v_fst_1972_ = lean_ctor_get(v_fst_1970_, 0);
lean_inc(v_fst_1972_);
v_snd_1973_ = lean_ctor_get(v_fst_1970_, 1);
lean_inc(v_snd_1973_);
lean_dec(v_fst_1970_);
v___x_1983_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_1957_, v_fst_1967_);
if (v___x_1983_ == 0)
{
v___y_1975_ = v___x_1983_;
goto v___jp_1974_;
}
else
{
uint8_t v___x_1984_; 
v___x_1984_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_1958_, v_fst_1972_);
v___y_1975_ = v___x_1984_;
goto v___jp_1974_;
}
v___jp_1974_:
{
if (v___y_1975_ == 0)
{
lean_object* v___x_1976_; lean_object* v_fst_1977_; lean_object* v_snd_1978_; lean_object* v_fst_1979_; lean_object* v_snd_1980_; lean_object* v___x_1981_; 
lean_dec_ref(v_e_1952_);
v___x_1976_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__3(v_fst_1967_, v_fst_1972_, v_snd_1973_, v_a_1955_, v_snd_1971_);
v_fst_1977_ = lean_ctor_get(v___x_1976_, 0);
lean_inc(v_fst_1977_);
v_snd_1978_ = lean_ctor_get(v___x_1976_, 1);
lean_inc(v_snd_1978_);
lean_dec_ref(v___x_1976_);
v_fst_1979_ = lean_ctor_get(v_fst_1977_, 0);
lean_inc(v_fst_1979_);
v_snd_1980_ = lean_ctor_get(v_fst_1977_, 1);
lean_inc(v_snd_1980_);
lean_dec(v_fst_1977_);
v___x_1981_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_1959_, v_fst_1979_, v_snd_1980_, v_snd_1978_);
return v___x_1981_;
}
else
{
lean_object* v___x_1982_; 
lean_dec(v_fst_1972_);
lean_dec(v_fst_1967_);
v___x_1982_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_1959_, v_e_1952_, v_snd_1973_, v_snd_1971_);
return v___x_1982_;
}
}
}
}
else
{
lean_object* v___x_1985_; 
v___x_1985_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1951_, v_e_1952_, v_offset_1953_, v_a_1954_, v_a_1955_, v_a_1956_);
return v___x_1985_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault___boxed(lean_object* v_subst_1986_, lean_object* v_e_1987_, lean_object* v_offset_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_){
_start:
{
uint8_t v_a_boxed_1992_; lean_object* v_res_1993_; 
v_a_boxed_1992_ = lean_unbox(v_a_1990_);
v_res_1993_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault(v_subst_1986_, v_e_1987_, v_offset_1988_, v_a_1989_, v_a_boxed_1992_, v_a_1991_);
lean_dec_ref(v_subst_1986_);
return v_res_1993_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild___boxed(lean_object* v_subst_1994_, lean_object* v_e_1995_, lean_object* v_offset_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_){
_start:
{
uint8_t v_a_boxed_2000_; lean_object* v_res_2001_; 
v_a_boxed_2000_ = lean_unbox(v_a_1998_);
v_res_2001_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1994_, v_e_1995_, v_offset_1996_, v_a_1997_, v_a_boxed_2000_, v_a_1999_);
lean_dec_ref(v_subst_1994_);
return v_res_2001_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___boxed(lean_object* v_subst_2002_, lean_object* v_e_2003_, lean_object* v_f_2004_, lean_object* v_arg_2005_, lean_object* v_offset_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_){
_start:
{
uint8_t v_a_boxed_2010_; lean_object* v_res_2011_; 
v_a_boxed_2010_ = lean_unbox(v_a_2008_);
v_res_2011_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg(v_subst_2002_, v_e_2003_, v_f_2004_, v_arg_2005_, v_offset_2006_, v_a_2007_, v_a_boxed_2010_, v_a_2009_);
lean_dec_ref(v_subst_2002_);
return v_res_2011_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___boxed(lean_object* v_subst_2012_, lean_object* v_e_2013_, lean_object* v_f_2014_, lean_object* v_argsRev_2015_, lean_object* v_offset_2016_, lean_object* v_modified_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_){
_start:
{
uint8_t v_modified_boxed_2021_; uint8_t v_a_boxed_2022_; lean_object* v_res_2023_; 
v_modified_boxed_2021_ = lean_unbox(v_modified_2017_);
v_a_boxed_2022_ = lean_unbox(v_a_2019_);
v_res_2023_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta(v_subst_2012_, v_e_2013_, v_f_2014_, v_argsRev_2015_, v_offset_2016_, v_modified_boxed_2021_, v_a_2018_, v_a_boxed_2022_, v_a_2020_);
lean_dec_ref(v_subst_2012_);
return v_res_2023_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___boxed(lean_object* v_subst_2024_, lean_object* v_e_2025_, lean_object* v_offset_2026_, lean_object* v_a_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_){
_start:
{
uint8_t v_a_boxed_2030_; lean_object* v_res_2031_; 
v_a_boxed_2030_ = lean_unbox(v_a_2028_);
v_res_2031_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit(v_subst_2024_, v_e_2025_, v_offset_2026_, v_a_2027_, v_a_boxed_2030_, v_a_2029_);
lean_dec_ref(v_subst_2024_);
return v_res_2031_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp(lean_object* v_subst_2032_, lean_object* v_e_2033_, lean_object* v_f_2034_, lean_object* v_arg_2035_, lean_object* v_offset_2036_, lean_object* v_x_2037_, lean_object* v_a_2038_, uint8_t v_a_2039_, lean_object* v_a_2040_){
_start:
{
lean_object* v___x_2041_; 
v___x_2041_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg(v_subst_2032_, v_e_2033_, v_f_2034_, v_arg_2035_, v_offset_2036_, v_a_2038_, v_a_2039_, v_a_2040_);
return v___x_2041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___boxed(lean_object* v_subst_2042_, lean_object* v_e_2043_, lean_object* v_f_2044_, lean_object* v_arg_2045_, lean_object* v_offset_2046_, lean_object* v_x_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_){
_start:
{
uint8_t v_a_boxed_2051_; lean_object* v_res_2052_; 
v_a_boxed_2051_ = lean_unbox(v_a_2049_);
v_res_2052_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp(v_subst_2042_, v_e_2043_, v_f_2044_, v_arg_2045_, v_offset_2046_, v_x_2047_, v_a_2048_, v_a_boxed_2051_, v_a_2050_);
lean_dec_ref(v_subst_2042_);
return v_res_2052_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27(lean_object* v_e_2053_, lean_object* v_subst_2054_, uint8_t v_a_2055_, lean_object* v_a_2056_){
_start:
{
uint8_t v___y_2058_; lean_object* v___x_2074_; lean_object* v___x_2075_; uint8_t v___x_2076_; 
v___x_2074_ = lean_array_get_size(v_subst_2054_);
v___x_2075_ = lean_unsigned_to_nat(0u);
v___x_2076_ = lean_nat_dec_eq(v___x_2074_, v___x_2075_);
if (v___x_2076_ == 0)
{
uint8_t v___x_2077_; 
v___x_2077_ = l_Lean_Expr_hasLooseBVars(v_e_2053_);
if (v___x_2077_ == 0)
{
lean_object* v___x_2078_; 
v___x_2078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2078_, 0, v_e_2053_);
lean_ctor_set(v___x_2078_, 1, v_a_2056_);
return v___x_2078_;
}
else
{
v___y_2058_ = v___x_2076_;
goto v___jp_2057_;
}
}
else
{
v___y_2058_ = v___x_2076_;
goto v___jp_2057_;
}
v___jp_2057_:
{
if (v___y_2058_ == 0)
{
lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v_fst_2062_; lean_object* v_snd_2063_; lean_object* v_fst_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2071_; 
v___x_2059_ = lean_unsigned_to_nat(0u);
v___x_2060_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__2, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__2_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__2);
v___x_2061_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit(v_subst_2054_, v_e_2053_, v___x_2059_, v___x_2060_, v_a_2055_, v_a_2056_);
v_fst_2062_ = lean_ctor_get(v___x_2061_, 0);
lean_inc(v_fst_2062_);
v_snd_2063_ = lean_ctor_get(v___x_2061_, 1);
lean_inc(v_snd_2063_);
lean_dec_ref(v___x_2061_);
v_fst_2064_ = lean_ctor_get(v_fst_2062_, 0);
v_isSharedCheck_2071_ = !lean_is_exclusive(v_fst_2062_);
if (v_isSharedCheck_2071_ == 0)
{
lean_object* v_unused_2072_; 
v_unused_2072_ = lean_ctor_get(v_fst_2062_, 1);
lean_dec(v_unused_2072_);
v___x_2066_ = v_fst_2062_;
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_fst_2064_);
lean_dec(v_fst_2062_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2069_; 
if (v_isShared_2067_ == 0)
{
lean_ctor_set(v___x_2066_, 1, v_snd_2063_);
v___x_2069_ = v___x_2066_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v_fst_2064_);
lean_ctor_set(v_reuseFailAlloc_2070_, 1, v_snd_2063_);
v___x_2069_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
return v___x_2069_;
}
}
}
else
{
lean_object* v___x_2073_; 
v___x_2073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2073_, 0, v_e_2053_);
lean_ctor_set(v___x_2073_, 1, v_a_2056_);
return v___x_2073_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27___boxed(lean_object* v_e_2079_, lean_object* v_subst_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_){
_start:
{
uint8_t v_a_boxed_2083_; lean_object* v_res_2084_; 
v_a_boxed_2083_ = lean_unbox(v_a_2081_);
v_res_2084_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27(v_e_2079_, v_subst_2080_, v_a_boxed_2083_, v_a_2082_);
lean_dec_ref(v_subst_2080_);
return v_res_2084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevBetaS___redArg(lean_object* v_e_2085_, lean_object* v_subst_2086_, lean_object* v_a_2087_){
_start:
{
uint8_t v___x_2089_; 
v___x_2089_ = l_Lean_Expr_hasLooseBVars(v_e_2085_);
if (v___x_2089_ == 0)
{
lean_object* v___x_2090_; 
v___x_2090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2090_, 0, v_e_2085_);
return v___x_2090_;
}
else
{
lean_object* v___x_2091_; lean_object* v___x_2092_; uint8_t v___x_2093_; 
v___x_2091_ = lean_array_get_size(v_subst_2086_);
v___x_2092_ = lean_unsigned_to_nat(0u);
v___x_2093_ = lean_nat_dec_eq(v___x_2091_, v___x_2092_);
if (v___x_2093_ == 0)
{
lean_object* v___x_2094_; lean_object* v_share_2095_; lean_object* v_maxFVar_2096_; lean_object* v_proofInstInfo_2097_; lean_object* v_inferType_2098_; lean_object* v_getLevel_2099_; lean_object* v_congrInfo_2100_; lean_object* v_defEqI_2101_; lean_object* v_extensions_2102_; lean_object* v_issues_2103_; lean_object* v_canon_2104_; uint8_t v_debug_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2140_; 
v___x_2094_ = lean_st_ref_take(v_a_2087_);
v_share_2095_ = lean_ctor_get(v___x_2094_, 0);
v_maxFVar_2096_ = lean_ctor_get(v___x_2094_, 1);
v_proofInstInfo_2097_ = lean_ctor_get(v___x_2094_, 2);
v_inferType_2098_ = lean_ctor_get(v___x_2094_, 3);
v_getLevel_2099_ = lean_ctor_get(v___x_2094_, 4);
v_congrInfo_2100_ = lean_ctor_get(v___x_2094_, 5);
v_defEqI_2101_ = lean_ctor_get(v___x_2094_, 6);
v_extensions_2102_ = lean_ctor_get(v___x_2094_, 7);
v_issues_2103_ = lean_ctor_get(v___x_2094_, 8);
v_canon_2104_ = lean_ctor_get(v___x_2094_, 9);
v_debug_2105_ = lean_ctor_get_uint8(v___x_2094_, sizeof(void*)*10);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2107_ = v___x_2094_;
v_isShared_2108_ = v_isSharedCheck_2140_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_canon_2104_);
lean_inc(v_issues_2103_);
lean_inc(v_extensions_2102_);
lean_inc(v_defEqI_2101_);
lean_inc(v_congrInfo_2100_);
lean_inc(v_getLevel_2099_);
lean_inc(v_inferType_2098_);
lean_inc(v_proofInstInfo_2097_);
lean_inc(v_maxFVar_2096_);
lean_inc(v_share_2095_);
lean_dec(v___x_2094_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2140_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v___x_2109_; lean_object* v___x_2111_; 
v___x_2109_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__0, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__0_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__0);
if (v_isShared_2108_ == 0)
{
lean_ctor_set(v___x_2107_, 0, v___x_2109_);
v___x_2111_ = v___x_2107_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v___x_2109_);
lean_ctor_set(v_reuseFailAlloc_2139_, 1, v_maxFVar_2096_);
lean_ctor_set(v_reuseFailAlloc_2139_, 2, v_proofInstInfo_2097_);
lean_ctor_set(v_reuseFailAlloc_2139_, 3, v_inferType_2098_);
lean_ctor_set(v_reuseFailAlloc_2139_, 4, v_getLevel_2099_);
lean_ctor_set(v_reuseFailAlloc_2139_, 5, v_congrInfo_2100_);
lean_ctor_set(v_reuseFailAlloc_2139_, 6, v_defEqI_2101_);
lean_ctor_set(v_reuseFailAlloc_2139_, 7, v_extensions_2102_);
lean_ctor_set(v_reuseFailAlloc_2139_, 8, v_issues_2103_);
lean_ctor_set(v_reuseFailAlloc_2139_, 9, v_canon_2104_);
lean_ctor_set_uint8(v_reuseFailAlloc_2139_, sizeof(void*)*10, v_debug_2105_);
v___x_2111_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; uint8_t v_debug_2114_; lean_object* v___x_2115_; lean_object* v_fst_2116_; lean_object* v_snd_2117_; lean_object* v___x_2118_; lean_object* v_maxFVar_2119_; lean_object* v_proofInstInfo_2120_; lean_object* v_inferType_2121_; lean_object* v_getLevel_2122_; lean_object* v_congrInfo_2123_; lean_object* v_defEqI_2124_; lean_object* v_extensions_2125_; lean_object* v_issues_2126_; lean_object* v_canon_2127_; uint8_t v_debug_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2137_; 
v___x_2112_ = lean_st_ref_set(v_a_2087_, v___x_2111_);
v___x_2113_ = lean_st_ref_get(v_a_2087_);
v_debug_2114_ = lean_ctor_get_uint8(v___x_2113_, sizeof(void*)*10);
lean_dec(v___x_2113_);
v___x_2115_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27(v_e_2085_, v_subst_2086_, v_debug_2114_, v_share_2095_);
v_fst_2116_ = lean_ctor_get(v___x_2115_, 0);
lean_inc(v_fst_2116_);
v_snd_2117_ = lean_ctor_get(v___x_2115_, 1);
lean_inc(v_snd_2117_);
lean_dec_ref(v___x_2115_);
v___x_2118_ = lean_st_ref_take(v_a_2087_);
v_maxFVar_2119_ = lean_ctor_get(v___x_2118_, 1);
v_proofInstInfo_2120_ = lean_ctor_get(v___x_2118_, 2);
v_inferType_2121_ = lean_ctor_get(v___x_2118_, 3);
v_getLevel_2122_ = lean_ctor_get(v___x_2118_, 4);
v_congrInfo_2123_ = lean_ctor_get(v___x_2118_, 5);
v_defEqI_2124_ = lean_ctor_get(v___x_2118_, 6);
v_extensions_2125_ = lean_ctor_get(v___x_2118_, 7);
v_issues_2126_ = lean_ctor_get(v___x_2118_, 8);
v_canon_2127_ = lean_ctor_get(v___x_2118_, 9);
v_debug_2128_ = lean_ctor_get_uint8(v___x_2118_, sizeof(void*)*10);
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2137_ == 0)
{
lean_object* v_unused_2138_; 
v_unused_2138_ = lean_ctor_get(v___x_2118_, 0);
lean_dec(v_unused_2138_);
v___x_2130_ = v___x_2118_;
v_isShared_2131_ = v_isSharedCheck_2137_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_canon_2127_);
lean_inc(v_issues_2126_);
lean_inc(v_extensions_2125_);
lean_inc(v_defEqI_2124_);
lean_inc(v_congrInfo_2123_);
lean_inc(v_getLevel_2122_);
lean_inc(v_inferType_2121_);
lean_inc(v_proofInstInfo_2120_);
lean_inc(v_maxFVar_2119_);
lean_dec(v___x_2118_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2137_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v___x_2133_; 
if (v_isShared_2131_ == 0)
{
lean_ctor_set(v___x_2130_, 0, v_snd_2117_);
v___x_2133_ = v___x_2130_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_snd_2117_);
lean_ctor_set(v_reuseFailAlloc_2136_, 1, v_maxFVar_2119_);
lean_ctor_set(v_reuseFailAlloc_2136_, 2, v_proofInstInfo_2120_);
lean_ctor_set(v_reuseFailAlloc_2136_, 3, v_inferType_2121_);
lean_ctor_set(v_reuseFailAlloc_2136_, 4, v_getLevel_2122_);
lean_ctor_set(v_reuseFailAlloc_2136_, 5, v_congrInfo_2123_);
lean_ctor_set(v_reuseFailAlloc_2136_, 6, v_defEqI_2124_);
lean_ctor_set(v_reuseFailAlloc_2136_, 7, v_extensions_2125_);
lean_ctor_set(v_reuseFailAlloc_2136_, 8, v_issues_2126_);
lean_ctor_set(v_reuseFailAlloc_2136_, 9, v_canon_2127_);
lean_ctor_set_uint8(v_reuseFailAlloc_2136_, sizeof(void*)*10, v_debug_2128_);
v___x_2133_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
lean_object* v___x_2134_; lean_object* v___x_2135_; 
v___x_2134_ = lean_st_ref_set(v_a_2087_, v___x_2133_);
v___x_2135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2135_, 0, v_fst_2116_);
return v___x_2135_;
}
}
}
}
}
else
{
lean_object* v___x_2141_; 
v___x_2141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2141_, 0, v_e_2085_);
return v___x_2141_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevBetaS___redArg___boxed(lean_object* v_e_2142_, lean_object* v_subst_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_){
_start:
{
lean_object* v_res_2146_; 
v_res_2146_ = l_Lean_Meta_Sym_instantiateRevBetaS___redArg(v_e_2142_, v_subst_2143_, v_a_2144_);
lean_dec(v_a_2144_);
lean_dec_ref(v_subst_2143_);
return v_res_2146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevBetaS(lean_object* v_e_2147_, lean_object* v_subst_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_){
_start:
{
lean_object* v___x_2156_; 
v___x_2156_ = l_Lean_Meta_Sym_instantiateRevBetaS___redArg(v_e_2147_, v_subst_2148_, v_a_2150_);
return v___x_2156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevBetaS___boxed(lean_object* v_e_2157_, lean_object* v_subst_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_){
_start:
{
lean_object* v_res_2166_; 
v_res_2166_ = l_Lean_Meta_Sym_instantiateRevBetaS(v_e_2157_, v_subst_2158_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_);
lean_dec(v_a_2164_);
lean_dec_ref(v_a_2163_);
lean_dec(v_a_2162_);
lean_dec_ref(v_a_2161_);
lean_dec(v_a_2160_);
lean_dec_ref(v_a_2159_);
lean_dec_ref(v_subst_2158_);
return v_res_2166_;
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
