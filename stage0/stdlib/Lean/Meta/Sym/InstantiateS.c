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
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
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
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0_spec__0(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_betaRevS___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_betaRevS___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_betaRevS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_betaRevS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_betaS___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_betaS___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_betaS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_betaS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0_spec__0(lean_object* v_f_1250_, lean_object* v_a_1251_, uint8_t v___y_1252_, lean_object* v___y_1253_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0_spec__0___boxed(lean_object* v_f_1262_, lean_object* v_a_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_){
_start:
{
uint8_t v___y_1584__boxed_1266_; lean_object* v_res_1267_; 
v___y_1584__boxed_1266_ = lean_unbox(v___y_1264_);
v_res_1267_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0_spec__0(v_f_1262_, v_a_1263_, v___y_1584__boxed_1266_, v___y_1265_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0(lean_object* v_revArgs_1268_, lean_object* v_start_1269_, lean_object* v_b_1270_, lean_object* v_i_1271_, uint8_t v___y_1272_, lean_object* v___y_1273_){
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
v___x_1279_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0_spec__0(v_b_1270_, v___x_1278_, v___y_1272_, v___y_1273_);
v_fst_1280_ = lean_ctor_get(v___x_1279_, 0);
lean_inc(v_fst_1280_);
v_snd_1281_ = lean_ctor_get(v___x_1279_, 1);
lean_inc(v_snd_1281_);
lean_dec_ref(v___x_1279_);
v_b_1270_ = v_fst_1280_;
v_i_1271_ = v_i_1276_;
v___y_1273_ = v_snd_1281_;
goto _start;
}
else
{
lean_object* v___x_1283_; 
lean_dec(v_i_1271_);
v___x_1283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1283_, 0, v_b_1270_);
lean_ctor_set(v___x_1283_, 1, v___y_1273_);
return v___x_1283_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0___boxed(lean_object* v_revArgs_1284_, lean_object* v_start_1285_, lean_object* v_b_1286_, lean_object* v_i_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
uint8_t v___y_1608__boxed_1290_; lean_object* v_res_1291_; 
v___y_1608__boxed_1290_ = lean_unbox(v___y_1288_);
v_res_1291_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0(v_revArgs_1284_, v_start_1285_, v_b_1286_, v_i_1287_, v___y_1608__boxed_1290_, v___y_1289_);
lean_dec(v_start_1285_);
lean_dec_ref(v_revArgs_1284_);
return v_res_1291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go(lean_object* v_revArgs_1292_, lean_object* v_sz_1293_, lean_object* v_e_1294_, lean_object* v_i_1295_, uint8_t v_a_1296_, lean_object* v_a_1297_){
_start:
{
switch(lean_obj_tag(v_e_1294_))
{
case 6:
{
lean_object* v_body_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; uint8_t v___x_1301_; 
v_body_1298_ = lean_ctor_get(v_e_1294_, 2);
lean_inc_ref(v_body_1298_);
lean_dec_ref(v_e_1294_);
v___x_1299_ = lean_unsigned_to_nat(1u);
v___x_1300_ = lean_nat_add(v_i_1295_, v___x_1299_);
lean_dec(v_i_1295_);
v___x_1301_ = lean_nat_dec_lt(v___x_1300_, v_sz_1293_);
if (v___x_1301_ == 0)
{
lean_object* v___x_1302_; 
lean_dec(v___x_1300_);
v___x_1302_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27(v_body_1298_, v_revArgs_1292_, v_a_1296_, v_a_1297_);
return v___x_1302_;
}
else
{
v_e_1294_ = v_body_1298_;
v_i_1295_ = v___x_1300_;
goto _start;
}
}
case 10:
{
lean_object* v_expr_1304_; 
v_expr_1304_ = lean_ctor_get(v_e_1294_, 1);
lean_inc_ref(v_expr_1304_);
lean_dec_ref(v_e_1294_);
v_e_1294_ = v_expr_1304_;
goto _start;
}
default: 
{
lean_object* v_n_1306_; lean_object* v___x_1307_; lean_object* v_fst_1308_; lean_object* v_snd_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
v_n_1306_ = lean_nat_sub(v_sz_1293_, v_i_1295_);
lean_dec(v_i_1295_);
v___x_1307_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27(v_e_1294_, v_n_1306_, v_sz_1293_, v_revArgs_1292_, v_a_1296_, v_a_1297_);
v_fst_1308_ = lean_ctor_get(v___x_1307_, 0);
lean_inc(v_fst_1308_);
v_snd_1309_ = lean_ctor_get(v___x_1307_, 1);
lean_inc(v_snd_1309_);
lean_dec_ref(v___x_1307_);
v___x_1310_ = lean_unsigned_to_nat(0u);
v___x_1311_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0(v_revArgs_1292_, v___x_1310_, v_fst_1308_, v_n_1306_, v_a_1296_, v_snd_1309_);
return v___x_1311_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go___boxed(lean_object* v_revArgs_1312_, lean_object* v_sz_1313_, lean_object* v_e_1314_, lean_object* v_i_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_){
_start:
{
uint8_t v_a_boxed_1318_; lean_object* v_res_1319_; 
v_a_boxed_1318_ = lean_unbox(v_a_1316_);
v_res_1319_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go(v_revArgs_1312_, v_sz_1313_, v_e_1314_, v_i_1315_, v_a_boxed_1318_, v_a_1317_);
lean_dec(v_sz_1313_);
lean_dec_ref(v_revArgs_1312_);
return v_res_1319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27(lean_object* v_f_1320_, lean_object* v_revArgs_1321_, uint8_t v_a_1322_, lean_object* v_a_1323_){
_start:
{
lean_object* v_sz_1324_; lean_object* v___x_1325_; uint8_t v___x_1326_; 
v_sz_1324_ = lean_array_get_size(v_revArgs_1321_);
v___x_1325_ = lean_unsigned_to_nat(0u);
v___x_1326_ = lean_nat_dec_eq(v_sz_1324_, v___x_1325_);
if (v___x_1326_ == 0)
{
lean_object* v___x_1327_; 
v___x_1327_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go(v_revArgs_1321_, v_sz_1324_, v_f_1320_, v___x_1325_, v_a_1322_, v_a_1323_);
return v___x_1327_;
}
else
{
lean_object* v___x_1328_; 
v___x_1328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1328_, 0, v_f_1320_);
lean_ctor_set(v___x_1328_, 1, v_a_1323_);
return v___x_1328_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27___boxed(lean_object* v_f_1329_, lean_object* v_revArgs_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_){
_start:
{
uint8_t v_a_boxed_1333_; lean_object* v_res_1334_; 
v_a_boxed_1333_ = lean_unbox(v_a_1331_);
v_res_1334_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27(v_f_1329_, v_revArgs_1330_, v_a_boxed_1333_, v_a_1332_);
lean_dec_ref(v_revArgs_1330_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_1335_, lean_object* v_x_1336_){
_start:
{
if (lean_obj_tag(v_x_1336_) == 0)
{
return v_x_1335_;
}
else
{
lean_object* v_key_1337_; lean_object* v_value_1338_; lean_object* v_tail_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1366_; 
v_key_1337_ = lean_ctor_get(v_x_1336_, 0);
v_value_1338_ = lean_ctor_get(v_x_1336_, 1);
v_tail_1339_ = lean_ctor_get(v_x_1336_, 2);
v_isSharedCheck_1366_ = !lean_is_exclusive(v_x_1336_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1341_ = v_x_1336_;
v_isShared_1342_ = v_isSharedCheck_1366_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_tail_1339_);
lean_inc(v_value_1338_);
lean_inc(v_key_1337_);
lean_dec(v_x_1336_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1366_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v_fst_1343_; lean_object* v_snd_1344_; lean_object* v___x_1345_; uint64_t v___x_1346_; uint64_t v___x_1347_; uint64_t v___x_1348_; uint64_t v___x_1349_; uint64_t v___x_1350_; uint64_t v_fold_1351_; uint64_t v___x_1352_; uint64_t v___x_1353_; uint64_t v___x_1354_; size_t v___x_1355_; size_t v___x_1356_; size_t v___x_1357_; size_t v___x_1358_; size_t v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1362_; 
v_fst_1343_ = lean_ctor_get(v_key_1337_, 0);
v_snd_1344_ = lean_ctor_get(v_key_1337_, 1);
v___x_1345_ = lean_array_get_size(v_x_1335_);
v___x_1346_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_1343_);
v___x_1347_ = lean_uint64_of_nat(v_snd_1344_);
v___x_1348_ = lean_uint64_mix_hash(v___x_1346_, v___x_1347_);
v___x_1349_ = 32ULL;
v___x_1350_ = lean_uint64_shift_right(v___x_1348_, v___x_1349_);
v_fold_1351_ = lean_uint64_xor(v___x_1348_, v___x_1350_);
v___x_1352_ = 16ULL;
v___x_1353_ = lean_uint64_shift_right(v_fold_1351_, v___x_1352_);
v___x_1354_ = lean_uint64_xor(v_fold_1351_, v___x_1353_);
v___x_1355_ = lean_uint64_to_usize(v___x_1354_);
v___x_1356_ = lean_usize_of_nat(v___x_1345_);
v___x_1357_ = ((size_t)1ULL);
v___x_1358_ = lean_usize_sub(v___x_1356_, v___x_1357_);
v___x_1359_ = lean_usize_land(v___x_1355_, v___x_1358_);
v___x_1360_ = lean_array_uget_borrowed(v_x_1335_, v___x_1359_);
lean_inc(v___x_1360_);
if (v_isShared_1342_ == 0)
{
lean_ctor_set(v___x_1341_, 2, v___x_1360_);
v___x_1362_ = v___x_1341_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_key_1337_);
lean_ctor_set(v_reuseFailAlloc_1365_, 1, v_value_1338_);
lean_ctor_set(v_reuseFailAlloc_1365_, 2, v___x_1360_);
v___x_1362_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
lean_object* v___x_1363_; 
v___x_1363_ = lean_array_uset(v_x_1335_, v___x_1359_, v___x_1362_);
v_x_1335_ = v___x_1363_;
v_x_1336_ = v_tail_1339_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2___redArg(lean_object* v_i_1367_, lean_object* v_source_1368_, lean_object* v_target_1369_){
_start:
{
lean_object* v___x_1370_; uint8_t v___x_1371_; 
v___x_1370_ = lean_array_get_size(v_source_1368_);
v___x_1371_ = lean_nat_dec_lt(v_i_1367_, v___x_1370_);
if (v___x_1371_ == 0)
{
lean_dec_ref(v_source_1368_);
lean_dec(v_i_1367_);
return v_target_1369_;
}
else
{
lean_object* v_es_1372_; lean_object* v___x_1373_; lean_object* v_source_1374_; lean_object* v_target_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; 
v_es_1372_ = lean_array_fget(v_source_1368_, v_i_1367_);
v___x_1373_ = lean_box(0);
v_source_1374_ = lean_array_fset(v_source_1368_, v_i_1367_, v___x_1373_);
v_target_1375_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3___redArg(v_target_1369_, v_es_1372_);
v___x_1376_ = lean_unsigned_to_nat(1u);
v___x_1377_ = lean_nat_add(v_i_1367_, v___x_1376_);
lean_dec(v_i_1367_);
v_i_1367_ = v___x_1377_;
v_source_1368_ = v_source_1374_;
v_target_1369_ = v_target_1375_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1___redArg(lean_object* v_data_1379_){
_start:
{
lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v_nbuckets_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; 
v___x_1380_ = lean_array_get_size(v_data_1379_);
v___x_1381_ = lean_unsigned_to_nat(2u);
v_nbuckets_1382_ = lean_nat_mul(v___x_1380_, v___x_1381_);
v___x_1383_ = lean_unsigned_to_nat(0u);
v___x_1384_ = lean_box(0);
v___x_1385_ = lean_mk_array(v_nbuckets_1382_, v___x_1384_);
v___x_1386_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2___redArg(v___x_1383_, v_data_1379_, v___x_1385_);
return v___x_1386_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(lean_object* v_a_1387_, lean_object* v_b_1388_, lean_object* v_x_1389_){
_start:
{
if (lean_obj_tag(v_x_1389_) == 0)
{
lean_dec(v_b_1388_);
lean_dec_ref(v_a_1387_);
return v_x_1389_;
}
else
{
lean_object* v_key_1390_; lean_object* v_value_1391_; lean_object* v_tail_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1411_; 
v_key_1390_ = lean_ctor_get(v_x_1389_, 0);
v_value_1391_ = lean_ctor_get(v_x_1389_, 1);
v_tail_1392_ = lean_ctor_get(v_x_1389_, 2);
v_isSharedCheck_1411_ = !lean_is_exclusive(v_x_1389_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1394_ = v_x_1389_;
v_isShared_1395_ = v_isSharedCheck_1411_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_tail_1392_);
lean_inc(v_value_1391_);
lean_inc(v_key_1390_);
lean_dec(v_x_1389_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1411_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
uint8_t v___y_1397_; lean_object* v_fst_1405_; lean_object* v_snd_1406_; lean_object* v_fst_1407_; lean_object* v_snd_1408_; uint8_t v___x_1409_; 
v_fst_1405_ = lean_ctor_get(v_key_1390_, 0);
v_snd_1406_ = lean_ctor_get(v_key_1390_, 1);
v_fst_1407_ = lean_ctor_get(v_a_1387_, 0);
v_snd_1408_ = lean_ctor_get(v_a_1387_, 1);
v___x_1409_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_1405_, v_fst_1407_);
if (v___x_1409_ == 0)
{
v___y_1397_ = v___x_1409_;
goto v___jp_1396_;
}
else
{
uint8_t v___x_1410_; 
v___x_1410_ = lean_nat_dec_eq(v_snd_1406_, v_snd_1408_);
v___y_1397_ = v___x_1410_;
goto v___jp_1396_;
}
v___jp_1396_:
{
if (v___y_1397_ == 0)
{
lean_object* v___x_1398_; lean_object* v___x_1400_; 
v___x_1398_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(v_a_1387_, v_b_1388_, v_tail_1392_);
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 2, v___x_1398_);
v___x_1400_ = v___x_1394_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v_key_1390_);
lean_ctor_set(v_reuseFailAlloc_1401_, 1, v_value_1391_);
lean_ctor_set(v_reuseFailAlloc_1401_, 2, v___x_1398_);
v___x_1400_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
return v___x_1400_;
}
}
else
{
lean_object* v___x_1403_; 
lean_dec(v_value_1391_);
lean_dec(v_key_1390_);
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 1, v_b_1388_);
lean_ctor_set(v___x_1394_, 0, v_a_1387_);
v___x_1403_ = v___x_1394_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v_a_1387_);
lean_ctor_set(v_reuseFailAlloc_1404_, 1, v_b_1388_);
lean_ctor_set(v_reuseFailAlloc_1404_, 2, v_tail_1392_);
v___x_1403_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
return v___x_1403_;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(lean_object* v_a_1412_, lean_object* v_x_1413_){
_start:
{
if (lean_obj_tag(v_x_1413_) == 0)
{
uint8_t v___x_1414_; 
v___x_1414_ = 0;
return v___x_1414_;
}
else
{
lean_object* v_key_1415_; lean_object* v_tail_1416_; uint8_t v___y_1418_; lean_object* v_fst_1420_; lean_object* v_snd_1421_; lean_object* v_fst_1422_; lean_object* v_snd_1423_; uint8_t v___x_1424_; 
v_key_1415_ = lean_ctor_get(v_x_1413_, 0);
v_tail_1416_ = lean_ctor_get(v_x_1413_, 2);
v_fst_1420_ = lean_ctor_get(v_key_1415_, 0);
v_snd_1421_ = lean_ctor_get(v_key_1415_, 1);
v_fst_1422_ = lean_ctor_get(v_a_1412_, 0);
v_snd_1423_ = lean_ctor_get(v_a_1412_, 1);
v___x_1424_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_1420_, v_fst_1422_);
if (v___x_1424_ == 0)
{
v___y_1418_ = v___x_1424_;
goto v___jp_1417_;
}
else
{
uint8_t v___x_1425_; 
v___x_1425_ = lean_nat_dec_eq(v_snd_1421_, v_snd_1423_);
v___y_1418_ = v___x_1425_;
goto v___jp_1417_;
}
v___jp_1417_:
{
if (v___y_1418_ == 0)
{
v_x_1413_ = v_tail_1416_;
goto _start;
}
else
{
return v___y_1418_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg___boxed(lean_object* v_a_1426_, lean_object* v_x_1427_){
_start:
{
uint8_t v_res_1428_; lean_object* v_r_1429_; 
v_res_1428_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_a_1426_, v_x_1427_);
lean_dec(v_x_1427_);
lean_dec_ref(v_a_1426_);
v_r_1429_ = lean_box(v_res_1428_);
return v_r_1429_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0___redArg(lean_object* v_m_1430_, lean_object* v_a_1431_, lean_object* v_b_1432_){
_start:
{
lean_object* v_size_1433_; lean_object* v_buckets_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1481_; 
v_size_1433_ = lean_ctor_get(v_m_1430_, 0);
v_buckets_1434_ = lean_ctor_get(v_m_1430_, 1);
v_isSharedCheck_1481_ = !lean_is_exclusive(v_m_1430_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1436_ = v_m_1430_;
v_isShared_1437_ = v_isSharedCheck_1481_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_buckets_1434_);
lean_inc(v_size_1433_);
lean_dec(v_m_1430_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1481_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v_fst_1438_; lean_object* v_snd_1439_; lean_object* v___x_1440_; uint64_t v___x_1441_; uint64_t v___x_1442_; uint64_t v___x_1443_; uint64_t v___x_1444_; uint64_t v___x_1445_; uint64_t v_fold_1446_; uint64_t v___x_1447_; uint64_t v___x_1448_; uint64_t v___x_1449_; size_t v___x_1450_; size_t v___x_1451_; size_t v___x_1452_; size_t v___x_1453_; size_t v___x_1454_; lean_object* v_bkt_1455_; uint8_t v___x_1456_; 
v_fst_1438_ = lean_ctor_get(v_a_1431_, 0);
v_snd_1439_ = lean_ctor_get(v_a_1431_, 1);
v___x_1440_ = lean_array_get_size(v_buckets_1434_);
v___x_1441_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_1438_);
v___x_1442_ = lean_uint64_of_nat(v_snd_1439_);
v___x_1443_ = lean_uint64_mix_hash(v___x_1441_, v___x_1442_);
v___x_1444_ = 32ULL;
v___x_1445_ = lean_uint64_shift_right(v___x_1443_, v___x_1444_);
v_fold_1446_ = lean_uint64_xor(v___x_1443_, v___x_1445_);
v___x_1447_ = 16ULL;
v___x_1448_ = lean_uint64_shift_right(v_fold_1446_, v___x_1447_);
v___x_1449_ = lean_uint64_xor(v_fold_1446_, v___x_1448_);
v___x_1450_ = lean_uint64_to_usize(v___x_1449_);
v___x_1451_ = lean_usize_of_nat(v___x_1440_);
v___x_1452_ = ((size_t)1ULL);
v___x_1453_ = lean_usize_sub(v___x_1451_, v___x_1452_);
v___x_1454_ = lean_usize_land(v___x_1450_, v___x_1453_);
v_bkt_1455_ = lean_array_uget_borrowed(v_buckets_1434_, v___x_1454_);
v___x_1456_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_a_1431_, v_bkt_1455_);
if (v___x_1456_ == 0)
{
lean_object* v___x_1457_; lean_object* v_size_x27_1458_; lean_object* v___x_1459_; lean_object* v_buckets_x27_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; uint8_t v___x_1466_; 
v___x_1457_ = lean_unsigned_to_nat(1u);
v_size_x27_1458_ = lean_nat_add(v_size_1433_, v___x_1457_);
lean_dec(v_size_1433_);
lean_inc(v_bkt_1455_);
v___x_1459_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1459_, 0, v_a_1431_);
lean_ctor_set(v___x_1459_, 1, v_b_1432_);
lean_ctor_set(v___x_1459_, 2, v_bkt_1455_);
v_buckets_x27_1460_ = lean_array_uset(v_buckets_1434_, v___x_1454_, v___x_1459_);
v___x_1461_ = lean_unsigned_to_nat(4u);
v___x_1462_ = lean_nat_mul(v_size_x27_1458_, v___x_1461_);
v___x_1463_ = lean_unsigned_to_nat(3u);
v___x_1464_ = lean_nat_div(v___x_1462_, v___x_1463_);
lean_dec(v___x_1462_);
v___x_1465_ = lean_array_get_size(v_buckets_x27_1460_);
v___x_1466_ = lean_nat_dec_le(v___x_1464_, v___x_1465_);
lean_dec(v___x_1464_);
if (v___x_1466_ == 0)
{
lean_object* v_val_1467_; lean_object* v___x_1469_; 
v_val_1467_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1___redArg(v_buckets_x27_1460_);
if (v_isShared_1437_ == 0)
{
lean_ctor_set(v___x_1436_, 1, v_val_1467_);
lean_ctor_set(v___x_1436_, 0, v_size_x27_1458_);
v___x_1469_ = v___x_1436_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v_size_x27_1458_);
lean_ctor_set(v_reuseFailAlloc_1470_, 1, v_val_1467_);
v___x_1469_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
return v___x_1469_;
}
}
else
{
lean_object* v___x_1472_; 
if (v_isShared_1437_ == 0)
{
lean_ctor_set(v___x_1436_, 1, v_buckets_x27_1460_);
lean_ctor_set(v___x_1436_, 0, v_size_x27_1458_);
v___x_1472_ = v___x_1436_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_size_x27_1458_);
lean_ctor_set(v_reuseFailAlloc_1473_, 1, v_buckets_x27_1460_);
v___x_1472_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
return v___x_1472_;
}
}
}
else
{
lean_object* v___x_1474_; lean_object* v_buckets_x27_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1479_; 
lean_inc(v_bkt_1455_);
v___x_1474_ = lean_box(0);
v_buckets_x27_1475_ = lean_array_uset(v_buckets_1434_, v___x_1454_, v___x_1474_);
v___x_1476_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(v_a_1431_, v_b_1432_, v_bkt_1455_);
v___x_1477_ = lean_array_uset(v_buckets_x27_1475_, v___x_1454_, v___x_1476_);
if (v_isShared_1437_ == 0)
{
lean_ctor_set(v___x_1436_, 1, v___x_1477_);
v___x_1479_ = v___x_1436_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v_size_1433_);
lean_ctor_set(v_reuseFailAlloc_1480_, 1, v___x_1477_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
return v___x_1479_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(lean_object* v_key_1482_, lean_object* v_r_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_){
_start:
{
lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; 
lean_inc_ref(v_r_1483_);
v___x_1486_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1484_, v_key_1482_, v_r_1483_);
v___x_1487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1487_, 0, v_r_1483_);
lean_ctor_set(v___x_1487_, 1, v___x_1486_);
v___x_1488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1487_);
lean_ctor_set(v___x_1488_, 1, v_a_1485_);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save(lean_object* v_key_1489_, lean_object* v_r_1490_, lean_object* v_a_1491_, uint8_t v_a_1492_, lean_object* v_a_1493_){
_start:
{
lean_object* v___x_1494_; 
v___x_1494_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_1489_, v_r_1490_, v_a_1491_, v_a_1493_);
return v___x_1494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___boxed(lean_object* v_key_1495_, lean_object* v_r_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_){
_start:
{
uint8_t v_a_boxed_1500_; lean_object* v_res_1501_; 
v_a_boxed_1500_ = lean_unbox(v_a_1498_);
v_res_1501_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save(v_key_1495_, v_r_1496_, v_a_1497_, v_a_boxed_1500_, v_a_1499_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0(lean_object* v_00_u03b2_1502_, lean_object* v_m_1503_, lean_object* v_a_1504_, lean_object* v_b_1505_){
_start:
{
lean_object* v___x_1506_; 
v___x_1506_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0___redArg(v_m_1503_, v_a_1504_, v_b_1505_);
return v___x_1506_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0(lean_object* v_00_u03b2_1507_, lean_object* v_a_1508_, lean_object* v_x_1509_){
_start:
{
uint8_t v___x_1510_; 
v___x_1510_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_a_1508_, v_x_1509_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1511_, lean_object* v_a_1512_, lean_object* v_x_1513_){
_start:
{
uint8_t v_res_1514_; lean_object* v_r_1515_; 
v_res_1514_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0(v_00_u03b2_1511_, v_a_1512_, v_x_1513_);
lean_dec(v_x_1513_);
lean_dec_ref(v_a_1512_);
v_r_1515_ = lean_box(v_res_1514_);
return v_r_1515_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1(lean_object* v_00_u03b2_1516_, lean_object* v_data_1517_){
_start:
{
lean_object* v___x_1518_; 
v___x_1518_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1___redArg(v_data_1517_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2(lean_object* v_00_u03b2_1519_, lean_object* v_a_1520_, lean_object* v_b_1521_, lean_object* v_x_1522_){
_start:
{
lean_object* v___x_1523_; 
v___x_1523_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(v_a_1520_, v_b_1521_, v_x_1522_);
return v___x_1523_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1524_, lean_object* v_i_1525_, lean_object* v_source_1526_, lean_object* v_target_1527_){
_start:
{
lean_object* v___x_1528_; 
v___x_1528_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2___redArg(v_i_1525_, v_source_1526_, v_target_1527_);
return v___x_1528_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1529_, lean_object* v_x_1530_, lean_object* v_x_1531_){
_start:
{
lean_object* v___x_1532_; 
v___x_1532_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1530_, v_x_1531_);
return v___x_1532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0___redArg(lean_object* v_idx_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_){
_start:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v_fst_1538_; lean_object* v_snd_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1547_; 
v___x_1536_ = l_Lean_Expr_bvar___override(v_idx_1533_);
v___x_1537_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1536_, v___y_1535_);
v_fst_1538_ = lean_ctor_get(v___x_1537_, 0);
v_snd_1539_ = lean_ctor_get(v___x_1537_, 1);
v_isSharedCheck_1547_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1547_ == 0)
{
v___x_1541_ = v___x_1537_;
v_isShared_1542_ = v_isSharedCheck_1547_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_snd_1539_);
lean_inc(v_fst_1538_);
lean_dec(v___x_1537_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1547_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v___x_1544_; 
if (v_isShared_1542_ == 0)
{
lean_ctor_set(v___x_1541_, 1, v___y_1534_);
v___x_1544_ = v___x_1541_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v_fst_1538_);
lean_ctor_set(v_reuseFailAlloc_1546_, 1, v___y_1534_);
v___x_1544_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
lean_object* v___x_1545_; 
v___x_1545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1545_, 0, v___x_1544_);
lean_ctor_set(v___x_1545_, 1, v_snd_1539_);
return v___x_1545_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0(lean_object* v_idx_1548_, lean_object* v___y_1549_, uint8_t v___y_1550_, lean_object* v___y_1551_){
_start:
{
lean_object* v___x_1552_; 
v___x_1552_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0___redArg(v_idx_1548_, v___y_1549_, v___y_1551_);
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0___boxed(lean_object* v_idx_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_){
_start:
{
uint8_t v___y_1291__boxed_1557_; lean_object* v_res_1558_; 
v___y_1291__boxed_1557_ = lean_unbox(v___y_1555_);
v_res_1558_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0(v_idx_1553_, v___y_1554_, v___y_1291__boxed_1557_, v___y_1556_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(lean_object* v_subst_1559_, lean_object* v_e_1560_, lean_object* v_bidx_1561_, lean_object* v_offset_1562_, lean_object* v_a_1563_, uint8_t v_a_1564_, lean_object* v_a_1565_){
_start:
{
uint8_t v___x_1566_; 
v___x_1566_ = lean_nat_dec_le(v_offset_1562_, v_bidx_1561_);
if (v___x_1566_ == 0)
{
lean_object* v___x_1567_; lean_object* v___x_1568_; 
v___x_1567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1567_, 0, v_e_1560_);
lean_ctor_set(v___x_1567_, 1, v_a_1563_);
v___x_1568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1567_);
lean_ctor_set(v___x_1568_, 1, v_a_1565_);
return v___x_1568_;
}
else
{
lean_object* v_n_1569_; lean_object* v___x_1570_; uint8_t v___x_1571_; 
lean_dec_ref(v_e_1560_);
v_n_1569_ = lean_array_get_size(v_subst_1559_);
v___x_1570_ = lean_nat_add(v_offset_1562_, v_n_1569_);
v___x_1571_ = lean_nat_dec_lt(v_bidx_1561_, v___x_1570_);
lean_dec(v___x_1570_);
if (v___x_1571_ == 0)
{
lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1572_ = lean_nat_sub(v_bidx_1561_, v_n_1569_);
v___x_1573_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0___redArg(v___x_1572_, v_a_1563_, v_a_1565_);
return v___x_1573_;
}
else
{
lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v_v_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v_fst_1581_; lean_object* v_snd_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1590_; 
v___x_1574_ = lean_nat_sub(v_bidx_1561_, v_offset_1562_);
v___x_1575_ = lean_nat_sub(v_n_1569_, v___x_1574_);
lean_dec(v___x_1574_);
v___x_1576_ = lean_unsigned_to_nat(1u);
v___x_1577_ = lean_nat_sub(v___x_1575_, v___x_1576_);
lean_dec(v___x_1575_);
v_v_1578_ = lean_array_fget_borrowed(v_subst_1559_, v___x_1577_);
lean_dec(v___x_1577_);
v___x_1579_ = lean_unsigned_to_nat(0u);
lean_inc(v_v_1578_);
v___x_1580_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(v_v_1578_, v___x_1579_, v_offset_1562_, v_a_1564_, v_a_1565_);
v_fst_1581_ = lean_ctor_get(v___x_1580_, 0);
v_snd_1582_ = lean_ctor_get(v___x_1580_, 1);
v_isSharedCheck_1590_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1584_ = v___x_1580_;
v_isShared_1585_ = v_isSharedCheck_1590_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_snd_1582_);
lean_inc(v_fst_1581_);
lean_dec(v___x_1580_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1590_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1587_; 
if (v_isShared_1585_ == 0)
{
lean_ctor_set(v___x_1584_, 1, v_a_1563_);
v___x_1587_ = v___x_1584_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_fst_1581_);
lean_ctor_set(v_reuseFailAlloc_1589_, 1, v_a_1563_);
v___x_1587_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
lean_object* v___x_1588_; 
v___x_1588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1587_);
lean_ctor_set(v___x_1588_, 1, v_snd_1582_);
return v___x_1588_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar___boxed(lean_object* v_subst_1591_, lean_object* v_e_1592_, lean_object* v_bidx_1593_, lean_object* v_offset_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_){
_start:
{
uint8_t v_a_boxed_1598_; lean_object* v_res_1599_; 
v_a_boxed_1598_ = lean_unbox(v_a_1596_);
v_res_1599_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(v_subst_1591_, v_e_1592_, v_bidx_1593_, v_offset_1594_, v_a_1595_, v_a_boxed_1598_, v_a_1597_);
lean_dec(v_offset_1594_);
lean_dec(v_bidx_1593_);
lean_dec_ref(v_subst_1591_);
return v_res_1599_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__3(void){
_start:
{
lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; 
v___x_1603_ = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__2));
v___x_1604_ = lean_unsigned_to_nat(25u);
v___x_1605_ = lean_unsigned_to_nat(148u);
v___x_1606_ = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__1));
v___x_1607_ = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__0));
v___x_1608_ = l_mkPanicMessageWithDecl(v___x_1607_, v___x_1606_, v___x_1605_, v___x_1604_, v___x_1603_);
return v___x_1608_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__1(void){
_start:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1610_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__2));
v___x_1611_ = lean_unsigned_to_nat(11u);
v___x_1612_ = lean_unsigned_to_nat(165u);
v___x_1613_ = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__0));
v___x_1614_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__3));
v___x_1615_ = l_mkPanicMessageWithDecl(v___x_1614_, v___x_1613_, v___x_1612_, v___x_1611_, v___x_1610_);
return v___x_1615_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta(lean_object* v_subst_1616_, lean_object* v_e_1617_, lean_object* v_f_1618_, lean_object* v_argsRev_1619_, lean_object* v_offset_1620_, uint8_t v_modified_1621_, lean_object* v_a_1622_, uint8_t v_a_1623_, lean_object* v_a_1624_){
_start:
{
switch(lean_obj_tag(v_f_1618_))
{
case 5:
{
lean_object* v_fn_1625_; lean_object* v_arg_1626_; lean_object* v___x_1627_; lean_object* v_fst_1628_; lean_object* v_snd_1629_; lean_object* v_fst_1630_; lean_object* v_snd_1631_; lean_object* v___x_1632_; 
v_fn_1625_ = lean_ctor_get(v_f_1618_, 0);
lean_inc_ref(v_fn_1625_);
v_arg_1626_ = lean_ctor_get(v_f_1618_, 1);
lean_inc_ref_n(v_arg_1626_, 2);
lean_dec_ref(v_f_1618_);
lean_inc(v_offset_1620_);
v___x_1627_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1616_, v_arg_1626_, v_offset_1620_, v_a_1622_, v_a_1623_, v_a_1624_);
v_fst_1628_ = lean_ctor_get(v___x_1627_, 0);
lean_inc(v_fst_1628_);
v_snd_1629_ = lean_ctor_get(v___x_1627_, 1);
lean_inc(v_snd_1629_);
lean_dec_ref(v___x_1627_);
v_fst_1630_ = lean_ctor_get(v_fst_1628_, 0);
lean_inc_n(v_fst_1630_, 2);
v_snd_1631_ = lean_ctor_get(v_fst_1628_, 1);
lean_inc(v_snd_1631_);
lean_dec(v_fst_1628_);
v___x_1632_ = lean_array_push(v_argsRev_1619_, v_fst_1630_);
if (v_modified_1621_ == 0)
{
uint8_t v___x_1633_; 
v___x_1633_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_1626_, v_fst_1630_);
lean_dec(v_fst_1630_);
lean_dec_ref(v_arg_1626_);
if (v___x_1633_ == 0)
{
uint8_t v___x_1634_; 
v___x_1634_ = 1;
v_f_1618_ = v_fn_1625_;
v_argsRev_1619_ = v___x_1632_;
v_modified_1621_ = v___x_1634_;
v_a_1622_ = v_snd_1631_;
v_a_1624_ = v_snd_1629_;
goto _start;
}
else
{
v_f_1618_ = v_fn_1625_;
v_argsRev_1619_ = v___x_1632_;
v_a_1622_ = v_snd_1631_;
v_a_1624_ = v_snd_1629_;
goto _start;
}
}
else
{
lean_dec(v_fst_1630_);
lean_dec_ref(v_arg_1626_);
v_f_1618_ = v_fn_1625_;
v_argsRev_1619_ = v___x_1632_;
v_a_1622_ = v_snd_1631_;
v_a_1624_ = v_snd_1629_;
goto _start;
}
}
case 0:
{
lean_object* v_deBruijnIndex_1638_; lean_object* v___x_1639_; lean_object* v_fst_1640_; lean_object* v_snd_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1670_; 
v_deBruijnIndex_1638_ = lean_ctor_get(v_f_1618_, 0);
lean_inc_ref(v_f_1618_);
v___x_1639_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(v_subst_1616_, v_f_1618_, v_deBruijnIndex_1638_, v_offset_1620_, v_a_1622_, v_a_1623_, v_a_1624_);
lean_dec(v_offset_1620_);
v_fst_1640_ = lean_ctor_get(v___x_1639_, 0);
v_snd_1641_ = lean_ctor_get(v___x_1639_, 1);
v_isSharedCheck_1670_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1670_ == 0)
{
v___x_1643_ = v___x_1639_;
v_isShared_1644_ = v_isSharedCheck_1670_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_snd_1641_);
lean_inc(v_fst_1640_);
lean_dec(v___x_1639_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1670_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v_fst_1645_; lean_object* v_snd_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1669_; 
v_fst_1645_ = lean_ctor_get(v_fst_1640_, 0);
v_snd_1646_ = lean_ctor_get(v_fst_1640_, 1);
v_isSharedCheck_1669_ = !lean_is_exclusive(v_fst_1640_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1648_ = v_fst_1640_;
v_isShared_1649_ = v_isSharedCheck_1669_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_snd_1646_);
lean_inc(v_fst_1645_);
lean_dec(v_fst_1640_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1669_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
if (v_modified_1621_ == 0)
{
uint8_t v___x_1664_; 
v___x_1664_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_f_1618_, v_fst_1645_);
lean_dec_ref(v_f_1618_);
if (v___x_1664_ == 0)
{
lean_del_object(v___x_1643_);
lean_dec_ref(v_e_1617_);
goto v___jp_1650_;
}
else
{
lean_object* v___x_1666_; 
lean_del_object(v___x_1648_);
lean_dec(v_fst_1645_);
lean_dec_ref(v_argsRev_1619_);
if (v_isShared_1644_ == 0)
{
lean_ctor_set(v___x_1643_, 1, v_snd_1646_);
lean_ctor_set(v___x_1643_, 0, v_e_1617_);
v___x_1666_ = v___x_1643_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_e_1617_);
lean_ctor_set(v_reuseFailAlloc_1668_, 1, v_snd_1646_);
v___x_1666_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
lean_object* v___x_1667_; 
v___x_1667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1666_);
lean_ctor_set(v___x_1667_, 1, v_snd_1641_);
return v___x_1667_;
}
}
}
else
{
lean_del_object(v___x_1643_);
lean_dec_ref(v_f_1618_);
lean_dec_ref(v_e_1617_);
goto v___jp_1650_;
}
v___jp_1650_:
{
lean_object* v___x_1651_; lean_object* v_fst_1652_; lean_object* v_snd_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1663_; 
v___x_1651_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27(v_fst_1645_, v_argsRev_1619_, v_a_1623_, v_snd_1641_);
lean_dec_ref(v_argsRev_1619_);
v_fst_1652_ = lean_ctor_get(v___x_1651_, 0);
v_snd_1653_ = lean_ctor_get(v___x_1651_, 1);
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1651_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1655_ = v___x_1651_;
v_isShared_1656_ = v_isSharedCheck_1663_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_snd_1653_);
lean_inc(v_fst_1652_);
lean_dec(v___x_1651_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1663_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1658_; 
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 1, v_snd_1646_);
v___x_1658_ = v___x_1655_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_fst_1652_);
lean_ctor_set(v_reuseFailAlloc_1662_, 1, v_snd_1646_);
v___x_1658_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
lean_object* v___x_1660_; 
if (v_isShared_1649_ == 0)
{
lean_ctor_set(v___x_1648_, 1, v_snd_1653_);
lean_ctor_set(v___x_1648_, 0, v___x_1658_);
v___x_1660_ = v___x_1648_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v___x_1658_);
lean_ctor_set(v_reuseFailAlloc_1661_, 1, v_snd_1653_);
v___x_1660_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
return v___x_1660_;
}
}
}
}
}
}
}
default: 
{
lean_object* v___x_1671_; lean_object* v___x_1672_; 
lean_dec(v_offset_1620_);
lean_dec_ref(v_argsRev_1619_);
lean_dec_ref(v_f_1618_);
lean_dec_ref(v_e_1617_);
v___x_1671_ = lean_obj_once(&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__1, &l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__1_once, _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__1);
v___x_1672_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9(v___x_1671_, v_a_1622_, v_a_1623_, v_a_1624_);
return v___x_1672_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg(lean_object* v_subst_1673_, lean_object* v_e_1674_, lean_object* v_f_1675_, lean_object* v_arg_1676_, lean_object* v_offset_1677_, lean_object* v_a_1678_, uint8_t v_a_1679_, lean_object* v_a_1680_){
_start:
{
lean_object* v___x_1681_; lean_object* v_fst_1682_; lean_object* v_snd_1683_; lean_object* v_fst_1684_; lean_object* v_snd_1685_; lean_object* v___x_1686_; uint8_t v___x_1687_; 
lean_inc(v_offset_1677_);
lean_inc_ref(v_arg_1676_);
v___x_1681_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1673_, v_arg_1676_, v_offset_1677_, v_a_1678_, v_a_1679_, v_a_1680_);
v_fst_1682_ = lean_ctor_get(v___x_1681_, 0);
lean_inc(v_fst_1682_);
v_snd_1683_ = lean_ctor_get(v___x_1681_, 1);
lean_inc(v_snd_1683_);
lean_dec_ref(v___x_1681_);
v_fst_1684_ = lean_ctor_get(v_fst_1682_, 0);
lean_inc(v_fst_1684_);
v_snd_1685_ = lean_ctor_get(v_fst_1682_, 1);
lean_inc(v_snd_1685_);
lean_dec(v_fst_1682_);
v___x_1686_ = l_Lean_Expr_getAppFn(v_f_1675_);
v___x_1687_ = l_Lean_Expr_isBVar(v___x_1686_);
lean_dec_ref(v___x_1686_);
if (v___x_1687_ == 0)
{
lean_object* v___x_1688_; lean_object* v_fst_1689_; lean_object* v_snd_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1715_; 
lean_dec_ref(v_arg_1676_);
v___x_1688_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault(v_subst_1673_, v_f_1675_, v_offset_1677_, v_snd_1685_, v_a_1679_, v_snd_1683_);
v_fst_1689_ = lean_ctor_get(v___x_1688_, 0);
v_snd_1690_ = lean_ctor_get(v___x_1688_, 1);
v_isSharedCheck_1715_ = !lean_is_exclusive(v___x_1688_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1692_ = v___x_1688_;
v_isShared_1693_ = v_isSharedCheck_1715_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_snd_1690_);
lean_inc(v_fst_1689_);
lean_dec(v___x_1688_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1715_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v_fst_1694_; lean_object* v_snd_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1714_; 
v_fst_1694_ = lean_ctor_get(v_fst_1689_, 0);
v_snd_1695_ = lean_ctor_get(v_fst_1689_, 1);
v_isSharedCheck_1714_ = !lean_is_exclusive(v_fst_1689_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1697_ = v_fst_1689_;
v_isShared_1698_ = v_isSharedCheck_1714_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_snd_1695_);
lean_inc(v_fst_1694_);
lean_dec(v_fst_1689_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1714_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
uint8_t v___y_1700_; 
if (lean_obj_tag(v_e_1674_) == 5)
{
lean_object* v_fn_1708_; lean_object* v_arg_1709_; uint8_t v___x_1710_; 
v_fn_1708_ = lean_ctor_get(v_e_1674_, 0);
v_arg_1709_ = lean_ctor_get(v_e_1674_, 1);
v___x_1710_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_1708_, v_fst_1694_);
if (v___x_1710_ == 0)
{
v___y_1700_ = v___x_1710_;
goto v___jp_1699_;
}
else
{
uint8_t v___x_1711_; 
v___x_1711_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_1709_, v_fst_1684_);
v___y_1700_ = v___x_1711_;
goto v___jp_1699_;
}
}
else
{
lean_object* v___x_1712_; lean_object* v___x_1713_; 
lean_del_object(v___x_1697_);
lean_dec(v_fst_1694_);
lean_del_object(v___x_1692_);
lean_dec(v_fst_1684_);
lean_dec_ref(v_e_1674_);
v___x_1712_ = lean_obj_once(&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__3, &l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__3_once, _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__3);
v___x_1713_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9(v___x_1712_, v_snd_1695_, v_a_1679_, v_snd_1690_);
return v___x_1713_;
}
v___jp_1699_:
{
if (v___y_1700_ == 0)
{
lean_object* v___x_1701_; 
lean_del_object(v___x_1697_);
lean_del_object(v___x_1692_);
lean_dec_ref(v_e_1674_);
v___x_1701_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__3(v_fst_1694_, v_fst_1684_, v_snd_1695_, v_a_1679_, v_snd_1690_);
return v___x_1701_;
}
else
{
lean_object* v___x_1703_; 
lean_dec(v_fst_1694_);
lean_dec(v_fst_1684_);
if (v_isShared_1698_ == 0)
{
lean_ctor_set(v___x_1697_, 0, v_e_1674_);
v___x_1703_ = v___x_1697_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v_e_1674_);
lean_ctor_set(v_reuseFailAlloc_1707_, 1, v_snd_1695_);
v___x_1703_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
lean_object* v___x_1705_; 
if (v_isShared_1693_ == 0)
{
lean_ctor_set(v___x_1692_, 0, v___x_1703_);
v___x_1705_ = v___x_1692_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v___x_1703_);
lean_ctor_set(v_reuseFailAlloc_1706_, 1, v_snd_1690_);
v___x_1705_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
return v___x_1705_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; uint8_t v___x_1719_; 
v___x_1716_ = lean_unsigned_to_nat(1u);
v___x_1717_ = lean_mk_empty_array_with_capacity(v___x_1716_);
lean_inc(v_fst_1684_);
v___x_1718_ = lean_array_push(v___x_1717_, v_fst_1684_);
v___x_1719_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_1676_, v_fst_1684_);
lean_dec(v_fst_1684_);
lean_dec_ref(v_arg_1676_);
if (v___x_1719_ == 0)
{
lean_object* v___x_1720_; 
v___x_1720_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta(v_subst_1673_, v_e_1674_, v_f_1675_, v___x_1718_, v_offset_1677_, v___x_1687_, v_snd_1685_, v_a_1679_, v_snd_1683_);
return v___x_1720_;
}
else
{
uint8_t v___x_1721_; lean_object* v___x_1722_; 
v___x_1721_ = 0;
v___x_1722_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta(v_subst_1673_, v_e_1674_, v_f_1675_, v___x_1718_, v_offset_1677_, v___x_1721_, v_snd_1685_, v_a_1679_, v_snd_1683_);
return v___x_1722_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__1(void){
_start:
{
lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___x_1724_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__2));
v___x_1725_ = lean_unsigned_to_nat(59u);
v___x_1726_ = lean_unsigned_to_nat(176u);
v___x_1727_ = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__0));
v___x_1728_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__3));
v___x_1729_ = l_mkPanicMessageWithDecl(v___x_1728_, v___x_1727_, v___x_1726_, v___x_1725_, v___x_1724_);
return v___x_1729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit(lean_object* v_subst_1730_, lean_object* v_e_1731_, lean_object* v_offset_1732_, lean_object* v_a_1733_, uint8_t v_a_1734_, lean_object* v_a_1735_){
_start:
{
switch(lean_obj_tag(v_e_1731_))
{
case 0:
{
lean_object* v_deBruijnIndex_1736_; lean_object* v___x_1737_; 
v_deBruijnIndex_1736_ = lean_ctor_get(v_e_1731_, 0);
lean_inc(v_deBruijnIndex_1736_);
v___x_1737_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(v_subst_1730_, v_e_1731_, v_deBruijnIndex_1736_, v_offset_1732_, v_a_1733_, v_a_1734_, v_a_1735_);
lean_dec(v_offset_1732_);
lean_dec(v_deBruijnIndex_1736_);
return v___x_1737_;
}
case 5:
{
lean_object* v_fn_1738_; lean_object* v_arg_1739_; lean_object* v___x_1740_; 
v_fn_1738_ = lean_ctor_get(v_e_1731_, 0);
lean_inc_ref(v_fn_1738_);
v_arg_1739_ = lean_ctor_get(v_e_1731_, 1);
lean_inc_ref(v_arg_1739_);
v___x_1740_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg(v_subst_1730_, v_e_1731_, v_fn_1738_, v_arg_1739_, v_offset_1732_, v_a_1733_, v_a_1734_, v_a_1735_);
return v___x_1740_;
}
case 6:
{
lean_object* v_binderName_1741_; lean_object* v_binderType_1742_; lean_object* v_body_1743_; uint8_t v_binderInfo_1744_; lean_object* v___x_1745_; lean_object* v_fst_1746_; lean_object* v_snd_1747_; lean_object* v_fst_1748_; lean_object* v_snd_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v_fst_1753_; lean_object* v_snd_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1775_; 
v_binderName_1741_ = lean_ctor_get(v_e_1731_, 0);
v_binderType_1742_ = lean_ctor_get(v_e_1731_, 1);
v_body_1743_ = lean_ctor_get(v_e_1731_, 2);
v_binderInfo_1744_ = lean_ctor_get_uint8(v_e_1731_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1732_);
lean_inc_ref(v_binderType_1742_);
v___x_1745_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1730_, v_binderType_1742_, v_offset_1732_, v_a_1733_, v_a_1734_, v_a_1735_);
v_fst_1746_ = lean_ctor_get(v___x_1745_, 0);
lean_inc(v_fst_1746_);
v_snd_1747_ = lean_ctor_get(v___x_1745_, 1);
lean_inc(v_snd_1747_);
lean_dec_ref(v___x_1745_);
v_fst_1748_ = lean_ctor_get(v_fst_1746_, 0);
lean_inc(v_fst_1748_);
v_snd_1749_ = lean_ctor_get(v_fst_1746_, 1);
lean_inc(v_snd_1749_);
lean_dec(v_fst_1746_);
v___x_1750_ = lean_unsigned_to_nat(1u);
v___x_1751_ = lean_nat_add(v_offset_1732_, v___x_1750_);
lean_dec(v_offset_1732_);
lean_inc_ref(v_body_1743_);
v___x_1752_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1730_, v_body_1743_, v___x_1751_, v_snd_1749_, v_a_1734_, v_snd_1747_);
v_fst_1753_ = lean_ctor_get(v___x_1752_, 0);
v_snd_1754_ = lean_ctor_get(v___x_1752_, 1);
v_isSharedCheck_1775_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1756_ = v___x_1752_;
v_isShared_1757_ = v_isSharedCheck_1775_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_snd_1754_);
lean_inc(v_fst_1753_);
lean_dec(v___x_1752_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1775_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v_fst_1758_; lean_object* v_snd_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1774_; 
v_fst_1758_ = lean_ctor_get(v_fst_1753_, 0);
v_snd_1759_ = lean_ctor_get(v_fst_1753_, 1);
v_isSharedCheck_1774_ = !lean_is_exclusive(v_fst_1753_);
if (v_isSharedCheck_1774_ == 0)
{
v___x_1761_ = v_fst_1753_;
v_isShared_1762_ = v_isSharedCheck_1774_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_snd_1759_);
lean_inc(v_fst_1758_);
lean_dec(v_fst_1753_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1774_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
uint8_t v___y_1764_; uint8_t v___x_1772_; 
v___x_1772_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_1742_, v_fst_1748_);
if (v___x_1772_ == 0)
{
v___y_1764_ = v___x_1772_;
goto v___jp_1763_;
}
else
{
uint8_t v___x_1773_; 
v___x_1773_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1743_, v_fst_1758_);
v___y_1764_ = v___x_1773_;
goto v___jp_1763_;
}
v___jp_1763_:
{
if (v___y_1764_ == 0)
{
lean_object* v___x_1765_; 
lean_inc(v_binderName_1741_);
lean_del_object(v___x_1761_);
lean_del_object(v___x_1756_);
lean_dec_ref(v_e_1731_);
v___x_1765_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__4(v_binderName_1741_, v_binderInfo_1744_, v_fst_1748_, v_fst_1758_, v_snd_1759_, v_a_1734_, v_snd_1754_);
return v___x_1765_;
}
else
{
lean_object* v___x_1767_; 
lean_dec(v_fst_1758_);
lean_dec(v_fst_1748_);
if (v_isShared_1762_ == 0)
{
lean_ctor_set(v___x_1761_, 0, v_e_1731_);
v___x_1767_ = v___x_1761_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v_e_1731_);
lean_ctor_set(v_reuseFailAlloc_1771_, 1, v_snd_1759_);
v___x_1767_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
lean_object* v___x_1769_; 
if (v_isShared_1757_ == 0)
{
lean_ctor_set(v___x_1756_, 0, v___x_1767_);
v___x_1769_ = v___x_1756_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v___x_1767_);
lean_ctor_set(v_reuseFailAlloc_1770_, 1, v_snd_1754_);
v___x_1769_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
return v___x_1769_;
}
}
}
}
}
}
}
case 7:
{
lean_object* v_binderName_1776_; lean_object* v_binderType_1777_; lean_object* v_body_1778_; uint8_t v_binderInfo_1779_; lean_object* v___x_1780_; lean_object* v_fst_1781_; lean_object* v_snd_1782_; lean_object* v_fst_1783_; lean_object* v_snd_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v_fst_1788_; lean_object* v_snd_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1810_; 
v_binderName_1776_ = lean_ctor_get(v_e_1731_, 0);
v_binderType_1777_ = lean_ctor_get(v_e_1731_, 1);
v_body_1778_ = lean_ctor_get(v_e_1731_, 2);
v_binderInfo_1779_ = lean_ctor_get_uint8(v_e_1731_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1732_);
lean_inc_ref(v_binderType_1777_);
v___x_1780_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1730_, v_binderType_1777_, v_offset_1732_, v_a_1733_, v_a_1734_, v_a_1735_);
v_fst_1781_ = lean_ctor_get(v___x_1780_, 0);
lean_inc(v_fst_1781_);
v_snd_1782_ = lean_ctor_get(v___x_1780_, 1);
lean_inc(v_snd_1782_);
lean_dec_ref(v___x_1780_);
v_fst_1783_ = lean_ctor_get(v_fst_1781_, 0);
lean_inc(v_fst_1783_);
v_snd_1784_ = lean_ctor_get(v_fst_1781_, 1);
lean_inc(v_snd_1784_);
lean_dec(v_fst_1781_);
v___x_1785_ = lean_unsigned_to_nat(1u);
v___x_1786_ = lean_nat_add(v_offset_1732_, v___x_1785_);
lean_dec(v_offset_1732_);
lean_inc_ref(v_body_1778_);
v___x_1787_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1730_, v_body_1778_, v___x_1786_, v_snd_1784_, v_a_1734_, v_snd_1782_);
v_fst_1788_ = lean_ctor_get(v___x_1787_, 0);
v_snd_1789_ = lean_ctor_get(v___x_1787_, 1);
v_isSharedCheck_1810_ = !lean_is_exclusive(v___x_1787_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1791_ = v___x_1787_;
v_isShared_1792_ = v_isSharedCheck_1810_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_snd_1789_);
lean_inc(v_fst_1788_);
lean_dec(v___x_1787_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1810_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v_fst_1793_; lean_object* v_snd_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1809_; 
v_fst_1793_ = lean_ctor_get(v_fst_1788_, 0);
v_snd_1794_ = lean_ctor_get(v_fst_1788_, 1);
v_isSharedCheck_1809_ = !lean_is_exclusive(v_fst_1788_);
if (v_isSharedCheck_1809_ == 0)
{
v___x_1796_ = v_fst_1788_;
v_isShared_1797_ = v_isSharedCheck_1809_;
goto v_resetjp_1795_;
}
else
{
lean_inc(v_snd_1794_);
lean_inc(v_fst_1793_);
lean_dec(v_fst_1788_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1809_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
uint8_t v___y_1799_; uint8_t v___x_1807_; 
v___x_1807_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_1777_, v_fst_1783_);
if (v___x_1807_ == 0)
{
v___y_1799_ = v___x_1807_;
goto v___jp_1798_;
}
else
{
uint8_t v___x_1808_; 
v___x_1808_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1778_, v_fst_1793_);
v___y_1799_ = v___x_1808_;
goto v___jp_1798_;
}
v___jp_1798_:
{
if (v___y_1799_ == 0)
{
lean_object* v___x_1800_; 
lean_inc(v_binderName_1776_);
lean_del_object(v___x_1796_);
lean_del_object(v___x_1791_);
lean_dec_ref(v_e_1731_);
v___x_1800_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__5(v_binderName_1776_, v_binderInfo_1779_, v_fst_1783_, v_fst_1793_, v_snd_1794_, v_a_1734_, v_snd_1789_);
return v___x_1800_;
}
else
{
lean_object* v___x_1802_; 
lean_dec(v_fst_1793_);
lean_dec(v_fst_1783_);
if (v_isShared_1797_ == 0)
{
lean_ctor_set(v___x_1796_, 0, v_e_1731_);
v___x_1802_ = v___x_1796_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v_e_1731_);
lean_ctor_set(v_reuseFailAlloc_1806_, 1, v_snd_1794_);
v___x_1802_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
lean_object* v___x_1804_; 
if (v_isShared_1792_ == 0)
{
lean_ctor_set(v___x_1791_, 0, v___x_1802_);
v___x_1804_ = v___x_1791_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v___x_1802_);
lean_ctor_set(v_reuseFailAlloc_1805_, 1, v_snd_1789_);
v___x_1804_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
return v___x_1804_;
}
}
}
}
}
}
}
case 8:
{
lean_object* v_declName_1811_; lean_object* v_type_1812_; lean_object* v_value_1813_; lean_object* v_body_1814_; uint8_t v_nondep_1815_; lean_object* v___x_1816_; lean_object* v_fst_1817_; lean_object* v_snd_1818_; lean_object* v_fst_1819_; lean_object* v_snd_1820_; lean_object* v___x_1821_; lean_object* v_fst_1822_; lean_object* v_snd_1823_; lean_object* v_fst_1824_; lean_object* v_snd_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v_fst_1829_; lean_object* v_snd_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1853_; 
v_declName_1811_ = lean_ctor_get(v_e_1731_, 0);
v_type_1812_ = lean_ctor_get(v_e_1731_, 1);
v_value_1813_ = lean_ctor_get(v_e_1731_, 2);
v_body_1814_ = lean_ctor_get(v_e_1731_, 3);
v_nondep_1815_ = lean_ctor_get_uint8(v_e_1731_, sizeof(void*)*4 + 8);
lean_inc_n(v_offset_1732_, 2);
lean_inc_ref(v_type_1812_);
v___x_1816_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1730_, v_type_1812_, v_offset_1732_, v_a_1733_, v_a_1734_, v_a_1735_);
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
lean_inc_ref(v_value_1813_);
v___x_1821_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1730_, v_value_1813_, v_offset_1732_, v_snd_1820_, v_a_1734_, v_snd_1818_);
v_fst_1822_ = lean_ctor_get(v___x_1821_, 0);
lean_inc(v_fst_1822_);
v_snd_1823_ = lean_ctor_get(v___x_1821_, 1);
lean_inc(v_snd_1823_);
lean_dec_ref(v___x_1821_);
v_fst_1824_ = lean_ctor_get(v_fst_1822_, 0);
lean_inc(v_fst_1824_);
v_snd_1825_ = lean_ctor_get(v_fst_1822_, 1);
lean_inc(v_snd_1825_);
lean_dec(v_fst_1822_);
v___x_1826_ = lean_unsigned_to_nat(1u);
v___x_1827_ = lean_nat_add(v_offset_1732_, v___x_1826_);
lean_dec(v_offset_1732_);
lean_inc_ref(v_body_1814_);
v___x_1828_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1730_, v_body_1814_, v___x_1827_, v_snd_1825_, v_a_1734_, v_snd_1823_);
v_fst_1829_ = lean_ctor_get(v___x_1828_, 0);
v_snd_1830_ = lean_ctor_get(v___x_1828_, 1);
v_isSharedCheck_1853_ = !lean_is_exclusive(v___x_1828_);
if (v_isSharedCheck_1853_ == 0)
{
v___x_1832_ = v___x_1828_;
v_isShared_1833_ = v_isSharedCheck_1853_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_snd_1830_);
lean_inc(v_fst_1829_);
lean_dec(v___x_1828_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1853_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v_fst_1834_; lean_object* v_snd_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1852_; 
v_fst_1834_ = lean_ctor_get(v_fst_1829_, 0);
v_snd_1835_ = lean_ctor_get(v_fst_1829_, 1);
v_isSharedCheck_1852_ = !lean_is_exclusive(v_fst_1829_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1837_ = v_fst_1829_;
v_isShared_1838_ = v_isSharedCheck_1852_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_snd_1835_);
lean_inc(v_fst_1834_);
lean_dec(v_fst_1829_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1852_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
uint8_t v___y_1840_; uint8_t v___x_1850_; 
v___x_1850_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_type_1812_, v_fst_1819_);
if (v___x_1850_ == 0)
{
v___y_1840_ = v___x_1850_;
goto v___jp_1839_;
}
else
{
uint8_t v___x_1851_; 
v___x_1851_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_value_1813_, v_fst_1824_);
v___y_1840_ = v___x_1851_;
goto v___jp_1839_;
}
v___jp_1839_:
{
if (v___y_1840_ == 0)
{
lean_object* v___x_1841_; 
lean_inc(v_declName_1811_);
lean_del_object(v___x_1837_);
lean_del_object(v___x_1832_);
lean_dec_ref(v_e_1731_);
v___x_1841_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6(v_declName_1811_, v_fst_1819_, v_fst_1824_, v_fst_1834_, v_nondep_1815_, v_snd_1835_, v_a_1734_, v_snd_1830_);
return v___x_1841_;
}
else
{
uint8_t v___x_1842_; 
v___x_1842_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1814_, v_fst_1834_);
if (v___x_1842_ == 0)
{
lean_object* v___x_1843_; 
lean_inc(v_declName_1811_);
lean_del_object(v___x_1837_);
lean_del_object(v___x_1832_);
lean_dec_ref(v_e_1731_);
v___x_1843_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6(v_declName_1811_, v_fst_1819_, v_fst_1824_, v_fst_1834_, v_nondep_1815_, v_snd_1835_, v_a_1734_, v_snd_1830_);
return v___x_1843_;
}
else
{
lean_object* v___x_1845_; 
lean_dec(v_fst_1834_);
lean_dec(v_fst_1824_);
lean_dec(v_fst_1819_);
if (v_isShared_1838_ == 0)
{
lean_ctor_set(v___x_1837_, 0, v_e_1731_);
v___x_1845_ = v___x_1837_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_e_1731_);
lean_ctor_set(v_reuseFailAlloc_1849_, 1, v_snd_1835_);
v___x_1845_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
lean_object* v___x_1847_; 
if (v_isShared_1833_ == 0)
{
lean_ctor_set(v___x_1832_, 0, v___x_1845_);
v___x_1847_ = v___x_1832_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v___x_1845_);
lean_ctor_set(v_reuseFailAlloc_1848_, 1, v_snd_1830_);
v___x_1847_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
return v___x_1847_;
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
lean_object* v_data_1854_; lean_object* v_expr_1855_; lean_object* v___x_1856_; lean_object* v_fst_1857_; lean_object* v_snd_1858_; lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_1876_; 
v_data_1854_ = lean_ctor_get(v_e_1731_, 0);
v_expr_1855_ = lean_ctor_get(v_e_1731_, 1);
lean_inc_ref(v_expr_1855_);
v___x_1856_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1730_, v_expr_1855_, v_offset_1732_, v_a_1733_, v_a_1734_, v_a_1735_);
v_fst_1857_ = lean_ctor_get(v___x_1856_, 0);
v_snd_1858_ = lean_ctor_get(v___x_1856_, 1);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1856_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1860_ = v___x_1856_;
v_isShared_1861_ = v_isSharedCheck_1876_;
goto v_resetjp_1859_;
}
else
{
lean_inc(v_snd_1858_);
lean_inc(v_fst_1857_);
lean_dec(v___x_1856_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_1876_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
lean_object* v_fst_1862_; lean_object* v_snd_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1875_; 
v_fst_1862_ = lean_ctor_get(v_fst_1857_, 0);
v_snd_1863_ = lean_ctor_get(v_fst_1857_, 1);
v_isSharedCheck_1875_ = !lean_is_exclusive(v_fst_1857_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1865_ = v_fst_1857_;
v_isShared_1866_ = v_isSharedCheck_1875_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_snd_1863_);
lean_inc(v_fst_1862_);
lean_dec(v_fst_1857_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1875_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
uint8_t v___x_1867_; 
v___x_1867_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_expr_1855_, v_fst_1862_);
if (v___x_1867_ == 0)
{
lean_object* v___x_1868_; 
lean_inc(v_data_1854_);
lean_del_object(v___x_1865_);
lean_del_object(v___x_1860_);
lean_dec_ref(v_e_1731_);
v___x_1868_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__7(v_data_1854_, v_fst_1862_, v_snd_1863_, v_a_1734_, v_snd_1858_);
return v___x_1868_;
}
else
{
lean_object* v___x_1870_; 
lean_dec(v_fst_1862_);
if (v_isShared_1866_ == 0)
{
lean_ctor_set(v___x_1865_, 0, v_e_1731_);
v___x_1870_ = v___x_1865_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_e_1731_);
lean_ctor_set(v_reuseFailAlloc_1874_, 1, v_snd_1863_);
v___x_1870_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
lean_object* v___x_1872_; 
if (v_isShared_1861_ == 0)
{
lean_ctor_set(v___x_1860_, 0, v___x_1870_);
v___x_1872_ = v___x_1860_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v___x_1870_);
lean_ctor_set(v_reuseFailAlloc_1873_, 1, v_snd_1858_);
v___x_1872_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
return v___x_1872_;
}
}
}
}
}
}
case 11:
{
lean_object* v_typeName_1877_; lean_object* v_idx_1878_; lean_object* v_struct_1879_; lean_object* v___x_1880_; lean_object* v_fst_1881_; lean_object* v_snd_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1900_; 
v_typeName_1877_ = lean_ctor_get(v_e_1731_, 0);
v_idx_1878_ = lean_ctor_get(v_e_1731_, 1);
v_struct_1879_ = lean_ctor_get(v_e_1731_, 2);
lean_inc_ref(v_struct_1879_);
v___x_1880_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1730_, v_struct_1879_, v_offset_1732_, v_a_1733_, v_a_1734_, v_a_1735_);
v_fst_1881_ = lean_ctor_get(v___x_1880_, 0);
v_snd_1882_ = lean_ctor_get(v___x_1880_, 1);
v_isSharedCheck_1900_ = !lean_is_exclusive(v___x_1880_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1884_ = v___x_1880_;
v_isShared_1885_ = v_isSharedCheck_1900_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_snd_1882_);
lean_inc(v_fst_1881_);
lean_dec(v___x_1880_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1900_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v_fst_1886_; lean_object* v_snd_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1899_; 
v_fst_1886_ = lean_ctor_get(v_fst_1881_, 0);
v_snd_1887_ = lean_ctor_get(v_fst_1881_, 1);
v_isSharedCheck_1899_ = !lean_is_exclusive(v_fst_1881_);
if (v_isSharedCheck_1899_ == 0)
{
v___x_1889_ = v_fst_1881_;
v_isShared_1890_ = v_isSharedCheck_1899_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_snd_1887_);
lean_inc(v_fst_1886_);
lean_dec(v_fst_1881_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1899_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
uint8_t v___x_1891_; 
v___x_1891_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_1879_, v_fst_1886_);
if (v___x_1891_ == 0)
{
lean_object* v___x_1892_; 
lean_inc(v_idx_1878_);
lean_inc(v_typeName_1877_);
lean_del_object(v___x_1889_);
lean_del_object(v___x_1884_);
lean_dec_ref(v_e_1731_);
v___x_1892_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__8(v_typeName_1877_, v_idx_1878_, v_fst_1886_, v_snd_1887_, v_a_1734_, v_snd_1882_);
return v___x_1892_;
}
else
{
lean_object* v___x_1894_; 
lean_dec(v_fst_1886_);
if (v_isShared_1890_ == 0)
{
lean_ctor_set(v___x_1889_, 0, v_e_1731_);
v___x_1894_ = v___x_1889_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v_e_1731_);
lean_ctor_set(v_reuseFailAlloc_1898_, 1, v_snd_1887_);
v___x_1894_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
lean_object* v___x_1896_; 
if (v_isShared_1885_ == 0)
{
lean_ctor_set(v___x_1884_, 0, v___x_1894_);
v___x_1896_ = v___x_1884_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v___x_1894_);
lean_ctor_set(v_reuseFailAlloc_1897_, 1, v_snd_1882_);
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
}
default: 
{
lean_object* v___x_1901_; lean_object* v___x_1902_; 
lean_dec(v_offset_1732_);
lean_dec_ref(v_e_1731_);
v___x_1901_ = lean_obj_once(&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__1, &l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__1_once, _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__1);
v___x_1902_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9(v___x_1901_, v_a_1733_, v_a_1734_, v_a_1735_);
return v___x_1902_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(lean_object* v_subst_1903_, lean_object* v_e_1904_, lean_object* v_offset_1905_, lean_object* v_a_1906_, uint8_t v_a_1907_, lean_object* v_a_1908_){
_start:
{
lean_object* v___x_1909_; uint8_t v___x_1910_; 
v___x_1909_ = l_Lean_Expr_looseBVarRange(v_e_1904_);
v___x_1910_ = lean_nat_dec_le(v___x_1909_, v_offset_1905_);
lean_dec(v___x_1909_);
if (v___x_1910_ == 0)
{
lean_object* v_key_1911_; lean_object* v___x_1912_; 
lean_inc(v_offset_1905_);
lean_inc_ref(v_e_1904_);
v_key_1911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1911_, 0, v_e_1904_);
lean_ctor_set(v_key_1911_, 1, v_offset_1905_);
v___x_1912_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___redArg(v_a_1906_, v_key_1911_);
if (lean_obj_tag(v___x_1912_) == 1)
{
lean_object* v_val_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; 
lean_dec_ref(v_key_1911_);
lean_dec(v_offset_1905_);
lean_dec_ref(v_e_1904_);
v_val_1913_ = lean_ctor_get(v___x_1912_, 0);
lean_inc(v_val_1913_);
lean_dec_ref(v___x_1912_);
v___x_1914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1914_, 0, v_val_1913_);
lean_ctor_set(v___x_1914_, 1, v_a_1906_);
v___x_1915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1914_);
lean_ctor_set(v___x_1915_, 1, v_a_1908_);
return v___x_1915_;
}
else
{
lean_dec(v___x_1912_);
switch(lean_obj_tag(v_e_1904_))
{
case 0:
{
lean_object* v_deBruijnIndex_1916_; lean_object* v___x_1917_; lean_object* v_fst_1918_; lean_object* v_snd_1919_; lean_object* v_fst_1920_; lean_object* v_snd_1921_; lean_object* v___x_1922_; 
v_deBruijnIndex_1916_ = lean_ctor_get(v_e_1904_, 0);
lean_inc(v_deBruijnIndex_1916_);
v___x_1917_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(v_subst_1903_, v_e_1904_, v_deBruijnIndex_1916_, v_offset_1905_, v_a_1906_, v_a_1907_, v_a_1908_);
lean_dec(v_offset_1905_);
lean_dec(v_deBruijnIndex_1916_);
v_fst_1918_ = lean_ctor_get(v___x_1917_, 0);
lean_inc(v_fst_1918_);
v_snd_1919_ = lean_ctor_get(v___x_1917_, 1);
lean_inc(v_snd_1919_);
lean_dec_ref(v___x_1917_);
v_fst_1920_ = lean_ctor_get(v_fst_1918_, 0);
lean_inc(v_fst_1920_);
v_snd_1921_ = lean_ctor_get(v_fst_1918_, 1);
lean_inc(v_snd_1921_);
lean_dec(v_fst_1918_);
v___x_1922_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_1911_, v_fst_1920_, v_snd_1921_, v_snd_1919_);
return v___x_1922_;
}
case 9:
{
lean_object* v___x_1923_; 
lean_dec(v_offset_1905_);
v___x_1923_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_1911_, v_e_1904_, v_a_1906_, v_a_1908_);
return v___x_1923_;
}
case 2:
{
lean_object* v___x_1924_; 
lean_dec(v_offset_1905_);
v___x_1924_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_1911_, v_e_1904_, v_a_1906_, v_a_1908_);
return v___x_1924_;
}
case 1:
{
lean_object* v___x_1925_; 
lean_dec(v_offset_1905_);
v___x_1925_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_1911_, v_e_1904_, v_a_1906_, v_a_1908_);
return v___x_1925_;
}
case 4:
{
lean_object* v___x_1926_; 
lean_dec(v_offset_1905_);
v___x_1926_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_1911_, v_e_1904_, v_a_1906_, v_a_1908_);
return v___x_1926_;
}
case 3:
{
lean_object* v___x_1927_; 
lean_dec(v_offset_1905_);
v___x_1927_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_1911_, v_e_1904_, v_a_1906_, v_a_1908_);
return v___x_1927_;
}
default: 
{
lean_object* v___x_1928_; lean_object* v_fst_1929_; lean_object* v_snd_1930_; lean_object* v_fst_1931_; lean_object* v_snd_1932_; lean_object* v___x_1933_; 
v___x_1928_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit(v_subst_1903_, v_e_1904_, v_offset_1905_, v_a_1906_, v_a_1907_, v_a_1908_);
v_fst_1929_ = lean_ctor_get(v___x_1928_, 0);
lean_inc(v_fst_1929_);
v_snd_1930_ = lean_ctor_get(v___x_1928_, 1);
lean_inc(v_snd_1930_);
lean_dec_ref(v___x_1928_);
v_fst_1931_ = lean_ctor_get(v_fst_1929_, 0);
lean_inc(v_fst_1931_);
v_snd_1932_ = lean_ctor_get(v_fst_1929_, 1);
lean_inc(v_snd_1932_);
lean_dec(v_fst_1929_);
v___x_1933_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_1911_, v_fst_1931_, v_snd_1932_, v_snd_1930_);
return v___x_1933_;
}
}
}
}
else
{
lean_object* v___x_1934_; lean_object* v___x_1935_; 
lean_dec(v_offset_1905_);
v___x_1934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1934_, 0, v_e_1904_);
lean_ctor_set(v___x_1934_, 1, v_a_1906_);
v___x_1935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1935_, 0, v___x_1934_);
lean_ctor_set(v___x_1935_, 1, v_a_1908_);
return v___x_1935_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault(lean_object* v_subst_1936_, lean_object* v_e_1937_, lean_object* v_offset_1938_, lean_object* v_a_1939_, uint8_t v_a_1940_, lean_object* v_a_1941_){
_start:
{
if (lean_obj_tag(v_e_1937_) == 5)
{
lean_object* v_fn_1942_; lean_object* v_arg_1943_; lean_object* v_key_1944_; lean_object* v___x_1945_; 
v_fn_1942_ = lean_ctor_get(v_e_1937_, 0);
v_arg_1943_ = lean_ctor_get(v_e_1937_, 1);
lean_inc(v_offset_1938_);
lean_inc_ref(v_e_1937_);
v_key_1944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1944_, 0, v_e_1937_);
lean_ctor_set(v_key_1944_, 1, v_offset_1938_);
v___x_1945_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___redArg(v_a_1939_, v_key_1944_);
if (lean_obj_tag(v___x_1945_) == 1)
{
lean_object* v_val_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; 
lean_dec_ref(v_key_1944_);
lean_dec_ref(v_e_1937_);
lean_dec(v_offset_1938_);
v_val_1946_ = lean_ctor_get(v___x_1945_, 0);
lean_inc(v_val_1946_);
lean_dec_ref(v___x_1945_);
v___x_1947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1947_, 0, v_val_1946_);
lean_ctor_set(v___x_1947_, 1, v_a_1939_);
v___x_1948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1948_, 0, v___x_1947_);
lean_ctor_set(v___x_1948_, 1, v_a_1941_);
return v___x_1948_;
}
else
{
lean_object* v___x_1949_; lean_object* v_fst_1950_; lean_object* v_snd_1951_; lean_object* v_fst_1952_; lean_object* v_snd_1953_; lean_object* v___x_1954_; lean_object* v_fst_1955_; lean_object* v_snd_1956_; lean_object* v_fst_1957_; lean_object* v_snd_1958_; uint8_t v___y_1960_; uint8_t v___x_1968_; 
lean_dec(v___x_1945_);
lean_inc(v_offset_1938_);
lean_inc_ref(v_fn_1942_);
v___x_1949_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault(v_subst_1936_, v_fn_1942_, v_offset_1938_, v_a_1939_, v_a_1940_, v_a_1941_);
v_fst_1950_ = lean_ctor_get(v___x_1949_, 0);
lean_inc(v_fst_1950_);
v_snd_1951_ = lean_ctor_get(v___x_1949_, 1);
lean_inc(v_snd_1951_);
lean_dec_ref(v___x_1949_);
v_fst_1952_ = lean_ctor_get(v_fst_1950_, 0);
lean_inc(v_fst_1952_);
v_snd_1953_ = lean_ctor_get(v_fst_1950_, 1);
lean_inc(v_snd_1953_);
lean_dec(v_fst_1950_);
lean_inc_ref(v_arg_1943_);
v___x_1954_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1936_, v_arg_1943_, v_offset_1938_, v_snd_1953_, v_a_1940_, v_snd_1951_);
v_fst_1955_ = lean_ctor_get(v___x_1954_, 0);
lean_inc(v_fst_1955_);
v_snd_1956_ = lean_ctor_get(v___x_1954_, 1);
lean_inc(v_snd_1956_);
lean_dec_ref(v___x_1954_);
v_fst_1957_ = lean_ctor_get(v_fst_1955_, 0);
lean_inc(v_fst_1957_);
v_snd_1958_ = lean_ctor_get(v_fst_1955_, 1);
lean_inc(v_snd_1958_);
lean_dec(v_fst_1955_);
v___x_1968_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_1942_, v_fst_1952_);
if (v___x_1968_ == 0)
{
v___y_1960_ = v___x_1968_;
goto v___jp_1959_;
}
else
{
uint8_t v___x_1969_; 
v___x_1969_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_1943_, v_fst_1957_);
v___y_1960_ = v___x_1969_;
goto v___jp_1959_;
}
v___jp_1959_:
{
if (v___y_1960_ == 0)
{
lean_object* v___x_1961_; lean_object* v_fst_1962_; lean_object* v_snd_1963_; lean_object* v_fst_1964_; lean_object* v_snd_1965_; lean_object* v___x_1966_; 
lean_dec_ref(v_e_1937_);
v___x_1961_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__3(v_fst_1952_, v_fst_1957_, v_snd_1958_, v_a_1940_, v_snd_1956_);
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
v___x_1966_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_1944_, v_fst_1964_, v_snd_1965_, v_snd_1963_);
return v___x_1966_;
}
else
{
lean_object* v___x_1967_; 
lean_dec(v_fst_1957_);
lean_dec(v_fst_1952_);
v___x_1967_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_1944_, v_e_1937_, v_snd_1958_, v_snd_1956_);
return v___x_1967_;
}
}
}
}
else
{
lean_object* v___x_1970_; 
v___x_1970_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1936_, v_e_1937_, v_offset_1938_, v_a_1939_, v_a_1940_, v_a_1941_);
return v___x_1970_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault___boxed(lean_object* v_subst_1971_, lean_object* v_e_1972_, lean_object* v_offset_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_){
_start:
{
uint8_t v_a_boxed_1977_; lean_object* v_res_1978_; 
v_a_boxed_1977_ = lean_unbox(v_a_1975_);
v_res_1978_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault(v_subst_1971_, v_e_1972_, v_offset_1973_, v_a_1974_, v_a_boxed_1977_, v_a_1976_);
lean_dec_ref(v_subst_1971_);
return v_res_1978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild___boxed(lean_object* v_subst_1979_, lean_object* v_e_1980_, lean_object* v_offset_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_){
_start:
{
uint8_t v_a_boxed_1985_; lean_object* v_res_1986_; 
v_a_boxed_1985_ = lean_unbox(v_a_1983_);
v_res_1986_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1979_, v_e_1980_, v_offset_1981_, v_a_1982_, v_a_boxed_1985_, v_a_1984_);
lean_dec_ref(v_subst_1979_);
return v_res_1986_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___boxed(lean_object* v_subst_1987_, lean_object* v_e_1988_, lean_object* v_f_1989_, lean_object* v_arg_1990_, lean_object* v_offset_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_){
_start:
{
uint8_t v_a_boxed_1995_; lean_object* v_res_1996_; 
v_a_boxed_1995_ = lean_unbox(v_a_1993_);
v_res_1996_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg(v_subst_1987_, v_e_1988_, v_f_1989_, v_arg_1990_, v_offset_1991_, v_a_1992_, v_a_boxed_1995_, v_a_1994_);
lean_dec_ref(v_subst_1987_);
return v_res_1996_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___boxed(lean_object* v_subst_1997_, lean_object* v_e_1998_, lean_object* v_f_1999_, lean_object* v_argsRev_2000_, lean_object* v_offset_2001_, lean_object* v_modified_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_){
_start:
{
uint8_t v_modified_boxed_2006_; uint8_t v_a_boxed_2007_; lean_object* v_res_2008_; 
v_modified_boxed_2006_ = lean_unbox(v_modified_2002_);
v_a_boxed_2007_ = lean_unbox(v_a_2004_);
v_res_2008_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta(v_subst_1997_, v_e_1998_, v_f_1999_, v_argsRev_2000_, v_offset_2001_, v_modified_boxed_2006_, v_a_2003_, v_a_boxed_2007_, v_a_2005_);
lean_dec_ref(v_subst_1997_);
return v_res_2008_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___boxed(lean_object* v_subst_2009_, lean_object* v_e_2010_, lean_object* v_offset_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_){
_start:
{
uint8_t v_a_boxed_2015_; lean_object* v_res_2016_; 
v_a_boxed_2015_ = lean_unbox(v_a_2013_);
v_res_2016_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit(v_subst_2009_, v_e_2010_, v_offset_2011_, v_a_2012_, v_a_boxed_2015_, v_a_2014_);
lean_dec_ref(v_subst_2009_);
return v_res_2016_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp(lean_object* v_subst_2017_, lean_object* v_e_2018_, lean_object* v_f_2019_, lean_object* v_arg_2020_, lean_object* v_offset_2021_, lean_object* v_x_2022_, lean_object* v_a_2023_, uint8_t v_a_2024_, lean_object* v_a_2025_){
_start:
{
lean_object* v___x_2026_; 
v___x_2026_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg(v_subst_2017_, v_e_2018_, v_f_2019_, v_arg_2020_, v_offset_2021_, v_a_2023_, v_a_2024_, v_a_2025_);
return v___x_2026_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___boxed(lean_object* v_subst_2027_, lean_object* v_e_2028_, lean_object* v_f_2029_, lean_object* v_arg_2030_, lean_object* v_offset_2031_, lean_object* v_x_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_, lean_object* v_a_2035_){
_start:
{
uint8_t v_a_boxed_2036_; lean_object* v_res_2037_; 
v_a_boxed_2036_ = lean_unbox(v_a_2034_);
v_res_2037_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp(v_subst_2027_, v_e_2028_, v_f_2029_, v_arg_2030_, v_offset_2031_, v_x_2032_, v_a_2033_, v_a_boxed_2036_, v_a_2035_);
lean_dec_ref(v_subst_2027_);
return v_res_2037_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27(lean_object* v_e_2038_, lean_object* v_subst_2039_, uint8_t v_a_2040_, lean_object* v_a_2041_){
_start:
{
uint8_t v___y_2043_; lean_object* v___x_2059_; lean_object* v___x_2060_; uint8_t v___x_2061_; 
v___x_2059_ = lean_array_get_size(v_subst_2039_);
v___x_2060_ = lean_unsigned_to_nat(0u);
v___x_2061_ = lean_nat_dec_eq(v___x_2059_, v___x_2060_);
if (v___x_2061_ == 0)
{
uint8_t v___x_2062_; 
v___x_2062_ = l_Lean_Expr_hasLooseBVars(v_e_2038_);
if (v___x_2062_ == 0)
{
lean_object* v___x_2063_; 
v___x_2063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2063_, 0, v_e_2038_);
lean_ctor_set(v___x_2063_, 1, v_a_2041_);
return v___x_2063_;
}
else
{
v___y_2043_ = v___x_2061_;
goto v___jp_2042_;
}
}
else
{
v___y_2043_ = v___x_2061_;
goto v___jp_2042_;
}
v___jp_2042_:
{
if (v___y_2043_ == 0)
{
lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v_fst_2047_; lean_object* v_snd_2048_; lean_object* v_fst_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2056_; 
v___x_2044_ = lean_unsigned_to_nat(0u);
v___x_2045_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__2, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__2_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__2);
v___x_2046_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit(v_subst_2039_, v_e_2038_, v___x_2044_, v___x_2045_, v_a_2040_, v_a_2041_);
v_fst_2047_ = lean_ctor_get(v___x_2046_, 0);
lean_inc(v_fst_2047_);
v_snd_2048_ = lean_ctor_get(v___x_2046_, 1);
lean_inc(v_snd_2048_);
lean_dec_ref(v___x_2046_);
v_fst_2049_ = lean_ctor_get(v_fst_2047_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v_fst_2047_);
if (v_isSharedCheck_2056_ == 0)
{
lean_object* v_unused_2057_; 
v_unused_2057_ = lean_ctor_get(v_fst_2047_, 1);
lean_dec(v_unused_2057_);
v___x_2051_ = v_fst_2047_;
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_fst_2049_);
lean_dec(v_fst_2047_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2054_; 
if (v_isShared_2052_ == 0)
{
lean_ctor_set(v___x_2051_, 1, v_snd_2048_);
v___x_2054_ = v___x_2051_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_fst_2049_);
lean_ctor_set(v_reuseFailAlloc_2055_, 1, v_snd_2048_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
}
else
{
lean_object* v___x_2058_; 
v___x_2058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2058_, 0, v_e_2038_);
lean_ctor_set(v___x_2058_, 1, v_a_2041_);
return v___x_2058_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27___boxed(lean_object* v_e_2064_, lean_object* v_subst_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_){
_start:
{
uint8_t v_a_boxed_2068_; lean_object* v_res_2069_; 
v_a_boxed_2068_ = lean_unbox(v_a_2066_);
v_res_2069_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27(v_e_2064_, v_subst_2065_, v_a_boxed_2068_, v_a_2067_);
lean_dec_ref(v_subst_2065_);
return v_res_2069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevBetaS___redArg(lean_object* v_e_2070_, lean_object* v_subst_2071_, lean_object* v_a_2072_){
_start:
{
uint8_t v___x_2074_; 
v___x_2074_ = l_Lean_Expr_hasLooseBVars(v_e_2070_);
if (v___x_2074_ == 0)
{
lean_object* v___x_2075_; 
v___x_2075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2075_, 0, v_e_2070_);
return v___x_2075_;
}
else
{
lean_object* v___x_2076_; lean_object* v___x_2077_; uint8_t v___x_2078_; 
v___x_2076_ = lean_array_get_size(v_subst_2071_);
v___x_2077_ = lean_unsigned_to_nat(0u);
v___x_2078_ = lean_nat_dec_eq(v___x_2076_, v___x_2077_);
if (v___x_2078_ == 0)
{
lean_object* v___x_2079_; lean_object* v_share_2080_; lean_object* v_maxFVar_2081_; lean_object* v_proofInstInfo_2082_; lean_object* v_inferType_2083_; lean_object* v_getLevel_2084_; lean_object* v_congrInfo_2085_; lean_object* v_defEqI_2086_; lean_object* v_extensions_2087_; lean_object* v_issues_2088_; lean_object* v_canon_2089_; uint8_t v_debug_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2125_; 
v___x_2079_ = lean_st_ref_take(v_a_2072_);
v_share_2080_ = lean_ctor_get(v___x_2079_, 0);
v_maxFVar_2081_ = lean_ctor_get(v___x_2079_, 1);
v_proofInstInfo_2082_ = lean_ctor_get(v___x_2079_, 2);
v_inferType_2083_ = lean_ctor_get(v___x_2079_, 3);
v_getLevel_2084_ = lean_ctor_get(v___x_2079_, 4);
v_congrInfo_2085_ = lean_ctor_get(v___x_2079_, 5);
v_defEqI_2086_ = lean_ctor_get(v___x_2079_, 6);
v_extensions_2087_ = lean_ctor_get(v___x_2079_, 7);
v_issues_2088_ = lean_ctor_get(v___x_2079_, 8);
v_canon_2089_ = lean_ctor_get(v___x_2079_, 9);
v_debug_2090_ = lean_ctor_get_uint8(v___x_2079_, sizeof(void*)*10);
v_isSharedCheck_2125_ = !lean_is_exclusive(v___x_2079_);
if (v_isSharedCheck_2125_ == 0)
{
v___x_2092_ = v___x_2079_;
v_isShared_2093_ = v_isSharedCheck_2125_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_canon_2089_);
lean_inc(v_issues_2088_);
lean_inc(v_extensions_2087_);
lean_inc(v_defEqI_2086_);
lean_inc(v_congrInfo_2085_);
lean_inc(v_getLevel_2084_);
lean_inc(v_inferType_2083_);
lean_inc(v_proofInstInfo_2082_);
lean_inc(v_maxFVar_2081_);
lean_inc(v_share_2080_);
lean_dec(v___x_2079_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2125_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2094_; lean_object* v___x_2096_; 
v___x_2094_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__0, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__0_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__0);
if (v_isShared_2093_ == 0)
{
lean_ctor_set(v___x_2092_, 0, v___x_2094_);
v___x_2096_ = v___x_2092_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v___x_2094_);
lean_ctor_set(v_reuseFailAlloc_2124_, 1, v_maxFVar_2081_);
lean_ctor_set(v_reuseFailAlloc_2124_, 2, v_proofInstInfo_2082_);
lean_ctor_set(v_reuseFailAlloc_2124_, 3, v_inferType_2083_);
lean_ctor_set(v_reuseFailAlloc_2124_, 4, v_getLevel_2084_);
lean_ctor_set(v_reuseFailAlloc_2124_, 5, v_congrInfo_2085_);
lean_ctor_set(v_reuseFailAlloc_2124_, 6, v_defEqI_2086_);
lean_ctor_set(v_reuseFailAlloc_2124_, 7, v_extensions_2087_);
lean_ctor_set(v_reuseFailAlloc_2124_, 8, v_issues_2088_);
lean_ctor_set(v_reuseFailAlloc_2124_, 9, v_canon_2089_);
lean_ctor_set_uint8(v_reuseFailAlloc_2124_, sizeof(void*)*10, v_debug_2090_);
v___x_2096_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
lean_object* v___x_2097_; lean_object* v___x_2098_; uint8_t v_debug_2099_; lean_object* v___x_2100_; lean_object* v_fst_2101_; lean_object* v_snd_2102_; lean_object* v___x_2103_; lean_object* v_maxFVar_2104_; lean_object* v_proofInstInfo_2105_; lean_object* v_inferType_2106_; lean_object* v_getLevel_2107_; lean_object* v_congrInfo_2108_; lean_object* v_defEqI_2109_; lean_object* v_extensions_2110_; lean_object* v_issues_2111_; lean_object* v_canon_2112_; uint8_t v_debug_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2122_; 
v___x_2097_ = lean_st_ref_set(v_a_2072_, v___x_2096_);
v___x_2098_ = lean_st_ref_get(v_a_2072_);
v_debug_2099_ = lean_ctor_get_uint8(v___x_2098_, sizeof(void*)*10);
lean_dec(v___x_2098_);
v___x_2100_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27(v_e_2070_, v_subst_2071_, v_debug_2099_, v_share_2080_);
v_fst_2101_ = lean_ctor_get(v___x_2100_, 0);
lean_inc(v_fst_2101_);
v_snd_2102_ = lean_ctor_get(v___x_2100_, 1);
lean_inc(v_snd_2102_);
lean_dec_ref(v___x_2100_);
v___x_2103_ = lean_st_ref_take(v_a_2072_);
v_maxFVar_2104_ = lean_ctor_get(v___x_2103_, 1);
v_proofInstInfo_2105_ = lean_ctor_get(v___x_2103_, 2);
v_inferType_2106_ = lean_ctor_get(v___x_2103_, 3);
v_getLevel_2107_ = lean_ctor_get(v___x_2103_, 4);
v_congrInfo_2108_ = lean_ctor_get(v___x_2103_, 5);
v_defEqI_2109_ = lean_ctor_get(v___x_2103_, 6);
v_extensions_2110_ = lean_ctor_get(v___x_2103_, 7);
v_issues_2111_ = lean_ctor_get(v___x_2103_, 8);
v_canon_2112_ = lean_ctor_get(v___x_2103_, 9);
v_debug_2113_ = lean_ctor_get_uint8(v___x_2103_, sizeof(void*)*10);
v_isSharedCheck_2122_ = !lean_is_exclusive(v___x_2103_);
if (v_isSharedCheck_2122_ == 0)
{
lean_object* v_unused_2123_; 
v_unused_2123_ = lean_ctor_get(v___x_2103_, 0);
lean_dec(v_unused_2123_);
v___x_2115_ = v___x_2103_;
v_isShared_2116_ = v_isSharedCheck_2122_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_canon_2112_);
lean_inc(v_issues_2111_);
lean_inc(v_extensions_2110_);
lean_inc(v_defEqI_2109_);
lean_inc(v_congrInfo_2108_);
lean_inc(v_getLevel_2107_);
lean_inc(v_inferType_2106_);
lean_inc(v_proofInstInfo_2105_);
lean_inc(v_maxFVar_2104_);
lean_dec(v___x_2103_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2122_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v___x_2118_; 
if (v_isShared_2116_ == 0)
{
lean_ctor_set(v___x_2115_, 0, v_snd_2102_);
v___x_2118_ = v___x_2115_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v_snd_2102_);
lean_ctor_set(v_reuseFailAlloc_2121_, 1, v_maxFVar_2104_);
lean_ctor_set(v_reuseFailAlloc_2121_, 2, v_proofInstInfo_2105_);
lean_ctor_set(v_reuseFailAlloc_2121_, 3, v_inferType_2106_);
lean_ctor_set(v_reuseFailAlloc_2121_, 4, v_getLevel_2107_);
lean_ctor_set(v_reuseFailAlloc_2121_, 5, v_congrInfo_2108_);
lean_ctor_set(v_reuseFailAlloc_2121_, 6, v_defEqI_2109_);
lean_ctor_set(v_reuseFailAlloc_2121_, 7, v_extensions_2110_);
lean_ctor_set(v_reuseFailAlloc_2121_, 8, v_issues_2111_);
lean_ctor_set(v_reuseFailAlloc_2121_, 9, v_canon_2112_);
lean_ctor_set_uint8(v_reuseFailAlloc_2121_, sizeof(void*)*10, v_debug_2113_);
v___x_2118_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2119_ = lean_st_ref_set(v_a_2072_, v___x_2118_);
v___x_2120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2120_, 0, v_fst_2101_);
return v___x_2120_;
}
}
}
}
}
else
{
lean_object* v___x_2126_; 
v___x_2126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2126_, 0, v_e_2070_);
return v___x_2126_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevBetaS___redArg___boxed(lean_object* v_e_2127_, lean_object* v_subst_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_){
_start:
{
lean_object* v_res_2131_; 
v_res_2131_ = l_Lean_Meta_Sym_instantiateRevBetaS___redArg(v_e_2127_, v_subst_2128_, v_a_2129_);
lean_dec(v_a_2129_);
lean_dec_ref(v_subst_2128_);
return v_res_2131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevBetaS(lean_object* v_e_2132_, lean_object* v_subst_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_){
_start:
{
lean_object* v___x_2141_; 
v___x_2141_ = l_Lean_Meta_Sym_instantiateRevBetaS___redArg(v_e_2132_, v_subst_2133_, v_a_2135_);
return v___x_2141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevBetaS___boxed(lean_object* v_e_2142_, lean_object* v_subst_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_){
_start:
{
lean_object* v_res_2151_; 
v_res_2151_ = l_Lean_Meta_Sym_instantiateRevBetaS(v_e_2142_, v_subst_2143_, v_a_2144_, v_a_2145_, v_a_2146_, v_a_2147_, v_a_2148_, v_a_2149_);
lean_dec(v_a_2149_);
lean_dec_ref(v_a_2148_);
lean_dec(v_a_2147_);
lean_dec_ref(v_a_2146_);
lean_dec(v_a_2145_);
lean_dec_ref(v_a_2144_);
lean_dec_ref(v_subst_2143_);
return v_res_2151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_betaRevS___redArg(lean_object* v_f_2152_, lean_object* v_revArgs_2153_, lean_object* v_a_2154_){
_start:
{
lean_object* v___x_2156_; lean_object* v_share_2157_; lean_object* v_maxFVar_2158_; lean_object* v_proofInstInfo_2159_; lean_object* v_inferType_2160_; lean_object* v_getLevel_2161_; lean_object* v_congrInfo_2162_; lean_object* v_defEqI_2163_; lean_object* v_extensions_2164_; lean_object* v_issues_2165_; lean_object* v_canon_2166_; uint8_t v_debug_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2202_; 
v___x_2156_ = lean_st_ref_take(v_a_2154_);
v_share_2157_ = lean_ctor_get(v___x_2156_, 0);
v_maxFVar_2158_ = lean_ctor_get(v___x_2156_, 1);
v_proofInstInfo_2159_ = lean_ctor_get(v___x_2156_, 2);
v_inferType_2160_ = lean_ctor_get(v___x_2156_, 3);
v_getLevel_2161_ = lean_ctor_get(v___x_2156_, 4);
v_congrInfo_2162_ = lean_ctor_get(v___x_2156_, 5);
v_defEqI_2163_ = lean_ctor_get(v___x_2156_, 6);
v_extensions_2164_ = lean_ctor_get(v___x_2156_, 7);
v_issues_2165_ = lean_ctor_get(v___x_2156_, 8);
v_canon_2166_ = lean_ctor_get(v___x_2156_, 9);
v_debug_2167_ = lean_ctor_get_uint8(v___x_2156_, sizeof(void*)*10);
v_isSharedCheck_2202_ = !lean_is_exclusive(v___x_2156_);
if (v_isSharedCheck_2202_ == 0)
{
v___x_2169_ = v___x_2156_;
v_isShared_2170_ = v_isSharedCheck_2202_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_canon_2166_);
lean_inc(v_issues_2165_);
lean_inc(v_extensions_2164_);
lean_inc(v_defEqI_2163_);
lean_inc(v_congrInfo_2162_);
lean_inc(v_getLevel_2161_);
lean_inc(v_inferType_2160_);
lean_inc(v_proofInstInfo_2159_);
lean_inc(v_maxFVar_2158_);
lean_inc(v_share_2157_);
lean_dec(v___x_2156_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2202_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v___x_2171_; lean_object* v___x_2173_; 
v___x_2171_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__0, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__0_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__0);
if (v_isShared_2170_ == 0)
{
lean_ctor_set(v___x_2169_, 0, v___x_2171_);
v___x_2173_ = v___x_2169_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v___x_2171_);
lean_ctor_set(v_reuseFailAlloc_2201_, 1, v_maxFVar_2158_);
lean_ctor_set(v_reuseFailAlloc_2201_, 2, v_proofInstInfo_2159_);
lean_ctor_set(v_reuseFailAlloc_2201_, 3, v_inferType_2160_);
lean_ctor_set(v_reuseFailAlloc_2201_, 4, v_getLevel_2161_);
lean_ctor_set(v_reuseFailAlloc_2201_, 5, v_congrInfo_2162_);
lean_ctor_set(v_reuseFailAlloc_2201_, 6, v_defEqI_2163_);
lean_ctor_set(v_reuseFailAlloc_2201_, 7, v_extensions_2164_);
lean_ctor_set(v_reuseFailAlloc_2201_, 8, v_issues_2165_);
lean_ctor_set(v_reuseFailAlloc_2201_, 9, v_canon_2166_);
lean_ctor_set_uint8(v_reuseFailAlloc_2201_, sizeof(void*)*10, v_debug_2167_);
v___x_2173_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
lean_object* v___x_2174_; lean_object* v___x_2175_; uint8_t v_debug_2176_; lean_object* v___x_2177_; lean_object* v_fst_2178_; lean_object* v_snd_2179_; lean_object* v___x_2180_; lean_object* v_maxFVar_2181_; lean_object* v_proofInstInfo_2182_; lean_object* v_inferType_2183_; lean_object* v_getLevel_2184_; lean_object* v_congrInfo_2185_; lean_object* v_defEqI_2186_; lean_object* v_extensions_2187_; lean_object* v_issues_2188_; lean_object* v_canon_2189_; uint8_t v_debug_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2199_; 
v___x_2174_ = lean_st_ref_set(v_a_2154_, v___x_2173_);
v___x_2175_ = lean_st_ref_get(v_a_2154_);
v_debug_2176_ = lean_ctor_get_uint8(v___x_2175_, sizeof(void*)*10);
lean_dec(v___x_2175_);
v___x_2177_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27(v_f_2152_, v_revArgs_2153_, v_debug_2176_, v_share_2157_);
v_fst_2178_ = lean_ctor_get(v___x_2177_, 0);
lean_inc(v_fst_2178_);
v_snd_2179_ = lean_ctor_get(v___x_2177_, 1);
lean_inc(v_snd_2179_);
lean_dec_ref(v___x_2177_);
v___x_2180_ = lean_st_ref_take(v_a_2154_);
v_maxFVar_2181_ = lean_ctor_get(v___x_2180_, 1);
v_proofInstInfo_2182_ = lean_ctor_get(v___x_2180_, 2);
v_inferType_2183_ = lean_ctor_get(v___x_2180_, 3);
v_getLevel_2184_ = lean_ctor_get(v___x_2180_, 4);
v_congrInfo_2185_ = lean_ctor_get(v___x_2180_, 5);
v_defEqI_2186_ = lean_ctor_get(v___x_2180_, 6);
v_extensions_2187_ = lean_ctor_get(v___x_2180_, 7);
v_issues_2188_ = lean_ctor_get(v___x_2180_, 8);
v_canon_2189_ = lean_ctor_get(v___x_2180_, 9);
v_debug_2190_ = lean_ctor_get_uint8(v___x_2180_, sizeof(void*)*10);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2180_);
if (v_isSharedCheck_2199_ == 0)
{
lean_object* v_unused_2200_; 
v_unused_2200_ = lean_ctor_get(v___x_2180_, 0);
lean_dec(v_unused_2200_);
v___x_2192_ = v___x_2180_;
v_isShared_2193_ = v_isSharedCheck_2199_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_canon_2189_);
lean_inc(v_issues_2188_);
lean_inc(v_extensions_2187_);
lean_inc(v_defEqI_2186_);
lean_inc(v_congrInfo_2185_);
lean_inc(v_getLevel_2184_);
lean_inc(v_inferType_2183_);
lean_inc(v_proofInstInfo_2182_);
lean_inc(v_maxFVar_2181_);
lean_dec(v___x_2180_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2199_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2195_; 
if (v_isShared_2193_ == 0)
{
lean_ctor_set(v___x_2192_, 0, v_snd_2179_);
v___x_2195_ = v___x_2192_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_snd_2179_);
lean_ctor_set(v_reuseFailAlloc_2198_, 1, v_maxFVar_2181_);
lean_ctor_set(v_reuseFailAlloc_2198_, 2, v_proofInstInfo_2182_);
lean_ctor_set(v_reuseFailAlloc_2198_, 3, v_inferType_2183_);
lean_ctor_set(v_reuseFailAlloc_2198_, 4, v_getLevel_2184_);
lean_ctor_set(v_reuseFailAlloc_2198_, 5, v_congrInfo_2185_);
lean_ctor_set(v_reuseFailAlloc_2198_, 6, v_defEqI_2186_);
lean_ctor_set(v_reuseFailAlloc_2198_, 7, v_extensions_2187_);
lean_ctor_set(v_reuseFailAlloc_2198_, 8, v_issues_2188_);
lean_ctor_set(v_reuseFailAlloc_2198_, 9, v_canon_2189_);
lean_ctor_set_uint8(v_reuseFailAlloc_2198_, sizeof(void*)*10, v_debug_2190_);
v___x_2195_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
lean_object* v___x_2196_; lean_object* v___x_2197_; 
v___x_2196_ = lean_st_ref_set(v_a_2154_, v___x_2195_);
v___x_2197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2197_, 0, v_fst_2178_);
return v___x_2197_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_betaRevS___redArg___boxed(lean_object* v_f_2203_, lean_object* v_revArgs_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_){
_start:
{
lean_object* v_res_2207_; 
v_res_2207_ = l_Lean_Meta_Sym_betaRevS___redArg(v_f_2203_, v_revArgs_2204_, v_a_2205_);
lean_dec(v_a_2205_);
lean_dec_ref(v_revArgs_2204_);
return v_res_2207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_betaRevS(lean_object* v_f_2208_, lean_object* v_revArgs_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_){
_start:
{
lean_object* v___x_2217_; 
v___x_2217_ = l_Lean_Meta_Sym_betaRevS___redArg(v_f_2208_, v_revArgs_2209_, v_a_2211_);
return v___x_2217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_betaRevS___boxed(lean_object* v_f_2218_, lean_object* v_revArgs_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_){
_start:
{
lean_object* v_res_2227_; 
v_res_2227_ = l_Lean_Meta_Sym_betaRevS(v_f_2218_, v_revArgs_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_);
lean_dec(v_a_2225_);
lean_dec_ref(v_a_2224_);
lean_dec(v_a_2223_);
lean_dec_ref(v_a_2222_);
lean_dec(v_a_2221_);
lean_dec_ref(v_a_2220_);
lean_dec_ref(v_revArgs_2219_);
return v_res_2227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_betaS___redArg(lean_object* v_f_2228_, lean_object* v_args_2229_, lean_object* v_a_2230_){
_start:
{
lean_object* v___x_2232_; lean_object* v___x_2233_; 
v___x_2232_ = l_Array_reverse___redArg(v_args_2229_);
v___x_2233_ = l_Lean_Meta_Sym_betaRevS___redArg(v_f_2228_, v___x_2232_, v_a_2230_);
lean_dec_ref(v___x_2232_);
return v___x_2233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_betaS___redArg___boxed(lean_object* v_f_2234_, lean_object* v_args_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_){
_start:
{
lean_object* v_res_2238_; 
v_res_2238_ = l_Lean_Meta_Sym_betaS___redArg(v_f_2234_, v_args_2235_, v_a_2236_);
lean_dec(v_a_2236_);
return v_res_2238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_betaS(lean_object* v_f_2239_, lean_object* v_args_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_){
_start:
{
lean_object* v___x_2248_; 
v___x_2248_ = l_Lean_Meta_Sym_betaS___redArg(v_f_2239_, v_args_2240_, v_a_2242_);
return v___x_2248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_betaS___boxed(lean_object* v_f_2249_, lean_object* v_args_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_){
_start:
{
lean_object* v_res_2258_; 
v_res_2258_ = l_Lean_Meta_Sym_betaS(v_f_2249_, v_args_2250_, v_a_2251_, v_a_2252_, v_a_2253_, v_a_2254_, v_a_2255_, v_a_2256_);
lean_dec(v_a_2256_);
lean_dec_ref(v_a_2255_);
lean_dec(v_a_2254_);
lean_dec_ref(v_a_2253_);
lean_dec(v_a_2252_);
lean_dec_ref(v_a_2251_);
return v_res_2258_;
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
