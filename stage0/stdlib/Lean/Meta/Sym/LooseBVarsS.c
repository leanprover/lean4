// Lean compiler output
// Module: Lean.Meta.Sym.LooseBVarsS
// Imports: public import Lean.Meta.Sym.ReplaceS
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
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Expr_looseBVarRange(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
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
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Builder_share1___redArg(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__0_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__2_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__3 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__3_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__4 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__4_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__5 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__5_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__6 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__6_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__6(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "_private.Lean.Meta.Sym.ReplaceS.0.Lean.Meta.Sym.visit"};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Meta.Sym.ReplaceS"};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__0;
static lean_once_cell_t l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_lowerLooseBVarsS_x27(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_lowerLooseBVarsS_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0(lean_object*);
static lean_once_cell_t l_Lean_Meta_Sym_lowerLooseBVarsS___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_lowerLooseBVarsS___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_lowerLooseBVarsS___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_lowerLooseBVarsS___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_lowerLooseBVarsS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_lowerLooseBVarsS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_liftLooseBVarsS_x27(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_liftLooseBVarsS_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_liftLooseBVarsS___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_liftLooseBVarsS___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_liftLooseBVarsS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_liftLooseBVarsS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0___redArg(lean_object* v_idx_1_, lean_object* v___y_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = l_Lean_Expr_bvar___override(v_idx_1_);
v___x_4_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_3_, v___y_2_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0(lean_object* v_idx_5_, uint8_t v___y_6_, lean_object* v___y_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0___redArg(v_idx_5_, v___y_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0___boxed(lean_object* v_idx_9_, lean_object* v___y_10_, lean_object* v___y_11_){
_start:
{
uint8_t v___y_21034__boxed_12_; lean_object* v_res_13_; 
v___y_21034__boxed_12_ = lean_unbox(v___y_10_);
v_res_13_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0(v_idx_9_, v___y_21034__boxed_12_, v___y_11_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__4(lean_object* v_x_14_, uint8_t v_bi_15_, lean_object* v_t_16_, lean_object* v_b_17_, lean_object* v___y_18_, uint8_t v___y_19_, lean_object* v___y_20_){
_start:
{
lean_object* v___y_22_; lean_object* v___y_23_; 
if (v___y_19_ == 0)
{
v___y_22_ = v___y_18_;
v___y_23_ = v___y_20_;
goto v___jp_21_;
}
else
{
lean_object* v___x_36_; lean_object* v_snd_37_; lean_object* v___x_38_; lean_object* v_snd_39_; 
lean_inc_ref(v_t_16_);
v___x_36_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_16_, v___y_19_, v___y_20_);
v_snd_37_ = lean_ctor_get(v___x_36_, 1);
lean_inc(v_snd_37_);
lean_dec_ref(v___x_36_);
lean_inc_ref(v_b_17_);
v___x_38_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_17_, v___y_19_, v_snd_37_);
v_snd_39_ = lean_ctor_get(v___x_38_, 1);
lean_inc(v_snd_39_);
lean_dec_ref(v___x_38_);
v___y_22_ = v___y_18_;
v___y_23_ = v_snd_39_;
goto v___jp_21_;
}
v___jp_21_:
{
lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v_fst_26_; lean_object* v_snd_27_; lean_object* v___x_29_; uint8_t v_isShared_30_; uint8_t v_isSharedCheck_35_; 
v___x_24_ = l_Lean_Expr_forallE___override(v_x_14_, v_t_16_, v_b_17_, v_bi_15_);
v___x_25_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_24_, v___y_23_);
v_fst_26_ = lean_ctor_get(v___x_25_, 0);
v_snd_27_ = lean_ctor_get(v___x_25_, 1);
v_isSharedCheck_35_ = !lean_is_exclusive(v___x_25_);
if (v_isSharedCheck_35_ == 0)
{
v___x_29_ = v___x_25_;
v_isShared_30_ = v_isSharedCheck_35_;
goto v_resetjp_28_;
}
else
{
lean_inc(v_snd_27_);
lean_inc(v_fst_26_);
lean_dec(v___x_25_);
v___x_29_ = lean_box(0);
v_isShared_30_ = v_isSharedCheck_35_;
goto v_resetjp_28_;
}
v_resetjp_28_:
{
lean_object* v___x_32_; 
if (v_isShared_30_ == 0)
{
lean_ctor_set(v___x_29_, 1, v___y_22_);
v___x_32_ = v___x_29_;
goto v_reusejp_31_;
}
else
{
lean_object* v_reuseFailAlloc_34_; 
v_reuseFailAlloc_34_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_34_, 0, v_fst_26_);
lean_ctor_set(v_reuseFailAlloc_34_, 1, v___y_22_);
v___x_32_ = v_reuseFailAlloc_34_;
goto v_reusejp_31_;
}
v_reusejp_31_:
{
lean_object* v___x_33_; 
v___x_33_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_33_, 0, v___x_32_);
lean_ctor_set(v___x_33_, 1, v_snd_27_);
return v___x_33_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__4___boxed(lean_object* v_x_40_, lean_object* v_bi_41_, lean_object* v_t_42_, lean_object* v_b_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_){
_start:
{
uint8_t v_bi_boxed_47_; uint8_t v___y_21043__boxed_48_; lean_object* v_res_49_; 
v_bi_boxed_47_ = lean_unbox(v_bi_41_);
v___y_21043__boxed_48_ = lean_unbox(v___y_45_);
v_res_49_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__4(v_x_40_, v_bi_boxed_47_, v_t_42_, v_b_43_, v___y_44_, v___y_21043__boxed_48_, v___y_46_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__7(lean_object* v_structName_50_, lean_object* v_idx_51_, lean_object* v_struct_52_, lean_object* v___y_53_, uint8_t v___y_54_, lean_object* v___y_55_){
_start:
{
lean_object* v___y_57_; lean_object* v___y_58_; 
if (v___y_54_ == 0)
{
v___y_57_ = v___y_53_;
v___y_58_ = v___y_55_;
goto v___jp_56_;
}
else
{
lean_object* v___x_71_; lean_object* v_snd_72_; 
lean_inc_ref(v_struct_52_);
v___x_71_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_struct_52_, v___y_54_, v___y_55_);
v_snd_72_ = lean_ctor_get(v___x_71_, 1);
lean_inc(v_snd_72_);
lean_dec_ref(v___x_71_);
v___y_57_ = v___y_53_;
v___y_58_ = v_snd_72_;
goto v___jp_56_;
}
v___jp_56_:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v_fst_61_; lean_object* v_snd_62_; lean_object* v___x_64_; uint8_t v_isShared_65_; uint8_t v_isSharedCheck_70_; 
v___x_59_ = l_Lean_Expr_proj___override(v_structName_50_, v_idx_51_, v_struct_52_);
v___x_60_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_59_, v___y_58_);
v_fst_61_ = lean_ctor_get(v___x_60_, 0);
v_snd_62_ = lean_ctor_get(v___x_60_, 1);
v_isSharedCheck_70_ = !lean_is_exclusive(v___x_60_);
if (v_isSharedCheck_70_ == 0)
{
v___x_64_ = v___x_60_;
v_isShared_65_ = v_isSharedCheck_70_;
goto v_resetjp_63_;
}
else
{
lean_inc(v_snd_62_);
lean_inc(v_fst_61_);
lean_dec(v___x_60_);
v___x_64_ = lean_box(0);
v_isShared_65_ = v_isSharedCheck_70_;
goto v_resetjp_63_;
}
v_resetjp_63_:
{
lean_object* v___x_67_; 
if (v_isShared_65_ == 0)
{
lean_ctor_set(v___x_64_, 1, v___y_57_);
v___x_67_ = v___x_64_;
goto v_reusejp_66_;
}
else
{
lean_object* v_reuseFailAlloc_69_; 
v_reuseFailAlloc_69_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_69_, 0, v_fst_61_);
lean_ctor_set(v_reuseFailAlloc_69_, 1, v___y_57_);
v___x_67_ = v_reuseFailAlloc_69_;
goto v_reusejp_66_;
}
v_reusejp_66_:
{
lean_object* v___x_68_; 
v___x_68_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_68_, 0, v___x_67_);
lean_ctor_set(v___x_68_, 1, v_snd_62_);
return v___x_68_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__7___boxed(lean_object* v_structName_73_, lean_object* v_idx_74_, lean_object* v_struct_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_){
_start:
{
uint8_t v___y_21092__boxed_79_; lean_object* v_res_80_; 
v___y_21092__boxed_79_ = lean_unbox(v___y_77_);
v_res_80_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__7(v_structName_73_, v_idx_74_, v_struct_75_, v___y_76_, v___y_21092__boxed_79_, v___y_78_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__3(lean_object* v_x_81_, uint8_t v_bi_82_, lean_object* v_t_83_, lean_object* v_b_84_, lean_object* v___y_85_, uint8_t v___y_86_, lean_object* v___y_87_){
_start:
{
lean_object* v___y_89_; lean_object* v___y_90_; 
if (v___y_86_ == 0)
{
v___y_89_ = v___y_85_;
v___y_90_ = v___y_87_;
goto v___jp_88_;
}
else
{
lean_object* v___x_103_; lean_object* v_snd_104_; lean_object* v___x_105_; lean_object* v_snd_106_; 
lean_inc_ref(v_t_83_);
v___x_103_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_83_, v___y_86_, v___y_87_);
v_snd_104_ = lean_ctor_get(v___x_103_, 1);
lean_inc(v_snd_104_);
lean_dec_ref(v___x_103_);
lean_inc_ref(v_b_84_);
v___x_105_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_84_, v___y_86_, v_snd_104_);
v_snd_106_ = lean_ctor_get(v___x_105_, 1);
lean_inc(v_snd_106_);
lean_dec_ref(v___x_105_);
v___y_89_ = v___y_85_;
v___y_90_ = v_snd_106_;
goto v___jp_88_;
}
v___jp_88_:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v_fst_93_; lean_object* v_snd_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_102_; 
v___x_91_ = l_Lean_Expr_lam___override(v_x_81_, v_t_83_, v_b_84_, v_bi_82_);
v___x_92_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_91_, v___y_90_);
v_fst_93_ = lean_ctor_get(v___x_92_, 0);
v_snd_94_ = lean_ctor_get(v___x_92_, 1);
v_isSharedCheck_102_ = !lean_is_exclusive(v___x_92_);
if (v_isSharedCheck_102_ == 0)
{
v___x_96_ = v___x_92_;
v_isShared_97_ = v_isSharedCheck_102_;
goto v_resetjp_95_;
}
else
{
lean_inc(v_snd_94_);
lean_inc(v_fst_93_);
lean_dec(v___x_92_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_102_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
lean_object* v___x_99_; 
if (v_isShared_97_ == 0)
{
lean_ctor_set(v___x_96_, 1, v___y_89_);
v___x_99_ = v___x_96_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v_fst_93_);
lean_ctor_set(v_reuseFailAlloc_101_, 1, v___y_89_);
v___x_99_ = v_reuseFailAlloc_101_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
lean_object* v___x_100_; 
v___x_100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_100_, 0, v___x_99_);
lean_ctor_set(v___x_100_, 1, v_snd_94_);
return v___x_100_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__3___boxed(lean_object* v_x_107_, lean_object* v_bi_108_, lean_object* v_t_109_, lean_object* v_b_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_){
_start:
{
uint8_t v_bi_boxed_114_; uint8_t v___y_21136__boxed_115_; lean_object* v_res_116_; 
v_bi_boxed_114_ = lean_unbox(v_bi_108_);
v___y_21136__boxed_115_ = lean_unbox(v___y_112_);
v_res_116_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__3(v_x_107_, v_bi_boxed_114_, v_t_109_, v_b_110_, v___y_111_, v___y_21136__boxed_115_, v___y_113_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8(lean_object* v_msg_124_, lean_object* v___y_125_, uint8_t v___y_126_, lean_object* v___y_127_){
_start:
{
lean_object* v___f_128_; lean_object* v___f_129_; lean_object* v___f_130_; lean_object* v___f_131_; lean_object* v___f_132_; lean_object* v___f_133_; lean_object* v___f_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___f_138_; lean_object* v___f_139_; lean_object* v___f_140_; lean_object* v___f_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___f_149_; lean_object* v___f_150_; lean_object* v___f_151_; lean_object* v___f_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_20767__overap_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___f_128_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__0));
v___f_129_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__1));
v___f_130_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__2));
v___f_131_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__3));
v___f_132_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__4));
v___f_133_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__5));
v___f_134_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__6));
v___x_135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_135_, 0, v___f_128_);
lean_ctor_set(v___x_135_, 1, v___f_129_);
v___x_136_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_136_, 0, v___x_135_);
lean_ctor_set(v___x_136_, 1, v___f_130_);
lean_ctor_set(v___x_136_, 2, v___f_131_);
lean_ctor_set(v___x_136_, 3, v___f_132_);
lean_ctor_set(v___x_136_, 4, v___f_133_);
v___x_137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_137_, 0, v___x_136_);
lean_ctor_set(v___x_137_, 1, v___f_134_);
lean_inc_ref_n(v___x_137_, 6);
v___f_138_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_138_, 0, v___x_137_);
v___f_139_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_139_, 0, v___x_137_);
v___f_140_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_140_, 0, v___x_137_);
v___f_141_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_141_, 0, v___x_137_);
v___x_142_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_142_, 0, lean_box(0));
lean_closure_set(v___x_142_, 1, lean_box(0));
lean_closure_set(v___x_142_, 2, v___x_137_);
v___x_143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_143_, 0, v___x_142_);
lean_ctor_set(v___x_143_, 1, v___f_138_);
v___x_144_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_144_, 0, lean_box(0));
lean_closure_set(v___x_144_, 1, lean_box(0));
lean_closure_set(v___x_144_, 2, v___x_137_);
v___x_145_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_145_, 0, v___x_143_);
lean_ctor_set(v___x_145_, 1, v___x_144_);
lean_ctor_set(v___x_145_, 2, v___f_139_);
lean_ctor_set(v___x_145_, 3, v___f_140_);
lean_ctor_set(v___x_145_, 4, v___f_141_);
v___x_146_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_146_, 0, lean_box(0));
lean_closure_set(v___x_146_, 1, lean_box(0));
lean_closure_set(v___x_146_, 2, v___x_137_);
v___x_147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_147_, 0, v___x_145_);
lean_ctor_set(v___x_147_, 1, v___x_146_);
v___x_148_ = l_ReaderT_instMonad___redArg(v___x_147_);
lean_inc_ref_n(v___x_148_, 6);
v___f_149_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_149_, 0, v___x_148_);
v___f_150_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_150_, 0, v___x_148_);
v___f_151_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_151_, 0, v___x_148_);
v___f_152_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_152_, 0, v___x_148_);
v___x_153_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_153_, 0, lean_box(0));
lean_closure_set(v___x_153_, 1, lean_box(0));
lean_closure_set(v___x_153_, 2, v___x_148_);
v___x_154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_154_, 0, v___x_153_);
lean_ctor_set(v___x_154_, 1, v___f_149_);
v___x_155_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_155_, 0, lean_box(0));
lean_closure_set(v___x_155_, 1, lean_box(0));
lean_closure_set(v___x_155_, 2, v___x_148_);
v___x_156_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_156_, 0, v___x_154_);
lean_ctor_set(v___x_156_, 1, v___x_155_);
lean_ctor_set(v___x_156_, 2, v___f_150_);
lean_ctor_set(v___x_156_, 3, v___f_151_);
lean_ctor_set(v___x_156_, 4, v___f_152_);
v___x_157_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_157_, 0, lean_box(0));
lean_closure_set(v___x_157_, 1, lean_box(0));
lean_closure_set(v___x_157_, 2, v___x_148_);
v___x_158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_158_, 0, v___x_156_);
lean_ctor_set(v___x_158_, 1, v___x_157_);
v___x_159_ = l_Lean_instInhabitedExpr;
v___x_160_ = l_instInhabitedOfMonad___redArg(v___x_158_, v___x_159_);
v___x_20767__overap_161_ = lean_panic_fn_borrowed(v___x_160_, v_msg_124_);
lean_dec(v___x_160_);
v___x_162_ = lean_box(v___y_126_);
v___x_163_ = lean_apply_3(v___x_20767__overap_161_, v___y_125_, v___x_162_, v___y_127_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___boxed(lean_object* v_msg_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_){
_start:
{
uint8_t v___y_21199__boxed_168_; lean_object* v_res_169_; 
v___y_21199__boxed_168_ = lean_unbox(v___y_166_);
v_res_169_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8(v_msg_164_, v___y_165_, v___y_21199__boxed_168_, v___y_167_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__2(lean_object* v_f_170_, lean_object* v_a_171_, lean_object* v___y_172_, uint8_t v___y_173_, lean_object* v___y_174_){
_start:
{
lean_object* v___y_176_; lean_object* v___y_177_; 
if (v___y_173_ == 0)
{
v___y_176_ = v___y_172_;
v___y_177_ = v___y_174_;
goto v___jp_175_;
}
else
{
lean_object* v___x_190_; lean_object* v_snd_191_; lean_object* v___x_192_; lean_object* v_snd_193_; 
lean_inc_ref(v_f_170_);
v___x_190_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_f_170_, v___y_173_, v___y_174_);
v_snd_191_ = lean_ctor_get(v___x_190_, 1);
lean_inc(v_snd_191_);
lean_dec_ref(v___x_190_);
lean_inc_ref(v_a_171_);
v___x_192_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_a_171_, v___y_173_, v_snd_191_);
v_snd_193_ = lean_ctor_get(v___x_192_, 1);
lean_inc(v_snd_193_);
lean_dec_ref(v___x_192_);
v___y_176_ = v___y_172_;
v___y_177_ = v_snd_193_;
goto v___jp_175_;
}
v___jp_175_:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v_fst_180_; lean_object* v_snd_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_189_; 
v___x_178_ = l_Lean_Expr_app___override(v_f_170_, v_a_171_);
v___x_179_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_178_, v___y_177_);
v_fst_180_ = lean_ctor_get(v___x_179_, 0);
v_snd_181_ = lean_ctor_get(v___x_179_, 1);
v_isSharedCheck_189_ = !lean_is_exclusive(v___x_179_);
if (v_isSharedCheck_189_ == 0)
{
v___x_183_ = v___x_179_;
v_isShared_184_ = v_isSharedCheck_189_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_snd_181_);
lean_inc(v_fst_180_);
lean_dec(v___x_179_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_189_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___x_186_; 
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 1, v___y_176_);
v___x_186_ = v___x_183_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v_fst_180_);
lean_ctor_set(v_reuseFailAlloc_188_, 1, v___y_176_);
v___x_186_ = v_reuseFailAlloc_188_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
lean_object* v___x_187_; 
v___x_187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_187_, 0, v___x_186_);
lean_ctor_set(v___x_187_, 1, v_snd_181_);
return v___x_187_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__2___boxed(lean_object* v_f_194_, lean_object* v_a_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_){
_start:
{
uint8_t v___y_21285__boxed_199_; lean_object* v_res_200_; 
v___y_21285__boxed_199_ = lean_unbox(v___y_197_);
v_res_200_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__2(v_f_194_, v_a_195_, v___y_196_, v___y_21285__boxed_199_, v___y_198_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10___redArg(lean_object* v_a_201_, lean_object* v_x_202_){
_start:
{
if (lean_obj_tag(v_x_202_) == 0)
{
lean_object* v___x_203_; 
v___x_203_ = lean_box(0);
return v___x_203_;
}
else
{
lean_object* v_key_204_; lean_object* v_value_205_; lean_object* v_tail_206_; uint8_t v___y_208_; lean_object* v_fst_211_; lean_object* v_snd_212_; lean_object* v_fst_213_; lean_object* v_snd_214_; uint8_t v___x_215_; 
v_key_204_ = lean_ctor_get(v_x_202_, 0);
v_value_205_ = lean_ctor_get(v_x_202_, 1);
v_tail_206_ = lean_ctor_get(v_x_202_, 2);
v_fst_211_ = lean_ctor_get(v_key_204_, 0);
v_snd_212_ = lean_ctor_get(v_key_204_, 1);
v_fst_213_ = lean_ctor_get(v_a_201_, 0);
v_snd_214_ = lean_ctor_get(v_a_201_, 1);
v___x_215_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_211_, v_fst_213_);
if (v___x_215_ == 0)
{
v___y_208_ = v___x_215_;
goto v___jp_207_;
}
else
{
uint8_t v___x_216_; 
v___x_216_ = lean_nat_dec_eq(v_snd_212_, v_snd_214_);
v___y_208_ = v___x_216_;
goto v___jp_207_;
}
v___jp_207_:
{
if (v___y_208_ == 0)
{
v_x_202_ = v_tail_206_;
goto _start;
}
else
{
lean_object* v___x_210_; 
lean_inc(v_value_205_);
v___x_210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_210_, 0, v_value_205_);
return v___x_210_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10___redArg___boxed(lean_object* v_a_217_, lean_object* v_x_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10___redArg(v_a_217_, v_x_218_);
lean_dec(v_x_218_);
lean_dec_ref(v_a_217_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___redArg(lean_object* v_m_220_, lean_object* v_a_221_){
_start:
{
lean_object* v_buckets_222_; lean_object* v_fst_223_; lean_object* v_snd_224_; lean_object* v___x_225_; uint64_t v___x_226_; uint64_t v___x_227_; uint64_t v___x_228_; uint64_t v___x_229_; uint64_t v___x_230_; uint64_t v_fold_231_; uint64_t v___x_232_; uint64_t v___x_233_; uint64_t v___x_234_; size_t v___x_235_; size_t v___x_236_; size_t v___x_237_; size_t v___x_238_; size_t v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v_buckets_222_ = lean_ctor_get(v_m_220_, 1);
v_fst_223_ = lean_ctor_get(v_a_221_, 0);
v_snd_224_ = lean_ctor_get(v_a_221_, 1);
v___x_225_ = lean_array_get_size(v_buckets_222_);
v___x_226_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_223_);
v___x_227_ = lean_uint64_of_nat(v_snd_224_);
v___x_228_ = lean_uint64_mix_hash(v___x_226_, v___x_227_);
v___x_229_ = 32ULL;
v___x_230_ = lean_uint64_shift_right(v___x_228_, v___x_229_);
v_fold_231_ = lean_uint64_xor(v___x_228_, v___x_230_);
v___x_232_ = 16ULL;
v___x_233_ = lean_uint64_shift_right(v_fold_231_, v___x_232_);
v___x_234_ = lean_uint64_xor(v_fold_231_, v___x_233_);
v___x_235_ = lean_uint64_to_usize(v___x_234_);
v___x_236_ = lean_usize_of_nat(v___x_225_);
v___x_237_ = ((size_t)1ULL);
v___x_238_ = lean_usize_sub(v___x_236_, v___x_237_);
v___x_239_ = lean_usize_land(v___x_235_, v___x_238_);
v___x_240_ = lean_array_uget_borrowed(v_buckets_222_, v___x_239_);
v___x_241_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10___redArg(v_a_221_, v___x_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_m_242_, lean_object* v_a_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___redArg(v_m_242_, v_a_243_);
lean_dec_ref(v_a_243_);
lean_dec_ref(v_m_242_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5(lean_object* v_x_245_, lean_object* v_t_246_, lean_object* v_v_247_, lean_object* v_b_248_, uint8_t v_nondep_249_, lean_object* v___y_250_, uint8_t v___y_251_, lean_object* v___y_252_){
_start:
{
lean_object* v___y_254_; lean_object* v___y_255_; 
if (v___y_251_ == 0)
{
v___y_254_ = v___y_250_;
v___y_255_ = v___y_252_;
goto v___jp_253_;
}
else
{
lean_object* v___x_268_; lean_object* v_snd_269_; lean_object* v___x_270_; lean_object* v_snd_271_; lean_object* v___x_272_; lean_object* v_snd_273_; 
lean_inc_ref(v_t_246_);
v___x_268_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_246_, v___y_251_, v___y_252_);
v_snd_269_ = lean_ctor_get(v___x_268_, 1);
lean_inc(v_snd_269_);
lean_dec_ref(v___x_268_);
lean_inc_ref(v_v_247_);
v___x_270_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_v_247_, v___y_251_, v_snd_269_);
v_snd_271_ = lean_ctor_get(v___x_270_, 1);
lean_inc(v_snd_271_);
lean_dec_ref(v___x_270_);
lean_inc_ref(v_b_248_);
v___x_272_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_248_, v___y_251_, v_snd_271_);
v_snd_273_ = lean_ctor_get(v___x_272_, 1);
lean_inc(v_snd_273_);
lean_dec_ref(v___x_272_);
v___y_254_ = v___y_250_;
v___y_255_ = v_snd_273_;
goto v___jp_253_;
}
v___jp_253_:
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v_fst_258_; lean_object* v_snd_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_267_; 
v___x_256_ = l_Lean_Expr_letE___override(v_x_245_, v_t_246_, v_v_247_, v_b_248_, v_nondep_249_);
v___x_257_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_256_, v___y_255_);
v_fst_258_ = lean_ctor_get(v___x_257_, 0);
v_snd_259_ = lean_ctor_get(v___x_257_, 1);
v_isSharedCheck_267_ = !lean_is_exclusive(v___x_257_);
if (v_isSharedCheck_267_ == 0)
{
v___x_261_ = v___x_257_;
v_isShared_262_ = v_isSharedCheck_267_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_snd_259_);
lean_inc(v_fst_258_);
lean_dec(v___x_257_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_267_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_264_; 
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 1, v___y_254_);
v___x_264_ = v___x_261_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v_fst_258_);
lean_ctor_set(v_reuseFailAlloc_266_, 1, v___y_254_);
v___x_264_ = v_reuseFailAlloc_266_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
lean_object* v___x_265_; 
v___x_265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_265_, 0, v___x_264_);
lean_ctor_set(v___x_265_, 1, v_snd_259_);
return v___x_265_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5___boxed(lean_object* v_x_274_, lean_object* v_t_275_, lean_object* v_v_276_, lean_object* v_b_277_, lean_object* v_nondep_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_){
_start:
{
uint8_t v_nondep_boxed_282_; uint8_t v___y_21403__boxed_283_; lean_object* v_res_284_; 
v_nondep_boxed_282_ = lean_unbox(v_nondep_278_);
v___y_21403__boxed_283_ = lean_unbox(v___y_280_);
v_res_284_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5(v_x_274_, v_t_275_, v_v_276_, v_b_277_, v_nondep_boxed_282_, v___y_279_, v___y_21403__boxed_283_, v___y_281_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__6(lean_object* v_d_285_, lean_object* v_e_286_, lean_object* v___y_287_, uint8_t v___y_288_, lean_object* v___y_289_){
_start:
{
lean_object* v___y_291_; lean_object* v___y_292_; 
if (v___y_288_ == 0)
{
v___y_291_ = v___y_287_;
v___y_292_ = v___y_289_;
goto v___jp_290_;
}
else
{
lean_object* v___x_305_; lean_object* v_snd_306_; 
lean_inc_ref(v_e_286_);
v___x_305_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_e_286_, v___y_288_, v___y_289_);
v_snd_306_ = lean_ctor_get(v___x_305_, 1);
lean_inc(v_snd_306_);
lean_dec_ref(v___x_305_);
v___y_291_ = v___y_287_;
v___y_292_ = v_snd_306_;
goto v___jp_290_;
}
v___jp_290_:
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v_fst_295_; lean_object* v_snd_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_304_; 
v___x_293_ = l_Lean_Expr_mdata___override(v_d_285_, v_e_286_);
v___x_294_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_293_, v___y_292_);
v_fst_295_ = lean_ctor_get(v___x_294_, 0);
v_snd_296_ = lean_ctor_get(v___x_294_, 1);
v_isSharedCheck_304_ = !lean_is_exclusive(v___x_294_);
if (v_isSharedCheck_304_ == 0)
{
v___x_298_ = v___x_294_;
v_isShared_299_ = v_isSharedCheck_304_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_snd_296_);
lean_inc(v_fst_295_);
lean_dec(v___x_294_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_304_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_301_; 
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 1, v___y_291_);
v___x_301_ = v___x_298_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_fst_295_);
lean_ctor_set(v_reuseFailAlloc_303_, 1, v___y_291_);
v___x_301_ = v_reuseFailAlloc_303_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
lean_object* v___x_302_; 
v___x_302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
lean_ctor_set(v___x_302_, 1, v_snd_296_);
return v___x_302_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__6___boxed(lean_object* v_d_307_, lean_object* v_e_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_){
_start:
{
uint8_t v___y_21457__boxed_312_; lean_object* v_res_313_; 
v___y_21457__boxed_312_ = lean_unbox(v___y_310_);
v_res_313_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__6(v_d_307_, v_e_308_, v___y_309_, v___y_21457__boxed_312_, v___y_311_);
return v_res_313_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3(void){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_317_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__2));
v___x_318_ = lean_unsigned_to_nat(67u);
v___x_319_ = lean_unsigned_to_nat(35u);
v___x_320_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__1));
v___x_321_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__0));
v___x_322_ = l_mkPanicMessageWithDecl(v___x_321_, v___x_320_, v___x_319_, v___x_318_, v___x_317_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1(lean_object* v_s_323_, lean_object* v_d_324_, lean_object* v_e_325_, lean_object* v_offset_326_, lean_object* v_a_327_, uint8_t v_a_328_, lean_object* v_a_329_){
_start:
{
switch(lean_obj_tag(v_e_325_))
{
case 5:
{
lean_object* v_fn_330_; lean_object* v_arg_331_; lean_object* v___x_332_; lean_object* v_fst_333_; lean_object* v_snd_334_; lean_object* v_fst_335_; lean_object* v_snd_336_; lean_object* v___x_337_; lean_object* v_fst_338_; lean_object* v_snd_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_360_; 
v_fn_330_ = lean_ctor_get(v_e_325_, 0);
v_arg_331_ = lean_ctor_get(v_e_325_, 1);
lean_inc(v_offset_326_);
lean_inc_ref(v_fn_330_);
v___x_332_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_323_, v_d_324_, v_fn_330_, v_offset_326_, v_a_327_, v_a_328_, v_a_329_);
v_fst_333_ = lean_ctor_get(v___x_332_, 0);
lean_inc(v_fst_333_);
v_snd_334_ = lean_ctor_get(v___x_332_, 1);
lean_inc(v_snd_334_);
lean_dec_ref(v___x_332_);
v_fst_335_ = lean_ctor_get(v_fst_333_, 0);
lean_inc(v_fst_335_);
v_snd_336_ = lean_ctor_get(v_fst_333_, 1);
lean_inc(v_snd_336_);
lean_dec(v_fst_333_);
lean_inc_ref(v_arg_331_);
v___x_337_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_323_, v_d_324_, v_arg_331_, v_offset_326_, v_snd_336_, v_a_328_, v_snd_334_);
v_fst_338_ = lean_ctor_get(v___x_337_, 0);
v_snd_339_ = lean_ctor_get(v___x_337_, 1);
v_isSharedCheck_360_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_360_ == 0)
{
v___x_341_ = v___x_337_;
v_isShared_342_ = v_isSharedCheck_360_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_snd_339_);
lean_inc(v_fst_338_);
lean_dec(v___x_337_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_360_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v_fst_343_; lean_object* v_snd_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_359_; 
v_fst_343_ = lean_ctor_get(v_fst_338_, 0);
v_snd_344_ = lean_ctor_get(v_fst_338_, 1);
v_isSharedCheck_359_ = !lean_is_exclusive(v_fst_338_);
if (v_isSharedCheck_359_ == 0)
{
v___x_346_ = v_fst_338_;
v_isShared_347_ = v_isSharedCheck_359_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_snd_344_);
lean_inc(v_fst_343_);
lean_dec(v_fst_338_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_359_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
uint8_t v___y_349_; uint8_t v___x_357_; 
v___x_357_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_330_, v_fst_335_);
if (v___x_357_ == 0)
{
v___y_349_ = v___x_357_;
goto v___jp_348_;
}
else
{
uint8_t v___x_358_; 
v___x_358_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_331_, v_fst_343_);
v___y_349_ = v___x_358_;
goto v___jp_348_;
}
v___jp_348_:
{
if (v___y_349_ == 0)
{
lean_object* v___x_350_; 
lean_del_object(v___x_346_);
lean_del_object(v___x_341_);
lean_dec_ref(v_e_325_);
v___x_350_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__2(v_fst_335_, v_fst_343_, v_snd_344_, v_a_328_, v_snd_339_);
return v___x_350_;
}
else
{
lean_object* v___x_352_; 
lean_dec(v_fst_343_);
lean_dec(v_fst_335_);
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 0, v_e_325_);
v___x_352_ = v___x_346_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_e_325_);
lean_ctor_set(v_reuseFailAlloc_356_, 1, v_snd_344_);
v___x_352_ = v_reuseFailAlloc_356_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
lean_object* v___x_354_; 
if (v_isShared_342_ == 0)
{
lean_ctor_set(v___x_341_, 0, v___x_352_);
v___x_354_ = v___x_341_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v___x_352_);
lean_ctor_set(v_reuseFailAlloc_355_, 1, v_snd_339_);
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
}
}
}
case 6:
{
lean_object* v_binderName_361_; lean_object* v_binderType_362_; lean_object* v_body_363_; uint8_t v_binderInfo_364_; lean_object* v___x_365_; lean_object* v_fst_366_; lean_object* v_snd_367_; lean_object* v_fst_368_; lean_object* v_snd_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v_fst_373_; lean_object* v_snd_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_395_; 
v_binderName_361_ = lean_ctor_get(v_e_325_, 0);
v_binderType_362_ = lean_ctor_get(v_e_325_, 1);
v_body_363_ = lean_ctor_get(v_e_325_, 2);
v_binderInfo_364_ = lean_ctor_get_uint8(v_e_325_, sizeof(void*)*3 + 8);
lean_inc(v_offset_326_);
lean_inc_ref(v_binderType_362_);
v___x_365_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_323_, v_d_324_, v_binderType_362_, v_offset_326_, v_a_327_, v_a_328_, v_a_329_);
v_fst_366_ = lean_ctor_get(v___x_365_, 0);
lean_inc(v_fst_366_);
v_snd_367_ = lean_ctor_get(v___x_365_, 1);
lean_inc(v_snd_367_);
lean_dec_ref(v___x_365_);
v_fst_368_ = lean_ctor_get(v_fst_366_, 0);
lean_inc(v_fst_368_);
v_snd_369_ = lean_ctor_get(v_fst_366_, 1);
lean_inc(v_snd_369_);
lean_dec(v_fst_366_);
v___x_370_ = lean_unsigned_to_nat(1u);
v___x_371_ = lean_nat_add(v_offset_326_, v___x_370_);
lean_dec(v_offset_326_);
lean_inc_ref(v_body_363_);
v___x_372_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_323_, v_d_324_, v_body_363_, v___x_371_, v_snd_369_, v_a_328_, v_snd_367_);
v_fst_373_ = lean_ctor_get(v___x_372_, 0);
v_snd_374_ = lean_ctor_get(v___x_372_, 1);
v_isSharedCheck_395_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_395_ == 0)
{
v___x_376_ = v___x_372_;
v_isShared_377_ = v_isSharedCheck_395_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_snd_374_);
lean_inc(v_fst_373_);
lean_dec(v___x_372_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_395_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v_fst_378_; lean_object* v_snd_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_394_; 
v_fst_378_ = lean_ctor_get(v_fst_373_, 0);
v_snd_379_ = lean_ctor_get(v_fst_373_, 1);
v_isSharedCheck_394_ = !lean_is_exclusive(v_fst_373_);
if (v_isSharedCheck_394_ == 0)
{
v___x_381_ = v_fst_373_;
v_isShared_382_ = v_isSharedCheck_394_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_snd_379_);
lean_inc(v_fst_378_);
lean_dec(v_fst_373_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_394_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
uint8_t v___y_384_; uint8_t v___x_392_; 
v___x_392_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_362_, v_fst_368_);
if (v___x_392_ == 0)
{
v___y_384_ = v___x_392_;
goto v___jp_383_;
}
else
{
uint8_t v___x_393_; 
v___x_393_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_363_, v_fst_378_);
v___y_384_ = v___x_393_;
goto v___jp_383_;
}
v___jp_383_:
{
if (v___y_384_ == 0)
{
lean_object* v___x_385_; 
lean_inc(v_binderName_361_);
lean_del_object(v___x_381_);
lean_del_object(v___x_376_);
lean_dec_ref(v_e_325_);
v___x_385_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__3(v_binderName_361_, v_binderInfo_364_, v_fst_368_, v_fst_378_, v_snd_379_, v_a_328_, v_snd_374_);
return v___x_385_;
}
else
{
lean_object* v___x_387_; 
lean_dec(v_fst_378_);
lean_dec(v_fst_368_);
if (v_isShared_382_ == 0)
{
lean_ctor_set(v___x_381_, 0, v_e_325_);
v___x_387_ = v___x_381_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_e_325_);
lean_ctor_set(v_reuseFailAlloc_391_, 1, v_snd_379_);
v___x_387_ = v_reuseFailAlloc_391_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
lean_object* v___x_389_; 
if (v_isShared_377_ == 0)
{
lean_ctor_set(v___x_376_, 0, v___x_387_);
v___x_389_ = v___x_376_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v___x_387_);
lean_ctor_set(v_reuseFailAlloc_390_, 1, v_snd_374_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
}
}
}
}
}
case 7:
{
lean_object* v_binderName_396_; lean_object* v_binderType_397_; lean_object* v_body_398_; uint8_t v_binderInfo_399_; lean_object* v___x_400_; lean_object* v_fst_401_; lean_object* v_snd_402_; lean_object* v_fst_403_; lean_object* v_snd_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v_fst_408_; lean_object* v_snd_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_430_; 
v_binderName_396_ = lean_ctor_get(v_e_325_, 0);
v_binderType_397_ = lean_ctor_get(v_e_325_, 1);
v_body_398_ = lean_ctor_get(v_e_325_, 2);
v_binderInfo_399_ = lean_ctor_get_uint8(v_e_325_, sizeof(void*)*3 + 8);
lean_inc(v_offset_326_);
lean_inc_ref(v_binderType_397_);
v___x_400_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_323_, v_d_324_, v_binderType_397_, v_offset_326_, v_a_327_, v_a_328_, v_a_329_);
v_fst_401_ = lean_ctor_get(v___x_400_, 0);
lean_inc(v_fst_401_);
v_snd_402_ = lean_ctor_get(v___x_400_, 1);
lean_inc(v_snd_402_);
lean_dec_ref(v___x_400_);
v_fst_403_ = lean_ctor_get(v_fst_401_, 0);
lean_inc(v_fst_403_);
v_snd_404_ = lean_ctor_get(v_fst_401_, 1);
lean_inc(v_snd_404_);
lean_dec(v_fst_401_);
v___x_405_ = lean_unsigned_to_nat(1u);
v___x_406_ = lean_nat_add(v_offset_326_, v___x_405_);
lean_dec(v_offset_326_);
lean_inc_ref(v_body_398_);
v___x_407_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_323_, v_d_324_, v_body_398_, v___x_406_, v_snd_404_, v_a_328_, v_snd_402_);
v_fst_408_ = lean_ctor_get(v___x_407_, 0);
v_snd_409_ = lean_ctor_get(v___x_407_, 1);
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_430_ == 0)
{
v___x_411_ = v___x_407_;
v_isShared_412_ = v_isSharedCheck_430_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_snd_409_);
lean_inc(v_fst_408_);
lean_dec(v___x_407_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_430_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v_fst_413_; lean_object* v_snd_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_429_; 
v_fst_413_ = lean_ctor_get(v_fst_408_, 0);
v_snd_414_ = lean_ctor_get(v_fst_408_, 1);
v_isSharedCheck_429_ = !lean_is_exclusive(v_fst_408_);
if (v_isSharedCheck_429_ == 0)
{
v___x_416_ = v_fst_408_;
v_isShared_417_ = v_isSharedCheck_429_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_snd_414_);
lean_inc(v_fst_413_);
lean_dec(v_fst_408_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_429_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
uint8_t v___y_419_; uint8_t v___x_427_; 
v___x_427_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_397_, v_fst_403_);
if (v___x_427_ == 0)
{
v___y_419_ = v___x_427_;
goto v___jp_418_;
}
else
{
uint8_t v___x_428_; 
v___x_428_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_398_, v_fst_413_);
v___y_419_ = v___x_428_;
goto v___jp_418_;
}
v___jp_418_:
{
if (v___y_419_ == 0)
{
lean_object* v___x_420_; 
lean_inc(v_binderName_396_);
lean_del_object(v___x_416_);
lean_del_object(v___x_411_);
lean_dec_ref(v_e_325_);
v___x_420_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__4(v_binderName_396_, v_binderInfo_399_, v_fst_403_, v_fst_413_, v_snd_414_, v_a_328_, v_snd_409_);
return v___x_420_;
}
else
{
lean_object* v___x_422_; 
lean_dec(v_fst_413_);
lean_dec(v_fst_403_);
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 0, v_e_325_);
v___x_422_ = v___x_416_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v_e_325_);
lean_ctor_set(v_reuseFailAlloc_426_, 1, v_snd_414_);
v___x_422_ = v_reuseFailAlloc_426_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
lean_object* v___x_424_; 
if (v_isShared_412_ == 0)
{
lean_ctor_set(v___x_411_, 0, v___x_422_);
v___x_424_ = v___x_411_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v___x_422_);
lean_ctor_set(v_reuseFailAlloc_425_, 1, v_snd_409_);
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
}
}
}
case 8:
{
lean_object* v_declName_431_; lean_object* v_type_432_; lean_object* v_value_433_; lean_object* v_body_434_; uint8_t v_nondep_435_; lean_object* v___x_436_; lean_object* v_fst_437_; lean_object* v_snd_438_; lean_object* v_fst_439_; lean_object* v_snd_440_; lean_object* v___x_441_; lean_object* v_fst_442_; lean_object* v_snd_443_; lean_object* v_fst_444_; lean_object* v_snd_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v_fst_449_; lean_object* v_snd_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_473_; 
v_declName_431_ = lean_ctor_get(v_e_325_, 0);
v_type_432_ = lean_ctor_get(v_e_325_, 1);
v_value_433_ = lean_ctor_get(v_e_325_, 2);
v_body_434_ = lean_ctor_get(v_e_325_, 3);
v_nondep_435_ = lean_ctor_get_uint8(v_e_325_, sizeof(void*)*4 + 8);
lean_inc_n(v_offset_326_, 2);
lean_inc_ref(v_type_432_);
v___x_436_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_323_, v_d_324_, v_type_432_, v_offset_326_, v_a_327_, v_a_328_, v_a_329_);
v_fst_437_ = lean_ctor_get(v___x_436_, 0);
lean_inc(v_fst_437_);
v_snd_438_ = lean_ctor_get(v___x_436_, 1);
lean_inc(v_snd_438_);
lean_dec_ref(v___x_436_);
v_fst_439_ = lean_ctor_get(v_fst_437_, 0);
lean_inc(v_fst_439_);
v_snd_440_ = lean_ctor_get(v_fst_437_, 1);
lean_inc(v_snd_440_);
lean_dec(v_fst_437_);
lean_inc_ref(v_value_433_);
v___x_441_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_323_, v_d_324_, v_value_433_, v_offset_326_, v_snd_440_, v_a_328_, v_snd_438_);
v_fst_442_ = lean_ctor_get(v___x_441_, 0);
lean_inc(v_fst_442_);
v_snd_443_ = lean_ctor_get(v___x_441_, 1);
lean_inc(v_snd_443_);
lean_dec_ref(v___x_441_);
v_fst_444_ = lean_ctor_get(v_fst_442_, 0);
lean_inc(v_fst_444_);
v_snd_445_ = lean_ctor_get(v_fst_442_, 1);
lean_inc(v_snd_445_);
lean_dec(v_fst_442_);
v___x_446_ = lean_unsigned_to_nat(1u);
v___x_447_ = lean_nat_add(v_offset_326_, v___x_446_);
lean_dec(v_offset_326_);
lean_inc_ref(v_body_434_);
v___x_448_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_323_, v_d_324_, v_body_434_, v___x_447_, v_snd_445_, v_a_328_, v_snd_443_);
v_fst_449_ = lean_ctor_get(v___x_448_, 0);
v_snd_450_ = lean_ctor_get(v___x_448_, 1);
v_isSharedCheck_473_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_473_ == 0)
{
v___x_452_ = v___x_448_;
v_isShared_453_ = v_isSharedCheck_473_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_snd_450_);
lean_inc(v_fst_449_);
lean_dec(v___x_448_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_473_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v_fst_454_; lean_object* v_snd_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_472_; 
v_fst_454_ = lean_ctor_get(v_fst_449_, 0);
v_snd_455_ = lean_ctor_get(v_fst_449_, 1);
v_isSharedCheck_472_ = !lean_is_exclusive(v_fst_449_);
if (v_isSharedCheck_472_ == 0)
{
v___x_457_ = v_fst_449_;
v_isShared_458_ = v_isSharedCheck_472_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_snd_455_);
lean_inc(v_fst_454_);
lean_dec(v_fst_449_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_472_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
uint8_t v___y_460_; uint8_t v___x_470_; 
v___x_470_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_type_432_, v_fst_439_);
if (v___x_470_ == 0)
{
v___y_460_ = v___x_470_;
goto v___jp_459_;
}
else
{
uint8_t v___x_471_; 
v___x_471_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_value_433_, v_fst_444_);
v___y_460_ = v___x_471_;
goto v___jp_459_;
}
v___jp_459_:
{
if (v___y_460_ == 0)
{
lean_object* v___x_461_; 
lean_inc(v_declName_431_);
lean_del_object(v___x_457_);
lean_del_object(v___x_452_);
lean_dec_ref(v_e_325_);
v___x_461_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5(v_declName_431_, v_fst_439_, v_fst_444_, v_fst_454_, v_nondep_435_, v_snd_455_, v_a_328_, v_snd_450_);
return v___x_461_;
}
else
{
uint8_t v___x_462_; 
v___x_462_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_434_, v_fst_454_);
if (v___x_462_ == 0)
{
lean_object* v___x_463_; 
lean_inc(v_declName_431_);
lean_del_object(v___x_457_);
lean_del_object(v___x_452_);
lean_dec_ref(v_e_325_);
v___x_463_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5(v_declName_431_, v_fst_439_, v_fst_444_, v_fst_454_, v_nondep_435_, v_snd_455_, v_a_328_, v_snd_450_);
return v___x_463_;
}
else
{
lean_object* v___x_465_; 
lean_dec(v_fst_454_);
lean_dec(v_fst_444_);
lean_dec(v_fst_439_);
if (v_isShared_458_ == 0)
{
lean_ctor_set(v___x_457_, 0, v_e_325_);
v___x_465_ = v___x_457_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_e_325_);
lean_ctor_set(v_reuseFailAlloc_469_, 1, v_snd_455_);
v___x_465_ = v_reuseFailAlloc_469_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
lean_object* v___x_467_; 
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 0, v___x_465_);
v___x_467_ = v___x_452_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v___x_465_);
lean_ctor_set(v_reuseFailAlloc_468_, 1, v_snd_450_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
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
lean_object* v_data_474_; lean_object* v_expr_475_; lean_object* v___x_476_; lean_object* v_fst_477_; lean_object* v_snd_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_496_; 
v_data_474_ = lean_ctor_get(v_e_325_, 0);
v_expr_475_ = lean_ctor_get(v_e_325_, 1);
lean_inc_ref(v_expr_475_);
v___x_476_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_323_, v_d_324_, v_expr_475_, v_offset_326_, v_a_327_, v_a_328_, v_a_329_);
v_fst_477_ = lean_ctor_get(v___x_476_, 0);
v_snd_478_ = lean_ctor_get(v___x_476_, 1);
v_isSharedCheck_496_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_496_ == 0)
{
v___x_480_ = v___x_476_;
v_isShared_481_ = v_isSharedCheck_496_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_snd_478_);
lean_inc(v_fst_477_);
lean_dec(v___x_476_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_496_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v_fst_482_; lean_object* v_snd_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_495_; 
v_fst_482_ = lean_ctor_get(v_fst_477_, 0);
v_snd_483_ = lean_ctor_get(v_fst_477_, 1);
v_isSharedCheck_495_ = !lean_is_exclusive(v_fst_477_);
if (v_isSharedCheck_495_ == 0)
{
v___x_485_ = v_fst_477_;
v_isShared_486_ = v_isSharedCheck_495_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_snd_483_);
lean_inc(v_fst_482_);
lean_dec(v_fst_477_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_495_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
uint8_t v___x_487_; 
v___x_487_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_expr_475_, v_fst_482_);
if (v___x_487_ == 0)
{
lean_object* v___x_488_; 
lean_inc(v_data_474_);
lean_del_object(v___x_485_);
lean_del_object(v___x_480_);
lean_dec_ref(v_e_325_);
v___x_488_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__6(v_data_474_, v_fst_482_, v_snd_483_, v_a_328_, v_snd_478_);
return v___x_488_;
}
else
{
lean_object* v___x_490_; 
lean_dec(v_fst_482_);
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 0, v_e_325_);
v___x_490_ = v___x_485_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_e_325_);
lean_ctor_set(v_reuseFailAlloc_494_, 1, v_snd_483_);
v___x_490_ = v_reuseFailAlloc_494_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
lean_object* v___x_492_; 
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 0, v___x_490_);
v___x_492_ = v___x_480_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v___x_490_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v_snd_478_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
}
}
}
}
case 11:
{
lean_object* v_typeName_497_; lean_object* v_idx_498_; lean_object* v_struct_499_; lean_object* v___x_500_; lean_object* v_fst_501_; lean_object* v_snd_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_520_; 
v_typeName_497_ = lean_ctor_get(v_e_325_, 0);
v_idx_498_ = lean_ctor_get(v_e_325_, 1);
v_struct_499_ = lean_ctor_get(v_e_325_, 2);
lean_inc_ref(v_struct_499_);
v___x_500_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_323_, v_d_324_, v_struct_499_, v_offset_326_, v_a_327_, v_a_328_, v_a_329_);
v_fst_501_ = lean_ctor_get(v___x_500_, 0);
v_snd_502_ = lean_ctor_get(v___x_500_, 1);
v_isSharedCheck_520_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_520_ == 0)
{
v___x_504_ = v___x_500_;
v_isShared_505_ = v_isSharedCheck_520_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_snd_502_);
lean_inc(v_fst_501_);
lean_dec(v___x_500_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_520_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v_fst_506_; lean_object* v_snd_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_519_; 
v_fst_506_ = lean_ctor_get(v_fst_501_, 0);
v_snd_507_ = lean_ctor_get(v_fst_501_, 1);
v_isSharedCheck_519_ = !lean_is_exclusive(v_fst_501_);
if (v_isSharedCheck_519_ == 0)
{
v___x_509_ = v_fst_501_;
v_isShared_510_ = v_isSharedCheck_519_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_snd_507_);
lean_inc(v_fst_506_);
lean_dec(v_fst_501_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_519_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
uint8_t v___x_511_; 
v___x_511_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_499_, v_fst_506_);
if (v___x_511_ == 0)
{
lean_object* v___x_512_; 
lean_inc(v_idx_498_);
lean_inc(v_typeName_497_);
lean_del_object(v___x_509_);
lean_del_object(v___x_504_);
lean_dec_ref(v_e_325_);
v___x_512_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__7(v_typeName_497_, v_idx_498_, v_fst_506_, v_snd_507_, v_a_328_, v_snd_502_);
return v___x_512_;
}
else
{
lean_object* v___x_514_; 
lean_dec(v_fst_506_);
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 0, v_e_325_);
v___x_514_ = v___x_509_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_e_325_);
lean_ctor_set(v_reuseFailAlloc_518_, 1, v_snd_507_);
v___x_514_ = v_reuseFailAlloc_518_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
lean_object* v___x_516_; 
if (v_isShared_505_ == 0)
{
lean_ctor_set(v___x_504_, 0, v___x_514_);
v___x_516_ = v___x_504_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_514_);
lean_ctor_set(v_reuseFailAlloc_517_, 1, v_snd_502_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_521_; lean_object* v___x_522_; 
lean_dec(v_offset_326_);
lean_dec_ref(v_e_325_);
v___x_521_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3);
v___x_522_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8(v___x_521_, v_a_327_, v_a_328_, v_a_329_);
return v___x_522_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(lean_object* v_s_523_, lean_object* v_d_524_, lean_object* v_e_525_, lean_object* v_offset_526_, lean_object* v_a_527_, uint8_t v_a_528_, lean_object* v_a_529_){
_start:
{
lean_object* v_key_530_; lean_object* v_snd_532_; lean_object* v___x_545_; 
lean_inc(v_offset_526_);
lean_inc_ref(v_e_525_);
v_key_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_530_, 0, v_e_525_);
lean_ctor_set(v_key_530_, 1, v_offset_526_);
v___x_545_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___redArg(v_a_527_, v_key_530_);
if (lean_obj_tag(v___x_545_) == 1)
{
lean_object* v_val_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
lean_dec_ref(v_key_530_);
lean_dec(v_offset_526_);
lean_dec_ref(v_e_525_);
v_val_546_ = lean_ctor_get(v___x_545_, 0);
lean_inc(v_val_546_);
lean_dec_ref(v___x_545_);
v___x_547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_547_, 0, v_val_546_);
lean_ctor_set(v___x_547_, 1, v_a_527_);
v___x_548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
lean_ctor_set(v___x_548_, 1, v_a_529_);
return v___x_548_;
}
else
{
lean_object* v_s_u2081_549_; lean_object* v___x_550_; uint8_t v___x_551_; 
lean_dec(v___x_545_);
v_s_u2081_549_ = lean_nat_add(v_s_523_, v_offset_526_);
v___x_550_ = l_Lean_Expr_looseBVarRange(v_e_525_);
v___x_551_ = lean_nat_dec_le(v___x_550_, v_s_u2081_549_);
lean_dec(v___x_550_);
if (v___x_551_ == 0)
{
if (lean_obj_tag(v_e_525_) == 0)
{
lean_object* v_deBruijnIndex_552_; uint8_t v___x_553_; 
v_deBruijnIndex_552_ = lean_ctor_get(v_e_525_, 0);
v___x_553_ = lean_nat_dec_le(v_s_u2081_549_, v_deBruijnIndex_552_);
lean_dec(v_s_u2081_549_);
if (v___x_553_ == 0)
{
v_snd_532_ = v_a_529_;
goto v___jp_531_;
}
else
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v_fst_556_; lean_object* v_snd_557_; lean_object* v___x_558_; 
lean_inc(v_deBruijnIndex_552_);
lean_dec_ref(v_e_525_);
lean_dec(v_offset_526_);
v___x_554_ = lean_nat_sub(v_deBruijnIndex_552_, v_d_524_);
lean_dec(v_deBruijnIndex_552_);
v___x_555_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0___redArg(v___x_554_, v_a_529_);
v_fst_556_ = lean_ctor_get(v___x_555_, 0);
lean_inc(v_fst_556_);
v_snd_557_ = lean_ctor_get(v___x_555_, 1);
lean_inc(v_snd_557_);
lean_dec_ref(v___x_555_);
v___x_558_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_530_, v_fst_556_, v_a_527_, v_a_528_, v_snd_557_);
return v___x_558_;
}
}
else
{
lean_dec(v_s_u2081_549_);
v_snd_532_ = v_a_529_;
goto v___jp_531_;
}
}
else
{
lean_object* v___x_559_; 
lean_dec(v_s_u2081_549_);
lean_dec(v_offset_526_);
v___x_559_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_530_, v_e_525_, v_a_527_, v_a_528_, v_a_529_);
return v___x_559_;
}
}
v___jp_531_:
{
switch(lean_obj_tag(v_e_525_))
{
case 9:
{
lean_object* v___x_533_; 
lean_dec(v_offset_526_);
v___x_533_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_530_, v_e_525_, v_a_527_, v_a_528_, v_snd_532_);
return v___x_533_;
}
case 2:
{
lean_object* v___x_534_; 
lean_dec(v_offset_526_);
v___x_534_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_530_, v_e_525_, v_a_527_, v_a_528_, v_snd_532_);
return v___x_534_;
}
case 0:
{
lean_object* v___x_535_; 
lean_dec(v_offset_526_);
v___x_535_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_530_, v_e_525_, v_a_527_, v_a_528_, v_snd_532_);
return v___x_535_;
}
case 1:
{
lean_object* v___x_536_; 
lean_dec(v_offset_526_);
v___x_536_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_530_, v_e_525_, v_a_527_, v_a_528_, v_snd_532_);
return v___x_536_;
}
case 4:
{
lean_object* v___x_537_; 
lean_dec(v_offset_526_);
v___x_537_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_530_, v_e_525_, v_a_527_, v_a_528_, v_snd_532_);
return v___x_537_;
}
case 3:
{
lean_object* v___x_538_; 
lean_dec(v_offset_526_);
v___x_538_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_530_, v_e_525_, v_a_527_, v_a_528_, v_snd_532_);
return v___x_538_;
}
default: 
{
lean_object* v___x_539_; lean_object* v_fst_540_; lean_object* v_snd_541_; lean_object* v_fst_542_; lean_object* v_snd_543_; lean_object* v___x_544_; 
v___x_539_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1(v_s_523_, v_d_524_, v_e_525_, v_offset_526_, v_a_527_, v_a_528_, v_snd_532_);
v_fst_540_ = lean_ctor_get(v___x_539_, 0);
lean_inc(v_fst_540_);
v_snd_541_ = lean_ctor_get(v___x_539_, 1);
lean_inc(v_snd_541_);
lean_dec_ref(v___x_539_);
v_fst_542_ = lean_ctor_get(v_fst_540_, 0);
lean_inc(v_fst_542_);
v_snd_543_ = lean_ctor_get(v_fst_540_, 1);
lean_inc(v_snd_543_);
lean_dec(v_fst_540_);
v___x_544_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_530_, v_fst_542_, v_snd_543_, v_a_528_, v_snd_541_);
return v___x_544_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1___boxed(lean_object* v_s_560_, lean_object* v_d_561_, lean_object* v_e_562_, lean_object* v_offset_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_){
_start:
{
uint8_t v_a_boxed_567_; lean_object* v_res_568_; 
v_a_boxed_567_ = lean_unbox(v_a_565_);
v_res_568_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_560_, v_d_561_, v_e_562_, v_offset_563_, v_a_564_, v_a_boxed_567_, v_a_566_);
lean_dec(v_d_561_);
lean_dec(v_s_560_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___boxed(lean_object* v_s_569_, lean_object* v_d_570_, lean_object* v_e_571_, lean_object* v_offset_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_){
_start:
{
uint8_t v_a_boxed_576_; lean_object* v_res_577_; 
v_a_boxed_576_ = lean_unbox(v_a_574_);
v_res_577_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1(v_s_569_, v_d_570_, v_e_571_, v_offset_572_, v_a_573_, v_a_boxed_576_, v_a_575_);
lean_dec(v_d_570_);
lean_dec(v_s_569_);
return v_res_577_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__0(void){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_578_ = lean_box(0);
v___x_579_ = lean_unsigned_to_nat(16u);
v___x_580_ = lean_mk_array(v___x_579_, v___x_578_);
return v___x_580_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1(void){
_start:
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_581_ = lean_obj_once(&l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__0, &l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__0_once, _init_l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__0);
v___x_582_ = lean_unsigned_to_nat(0u);
v___x_583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_583_, 0, v___x_582_);
lean_ctor_set(v___x_583_, 1, v___x_581_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_lowerLooseBVarsS_x27(lean_object* v_e_584_, lean_object* v_s_585_, lean_object* v_d_586_, uint8_t v_a_587_, lean_object* v_a_588_){
_start:
{
lean_object* v___x_589_; uint8_t v___x_590_; 
v___x_589_ = l_Lean_Expr_looseBVarRange(v_e_584_);
v___x_590_ = lean_nat_dec_le(v___x_589_, v_s_585_);
lean_dec(v___x_589_);
if (v___x_590_ == 0)
{
lean_object* v___x_591_; lean_object* v_snd_593_; 
v___x_591_ = lean_unsigned_to_nat(0u);
if (lean_obj_tag(v_e_584_) == 0)
{
lean_object* v_deBruijnIndex_613_; uint8_t v___x_614_; 
v_deBruijnIndex_613_ = lean_ctor_get(v_e_584_, 0);
v___x_614_ = lean_nat_dec_le(v_s_585_, v_deBruijnIndex_613_);
if (v___x_614_ == 0)
{
v_snd_593_ = v_a_588_;
goto v___jp_592_;
}
else
{
lean_object* v___x_615_; lean_object* v___x_616_; 
lean_inc(v_deBruijnIndex_613_);
lean_dec_ref(v_e_584_);
v___x_615_ = lean_nat_sub(v_deBruijnIndex_613_, v_d_586_);
lean_dec(v_deBruijnIndex_613_);
v___x_616_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0___redArg(v___x_615_, v_a_588_);
return v___x_616_;
}
}
else
{
v_snd_593_ = v_a_588_;
goto v___jp_592_;
}
v___jp_592_:
{
switch(lean_obj_tag(v_e_584_))
{
case 9:
{
lean_object* v___x_594_; 
v___x_594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_594_, 0, v_e_584_);
lean_ctor_set(v___x_594_, 1, v_snd_593_);
return v___x_594_;
}
case 2:
{
lean_object* v___x_595_; 
v___x_595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_595_, 0, v_e_584_);
lean_ctor_set(v___x_595_, 1, v_snd_593_);
return v___x_595_;
}
case 0:
{
lean_object* v___x_596_; 
v___x_596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_596_, 0, v_e_584_);
lean_ctor_set(v___x_596_, 1, v_snd_593_);
return v___x_596_;
}
case 1:
{
lean_object* v___x_597_; 
v___x_597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_597_, 0, v_e_584_);
lean_ctor_set(v___x_597_, 1, v_snd_593_);
return v___x_597_;
}
case 4:
{
lean_object* v___x_598_; 
v___x_598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_598_, 0, v_e_584_);
lean_ctor_set(v___x_598_, 1, v_snd_593_);
return v___x_598_;
}
case 3:
{
lean_object* v___x_599_; 
v___x_599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_599_, 0, v_e_584_);
lean_ctor_set(v___x_599_, 1, v_snd_593_);
return v___x_599_;
}
default: 
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v_fst_602_; lean_object* v_snd_603_; lean_object* v_fst_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_611_; 
v___x_600_ = lean_obj_once(&l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1, &l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1_once, _init_l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1);
v___x_601_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1(v_s_585_, v_d_586_, v_e_584_, v___x_591_, v___x_600_, v_a_587_, v_snd_593_);
v_fst_602_ = lean_ctor_get(v___x_601_, 0);
lean_inc(v_fst_602_);
v_snd_603_ = lean_ctor_get(v___x_601_, 1);
lean_inc(v_snd_603_);
lean_dec_ref(v___x_601_);
v_fst_604_ = lean_ctor_get(v_fst_602_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v_fst_602_);
if (v_isSharedCheck_611_ == 0)
{
lean_object* v_unused_612_; 
v_unused_612_ = lean_ctor_get(v_fst_602_, 1);
lean_dec(v_unused_612_);
v___x_606_ = v_fst_602_;
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_fst_604_);
lean_dec(v_fst_602_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_609_; 
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 1, v_snd_603_);
v___x_609_ = v___x_606_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_fst_604_);
lean_ctor_set(v_reuseFailAlloc_610_, 1, v_snd_603_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
}
}
}
else
{
lean_object* v___x_617_; 
v___x_617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_617_, 0, v_e_584_);
lean_ctor_set(v___x_617_, 1, v_a_588_);
return v___x_617_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_lowerLooseBVarsS_x27___boxed(lean_object* v_e_618_, lean_object* v_s_619_, lean_object* v_d_620_, lean_object* v_a_621_, lean_object* v_a_622_){
_start:
{
uint8_t v_a_boxed_623_; lean_object* v_res_624_; 
v_a_boxed_623_ = lean_unbox(v_a_621_);
v_res_624_ = l_Lean_Meta_Sym_lowerLooseBVarsS_x27(v_e_618_, v_s_619_, v_d_620_, v_a_boxed_623_, v_a_622_);
lean_dec(v_d_620_);
lean_dec(v_s_619_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_625_, lean_object* v_m_626_, lean_object* v_a_627_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___redArg(v_m_626_, v_a_627_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_629_, lean_object* v_m_630_, lean_object* v_a_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2(v_00_u03b2_629_, v_m_630_, v_a_631_);
lean_dec_ref(v_a_631_);
lean_dec_ref(v_m_630_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10(lean_object* v_00_u03b2_633_, lean_object* v_a_634_, lean_object* v_x_635_){
_start:
{
lean_object* v___x_636_; 
v___x_636_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10___redArg(v_a_634_, v_x_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10___boxed(lean_object* v_00_u03b2_637_, lean_object* v_a_638_, lean_object* v_x_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10(v_00_u03b2_637_, v_a_638_, v_x_639_);
lean_dec(v_x_639_);
lean_dec_ref(v_a_638_);
return v_res_640_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__0(void){
_start:
{
lean_object* v___x_641_; 
v___x_641_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_641_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__1(void){
_start:
{
lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_642_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__0);
v___x_643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0(lean_object* v_00_u03b2_644_){
_start:
{
lean_object* v___x_645_; 
v___x_645_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__1);
return v___x_645_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_lowerLooseBVarsS___redArg___closed__0(void){
_start:
{
lean_object* v___x_646_; 
v___x_646_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0(lean_box(0));
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_lowerLooseBVarsS___redArg(lean_object* v_e_647_, lean_object* v_s_648_, lean_object* v_d_649_, lean_object* v_a_650_){
_start:
{
lean_object* v___x_652_; lean_object* v_share_653_; lean_object* v_maxFVar_654_; lean_object* v_proofInstInfo_655_; lean_object* v_inferType_656_; lean_object* v_getLevel_657_; lean_object* v_congrInfo_658_; lean_object* v_defEqI_659_; lean_object* v_extensions_660_; lean_object* v_issues_661_; lean_object* v_canon_662_; uint8_t v_debug_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_698_; 
v___x_652_ = lean_st_ref_take(v_a_650_);
v_share_653_ = lean_ctor_get(v___x_652_, 0);
v_maxFVar_654_ = lean_ctor_get(v___x_652_, 1);
v_proofInstInfo_655_ = lean_ctor_get(v___x_652_, 2);
v_inferType_656_ = lean_ctor_get(v___x_652_, 3);
v_getLevel_657_ = lean_ctor_get(v___x_652_, 4);
v_congrInfo_658_ = lean_ctor_get(v___x_652_, 5);
v_defEqI_659_ = lean_ctor_get(v___x_652_, 6);
v_extensions_660_ = lean_ctor_get(v___x_652_, 7);
v_issues_661_ = lean_ctor_get(v___x_652_, 8);
v_canon_662_ = lean_ctor_get(v___x_652_, 9);
v_debug_663_ = lean_ctor_get_uint8(v___x_652_, sizeof(void*)*10);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_698_ == 0)
{
v___x_665_ = v___x_652_;
v_isShared_666_ = v_isSharedCheck_698_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_canon_662_);
lean_inc(v_issues_661_);
lean_inc(v_extensions_660_);
lean_inc(v_defEqI_659_);
lean_inc(v_congrInfo_658_);
lean_inc(v_getLevel_657_);
lean_inc(v_inferType_656_);
lean_inc(v_proofInstInfo_655_);
lean_inc(v_maxFVar_654_);
lean_inc(v_share_653_);
lean_dec(v___x_652_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_698_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_667_; lean_object* v___x_669_; 
v___x_667_ = lean_obj_once(&l_Lean_Meta_Sym_lowerLooseBVarsS___redArg___closed__0, &l_Lean_Meta_Sym_lowerLooseBVarsS___redArg___closed__0_once, _init_l_Lean_Meta_Sym_lowerLooseBVarsS___redArg___closed__0);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 0, v___x_667_);
v___x_669_ = v___x_665_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v___x_667_);
lean_ctor_set(v_reuseFailAlloc_697_, 1, v_maxFVar_654_);
lean_ctor_set(v_reuseFailAlloc_697_, 2, v_proofInstInfo_655_);
lean_ctor_set(v_reuseFailAlloc_697_, 3, v_inferType_656_);
lean_ctor_set(v_reuseFailAlloc_697_, 4, v_getLevel_657_);
lean_ctor_set(v_reuseFailAlloc_697_, 5, v_congrInfo_658_);
lean_ctor_set(v_reuseFailAlloc_697_, 6, v_defEqI_659_);
lean_ctor_set(v_reuseFailAlloc_697_, 7, v_extensions_660_);
lean_ctor_set(v_reuseFailAlloc_697_, 8, v_issues_661_);
lean_ctor_set(v_reuseFailAlloc_697_, 9, v_canon_662_);
lean_ctor_set_uint8(v_reuseFailAlloc_697_, sizeof(void*)*10, v_debug_663_);
v___x_669_ = v_reuseFailAlloc_697_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
lean_object* v___x_670_; lean_object* v___x_671_; uint8_t v_debug_672_; lean_object* v___x_673_; lean_object* v_fst_674_; lean_object* v_snd_675_; lean_object* v___x_676_; lean_object* v_maxFVar_677_; lean_object* v_proofInstInfo_678_; lean_object* v_inferType_679_; lean_object* v_getLevel_680_; lean_object* v_congrInfo_681_; lean_object* v_defEqI_682_; lean_object* v_extensions_683_; lean_object* v_issues_684_; lean_object* v_canon_685_; uint8_t v_debug_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_695_; 
v___x_670_ = lean_st_ref_set(v_a_650_, v___x_669_);
v___x_671_ = lean_st_ref_get(v_a_650_);
v_debug_672_ = lean_ctor_get_uint8(v___x_671_, sizeof(void*)*10);
lean_dec(v___x_671_);
v___x_673_ = l_Lean_Meta_Sym_lowerLooseBVarsS_x27(v_e_647_, v_s_648_, v_d_649_, v_debug_672_, v_share_653_);
v_fst_674_ = lean_ctor_get(v___x_673_, 0);
lean_inc(v_fst_674_);
v_snd_675_ = lean_ctor_get(v___x_673_, 1);
lean_inc(v_snd_675_);
lean_dec_ref(v___x_673_);
v___x_676_ = lean_st_ref_take(v_a_650_);
v_maxFVar_677_ = lean_ctor_get(v___x_676_, 1);
v_proofInstInfo_678_ = lean_ctor_get(v___x_676_, 2);
v_inferType_679_ = lean_ctor_get(v___x_676_, 3);
v_getLevel_680_ = lean_ctor_get(v___x_676_, 4);
v_congrInfo_681_ = lean_ctor_get(v___x_676_, 5);
v_defEqI_682_ = lean_ctor_get(v___x_676_, 6);
v_extensions_683_ = lean_ctor_get(v___x_676_, 7);
v_issues_684_ = lean_ctor_get(v___x_676_, 8);
v_canon_685_ = lean_ctor_get(v___x_676_, 9);
v_debug_686_ = lean_ctor_get_uint8(v___x_676_, sizeof(void*)*10);
v_isSharedCheck_695_ = !lean_is_exclusive(v___x_676_);
if (v_isSharedCheck_695_ == 0)
{
lean_object* v_unused_696_; 
v_unused_696_ = lean_ctor_get(v___x_676_, 0);
lean_dec(v_unused_696_);
v___x_688_ = v___x_676_;
v_isShared_689_ = v_isSharedCheck_695_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_canon_685_);
lean_inc(v_issues_684_);
lean_inc(v_extensions_683_);
lean_inc(v_defEqI_682_);
lean_inc(v_congrInfo_681_);
lean_inc(v_getLevel_680_);
lean_inc(v_inferType_679_);
lean_inc(v_proofInstInfo_678_);
lean_inc(v_maxFVar_677_);
lean_dec(v___x_676_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_695_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v___x_691_; 
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 0, v_snd_675_);
v___x_691_ = v___x_688_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_snd_675_);
lean_ctor_set(v_reuseFailAlloc_694_, 1, v_maxFVar_677_);
lean_ctor_set(v_reuseFailAlloc_694_, 2, v_proofInstInfo_678_);
lean_ctor_set(v_reuseFailAlloc_694_, 3, v_inferType_679_);
lean_ctor_set(v_reuseFailAlloc_694_, 4, v_getLevel_680_);
lean_ctor_set(v_reuseFailAlloc_694_, 5, v_congrInfo_681_);
lean_ctor_set(v_reuseFailAlloc_694_, 6, v_defEqI_682_);
lean_ctor_set(v_reuseFailAlloc_694_, 7, v_extensions_683_);
lean_ctor_set(v_reuseFailAlloc_694_, 8, v_issues_684_);
lean_ctor_set(v_reuseFailAlloc_694_, 9, v_canon_685_);
lean_ctor_set_uint8(v_reuseFailAlloc_694_, sizeof(void*)*10, v_debug_686_);
v___x_691_ = v_reuseFailAlloc_694_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_692_ = lean_st_ref_set(v_a_650_, v___x_691_);
v___x_693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_693_, 0, v_fst_674_);
return v___x_693_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_lowerLooseBVarsS___redArg___boxed(lean_object* v_e_699_, lean_object* v_s_700_, lean_object* v_d_701_, lean_object* v_a_702_, lean_object* v_a_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_Lean_Meta_Sym_lowerLooseBVarsS___redArg(v_e_699_, v_s_700_, v_d_701_, v_a_702_);
lean_dec(v_a_702_);
lean_dec(v_d_701_);
lean_dec(v_s_700_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_lowerLooseBVarsS(lean_object* v_e_705_, lean_object* v_s_706_, lean_object* v_d_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_){
_start:
{
lean_object* v___x_715_; 
v___x_715_ = l_Lean_Meta_Sym_lowerLooseBVarsS___redArg(v_e_705_, v_s_706_, v_d_707_, v_a_709_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_lowerLooseBVarsS___boxed(lean_object* v_e_716_, lean_object* v_s_717_, lean_object* v_d_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_){
_start:
{
lean_object* v_res_726_; 
v_res_726_ = l_Lean_Meta_Sym_lowerLooseBVarsS(v_e_716_, v_s_717_, v_d_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_);
lean_dec(v_a_724_);
lean_dec_ref(v_a_723_);
lean_dec(v_a_722_);
lean_dec_ref(v_a_721_);
lean_dec(v_a_720_);
lean_dec_ref(v_a_719_);
lean_dec(v_d_718_);
lean_dec(v_s_717_);
return v_res_726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0(lean_object* v_s_727_, lean_object* v_d_728_, lean_object* v_e_729_, lean_object* v_offset_730_, lean_object* v_a_731_, uint8_t v_a_732_, lean_object* v_a_733_){
_start:
{
switch(lean_obj_tag(v_e_729_))
{
case 5:
{
lean_object* v_fn_734_; lean_object* v_arg_735_; lean_object* v___x_736_; lean_object* v_fst_737_; lean_object* v_snd_738_; lean_object* v_fst_739_; lean_object* v_snd_740_; lean_object* v___x_741_; lean_object* v_fst_742_; lean_object* v_snd_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_764_; 
v_fn_734_ = lean_ctor_get(v_e_729_, 0);
v_arg_735_ = lean_ctor_get(v_e_729_, 1);
lean_inc(v_offset_730_);
lean_inc_ref(v_fn_734_);
v___x_736_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_727_, v_d_728_, v_fn_734_, v_offset_730_, v_a_731_, v_a_732_, v_a_733_);
v_fst_737_ = lean_ctor_get(v___x_736_, 0);
lean_inc(v_fst_737_);
v_snd_738_ = lean_ctor_get(v___x_736_, 1);
lean_inc(v_snd_738_);
lean_dec_ref(v___x_736_);
v_fst_739_ = lean_ctor_get(v_fst_737_, 0);
lean_inc(v_fst_739_);
v_snd_740_ = lean_ctor_get(v_fst_737_, 1);
lean_inc(v_snd_740_);
lean_dec(v_fst_737_);
lean_inc_ref(v_arg_735_);
v___x_741_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_727_, v_d_728_, v_arg_735_, v_offset_730_, v_snd_740_, v_a_732_, v_snd_738_);
v_fst_742_ = lean_ctor_get(v___x_741_, 0);
v_snd_743_ = lean_ctor_get(v___x_741_, 1);
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_741_);
if (v_isSharedCheck_764_ == 0)
{
v___x_745_ = v___x_741_;
v_isShared_746_ = v_isSharedCheck_764_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_snd_743_);
lean_inc(v_fst_742_);
lean_dec(v___x_741_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_764_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v_fst_747_; lean_object* v_snd_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_763_; 
v_fst_747_ = lean_ctor_get(v_fst_742_, 0);
v_snd_748_ = lean_ctor_get(v_fst_742_, 1);
v_isSharedCheck_763_ = !lean_is_exclusive(v_fst_742_);
if (v_isSharedCheck_763_ == 0)
{
v___x_750_ = v_fst_742_;
v_isShared_751_ = v_isSharedCheck_763_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_snd_748_);
lean_inc(v_fst_747_);
lean_dec(v_fst_742_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_763_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
uint8_t v___y_753_; uint8_t v___x_761_; 
v___x_761_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_734_, v_fst_739_);
if (v___x_761_ == 0)
{
v___y_753_ = v___x_761_;
goto v___jp_752_;
}
else
{
uint8_t v___x_762_; 
v___x_762_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_735_, v_fst_747_);
v___y_753_ = v___x_762_;
goto v___jp_752_;
}
v___jp_752_:
{
if (v___y_753_ == 0)
{
lean_object* v___x_754_; 
lean_del_object(v___x_750_);
lean_del_object(v___x_745_);
lean_dec_ref(v_e_729_);
v___x_754_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__2(v_fst_739_, v_fst_747_, v_snd_748_, v_a_732_, v_snd_743_);
return v___x_754_;
}
else
{
lean_object* v___x_756_; 
lean_dec(v_fst_747_);
lean_dec(v_fst_739_);
if (v_isShared_751_ == 0)
{
lean_ctor_set(v___x_750_, 0, v_e_729_);
v___x_756_ = v___x_750_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_e_729_);
lean_ctor_set(v_reuseFailAlloc_760_, 1, v_snd_748_);
v___x_756_ = v_reuseFailAlloc_760_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
lean_object* v___x_758_; 
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 0, v___x_756_);
v___x_758_ = v___x_745_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v___x_756_);
lean_ctor_set(v_reuseFailAlloc_759_, 1, v_snd_743_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
}
}
}
}
case 6:
{
lean_object* v_binderName_765_; lean_object* v_binderType_766_; lean_object* v_body_767_; uint8_t v_binderInfo_768_; lean_object* v___x_769_; lean_object* v_fst_770_; lean_object* v_snd_771_; lean_object* v_fst_772_; lean_object* v_snd_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v_fst_777_; lean_object* v_snd_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_799_; 
v_binderName_765_ = lean_ctor_get(v_e_729_, 0);
v_binderType_766_ = lean_ctor_get(v_e_729_, 1);
v_body_767_ = lean_ctor_get(v_e_729_, 2);
v_binderInfo_768_ = lean_ctor_get_uint8(v_e_729_, sizeof(void*)*3 + 8);
lean_inc(v_offset_730_);
lean_inc_ref(v_binderType_766_);
v___x_769_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_727_, v_d_728_, v_binderType_766_, v_offset_730_, v_a_731_, v_a_732_, v_a_733_);
v_fst_770_ = lean_ctor_get(v___x_769_, 0);
lean_inc(v_fst_770_);
v_snd_771_ = lean_ctor_get(v___x_769_, 1);
lean_inc(v_snd_771_);
lean_dec_ref(v___x_769_);
v_fst_772_ = lean_ctor_get(v_fst_770_, 0);
lean_inc(v_fst_772_);
v_snd_773_ = lean_ctor_get(v_fst_770_, 1);
lean_inc(v_snd_773_);
lean_dec(v_fst_770_);
v___x_774_ = lean_unsigned_to_nat(1u);
v___x_775_ = lean_nat_add(v_offset_730_, v___x_774_);
lean_dec(v_offset_730_);
lean_inc_ref(v_body_767_);
v___x_776_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_727_, v_d_728_, v_body_767_, v___x_775_, v_snd_773_, v_a_732_, v_snd_771_);
v_fst_777_ = lean_ctor_get(v___x_776_, 0);
v_snd_778_ = lean_ctor_get(v___x_776_, 1);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_776_);
if (v_isSharedCheck_799_ == 0)
{
v___x_780_ = v___x_776_;
v_isShared_781_ = v_isSharedCheck_799_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_snd_778_);
lean_inc(v_fst_777_);
lean_dec(v___x_776_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_799_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v_fst_782_; lean_object* v_snd_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_798_; 
v_fst_782_ = lean_ctor_get(v_fst_777_, 0);
v_snd_783_ = lean_ctor_get(v_fst_777_, 1);
v_isSharedCheck_798_ = !lean_is_exclusive(v_fst_777_);
if (v_isSharedCheck_798_ == 0)
{
v___x_785_ = v_fst_777_;
v_isShared_786_ = v_isSharedCheck_798_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_snd_783_);
lean_inc(v_fst_782_);
lean_dec(v_fst_777_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_798_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
uint8_t v___y_788_; uint8_t v___x_796_; 
v___x_796_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_766_, v_fst_772_);
if (v___x_796_ == 0)
{
v___y_788_ = v___x_796_;
goto v___jp_787_;
}
else
{
uint8_t v___x_797_; 
v___x_797_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_767_, v_fst_782_);
v___y_788_ = v___x_797_;
goto v___jp_787_;
}
v___jp_787_:
{
if (v___y_788_ == 0)
{
lean_object* v___x_789_; 
lean_inc(v_binderName_765_);
lean_del_object(v___x_785_);
lean_del_object(v___x_780_);
lean_dec_ref(v_e_729_);
v___x_789_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__3(v_binderName_765_, v_binderInfo_768_, v_fst_772_, v_fst_782_, v_snd_783_, v_a_732_, v_snd_778_);
return v___x_789_;
}
else
{
lean_object* v___x_791_; 
lean_dec(v_fst_782_);
lean_dec(v_fst_772_);
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 0, v_e_729_);
v___x_791_ = v___x_785_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_e_729_);
lean_ctor_set(v_reuseFailAlloc_795_, 1, v_snd_783_);
v___x_791_ = v_reuseFailAlloc_795_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
lean_object* v___x_793_; 
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 0, v___x_791_);
v___x_793_ = v___x_780_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v___x_791_);
lean_ctor_set(v_reuseFailAlloc_794_, 1, v_snd_778_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
}
}
}
}
case 7:
{
lean_object* v_binderName_800_; lean_object* v_binderType_801_; lean_object* v_body_802_; uint8_t v_binderInfo_803_; lean_object* v___x_804_; lean_object* v_fst_805_; lean_object* v_snd_806_; lean_object* v_fst_807_; lean_object* v_snd_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v_fst_812_; lean_object* v_snd_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_834_; 
v_binderName_800_ = lean_ctor_get(v_e_729_, 0);
v_binderType_801_ = lean_ctor_get(v_e_729_, 1);
v_body_802_ = lean_ctor_get(v_e_729_, 2);
v_binderInfo_803_ = lean_ctor_get_uint8(v_e_729_, sizeof(void*)*3 + 8);
lean_inc(v_offset_730_);
lean_inc_ref(v_binderType_801_);
v___x_804_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_727_, v_d_728_, v_binderType_801_, v_offset_730_, v_a_731_, v_a_732_, v_a_733_);
v_fst_805_ = lean_ctor_get(v___x_804_, 0);
lean_inc(v_fst_805_);
v_snd_806_ = lean_ctor_get(v___x_804_, 1);
lean_inc(v_snd_806_);
lean_dec_ref(v___x_804_);
v_fst_807_ = lean_ctor_get(v_fst_805_, 0);
lean_inc(v_fst_807_);
v_snd_808_ = lean_ctor_get(v_fst_805_, 1);
lean_inc(v_snd_808_);
lean_dec(v_fst_805_);
v___x_809_ = lean_unsigned_to_nat(1u);
v___x_810_ = lean_nat_add(v_offset_730_, v___x_809_);
lean_dec(v_offset_730_);
lean_inc_ref(v_body_802_);
v___x_811_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_727_, v_d_728_, v_body_802_, v___x_810_, v_snd_808_, v_a_732_, v_snd_806_);
v_fst_812_ = lean_ctor_get(v___x_811_, 0);
v_snd_813_ = lean_ctor_get(v___x_811_, 1);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_834_ == 0)
{
v___x_815_ = v___x_811_;
v_isShared_816_ = v_isSharedCheck_834_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_snd_813_);
lean_inc(v_fst_812_);
lean_dec(v___x_811_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_834_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v_fst_817_; lean_object* v_snd_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_833_; 
v_fst_817_ = lean_ctor_get(v_fst_812_, 0);
v_snd_818_ = lean_ctor_get(v_fst_812_, 1);
v_isSharedCheck_833_ = !lean_is_exclusive(v_fst_812_);
if (v_isSharedCheck_833_ == 0)
{
v___x_820_ = v_fst_812_;
v_isShared_821_ = v_isSharedCheck_833_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_snd_818_);
lean_inc(v_fst_817_);
lean_dec(v_fst_812_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_833_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
uint8_t v___y_823_; uint8_t v___x_831_; 
v___x_831_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_801_, v_fst_807_);
if (v___x_831_ == 0)
{
v___y_823_ = v___x_831_;
goto v___jp_822_;
}
else
{
uint8_t v___x_832_; 
v___x_832_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_802_, v_fst_817_);
v___y_823_ = v___x_832_;
goto v___jp_822_;
}
v___jp_822_:
{
if (v___y_823_ == 0)
{
lean_object* v___x_824_; 
lean_inc(v_binderName_800_);
lean_del_object(v___x_820_);
lean_del_object(v___x_815_);
lean_dec_ref(v_e_729_);
v___x_824_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__4(v_binderName_800_, v_binderInfo_803_, v_fst_807_, v_fst_817_, v_snd_818_, v_a_732_, v_snd_813_);
return v___x_824_;
}
else
{
lean_object* v___x_826_; 
lean_dec(v_fst_817_);
lean_dec(v_fst_807_);
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 0, v_e_729_);
v___x_826_ = v___x_820_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_e_729_);
lean_ctor_set(v_reuseFailAlloc_830_, 1, v_snd_818_);
v___x_826_ = v_reuseFailAlloc_830_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
lean_object* v___x_828_; 
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 0, v___x_826_);
v___x_828_ = v___x_815_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v___x_826_);
lean_ctor_set(v_reuseFailAlloc_829_, 1, v_snd_813_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
}
}
}
}
case 8:
{
lean_object* v_declName_835_; lean_object* v_type_836_; lean_object* v_value_837_; lean_object* v_body_838_; uint8_t v_nondep_839_; lean_object* v___x_840_; lean_object* v_fst_841_; lean_object* v_snd_842_; lean_object* v_fst_843_; lean_object* v_snd_844_; lean_object* v___x_845_; lean_object* v_fst_846_; lean_object* v_snd_847_; lean_object* v_fst_848_; lean_object* v_snd_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v_fst_853_; lean_object* v_snd_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_877_; 
v_declName_835_ = lean_ctor_get(v_e_729_, 0);
v_type_836_ = lean_ctor_get(v_e_729_, 1);
v_value_837_ = lean_ctor_get(v_e_729_, 2);
v_body_838_ = lean_ctor_get(v_e_729_, 3);
v_nondep_839_ = lean_ctor_get_uint8(v_e_729_, sizeof(void*)*4 + 8);
lean_inc_n(v_offset_730_, 2);
lean_inc_ref(v_type_836_);
v___x_840_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_727_, v_d_728_, v_type_836_, v_offset_730_, v_a_731_, v_a_732_, v_a_733_);
v_fst_841_ = lean_ctor_get(v___x_840_, 0);
lean_inc(v_fst_841_);
v_snd_842_ = lean_ctor_get(v___x_840_, 1);
lean_inc(v_snd_842_);
lean_dec_ref(v___x_840_);
v_fst_843_ = lean_ctor_get(v_fst_841_, 0);
lean_inc(v_fst_843_);
v_snd_844_ = lean_ctor_get(v_fst_841_, 1);
lean_inc(v_snd_844_);
lean_dec(v_fst_841_);
lean_inc_ref(v_value_837_);
v___x_845_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_727_, v_d_728_, v_value_837_, v_offset_730_, v_snd_844_, v_a_732_, v_snd_842_);
v_fst_846_ = lean_ctor_get(v___x_845_, 0);
lean_inc(v_fst_846_);
v_snd_847_ = lean_ctor_get(v___x_845_, 1);
lean_inc(v_snd_847_);
lean_dec_ref(v___x_845_);
v_fst_848_ = lean_ctor_get(v_fst_846_, 0);
lean_inc(v_fst_848_);
v_snd_849_ = lean_ctor_get(v_fst_846_, 1);
lean_inc(v_snd_849_);
lean_dec(v_fst_846_);
v___x_850_ = lean_unsigned_to_nat(1u);
v___x_851_ = lean_nat_add(v_offset_730_, v___x_850_);
lean_dec(v_offset_730_);
lean_inc_ref(v_body_838_);
v___x_852_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_727_, v_d_728_, v_body_838_, v___x_851_, v_snd_849_, v_a_732_, v_snd_847_);
v_fst_853_ = lean_ctor_get(v___x_852_, 0);
v_snd_854_ = lean_ctor_get(v___x_852_, 1);
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_877_ == 0)
{
v___x_856_ = v___x_852_;
v_isShared_857_ = v_isSharedCheck_877_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_snd_854_);
lean_inc(v_fst_853_);
lean_dec(v___x_852_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_877_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v_fst_858_; lean_object* v_snd_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_876_; 
v_fst_858_ = lean_ctor_get(v_fst_853_, 0);
v_snd_859_ = lean_ctor_get(v_fst_853_, 1);
v_isSharedCheck_876_ = !lean_is_exclusive(v_fst_853_);
if (v_isSharedCheck_876_ == 0)
{
v___x_861_ = v_fst_853_;
v_isShared_862_ = v_isSharedCheck_876_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_snd_859_);
lean_inc(v_fst_858_);
lean_dec(v_fst_853_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_876_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
uint8_t v___y_864_; uint8_t v___x_874_; 
v___x_874_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_type_836_, v_fst_843_);
if (v___x_874_ == 0)
{
v___y_864_ = v___x_874_;
goto v___jp_863_;
}
else
{
uint8_t v___x_875_; 
v___x_875_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_value_837_, v_fst_848_);
v___y_864_ = v___x_875_;
goto v___jp_863_;
}
v___jp_863_:
{
if (v___y_864_ == 0)
{
lean_object* v___x_865_; 
lean_inc(v_declName_835_);
lean_del_object(v___x_861_);
lean_del_object(v___x_856_);
lean_dec_ref(v_e_729_);
v___x_865_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5(v_declName_835_, v_fst_843_, v_fst_848_, v_fst_858_, v_nondep_839_, v_snd_859_, v_a_732_, v_snd_854_);
return v___x_865_;
}
else
{
uint8_t v___x_866_; 
v___x_866_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_838_, v_fst_858_);
if (v___x_866_ == 0)
{
lean_object* v___x_867_; 
lean_inc(v_declName_835_);
lean_del_object(v___x_861_);
lean_del_object(v___x_856_);
lean_dec_ref(v_e_729_);
v___x_867_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5(v_declName_835_, v_fst_843_, v_fst_848_, v_fst_858_, v_nondep_839_, v_snd_859_, v_a_732_, v_snd_854_);
return v___x_867_;
}
else
{
lean_object* v___x_869_; 
lean_dec(v_fst_858_);
lean_dec(v_fst_848_);
lean_dec(v_fst_843_);
if (v_isShared_862_ == 0)
{
lean_ctor_set(v___x_861_, 0, v_e_729_);
v___x_869_ = v___x_861_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_e_729_);
lean_ctor_set(v_reuseFailAlloc_873_, 1, v_snd_859_);
v___x_869_ = v_reuseFailAlloc_873_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
lean_object* v___x_871_; 
if (v_isShared_857_ == 0)
{
lean_ctor_set(v___x_856_, 0, v___x_869_);
v___x_871_ = v___x_856_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v___x_869_);
lean_ctor_set(v_reuseFailAlloc_872_, 1, v_snd_854_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
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
lean_object* v_data_878_; lean_object* v_expr_879_; lean_object* v___x_880_; lean_object* v_fst_881_; lean_object* v_snd_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_900_; 
v_data_878_ = lean_ctor_get(v_e_729_, 0);
v_expr_879_ = lean_ctor_get(v_e_729_, 1);
lean_inc_ref(v_expr_879_);
v___x_880_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_727_, v_d_728_, v_expr_879_, v_offset_730_, v_a_731_, v_a_732_, v_a_733_);
v_fst_881_ = lean_ctor_get(v___x_880_, 0);
v_snd_882_ = lean_ctor_get(v___x_880_, 1);
v_isSharedCheck_900_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_900_ == 0)
{
v___x_884_ = v___x_880_;
v_isShared_885_ = v_isSharedCheck_900_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_snd_882_);
lean_inc(v_fst_881_);
lean_dec(v___x_880_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_900_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v_fst_886_; lean_object* v_snd_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_899_; 
v_fst_886_ = lean_ctor_get(v_fst_881_, 0);
v_snd_887_ = lean_ctor_get(v_fst_881_, 1);
v_isSharedCheck_899_ = !lean_is_exclusive(v_fst_881_);
if (v_isSharedCheck_899_ == 0)
{
v___x_889_ = v_fst_881_;
v_isShared_890_ = v_isSharedCheck_899_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_snd_887_);
lean_inc(v_fst_886_);
lean_dec(v_fst_881_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_899_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
uint8_t v___x_891_; 
v___x_891_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_expr_879_, v_fst_886_);
if (v___x_891_ == 0)
{
lean_object* v___x_892_; 
lean_inc(v_data_878_);
lean_del_object(v___x_889_);
lean_del_object(v___x_884_);
lean_dec_ref(v_e_729_);
v___x_892_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__6(v_data_878_, v_fst_886_, v_snd_887_, v_a_732_, v_snd_882_);
return v___x_892_;
}
else
{
lean_object* v___x_894_; 
lean_dec(v_fst_886_);
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 0, v_e_729_);
v___x_894_ = v___x_889_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_e_729_);
lean_ctor_set(v_reuseFailAlloc_898_, 1, v_snd_887_);
v___x_894_ = v_reuseFailAlloc_898_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
lean_object* v___x_896_; 
if (v_isShared_885_ == 0)
{
lean_ctor_set(v___x_884_, 0, v___x_894_);
v___x_896_ = v___x_884_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v___x_894_);
lean_ctor_set(v_reuseFailAlloc_897_, 1, v_snd_882_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
}
}
}
}
case 11:
{
lean_object* v_typeName_901_; lean_object* v_idx_902_; lean_object* v_struct_903_; lean_object* v___x_904_; lean_object* v_fst_905_; lean_object* v_snd_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_924_; 
v_typeName_901_ = lean_ctor_get(v_e_729_, 0);
v_idx_902_ = lean_ctor_get(v_e_729_, 1);
v_struct_903_ = lean_ctor_get(v_e_729_, 2);
lean_inc_ref(v_struct_903_);
v___x_904_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_727_, v_d_728_, v_struct_903_, v_offset_730_, v_a_731_, v_a_732_, v_a_733_);
v_fst_905_ = lean_ctor_get(v___x_904_, 0);
v_snd_906_ = lean_ctor_get(v___x_904_, 1);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_904_);
if (v_isSharedCheck_924_ == 0)
{
v___x_908_ = v___x_904_;
v_isShared_909_ = v_isSharedCheck_924_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_snd_906_);
lean_inc(v_fst_905_);
lean_dec(v___x_904_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_924_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v_fst_910_; lean_object* v_snd_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_923_; 
v_fst_910_ = lean_ctor_get(v_fst_905_, 0);
v_snd_911_ = lean_ctor_get(v_fst_905_, 1);
v_isSharedCheck_923_ = !lean_is_exclusive(v_fst_905_);
if (v_isSharedCheck_923_ == 0)
{
v___x_913_ = v_fst_905_;
v_isShared_914_ = v_isSharedCheck_923_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_snd_911_);
lean_inc(v_fst_910_);
lean_dec(v_fst_905_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_923_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
uint8_t v___x_915_; 
v___x_915_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_903_, v_fst_910_);
if (v___x_915_ == 0)
{
lean_object* v___x_916_; 
lean_inc(v_idx_902_);
lean_inc(v_typeName_901_);
lean_del_object(v___x_913_);
lean_del_object(v___x_908_);
lean_dec_ref(v_e_729_);
v___x_916_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__7(v_typeName_901_, v_idx_902_, v_fst_910_, v_snd_911_, v_a_732_, v_snd_906_);
return v___x_916_;
}
else
{
lean_object* v___x_918_; 
lean_dec(v_fst_910_);
if (v_isShared_914_ == 0)
{
lean_ctor_set(v___x_913_, 0, v_e_729_);
v___x_918_ = v___x_913_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_e_729_);
lean_ctor_set(v_reuseFailAlloc_922_, 1, v_snd_911_);
v___x_918_ = v_reuseFailAlloc_922_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
lean_object* v___x_920_; 
if (v_isShared_909_ == 0)
{
lean_ctor_set(v___x_908_, 0, v___x_918_);
v___x_920_ = v___x_908_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v___x_918_);
lean_ctor_set(v_reuseFailAlloc_921_, 1, v_snd_906_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_925_; lean_object* v___x_926_; 
lean_dec(v_offset_730_);
lean_dec_ref(v_e_729_);
v___x_925_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3);
v___x_926_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8(v___x_925_, v_a_731_, v_a_732_, v_a_733_);
return v___x_926_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(lean_object* v_s_927_, lean_object* v_d_928_, lean_object* v_e_929_, lean_object* v_offset_930_, lean_object* v_a_931_, uint8_t v_a_932_, lean_object* v_a_933_){
_start:
{
lean_object* v_key_934_; lean_object* v_snd_936_; lean_object* v___x_949_; 
lean_inc(v_offset_930_);
lean_inc_ref(v_e_929_);
v_key_934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_934_, 0, v_e_929_);
lean_ctor_set(v_key_934_, 1, v_offset_930_);
v___x_949_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___redArg(v_a_931_, v_key_934_);
if (lean_obj_tag(v___x_949_) == 1)
{
lean_object* v_val_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
lean_dec_ref(v_key_934_);
lean_dec(v_offset_930_);
lean_dec_ref(v_e_929_);
v_val_950_ = lean_ctor_get(v___x_949_, 0);
lean_inc(v_val_950_);
lean_dec_ref(v___x_949_);
v___x_951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_951_, 0, v_val_950_);
lean_ctor_set(v___x_951_, 1, v_a_931_);
v___x_952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_952_, 0, v___x_951_);
lean_ctor_set(v___x_952_, 1, v_a_933_);
return v___x_952_;
}
else
{
lean_object* v_s_u2081_953_; lean_object* v___x_954_; uint8_t v___x_955_; 
lean_dec(v___x_949_);
v_s_u2081_953_ = lean_nat_add(v_s_927_, v_offset_930_);
v___x_954_ = l_Lean_Expr_looseBVarRange(v_e_929_);
v___x_955_ = lean_nat_dec_le(v___x_954_, v_s_u2081_953_);
lean_dec(v___x_954_);
if (v___x_955_ == 0)
{
if (lean_obj_tag(v_e_929_) == 0)
{
lean_object* v_deBruijnIndex_956_; uint8_t v___x_957_; 
v_deBruijnIndex_956_ = lean_ctor_get(v_e_929_, 0);
v___x_957_ = lean_nat_dec_le(v_s_u2081_953_, v_deBruijnIndex_956_);
lean_dec(v_s_u2081_953_);
if (v___x_957_ == 0)
{
v_snd_936_ = v_a_933_;
goto v___jp_935_;
}
else
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v_fst_960_; lean_object* v_snd_961_; lean_object* v___x_962_; 
lean_inc(v_deBruijnIndex_956_);
lean_dec_ref(v_e_929_);
lean_dec(v_offset_930_);
v___x_958_ = lean_nat_add(v_deBruijnIndex_956_, v_d_928_);
lean_dec(v_deBruijnIndex_956_);
v___x_959_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0___redArg(v___x_958_, v_a_933_);
v_fst_960_ = lean_ctor_get(v___x_959_, 0);
lean_inc(v_fst_960_);
v_snd_961_ = lean_ctor_get(v___x_959_, 1);
lean_inc(v_snd_961_);
lean_dec_ref(v___x_959_);
v___x_962_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_934_, v_fst_960_, v_a_931_, v_a_932_, v_snd_961_);
return v___x_962_;
}
}
else
{
lean_dec(v_s_u2081_953_);
v_snd_936_ = v_a_933_;
goto v___jp_935_;
}
}
else
{
lean_object* v___x_963_; 
lean_dec(v_s_u2081_953_);
lean_dec(v_offset_930_);
v___x_963_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_934_, v_e_929_, v_a_931_, v_a_932_, v_a_933_);
return v___x_963_;
}
}
v___jp_935_:
{
switch(lean_obj_tag(v_e_929_))
{
case 9:
{
lean_object* v___x_937_; 
lean_dec(v_offset_930_);
v___x_937_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_934_, v_e_929_, v_a_931_, v_a_932_, v_snd_936_);
return v___x_937_;
}
case 2:
{
lean_object* v___x_938_; 
lean_dec(v_offset_930_);
v___x_938_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_934_, v_e_929_, v_a_931_, v_a_932_, v_snd_936_);
return v___x_938_;
}
case 0:
{
lean_object* v___x_939_; 
lean_dec(v_offset_930_);
v___x_939_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_934_, v_e_929_, v_a_931_, v_a_932_, v_snd_936_);
return v___x_939_;
}
case 1:
{
lean_object* v___x_940_; 
lean_dec(v_offset_930_);
v___x_940_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_934_, v_e_929_, v_a_931_, v_a_932_, v_snd_936_);
return v___x_940_;
}
case 4:
{
lean_object* v___x_941_; 
lean_dec(v_offset_930_);
v___x_941_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_934_, v_e_929_, v_a_931_, v_a_932_, v_snd_936_);
return v___x_941_;
}
case 3:
{
lean_object* v___x_942_; 
lean_dec(v_offset_930_);
v___x_942_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_934_, v_e_929_, v_a_931_, v_a_932_, v_snd_936_);
return v___x_942_;
}
default: 
{
lean_object* v___x_943_; lean_object* v_fst_944_; lean_object* v_snd_945_; lean_object* v_fst_946_; lean_object* v_snd_947_; lean_object* v___x_948_; 
v___x_943_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0(v_s_927_, v_d_928_, v_e_929_, v_offset_930_, v_a_931_, v_a_932_, v_snd_936_);
v_fst_944_ = lean_ctor_get(v___x_943_, 0);
lean_inc(v_fst_944_);
v_snd_945_ = lean_ctor_get(v___x_943_, 1);
lean_inc(v_snd_945_);
lean_dec_ref(v___x_943_);
v_fst_946_ = lean_ctor_get(v_fst_944_, 0);
lean_inc(v_fst_946_);
v_snd_947_ = lean_ctor_get(v_fst_944_, 1);
lean_inc(v_snd_947_);
lean_dec(v_fst_944_);
v___x_948_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_934_, v_fst_946_, v_snd_947_, v_a_932_, v_snd_945_);
return v___x_948_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0___boxed(lean_object* v_s_964_, lean_object* v_d_965_, lean_object* v_e_966_, lean_object* v_offset_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_){
_start:
{
uint8_t v_a_boxed_971_; lean_object* v_res_972_; 
v_a_boxed_971_ = lean_unbox(v_a_969_);
v_res_972_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_964_, v_d_965_, v_e_966_, v_offset_967_, v_a_968_, v_a_boxed_971_, v_a_970_);
lean_dec(v_d_965_);
lean_dec(v_s_964_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0___boxed(lean_object* v_s_973_, lean_object* v_d_974_, lean_object* v_e_975_, lean_object* v_offset_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_){
_start:
{
uint8_t v_a_boxed_980_; lean_object* v_res_981_; 
v_a_boxed_980_ = lean_unbox(v_a_978_);
v_res_981_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0(v_s_973_, v_d_974_, v_e_975_, v_offset_976_, v_a_977_, v_a_boxed_980_, v_a_979_);
lean_dec(v_d_974_);
lean_dec(v_s_973_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_liftLooseBVarsS_x27(lean_object* v_e_982_, lean_object* v_s_983_, lean_object* v_d_984_, uint8_t v_a_985_, lean_object* v_a_986_){
_start:
{
lean_object* v___x_987_; uint8_t v___x_988_; 
v___x_987_ = l_Lean_Expr_looseBVarRange(v_e_982_);
v___x_988_ = lean_nat_dec_le(v___x_987_, v_s_983_);
lean_dec(v___x_987_);
if (v___x_988_ == 0)
{
lean_object* v___x_989_; lean_object* v_snd_991_; 
v___x_989_ = lean_unsigned_to_nat(0u);
if (lean_obj_tag(v_e_982_) == 0)
{
lean_object* v_deBruijnIndex_1011_; uint8_t v___x_1012_; 
v_deBruijnIndex_1011_ = lean_ctor_get(v_e_982_, 0);
v___x_1012_ = lean_nat_dec_le(v_s_983_, v_deBruijnIndex_1011_);
if (v___x_1012_ == 0)
{
v_snd_991_ = v_a_986_;
goto v___jp_990_;
}
else
{
lean_object* v___x_1013_; lean_object* v___x_1014_; 
lean_inc(v_deBruijnIndex_1011_);
lean_dec_ref(v_e_982_);
v___x_1013_ = lean_nat_add(v_deBruijnIndex_1011_, v_d_984_);
lean_dec(v_deBruijnIndex_1011_);
v___x_1014_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0___redArg(v___x_1013_, v_a_986_);
return v___x_1014_;
}
}
else
{
v_snd_991_ = v_a_986_;
goto v___jp_990_;
}
v___jp_990_:
{
switch(lean_obj_tag(v_e_982_))
{
case 9:
{
lean_object* v___x_992_; 
v___x_992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_992_, 0, v_e_982_);
lean_ctor_set(v___x_992_, 1, v_snd_991_);
return v___x_992_;
}
case 2:
{
lean_object* v___x_993_; 
v___x_993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_993_, 0, v_e_982_);
lean_ctor_set(v___x_993_, 1, v_snd_991_);
return v___x_993_;
}
case 0:
{
lean_object* v___x_994_; 
v___x_994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_994_, 0, v_e_982_);
lean_ctor_set(v___x_994_, 1, v_snd_991_);
return v___x_994_;
}
case 1:
{
lean_object* v___x_995_; 
v___x_995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_995_, 0, v_e_982_);
lean_ctor_set(v___x_995_, 1, v_snd_991_);
return v___x_995_;
}
case 4:
{
lean_object* v___x_996_; 
v___x_996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_996_, 0, v_e_982_);
lean_ctor_set(v___x_996_, 1, v_snd_991_);
return v___x_996_;
}
case 3:
{
lean_object* v___x_997_; 
v___x_997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_997_, 0, v_e_982_);
lean_ctor_set(v___x_997_, 1, v_snd_991_);
return v___x_997_;
}
default: 
{
lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v_fst_1000_; lean_object* v_snd_1001_; lean_object* v_fst_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1009_; 
v___x_998_ = lean_obj_once(&l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1, &l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1_once, _init_l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1);
v___x_999_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0(v_s_983_, v_d_984_, v_e_982_, v___x_989_, v___x_998_, v_a_985_, v_snd_991_);
v_fst_1000_ = lean_ctor_get(v___x_999_, 0);
lean_inc(v_fst_1000_);
v_snd_1001_ = lean_ctor_get(v___x_999_, 1);
lean_inc(v_snd_1001_);
lean_dec_ref(v___x_999_);
v_fst_1002_ = lean_ctor_get(v_fst_1000_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v_fst_1000_);
if (v_isSharedCheck_1009_ == 0)
{
lean_object* v_unused_1010_; 
v_unused_1010_ = lean_ctor_get(v_fst_1000_, 1);
lean_dec(v_unused_1010_);
v___x_1004_ = v_fst_1000_;
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_fst_1002_);
lean_dec(v_fst_1000_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1007_; 
if (v_isShared_1005_ == 0)
{
lean_ctor_set(v___x_1004_, 1, v_snd_1001_);
v___x_1007_ = v___x_1004_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_fst_1002_);
lean_ctor_set(v_reuseFailAlloc_1008_, 1, v_snd_1001_);
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
else
{
lean_object* v___x_1015_; 
v___x_1015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1015_, 0, v_e_982_);
lean_ctor_set(v___x_1015_, 1, v_a_986_);
return v___x_1015_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_liftLooseBVarsS_x27___boxed(lean_object* v_e_1016_, lean_object* v_s_1017_, lean_object* v_d_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_){
_start:
{
uint8_t v_a_boxed_1021_; lean_object* v_res_1022_; 
v_a_boxed_1021_ = lean_unbox(v_a_1019_);
v_res_1022_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(v_e_1016_, v_s_1017_, v_d_1018_, v_a_boxed_1021_, v_a_1020_);
lean_dec(v_d_1018_);
lean_dec(v_s_1017_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_liftLooseBVarsS___redArg(lean_object* v_e_1023_, lean_object* v_s_1024_, lean_object* v_d_1025_, lean_object* v_a_1026_){
_start:
{
lean_object* v___x_1028_; lean_object* v_share_1029_; lean_object* v_maxFVar_1030_; lean_object* v_proofInstInfo_1031_; lean_object* v_inferType_1032_; lean_object* v_getLevel_1033_; lean_object* v_congrInfo_1034_; lean_object* v_defEqI_1035_; lean_object* v_extensions_1036_; lean_object* v_issues_1037_; lean_object* v_canon_1038_; uint8_t v_debug_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1074_; 
v___x_1028_ = lean_st_ref_take(v_a_1026_);
v_share_1029_ = lean_ctor_get(v___x_1028_, 0);
v_maxFVar_1030_ = lean_ctor_get(v___x_1028_, 1);
v_proofInstInfo_1031_ = lean_ctor_get(v___x_1028_, 2);
v_inferType_1032_ = lean_ctor_get(v___x_1028_, 3);
v_getLevel_1033_ = lean_ctor_get(v___x_1028_, 4);
v_congrInfo_1034_ = lean_ctor_get(v___x_1028_, 5);
v_defEqI_1035_ = lean_ctor_get(v___x_1028_, 6);
v_extensions_1036_ = lean_ctor_get(v___x_1028_, 7);
v_issues_1037_ = lean_ctor_get(v___x_1028_, 8);
v_canon_1038_ = lean_ctor_get(v___x_1028_, 9);
v_debug_1039_ = lean_ctor_get_uint8(v___x_1028_, sizeof(void*)*10);
v_isSharedCheck_1074_ = !lean_is_exclusive(v___x_1028_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1041_ = v___x_1028_;
v_isShared_1042_ = v_isSharedCheck_1074_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_canon_1038_);
lean_inc(v_issues_1037_);
lean_inc(v_extensions_1036_);
lean_inc(v_defEqI_1035_);
lean_inc(v_congrInfo_1034_);
lean_inc(v_getLevel_1033_);
lean_inc(v_inferType_1032_);
lean_inc(v_proofInstInfo_1031_);
lean_inc(v_maxFVar_1030_);
lean_inc(v_share_1029_);
lean_dec(v___x_1028_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1074_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1043_; lean_object* v___x_1045_; 
v___x_1043_ = lean_obj_once(&l_Lean_Meta_Sym_lowerLooseBVarsS___redArg___closed__0, &l_Lean_Meta_Sym_lowerLooseBVarsS___redArg___closed__0_once, _init_l_Lean_Meta_Sym_lowerLooseBVarsS___redArg___closed__0);
if (v_isShared_1042_ == 0)
{
lean_ctor_set(v___x_1041_, 0, v___x_1043_);
v___x_1045_ = v___x_1041_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v___x_1043_);
lean_ctor_set(v_reuseFailAlloc_1073_, 1, v_maxFVar_1030_);
lean_ctor_set(v_reuseFailAlloc_1073_, 2, v_proofInstInfo_1031_);
lean_ctor_set(v_reuseFailAlloc_1073_, 3, v_inferType_1032_);
lean_ctor_set(v_reuseFailAlloc_1073_, 4, v_getLevel_1033_);
lean_ctor_set(v_reuseFailAlloc_1073_, 5, v_congrInfo_1034_);
lean_ctor_set(v_reuseFailAlloc_1073_, 6, v_defEqI_1035_);
lean_ctor_set(v_reuseFailAlloc_1073_, 7, v_extensions_1036_);
lean_ctor_set(v_reuseFailAlloc_1073_, 8, v_issues_1037_);
lean_ctor_set(v_reuseFailAlloc_1073_, 9, v_canon_1038_);
lean_ctor_set_uint8(v_reuseFailAlloc_1073_, sizeof(void*)*10, v_debug_1039_);
v___x_1045_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; uint8_t v_debug_1048_; lean_object* v___x_1049_; lean_object* v_fst_1050_; lean_object* v_snd_1051_; lean_object* v___x_1052_; lean_object* v_maxFVar_1053_; lean_object* v_proofInstInfo_1054_; lean_object* v_inferType_1055_; lean_object* v_getLevel_1056_; lean_object* v_congrInfo_1057_; lean_object* v_defEqI_1058_; lean_object* v_extensions_1059_; lean_object* v_issues_1060_; lean_object* v_canon_1061_; uint8_t v_debug_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1071_; 
v___x_1046_ = lean_st_ref_set(v_a_1026_, v___x_1045_);
v___x_1047_ = lean_st_ref_get(v_a_1026_);
v_debug_1048_ = lean_ctor_get_uint8(v___x_1047_, sizeof(void*)*10);
lean_dec(v___x_1047_);
v___x_1049_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(v_e_1023_, v_s_1024_, v_d_1025_, v_debug_1048_, v_share_1029_);
v_fst_1050_ = lean_ctor_get(v___x_1049_, 0);
lean_inc(v_fst_1050_);
v_snd_1051_ = lean_ctor_get(v___x_1049_, 1);
lean_inc(v_snd_1051_);
lean_dec_ref(v___x_1049_);
v___x_1052_ = lean_st_ref_take(v_a_1026_);
v_maxFVar_1053_ = lean_ctor_get(v___x_1052_, 1);
v_proofInstInfo_1054_ = lean_ctor_get(v___x_1052_, 2);
v_inferType_1055_ = lean_ctor_get(v___x_1052_, 3);
v_getLevel_1056_ = lean_ctor_get(v___x_1052_, 4);
v_congrInfo_1057_ = lean_ctor_get(v___x_1052_, 5);
v_defEqI_1058_ = lean_ctor_get(v___x_1052_, 6);
v_extensions_1059_ = lean_ctor_get(v___x_1052_, 7);
v_issues_1060_ = lean_ctor_get(v___x_1052_, 8);
v_canon_1061_ = lean_ctor_get(v___x_1052_, 9);
v_debug_1062_ = lean_ctor_get_uint8(v___x_1052_, sizeof(void*)*10);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1071_ == 0)
{
lean_object* v_unused_1072_; 
v_unused_1072_ = lean_ctor_get(v___x_1052_, 0);
lean_dec(v_unused_1072_);
v___x_1064_ = v___x_1052_;
v_isShared_1065_ = v_isSharedCheck_1071_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_canon_1061_);
lean_inc(v_issues_1060_);
lean_inc(v_extensions_1059_);
lean_inc(v_defEqI_1058_);
lean_inc(v_congrInfo_1057_);
lean_inc(v_getLevel_1056_);
lean_inc(v_inferType_1055_);
lean_inc(v_proofInstInfo_1054_);
lean_inc(v_maxFVar_1053_);
lean_dec(v___x_1052_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1071_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1067_; 
if (v_isShared_1065_ == 0)
{
lean_ctor_set(v___x_1064_, 0, v_snd_1051_);
v___x_1067_ = v___x_1064_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_snd_1051_);
lean_ctor_set(v_reuseFailAlloc_1070_, 1, v_maxFVar_1053_);
lean_ctor_set(v_reuseFailAlloc_1070_, 2, v_proofInstInfo_1054_);
lean_ctor_set(v_reuseFailAlloc_1070_, 3, v_inferType_1055_);
lean_ctor_set(v_reuseFailAlloc_1070_, 4, v_getLevel_1056_);
lean_ctor_set(v_reuseFailAlloc_1070_, 5, v_congrInfo_1057_);
lean_ctor_set(v_reuseFailAlloc_1070_, 6, v_defEqI_1058_);
lean_ctor_set(v_reuseFailAlloc_1070_, 7, v_extensions_1059_);
lean_ctor_set(v_reuseFailAlloc_1070_, 8, v_issues_1060_);
lean_ctor_set(v_reuseFailAlloc_1070_, 9, v_canon_1061_);
lean_ctor_set_uint8(v_reuseFailAlloc_1070_, sizeof(void*)*10, v_debug_1062_);
v___x_1067_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1068_ = lean_st_ref_set(v_a_1026_, v___x_1067_);
v___x_1069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1069_, 0, v_fst_1050_);
return v___x_1069_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_liftLooseBVarsS___redArg___boxed(lean_object* v_e_1075_, lean_object* v_s_1076_, lean_object* v_d_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_){
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l_Lean_Meta_Sym_liftLooseBVarsS___redArg(v_e_1075_, v_s_1076_, v_d_1077_, v_a_1078_);
lean_dec(v_a_1078_);
lean_dec(v_d_1077_);
lean_dec(v_s_1076_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_liftLooseBVarsS(lean_object* v_e_1081_, lean_object* v_s_1082_, lean_object* v_d_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_){
_start:
{
lean_object* v___x_1091_; 
v___x_1091_ = l_Lean_Meta_Sym_liftLooseBVarsS___redArg(v_e_1081_, v_s_1082_, v_d_1083_, v_a_1085_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_liftLooseBVarsS___boxed(lean_object* v_e_1092_, lean_object* v_s_1093_, lean_object* v_d_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l_Lean_Meta_Sym_liftLooseBVarsS(v_e_1092_, v_s_1093_, v_d_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_);
lean_dec(v_a_1100_);
lean_dec_ref(v_a_1099_);
lean_dec(v_a_1098_);
lean_dec_ref(v_a_1097_);
lean_dec(v_a_1096_);
lean_dec_ref(v_a_1095_);
lean_dec(v_d_1094_);
lean_dec(v_s_1093_);
return v_res_1102_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_ReplaceS(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_LooseBVarsS(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Sym_ReplaceS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_LooseBVarsS(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_ReplaceS(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_LooseBVarsS(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_ReplaceS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_LooseBVarsS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_LooseBVarsS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_LooseBVarsS(builtin);
}
#ifdef __cplusplus
}
#endif
